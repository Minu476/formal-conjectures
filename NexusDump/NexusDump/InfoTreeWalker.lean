module

public meta import Mathlib.Lean.Elab.InfoTree
public meta import Mathlib.Lean.ContextInfo
public meta import Lean.Server.InfoUtils
public meta import Lean.Elab.Command
import Lean.Data.Options
import Lean.Data.Json.Basic
import Lean.Data.Json.FromToJson.Basic
import Lean.Server.InfoUtils
import Lean.Meta.Basic
import Lean.CoreM
import Lean.Elab.Command

public meta section

open Lean Elab Command Meta

namespace NexusLean.InfoTreeWalker

namespace Lean.Elab.InfoTree

/-- Monadic variant of `InfoTree.foldInfo` used for command elaboration. -/
def foldInfoM {α m} [Monad m] (f : ContextInfo → Info → α → m α) (init : α) : InfoTree → m α :=
  InfoTree.foldInfo (fun ctx i ma => do f ctx i (← ma)) (pure init)

end Lean.Elab.InfoTree

structure TransitionRow where
  module_source : String
  theorem_source : String
  theorem_namespace : String
  theorem_statement : String
  goal_before : String
  goal_before_hash : String := ""
  tactic_raw : String
  goals_after : Array String
  goals_after_hashes : Array String := #[]
  premises : Array String := #[]
  success : Bool

instance instToJsonTransitionRow : ToJson TransitionRow :=
  ⟨fun r => Json.mkObj [
    ("module_source", toJson r.module_source),
    ("theorem_source", toJson r.theorem_source),
    ("theorem_namespace", toJson r.theorem_namespace),
    ("theorem_statement", toJson r.theorem_statement),
    ("goal_before", toJson r.goal_before),
    ("goal_before_hash", toJson r.goal_before_hash),
    ("tactic_raw", toJson r.tactic_raw),
    ("goals_after", toJson r.goals_after),
    ("goals_after_hashes", toJson r.goals_after_hashes),
    ("premises", toJson r.premises),
    ("success", toJson r.success)
  ]⟩

register_option nexus.dumpInfoTreesPath : String := {
  defValue := ""
  descr := "If non-empty, append InfoTree tactic transition JSONL rows for each elaborated command to this path."
}

private def renderExpr (e : Expr) : MetaM String := do
  return (← ppExpr (← instantiateMVars e)).pretty

private def renderGoal (mctx : MetavarContext) (goal : MVarId) : MetaM String := do
  match mctx.decls.find? goal with
  | none =>
      return goal.name.toString
  | some decl =>
      renderExpr decl.type

private def renderGoals (mctx : MetavarContext) (goals : Array MVarId) : MetaM (Array String) := do
  goals.mapM (renderGoal mctx)

private def renderTheoremStatement (declName : Name) : MetaM String := do
  let some constInfo := (← getEnv).find? declName
    | return ""
  renderExpr constInfo.type

private def runMetaMInCommandElabM
    (ci : ContextInfo)
    (lctx : LocalContext)
    (x : MetaM String)
    : CommandElabM String := do
  let x := (withLocalInstances lctx.decls.toList.reduceOption x).run { lctx := lctx } { mctx := ci.mctx }
  let initHeartbeats ← IO.getNumHeartbeats
  let ((a, _), st) ←
    x.toIO {
      options := ci.options
      currNamespace := ci.currNamespace
      openDecls := ci.openDecls
      fileName := (← getFileName)
      fileMap := ci.fileMap
      initHeartbeats
    } {
      env := ci.env
      ngen := ci.ngen
      infoState := ← getInfoState
      traceState := ← getTraceState
    }
  modify fun s =>
    { s with
      messages := s.messages ++ st.messages
      infoState := st.infoState
      traceState := st.traceState
    }
  return a

private def textHash (s : String) : String :=
  toString (hash s)

private def isNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.'

private def extractDottedRefs (s : String) : Array String :=
  let chars := s.toList
  let (refs, token) := chars.foldl (init := (#[], "")) fun (refs, tok) ch =>
    if isNameChar ch then
      (refs, tok.push ch)
    else if tok.isEmpty then
      (refs, "")
    else if tok.contains "." then
      (refs.push tok, "")
    else
      (refs, "")
  let refs := if !token.isEmpty && token.contains "." then refs.push token else refs
  refs

private def isUsefulRef (ref : String) : Bool :=
  ref.contains "." &&
  !ref.startsWith "._" &&
  !ref.startsWith "Term." &&
  !ref.contains "_hygCtx" &&
  !ref.contains "._hyg."

private partial def collectConstNames (e : Expr) (acc : NameSet := {}) : NameSet :=
  match e with
  | .const n _ => acc.insert n
  | .app f a =>
      let acc := collectConstNames f acc
      collectConstNames a acc
  | .lam _ t b _ =>
      let acc := collectConstNames t acc
      collectConstNames b acc
  | .forallE _ t b _ =>
      let acc := collectConstNames t acc
      collectConstNames b acc
  | .letE _ t v b _ =>
      let acc := collectConstNames t acc
      let acc := collectConstNames v acc
      collectConstNames b acc
  | .mdata _ b => collectConstNames b acc
  | .proj _ _ b => collectConstNames b acc
  | _ => acc

private partial def collectIdentNames (stx : Syntax) (acc : NameSet := {}) : NameSet :=
  let acc :=
    if stx.isIdent then
      acc.insert stx.getId
    else
      acc
  stx.getArgs.foldl (init := acc) fun acc child => collectIdentNames child acc

private def renderConstType (name : Name) : MetaM String := do
  let some constInfo := (← getEnv).find? name
    | return ""
  renderExpr constInfo.type

private def isUsefulConst (n : Name) : Bool :=
  !n.isInternal && n != Name.anonymous

private def makeRowsFromTermInfo (moduleSource : String) (ci : ContextInfo) (ti : TermInfo) : CommandElabM (Array TransitionRow) := do
  let theoremName := ci.parentDecl?.getD Name.anonymous
  if theoremName == Name.anonymous then
    return #[]
  let theoremSource := theoremName.toString
  let theoremNamespace := theoremName.getPrefix.toString
  let theoremStatement := ← liftCoreM <| MetaM.run' <| renderTheoremStatement theoremName
  let stxText := toString ti.stx
  let goalBefore := ← runMetaMInCommandElabM ci ti.lctx do
    renderExpr (← inferType ti.expr)
  let consts : Array Name :=
    ((collectConstNames ti.expr).toList ++ (collectIdentNames ti.stx).toList
      |>.filter isUsefulConst).toArray
  let mut seenConsts : NameSet := {}
  let mut seenRefs : Array String := #[]
  let mut rows : Array TransitionRow := #[]
  for c in consts do
    if seenConsts.contains c then
      continue
    seenConsts := seenConsts.insert c
    let afterGoal := ← runMetaMInCommandElabM ci ti.lctx do
      renderConstType c
    if afterGoal.isEmpty then
      continue
    rows := rows.push {
      module_source := moduleSource
      theorem_source := theoremSource
      theorem_namespace := theoremNamespace
      theorem_statement := theoremStatement
      goal_before := goalBefore
      goal_before_hash := textHash goalBefore
      tactic_raw := c.toString
      goals_after := #[afterGoal]
      goals_after_hashes := #[textHash afterGoal]
      premises := #[]
      success := true
    }
    seenRefs := seenRefs.push c.toString
  for ref in extractDottedRefs stxText do
    if seenRefs.contains ref || !isUsefulRef ref then
      continue
    seenRefs := seenRefs.push ref
    rows := rows.push {
      module_source := moduleSource
      theorem_source := theoremSource
      theorem_namespace := theoremNamespace
      theorem_statement := theoremStatement
      goal_before := goalBefore
      goal_before_hash := textHash goalBefore
      tactic_raw := ref
      goals_after := #[goalBefore]
      goals_after_hashes := #[textHash goalBefore]
      premises := #[]
      success := true
    }
  return rows

private def appendCommandRefs (cmdStx : Syntax) (rows : Array TransitionRow) : Array TransitionRow :=
  if rows.isEmpty then
    rows
  else
    match rows[0]? with
    | none => rows
    | some anchor =>
        Id.run do
          let mut out := rows
          let mut seen : Array String := rows.map (fun r => r.tactic_raw)
          for ref in extractDottedRefs (toString cmdStx) do
            if seen.contains ref || !isUsefulRef ref then
              continue
            seen := seen.push ref
            out := out.push {
              anchor with
              tactic_raw := ref
              goals_after := #[anchor.goal_before]
              goals_after_hashes := #[textHash anchor.goal_before]
            }
          out

private def makeRow (moduleSource : String) (ci : ContextInfo) (tac : TacticInfo) : CommandElabM (Option TransitionRow) := do
  if tac.goalsBefore.isEmpty then
    return none
  let theoremName := ci.parentDecl?.getD Name.anonymous
  let theoremSource := if theoremName == Name.anonymous then "<unknown>" else theoremName.toString
  let theoremNamespace := if theoremName == Name.anonymous then "" else theoremName.getPrefix.toString
  let theoremStatement ←
    if theoremName == Name.anonymous then
      pure ""
    else
      liftCoreM <| MetaM.run' <| renderTheoremStatement theoremName
  let goalBeforeLines := ← liftCoreM <| MetaM.run' <| renderGoals tac.mctxBefore tac.goalsBefore.toArray
  let goalsAfter := ← liftCoreM <| MetaM.run' <| renderGoals tac.mctxAfter tac.goalsAfter.toArray
  let goalBefore := String.intercalate "\n---\n" goalBeforeLines.toList
  let tacticRaw := toString tac.stx
  return some {
    module_source := moduleSource
    theorem_source := theoremSource
    theorem_namespace := theoremNamespace
    theorem_statement := theoremStatement
    goal_before := goalBefore
    tactic_raw := tacticRaw
    goals_after := goalsAfter
    premises := #[]
    success := tac.goalsAfter.isEmpty
  }

private def collectRowsFromTrees
    (moduleSource : String)
    (trees : Array InfoTree)
    : CommandElabM (Nat × Nat × Array TransitionRow) := do
  let mut rows : Array TransitionRow := #[]
  let mut tacticInfos : Nat := 0
  let mut termInfos : Nat := 0
  for tree in trees do
    let (treeRows, treeTacticInfos, treeTermInfos) ← tree.foldInfoM (init := (rows, tacticInfos, termInfos)) fun ci info acc => do
      let (accRows, accTacticInfos, accTermInfos) := acc
      match info with
      | .ofTacticInfo tac =>
          let accTacticInfos := accTacticInfos + 1
          match (← makeRow moduleSource ci tac) with
          | some row => return (accRows.push row, accTacticInfos, accTermInfos)
          | none => return (accRows, accTacticInfos, accTermInfos)
      | .ofTermInfo ti =>
          let accTermInfos := accTermInfos + 1
          let termRows ← makeRowsFromTermInfo moduleSource ci ti
          return (accRows ++ termRows, accTacticInfos, accTermInfos)
      | _ => return (accRows, accTacticInfos, accTermInfos)
    rows := treeRows
    tacticInfos := treeTacticInfos
    termInfos := treeTermInfos
  return (tacticInfos, termInfos, rows)

private def appendRowsJsonl (outPath : String) (rows : Array TransitionRow) : IO Unit := do
  if rows.isEmpty then
    return
  let outFile := System.FilePath.mk outPath
  IO.FS.createDirAll <| outFile.parent.getD "."
  let jsonLines := rows.map (fun row => toJson row |>.compress)
  let payload := String.intercalate "\n" jsonLines.toList ++ "\n"
  IO.FS.withFile outPath IO.FS.Mode.append fun h => h.putStr payload

def nexusDumpLinter : Linter where
  run := fun cmdStx => do
      let outPath := nexus.dumpInfoTreesPath.get (← getOptions)
      let moduleSource := (← getFileName)
      let trees := (← get).infoState.trees.toArray
      logInfo m!"InfoTree linter: cmd={cmdStx.getKind}, outPath='{outPath}', trees={trees.size}"
      if outPath.isEmpty then
        return
      let (tacticInfos, termInfos, rows) ← collectRowsFromTrees moduleSource trees
      liftIO <| appendRowsJsonl outPath rows
      logInfo m!"InfoTree linter dump: cmd={cmdStx.getKind}, trees={trees.size}, tacticInfos={tacticInfos}, termInfos={termInfos}, emitted={rows.size}, out={outPath}"

initialize addLinter nexusDumpLinter

syntax (name := dumpInfoTreesCmd) "#dump_info_trees" str : command
syntax (name := dumpInfoTreesInCmd) "#dump_info_trees_in" command str : command

@[command_elab dumpInfoTreesInCmd]
public def elabDumpInfoTreesIn : CommandElab := fun stx => do
  let cmdStx := stx[1]
  let some outPath := stx[2].isStrLit?
    | throwErrorAt stx "expected a string literal output path"
  modifyInfoState fun s => { s with enabled := true }
  elabCommand cmdStx
  let moduleSource := (← getFileName)
  let trees := (← get).infoState.trees.toArray
  let (tacticInfos, termInfos, rows0) ← collectRowsFromTrees moduleSource trees
  let rows := appendCommandRefs cmdStx rows0
  liftIO do
    let outFile := System.FilePath.mk outPath
    IO.FS.createDirAll <| outFile.parent.getD "."
    IO.FS.writeFile outPath ""
  liftIO <| appendRowsJsonl outPath rows
  logInfo m!"InfoTree dump(in): trees={trees.size}, tacticInfos={tacticInfos}, termInfos={termInfos}, emitted={rows.size}, out={outPath}"

@[command_elab dumpInfoTreesCmd]
public def elabDumpInfoTrees : CommandElab := fun stx => do
  let some outPath := stx[1].isStrLit?
    | throwErrorAt stx "expected a string literal output path"
  let moduleSource := (← getFileName)
  let trees := (← get).infoState.trees.toArray
  let (tacticInfos, termInfos, rows) ← collectRowsFromTrees moduleSource trees
  liftIO do
    let outFile := System.FilePath.mk outPath
    IO.FS.createDirAll <| outFile.parent.getD "."
    IO.FS.writeFile outPath ""
  liftIO <| appendRowsJsonl outPath rows
  logInfo m!"InfoTree dump: trees={trees.size}, tacticInfos={tacticInfos}, termInfos={termInfos}, emitted={rows.size}, out={outPath}"

end NexusLean.InfoTreeWalker