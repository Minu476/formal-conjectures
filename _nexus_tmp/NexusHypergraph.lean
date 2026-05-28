/-
  NexusHypergraph.lean

  In-memory hypergraph of proven mathematical facts.
  Nodes  = canonicalized goal shapes (proven sub-problems)
  Edges  = Mathlib4 functions connecting them
  Search = AND/OR backward chaining

  Architecture:
    - Lives entirely in Lean — no serialization, no external DB
    - Canonicalization via Expr.hash (de Bruijn indices — bound var names irrelevant)
    - Single output per edge
    - Built directly from Lean Environment

  Run: cd formal-conjectures && lake env lean _nexus_tmp/NexusHypergraph.lean
-/

-- Fix 1: use ProblemImports (→ Mathlib/Batteries). Use Std.HashMap / Std.HashSet
--         with explicit prefix — bare HashMap/HashSet are not in scope (confirmed
--         by compiler; the whole formal-conjectures codebase uses Std.HashMap too).
import FormalConjectures.Util.ProblemImports

open Lean Meta Elab

namespace NexusHypergraph

-- ═══════════════════════════════════════════
--  Data model
-- ═══════════════════════════════════════════

structure GoalNode where
  hash     : UInt64
  declName : Name
  exprStr  : String
  isAxiom  : Bool := false
  deriving Inhabited, Repr

structure HyperEdge where
  functionName : Name
  inputHashes  : Array UInt64
  outputHash   : UInt64
  deriving Inhabited, Repr

inductive SearchResult where
  | proved     (steps : Array (Name × UInt64)) (visited : Nat)
  | notProved  (missing : Array UInt64) (visited : Nat)
  deriving Inhabited, Repr

-- ═══════════════════════════════════════════
--  Hypergraph structure
-- ═══════════════════════════════════════════

-- No default field values (causes universe errors); use Hypergraph.empty instead.
structure Hypergraph where
  nodes         : Std.HashMap UInt64 GoalNode
  edges         : Array HyperEdge
  backwardIndex : Std.HashMap UInt64 (Array HyperEdge)
  forwardIndex  : Std.HashMap UInt64 (Array HyperEdge)

namespace Hypergraph

def empty : Hypergraph :=
  { nodes := .empty, edges := #[], backwardIndex := .empty, forwardIndex := .empty }

def nodeCount (g : Hypergraph) : Nat := g.nodes.size
def edgeCount (g : Hypergraph) : Nat := g.edges.size

def hasNode (g : Hypergraph) (h : UInt64) : Bool :=
  g.nodes.contains h

def addNode (g : Hypergraph) (node : GoalNode) : Hypergraph :=
  if g.nodes.contains node.hash then g
  else { g with nodes := g.nodes.insert node.hash node }

def addEdge (g : Hypergraph) (edge : HyperEdge) : Hypergraph :=
  let g    := { g with edges := g.edges.push edge }
  let back := g.backwardIndex.find? edge.outputHash |>.getD #[]
  let g    := { g with backwardIndex :=
    g.backwardIndex.insert edge.outputHash (back.push edge) }
  let g    := edge.inputHashes.foldl (init := g) fun g inHash =>
    let fwd := g.forwardIndex.find? inHash |>.getD #[]
    { g with forwardIndex := g.forwardIndex.insert inHash (fwd.push edge) }
  g

def backwardEdges (g : Hypergraph) (goalHash : UInt64) : Array HyperEdge :=
  g.backwardIndex.find? goalHash |>.getD #[]

def forwardEdges (g : Hypergraph) (goalHash : UInt64) : Array HyperEdge :=
  g.forwardIndex.find? goalHash |>.getD #[]

end Hypergraph

-- ═══════════════════════════════════════════
--  Expr-level canonicalization
-- ═══════════════════════════════════════════

def canonicalHash (e : Expr) : UInt64 :=
  e.hash

def ppGoal (e : Expr) : MetaM String := do
  let fmt ← ppExpr e
  return fmt.pretty

-- ═══════════════════════════════════════════
--  Build hypergraph from Environment
-- ═══════════════════════════════════════════

def mkGoalNode (env : Environment) (name : Name) : MetaM GoalNode := do
  let info := env.find? name |>.get!
  let ty := info.type
  let str ← ppGoal ty
  return {
    hash := canonicalHash ty
    declName := name
    exprStr := str
    isAxiom := info.isAxiom || info matches .opaqueInfo ..
  }

def mkHyperEdge (env : Environment) (name : Name) : MetaM (Option HyperEdge) := do
  let some info  := env.find? name | return none
  let some value := info.value?     | return none
  let outputHash := canonicalHash info.type
  -- Collect into rawInputs first (avoids shadowing the mut variable).
  let mut rawInputs : Array UInt64 := #[]
  for c in value.getUsedConstants do
    if let some cInfo := env.find? c then
      let h := canonicalHash cInfo.type
      if h != outputHash then
        rawInputs := rawInputs.push h
  -- Array.sortAndDeduplicate doesn't exist; List.eraseDups removes duplicates.
  let inputHashes := rawInputs.toList.eraseDups.toArray
  return some { functionName := name, inputHashes, outputHash }

def isRelevantDecl (env : Environment) (name : Name) : Bool :=
  !name.isInternal
  && !isPrivateName name
  && !(env.find? name |>.map (·.isUnsafe) |>.getD true)

-- `prefix` is a reserved Lean 4 keyword → renamed to `namePrefix`.
-- Collect names via forM first, then process in a `for` loop so that
-- `let mut` state is threaded through `forIn` (not a lambda boundary).
def buildFromEnvironment
    (env : Environment)
    (namePrefix : Name := .anonymous)
    : MetaM Hypergraph := do
  let mut graph     := Hypergraph.empty
  let mut edgeCount := 0
  let mut skipCount := 0
  -- Phase 1: collect matching names (forM callback is read-only here).
  let mut constNames : Array Name := #[]
  env.constants.forM fun name _ => do
    if namePrefix == .anonymous || namePrefix.isPrefixOf name then
      if isRelevantDecl env name then
        constNames := constNames.push name
  -- Phase 2: process via for loop so mut state threads correctly.
  for name in constNames do
    let node ← mkGoalNode env name
    graph := graph.addNode node
    if let some edge ← mkHyperEdge env name then
      for inHash in edge.inputHashes do
        if !graph.hasNode inHash then
          graph := graph.addNode {
            hash := inHash, declName := .anonymous,
            exprStr := s!"(dep of {name})" }
      graph := graph.addEdge edge
      edgeCount := edgeCount + 1
    else
      skipCount := skipCount + 1
  IO.println s!"[Hypergraph] {graph.nodeCount} nodes, {edgeCount} edges ({skipCount} skipped)"
  return graph

def buildFromDecls (env : Environment) (decls : Array Name) : MetaM Hypergraph := do
  let mut graph := Hypergraph.empty

  for name in decls do
    let some _ := env.find? name | do
      IO.println s!"[Hypergraph] Warning: {name} not found"
      continue
    let node ← mkGoalNode env name
    graph := graph.addNode node
    if let some edge ← mkHyperEdge env name then
      for inHash in edge.inputHashes do
        if !graph.hasNode inHash then
          graph := graph.addNode {
            hash := inHash, declName := .anonymous,
            exprStr := s!"(dep of {name})" }
      graph := graph.addEdge edge

  IO.println s!"[Hypergraph] {decls.size} decls → {graph.nodeCount} nodes, {graph.edgeCount} edges"
  return graph

-- ═══════════════════════════════════════════
--  AND/OR Backward Chaining Proof Search
-- ═══════════════════════════════════════════

-- `go` was a PURE function using `return` and if-without-else (invalid in Lean 4).
-- Fix: lift to Id.run do — gives early-return semantics while staying pure
-- (Id α = α, so callers receive a plain tuple). break/return in for loops
-- both work correctly inside Id.run do.
-- Use an explicit visitedCount counter instead of HashSet.size
-- (size availability varies across Lean/Batteries versions).

private partial def go
    (graph : Hypergraph) (goalHash : UInt64) (depth : Nat)
    (visited : Std.HashSet UInt64) (visitedCount : Nat)
    : Bool × Array (Name × UInt64) × Array UInt64 × Nat := Id.run do
  -- Base: leaf node (axiom or no backward edges).
  if graph.hasNode goalHash then
    match graph.nodes.find? goalHash with
    | some node =>
      if node.isAxiom || (graph.backwardEdges goalHash).isEmpty then
        return (true, #[], #[], visitedCount)
    | none => pure ()
  -- Cycle / depth limit.
  if visited.contains goalHash || depth == 0 then
    return (graph.hasNode goalHash, #[],
      (if graph.hasNode goalHash then #[] else #[goalHash]), visitedCount)
  let visited      := visited.insert goalHash
  let visitedCount := visitedCount + 1
  let candidates   := graph.backwardEdges goalHash
  if candidates.isEmpty then
    return (graph.hasNode goalHash, #[],
      (if graph.hasNode goalHash then #[] else #[goalHash]), visitedCount)
  -- Sort: simpler edges (fewer inputs) first.
  let sorted := candidates.qsort fun a b => a.inputHashes.size < b.inputHashes.size
  -- OR: try each candidate edge; stop at first success.
  let mut found : Option (Array (Name × UInt64) × Nat) := none
  for edge in sorted do
    if found.isSome then break
    -- AND: all inputs must be provable.
    let mut allOk       := true
    let mut accSteps    : Array (Name × UInt64) := #[]
    let mut currVisited : Std.HashSet UInt64 := visited
    let mut currCount   := visitedCount
    for inHash in edge.inputHashes do
      if !allOk then break
      let (ok, steps, _, n) := go graph inHash (depth - 1) currVisited currCount
      if ok then
        accSteps    := accSteps ++ steps
        currVisited := currVisited.insert inHash
        currCount   := n
      else
        allOk := false
    if allOk then
      found := some (accSteps.push (edge.functionName, goalHash), currCount)
  match found with
  | some (steps, n) => return (true,  steps, #[],          n)
  | none            => return (false, #[],   #[goalHash], visitedCount)

def search (graph : Hypergraph) (targetHash : UInt64) (maxDepth : Nat := 50) : SearchResult :=
  let (proved, steps, missing, n) := go graph targetHash maxDepth (Std.HashSet.empty) 0
  if proved then .proved steps n else .notProved missing n

-- ═══════════════════════════════════════════
--  Diagnostics
-- ═══════════════════════════════════════════

def printSummary (graph : Hypergraph) : IO Unit := do
  let axiomCount := graph.nodes.toList.filter (·.2.isAxiom) |>.length
  let leafCount := graph.nodes.toList.filter
    (fun (h, _) => (graph.backwardEdges h).isEmpty) |>.length

  IO.println "═══════════════════════════════════════"
  IO.println "  ERDŐS HYPERGRAPH SUMMARY"
  IO.println "═══════════════════════════════════════"
  IO.println s!"  Nodes:      {graph.nodeCount}"
  IO.println s!"  Edges:      {graph.edgeCount}"
  IO.println s!"  Axioms:     {axiomCount}"
  IO.println s!"  Leaves:     {leafCount}"
  IO.println "═══════════════════════════════════════"

-- Fix 7: `scored.toArray` — scored is a List; type inference can fail on dot
--         notation.  Use explicit `List.toArray` to guide elaboration.
def printTopNodes (graph : Hypergraph) (topN : Nat := 10) : IO Unit := do
  let scored : Array (GoalNode × Nat) := List.toArray <|
    graph.nodes.toList.map fun (h, node) =>
      (node, (graph.backwardEdges h).size + (graph.forwardEdges h).size)
  let sorted := scored.qsort fun a b => a.2 > b.2
  let top    := sorted.toSubarray 0 (min topN sorted.size)
  IO.println s!"\nTop {top.size} most connected nodes:"
  for (node, deg) in top.toArray do
    IO.println s!"  [{deg}] {node.declName} : {node.exprStr}"

end NexusHypergraph
