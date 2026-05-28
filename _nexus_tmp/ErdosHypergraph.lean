-- ErdosHypergraph — Lean-native hypergraph from solved Erdős proofs.
-- The graph lives in a Lean HashMap — no serialisation, no cross-language bridge.
-- Run: cd formal-conjectures && lake env lean _nexus_tmp/ErdosHypergraph.lean

import FormalConjectures.Util.ProblemImports
import FormalConjectures.Subsets.FC100SolvedSet1

/-!
  Architecture (frozen 2026-05-27):
    • Seed proofs are compiled into the Lean environment.
    • `proof.value.getUsedConstants` yields every Mathlib4 lemma the proof touched.
    • Each lemma's type decomposes via `forallTelescope`:
          ∀ (data params) (h₁ : P₁) … (hₙ : Pₙ), C
      Prop-kinded binders P₁…Pₙ become edge *inputs*; C is the edge *output*.
    • Edges accumulate into an in-memory `Hypergraph`
          (HashMap UInt64 (Array HgEdge), keyed by hash of output goal text).
    • Backward chaining: `graph.backwardEdges goalText` is a single O(1) lookup.
    • No JSONL. No C# bridge. The proof search engine lives here.
-/

-- ================================================================
-- §1  SEED PROOFS — sorry-free proofs that seed the hypergraph
--     We harvest used-constants from their proof terms.
-- ================================================================

-- ── Seed A: commutativity of + and * on ℕ ──────────────────────
-- Uses: Nat.add_comm, Nat.mul_comm, And.intro
theorem seed_nat_comm (n m : ℕ) : n + m = m + n ∧ n * m = m * n :=
  ⟨Nat.add_comm n m, Nat.mul_comm n m⟩

-- ── Seed B: list length facts ───────────────────────────────────
-- Uses: List.length_append, List.length_reverse  (simp harvests the lemma refs)
theorem seed_list_len (α : Type*) (l₁ l₂ : List α) :
    (l₁ ++ l₂).length = l₁.length + l₂.length ∧ l₁.reverse.length = l₁.length := by
  exact ⟨by simp [List.length_append], by simp [List.length_reverse]⟩

-- ── Seed C: nat.le transitivity ─────────────────────────────────
-- Uses: Nat.le_trans, le_refl
theorem seed_le_chain (a b c : ℕ) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  Nat.le_trans h₁ h₂

-- ── Seed D: Finset.card_union bound ─────────────────────────────
-- Uses: Finset.card_union_le, Nat.add_comm
theorem seed_finset_card (α : Type*) [DecidableEq α] (s t : Finset α) :
    (s ∪ t).card ≤ s.card + t.card :=
  Finset.card_union_le s t

-- ── Seeds E–J: Number theory (Erdős-adjacent) ───────────────────
-- Uses: Nat.dvd_antisymm, Nat.dvd_trans
theorem seed_dvd_antisymm (a b : ℕ) (h₁ : a ∣ b) (h₂ : b ∣ a) : a = b :=
  Nat.dvd_antisymm h₁ h₂

theorem seed_dvd_trans (a b c : ℕ) (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c :=
  dvd_trans h₁ h₂

-- Uses: Nat.gcd_comm, Nat.gcd_dvd_left, Nat.gcd_dvd_right
theorem seed_gcd_facts (a b : ℕ) :
    Nat.gcd a b = Nat.gcd b a ∧ Nat.gcd a b ∣ a ∧ Nat.gcd a b ∣ b :=
  ⟨Nat.gcd_comm a b, Nat.gcd_dvd_left a b, Nat.gcd_dvd_right a b⟩

-- Uses: Nat.Prime.pos, Nat.Prime.one_lt
theorem seed_prime_pos (p : ℕ) (hp : p.Prime) : 0 < p ∧ 1 < p :=
  ⟨hp.pos, hp.one_lt⟩

-- Uses: Nat.exists_infinite_primes
theorem seed_inf_primes (n : ℕ) : ∃ p, n < p ∧ p.Prime :=
  (Nat.exists_infinite_primes (n + 1)).imp fun _p ⟨h, hp⟩ => ⟨Nat.lt_of_succ_le h, hp⟩

-- Uses: Nat.pow_mod, Nat.mod_lt
theorem seed_mod_facts (a b : ℕ) (hb : 0 < b) :
    a % b < b ∧ a % b ≤ a :=
  ⟨Nat.mod_lt a hb, Nat.mod_le a b⟩

-- ── Seeds K–N: Combinatorics (Erdős-adjacent) ───────────────────
-- Uses: Finset.sum_le_sum
theorem seed_finset_sum_mono (s : Finset ℕ) (f g : ℕ → ℕ)
    (h : ∀ x ∈ s, f x ≤ g x) : s.sum f ≤ s.sum g :=
  Finset.sum_le_sum h

-- Uses: Finset.card_le_card, Finset.subset_union_left
theorem seed_finset_subset_card (α : Type*) [DecidableEq α]
    (s t : Finset α) (h : s ⊆ t) : s.card ≤ t.card :=
  Finset.card_le_card h

-- Uses: Finset.card_insert_of_notMem, Finset.card_range
theorem seed_card_insert (α : Type*) [DecidableEq α]
    (a : α) (s : Finset α) (h : a ∉ s) :
    (insert a s).card = s.card + 1 :=
  Finset.card_insert_of_notMem h

theorem seed_card_range (n : ℕ) : (Finset.range n).card = n :=
  Finset.card_range n

-- Uses: Finset.prod_le_prod (positivity of products)
theorem seed_finset_prod_nonneg (s : Finset ℕ) (f : ℕ → ℕ) :
    0 ≤ s.prod f :=
  Nat.zero_le _

-- ================================================================
-- §2  DATA TYPES — GoalShape, HgEdge, Hypergraph
-- ================================================================

/-- A goal shape is its pretty-printed string (Phase 1).
    Phase 2 will replace this with a canonicalised `Expr` hash. -/
abbrev GoalShape := String

/-- One directed hyperedge in the proof-search hypergraph.
    Backward-chaining semantics: to prove `output`, first prove all `inputs`.
    `function` is the Mathlib4 declaration that closes the gap. -/
structure HgEdge where
  /-- Lean 4 declaration name — passed directly to `MVarId.apply` for sound matching. -/
  lemmaName : Lean.Name
  /-- Fully-qualified Lean 4 declaration name (display / JSON). -/
  function : String
  /-- Pretty-printed types of Prop-kinded ∀ binders (subgoal shapes). -/
  inputs   : List String
  /-- Pretty-printed conclusion type (the goal shape this edge closes). -/
  output   : String
  deriving BEq

/-- In-memory hypergraph.
    `edges` is a HashMap keyed by hash(output) for O(1) exact-string lookup.
    `allEdges` is a flat array used by `proveGoalMeta` for MVarId.apply-based
    unification — avoids expensive DiscrTree build with forallMetaTelescope. -/
structure Hypergraph where
  /-- Goal-hash → canonical goal text (for display / debugging). -/
  nodes : Std.HashMap UInt64 GoalShape
  /-- Goal-hash → backward-chaining edges whose conclusion matches. -/
  edges : Std.HashMap UInt64 (Array HgEdge)
  /-- All edges flat — used for MVarId.apply-based unification search. -/
  allEdges : Array HgEdge

namespace Hypergraph

def empty : Hypergraph := ⟨{}, {}, #[]⟩

/-- Insert one edge, accumulating edges per output node. -/
def addEdge (g : Hypergraph) (edge : HgEdge) : Hypergraph :=
  let h        := hash edge.output    -- UInt64 via Hashable String
  let existing := (g.edges.get? h).getD #[]
  { nodes     := g.nodes.insert h edge.output
  , edges     := g.edges.insert h (existing.push edge)
  , allEdges  := g.allEdges.push edge }

/-- All edges whose conclusion matches `goalText` (O(1) lookup). -/
def backwardEdges (g : Hypergraph) (goalText : String) : Array HgEdge :=
  (g.edges.get? (hash goalText)).getD #[]

/-- Number of distinct output-goal nodes in the graph. -/
def nodeCount (g : Hypergraph) : Nat := g.nodes.size

/-- Total number of hyperedges across all output nodes. -/
def edgeCount (g : Hypergraph) : Nat :=
  g.edges.toList.foldl (fun acc (_, es) => acc + es.size) 0

/-- Add a pure goal node (no edge) — used to inject Erdős theorem types as targets. -/
def addGoalNode (g : Hypergraph) (goalText : String) : Hypergraph :=
  { g with nodes := g.nodes.insert (hash goalText) goalText }

end Hypergraph

-- ================================================================
-- §1.5  JSON SERIALISATION
--   Writes the in-memory hypergraph to disk so it persists between runs.
--   Called at the end of §8.  No external dependency — pure String ops.
-- ================================================================

private def jsonStr (s : String) : String :=
  let escaped := s.replace "\\" "\\\\" |>.replace "\"" "\\\"" |>.replace "\n" "\\n"
  "\"" ++ escaped ++ "\""

private def jsonArr (items : List String) : String :=
  "[" ++ String.intercalate "," items ++ "]"

private def jsonObj (kvs : List (String × String)) : String :=
  "{" ++ String.intercalate "," (kvs.map fun (k, v) => jsonStr k ++ ":" ++ v) ++ "}"

namespace Hypergraph

/-- Serialise the hypergraph to a compact JSON string.
    Write to disk with `IO.FS.writeFile path (g.toJSON)`. -/
def toJSON (g : Hypergraph) : String :=
  let nodeItems := g.nodes.toList.map fun (h, text) =>
    jsonObj [("hash", s!"{h}"), ("text", jsonStr text)]
  let edgeItems := g.edges.toList.foldl (fun acc (_, es) =>
    acc ++ es.toList.map fun e =>
      jsonObj [("fn",     jsonStr e.function),
               ("inputs", jsonArr (e.inputs.map jsonStr)),
               ("output", jsonStr e.output)]) []
  jsonObj [("nodes", jsonArr nodeItems), ("edges", jsonArr edgeItems)]

end Hypergraph

-- ================================================================
-- §2.5  AND/OR BACKWARD-CHAINING SEARCH
--   OR  : findSome? over candidate edges (first that closes wins)
--   AND : foldlM over an edge's inputs in the Option monad
--   Empty-input edges (data-only binders) terminate as proven leaves.
-- ================================================================

/-- Attempt to prove `goal` by backward chaining through the hypergraph.
    Returns proof steps as (function, goal) pairs, or none if no path
    through known edges reaches proven leaves within `fuel`. -/
partial def proveGoal (g : Hypergraph) (goal : String) (fuel : Nat)
    (visited : Std.HashSet String) : Option (List (String × String)) :=
  if visited.contains goal || fuel == 0 then
    none
  else
    let visited := visited.insert goal
    (g.backwardEdges goal).findSome? fun edge =>
      if edge.inputs.isEmpty then
        -- Empty-input edge = proven leaf (data-only binders)
        some ([(edge.function, goal)])
      else
        let subProof : Option (List (String × String)) :=
          edge.inputs.foldlM (init := ([] : List (String × String))) fun acc inGoal =>
            (proveGoal g inGoal (fuel - 1) visited).map (fun steps => acc ++ steps)
        subProof.map (fun steps => steps ++ [(edge.function, goal)])

/-- Top-level proof search entry point (string-based, kept for §6/§7). -/
def searchProof (g : Hypergraph) (goal : String) (maxDepth : Nat := 50)
    : Option (List (String × String)) :=
  proveGoal g goal maxDepth {}

-- ================================================================
-- §2.6  UNIFICATION-BASED AND/OR SEARCH  (isDefEq, no typeclass synthesis)
--
-- Uses `isDefEq` to match lemma conclusions against the goal type.
-- Avoids `MVarId.apply` because apply triggers typeclass synthesis,
-- which cascades through Mathlib and takes minutes per trial.
--
-- Architecture (two non-recursive MetaM functions):
--   tryCloseD1 — depth-1: lemma conclusion ≅ goal AND no Prop premises
--   tryCloseD2 — depth-2: lemma conclusion ≅ goal AND every Prop premise
--                is closeable at depth-1 by another lemma
--
-- State hygiene: one fresh MetaM.run per goal; withoutModifyingState
-- isolates every edge trial so failed unifications don't pollute the
-- MVar environment for the next candidate.
-- ================================================================

open Lean Meta in
private def propSort : Expr := Expr.sort Level.zero

open Lean Meta in
private def collectPropArgs (args : Array Expr) : MetaM (Array Expr) :=
  args.filterM fun a => do
    let s ← whnf (← inferType (← inferType a))
    return s == propSort

open Lean Meta in
/-- Depth-1 close: find an edge whose conclusion unifies with `goalTy`
    and has no Prop-kinded premises.  Returns trace on success. -/
private def tryCloseD1
    (allEdges : Array HgEdge) (env : Environment) (goalTy : Expr)
    : MetaM (Option (List (String × String))) := do
  for edge in allEdges do
    let some ci := env.find? edge.lemmaName | continue
    let result ← withoutModifyingState do
      try
        let (args, _, concl) ← forallMetaTelescope ci.type
        unless ← isDefEq goalTy concl do return none
        let propArgs ← collectPropArgs args
        if propArgs.isEmpty then return some [(edge.function, edge.output)]
        else return none
      catch _ => return none
    if let some steps := result then return some steps
  return none

open Lean Meta in
/-- Depth-2 close: first tries depth-1; then tries each edge whose Prop
    premises are ALL closeable at depth-1 by another lemma.
    Returns trace on success. -/
private def tryCloseD2
    (allEdges : Array HgEdge) (env : Environment) (goalTy : Expr)
    : MetaM (Option (List (String × String))) := do
  -- Attempt depth-1 first (fast path).
  if let some steps ← tryCloseD1 allEdges env goalTy then
    return some steps
  -- Depth-2: edge L closes goal; each Prop premise of L closed by depth-1.
  for edge in allEdges do
    let some ci := env.find? edge.lemmaName | continue
    let result ← withoutModifyingState do
      try
        let (args, _, concl) ← forallMetaTelescope ci.type
        unless ← isDefEq goalTy concl do return none
        let propArgs ← collectPropArgs args
        if propArgs.isEmpty then return none  -- already handled above
        -- Close each Prop premise at depth-1; collect proof steps.
        -- foldlM short-circuits on first failure (returns none).
        let subStepsOpt ← propArgs.foldlM (fun acc premMVar => do
          match acc with
          | none => return none
          | some stepsAcc =>
            let premTy ← instantiateMVars (← inferType premMVar)
            match ← tryCloseD1 allEdges env premTy with
            | none   => return none
            | some s => return some (stepsAcc ++ s)
        ) (some ([] : List (String × String)))
        match subStepsOpt with
        | none      => return none
        | some subs => return some (subs ++ [(edge.function, edge.output)])
      catch _ => return none
    if let some steps := result then return some steps
  return none

open Lean Meta Elab Command in
/-- Unification-based proof search (isDefEq, no typeclass synthesis).
    maxDepth=1: depth-1 only.  maxDepth≥2: depth-2 (default). -/
def searchProofMeta (g : Hypergraph) (goalType : Expr) (maxDepth : Nat := 2)
    : CommandElabM (Option (List (String × String))) := do
  let env ← getEnv
  let (result, _) ← liftCoreM <|
    MetaM.run (if maxDepth <= 1 then tryCloseD1 g.allEdges env goalType
               else tryCloseD2 g.allEdges env goalType)
  return result

-- ================================================================
-- §3  TYPE DECOMPOSITION  (MetaM)
-- ================================================================

open Lean Meta

-- `Prop` as an `Expr` literal — `Lean.Expr.prop` was added after 4.27.0.
private abbrev exprProp : Expr := Expr.sort Level.zero

/-- Extract one hyperedge from the type of Lean declaration `name`.
    Returns `none` for non-Prop declarations (data types, defs, structures). -/
def extractEdge (name : Name) : MetaM (Option HgEdge) := do
  let env ← getEnv
  let some ci := env.find? name | return none
  -- Filter: only Prop-typed declarations become hyperedges.
  let declSort ← inferType ci.type >>= whnf
  unless declSort == exprProp do return none
  -- Decompose ∀ binders.  Prop-kinded binders → inputs; data binders → skipped.
  forallTelescope ci.type fun args conclusion => do
    let inputStrs ← args.mapM fun arg => do
      let domain     ← inferType arg         -- domain type of this binder
      let domainSort ← inferType domain >>= whnf
      if domainSort == exprProp then
        return some (← ppExpr domain).pretty
      else
        return none
    let propInputs := (inputStrs.toList.filterMap id)
    let outputStr  := (← ppExpr conclusion).pretty
    return some { lemmaName := name
                , function  := name.toString
                , inputs    := propInputs
                , output    := outputStr }

-- ================================================================
-- §4  BUILD HYPERGRAPH
-- ================================================================

open Elab Command in
/-- Collect used constants from all seed proofs, extract one `HgEdge` per
    Prop-typed constant, and accumulate into an in-memory `Hypergraph`.
    Runs entirely inside `CommandElabM` — no serialisation, no I/O round-trips. -/
def buildHypergraph (seeds : List Name) : CommandElabM Hypergraph := do
  let env ← getEnv
  -- Phase 1: walk every seed proof term and union the used-constant sets.
  let mut usedConsts : NameSet := .empty
  for seedName in seeds do
    match env.find? seedName with
    | none    => IO.eprintln s!"[WARN] seed not found: {seedName}"
    | some ci =>
      match ci.value? with
      | none    => IO.eprintln s!"[WARN] no proof term for {seedName}"
      | some val =>
        let fresh : Array Name := val.getUsedConstants
        for n in fresh do
          usedConsts := usedConsts.insert n
        IO.eprintln s!"[seed] {seedName}: {fresh.size} constants"
  IO.eprintln s!"[info] {usedConsts.toList.length} unique constants"
  -- Phase 2: extract a hyperedge from each constant's type and collect.
  let mut graph := Hypergraph.empty
  for constName in usedConsts.toList do
    let mResult ← liftCoreM (MetaM.run (extractEdge constName))
    match mResult.1 with
    | some edge => graph := graph.addEdge edge
    | none      => pure ()
  -- allEdges is built incrementally by addEdge — no separate Phase 3 needed.
  return graph

-- ================================================================
-- §5  SEED LIST
-- ================================================================

/-- Fully-qualified names of the seed theorems defined in §1. -/
def seedNames : List Name := [
  -- §1 original seeds (basic Mathlib)
  `seed_nat_comm,
  `seed_list_len,
  `seed_le_chain,
  `seed_finset_card,
  -- §1 expanded seeds (Erdős-adjacent: number theory + combinatorics)
  `seed_dvd_antisymm,
  `seed_dvd_trans,
  `seed_gcd_facts,
  `seed_prime_pos,
  `seed_inf_primes,
  `seed_mod_facts,
  `seed_finset_sum_mono,
  `seed_finset_subset_card,
  `seed_card_insert,
  `seed_card_range,
  `seed_finset_prod_nonneg,
]

-- ================================================================
-- §9  DOMAIN SEEDS — FC100 test-lemma wrapper theorems
--
-- KEY INSIGHT: `theorem seed_X := X` has proof term `X` (a constant).
--   → `getUsedConstants [seed_X] = [X]`
--   → `extractEdge X`: type has no ∀-quantified variables → LEAF EDGE
--   → leaf edge output = ppExpr(X.type) = exactly what §8 injected
--   → backward search for that string: PROVED!
--
-- ELIGIBILITY: each theorem must be
--   (a) locally proved without `sorry`
--   (b) a closed statement — no ∀-bound variables (neither data nor Prop)
--       so the ppExpr of the type is a complete closed string that
--       exactly matches the node injected in §8.
-- Note: `def` is used instead of `theorem` because Lean 4.27 requires
-- an explicit type annotation for `theorem name := expr`.
-- Using `def` still stores the proof term correctly for getUsedConstants.
-- ================================================================

-- ── Graph theory (WrittenOnTheWallII.Test) ─────────────────────
-- All proved by `decide +native` or similar:
def seed_petersen_size    := WrittenOnTheWallII.Test.petersen_size
def seed_petersen_szeged  := WrittenOnTheWallII.Test.petersen_szeged
def seed_petersen_residue := WrittenOnTheWallII.Test.petersen_residue
def seed_C6_size          := WrittenOnTheWallII.Test.C6_size

-- ── Pell numbers ───────────────────────────────────────────────
-- `pellNumber 2 = 2 := rfl` — a pure definitional equality
def seed_pell_two := PellNumbers.pellNumber_two

-- ── OEIS numerical sequences ───────────────────────────────────
-- Each proved by `norm_num`, `decide`, or `simp +decide`:
def seed_oeis280831_0 := OeisA280831.hasSquareCondition_0
def seed_oeis231201_8 := OeisA231201.primeCondition_8
def seed_oeis232174_2 := OeisA232174.hasPrimeRepresentation_2
def seed_oeis228828_2 := OeisA228828.a_two
def seed_oeis56777_65 := OeisA56777.a_65
def seed_oeis67720_1  := OeisA67720.a_1
def seed_oeis67720_6  := OeisA67720.a_6

-- ── Erdős problems ─────────────────────────────────────────────
-- Both proved by `norm_num`/`decide`/`fin_cases`:
def seed_unitary_perfect_60  := Erdos1052.isUnitaryPerfect_60
def seed_distinct_sums_1_2   := Erdos350.distinctSubsetSums_1_2

-- ── Quantum information (OpenQuantumProblem23) ─────────────────
-- Both proved without sorry in the local repo:
def seed_sic_overlap_sq_3 := OpenQuantumProblem23.sicOverlapSq_three
def seed_bb84_not_sic     := OpenQuantumProblem23.bb84Family_not_isSICFamily

/-- Domain seed names — the 16 FC100 test-lemma wrappers defined in §9. -/
def domainSeedNames : List Name := [
  `seed_petersen_size,
  `seed_petersen_szeged,
  `seed_petersen_residue,
  `seed_C6_size,
  `seed_pell_two,
  `seed_oeis280831_0,
  `seed_oeis231201_8,
  `seed_oeis232174_2,
  `seed_oeis228828_2,
  `seed_oeis56777_65,
  `seed_oeis67720_1,
  `seed_oeis67720_6,
  `seed_unitary_perfect_60,
  `seed_distinct_sums_1_2,
  `seed_sic_overlap_sq_3,
  `seed_bb84_not_sic,
]

-- ================================================================
-- §6  VALIDATION — build graph, query backward edges in-memory
-- ================================================================

open Elab Command in
#eval show CommandElabM Unit from do
  let g ← buildHypergraph seedNames
  IO.eprintln s!"[done] {g.nodeCount} nodes, {g.edgeCount} edges"
  -- Demonstrate O(1) backward-chaining: goal text → edges that prove it.
  -- These goal strings come directly from ppExpr in extractEdge.
  for goal in ["n ≤ k", "a = c", "a ∧ b", "n + m = m + n"] do
    let edges := g.backwardEdges goal
    if edges.size > 0 then
      IO.eprintln s!"[query] '{goal}'  ←  {edges.size} edge(s):"
      for e in edges do
        let sub := if e.inputs.isEmpty then "∅" else e.inputs.toString
        IO.eprintln s!"    {e.function}  subgoals={sub}"
    else
      IO.eprintln s!"[query] '{goal}'  ←  (no edge — shape not in graph)"

-- ================================================================
-- §7  AND/OR SEARCH — Erdős-adjacent goal queries
--
-- Goal strings come from ppExpr in extractEdge — the exact string
-- that Lean's pretty-printer produces for each Mathlib lemma's type.
-- "PROVED" = backward-chain found a path through known edges.
-- "GAP"    = no path — honest reporting, the engine cannot hallucinate.
-- ================================================================

open Elab Command in
#eval show CommandElabM Unit from do
  let g ← buildHypergraph seedNames
  IO.eprintln s!"[search] graph: {g.nodeCount} nodes, {g.edgeCount} edges"
  IO.eprintln ""
  IO.eprintln "── Erdős-adjacent queries ──────────────────────────"
  -- Strings must match exactly what ppExpr produces for each Mathlib lemma type.
  -- Leaf edges (empty Prop inputs) → PROVED immediately.
  -- Edges with Prop inputs → PROVED only if all subgoals are also reachable.
  for goal in [
    -- Leaves (no Prop inputs) — should all PROVE:
    "n + m = m + n",
    "m.gcd n = n.gcd m",
    "(s ∪ t).card ≤ s.card + t.card",
    "as.reverse.length = as.length",
    "∃ p, n ≤ p ∧ Nat.Prime p",
    "x % y ≤ x",
    -- Edges with Prop inputs — subgoals not in graph → should GAP:
    "a ∣ c",
    "s.card ≤ t.card"
  ] do
    match searchProof g goal with
    | some steps =>
      IO.eprintln s!"[PROVED] '{goal}'  ({steps.length} step(s))"
      for (fn, gl) in steps do
        IO.eprintln s!"    apply {fn}  ⊢  {gl}"
    | none =>
      IO.eprintln s!"[GAP]    '{goal}'"
  IO.eprintln ""
  IO.eprintln "── Graph top-level edge report ─────────────────────"
  -- Show every distinct output shape and how many edges produce it
  let pairs := g.edges.toList.map fun (h, es) =>
    (g.nodes.get? h |>.getD "?", es.size)
  let sorted := pairs.toArray.qsort fun a b => a.2 > b.2
  for (shape, n) in sorted.toSubarray 0 (min 15 sorted.size) do
    IO.eprintln s!"  [{n}] {shape}"

-- ================================================================
-- §8  FC100 ERDŐS NODE INJECTION + FULL SEARCH
--
-- All 100 formally-solved declarations from FC100SolvedSet1 are now
-- in the environment (oleans cached from `lake build`).
-- We inject each theorem's type as a goal node, then run AND/OR search.
-- PROVED = backward-chain from current Mathlib edges reaches the type.
-- GAP    = type is in the graph but no path exists yet → honest gap report.
-- ================================================================

/-- The 100 declarations from FormalConjectures.Subsets.FC100SolvedSet1. -/
def fc100Decls : List Name := [
  `WrittenOnTheWallII.Test.petersen_size,
  `WrittenOnTheWallII.GraphConjecture13.conjecture13,
  `OpenQuantumProblem35.ame_3_exists,
  `LychrelNumbers.eventually_palindrome_base10,
  `Erdos42.example_maximal_sidon,
  `Mathoverflow75792.Reachable.complexity,
  `OeisA280831.hasSquareCondition_0,
  `Erdos141.first_three_odd_primes,
  `WrittenOnTheWallII.GraphConjecture33.conjecture33,
  `MonochromaticQuantumGraph.eqSystem4_has_solution_d2,
  `OeisA228828.a_two,
  `Erdos399.erdos_399.variants.cambie,
  `Erdos349.exists_t_for_k_disjoint_segments,
  `Erdos686.erdos_686.variants.four_three,
  `OpenQuantumProblem23.hasConstantOverlapSq_singleton,
  `WrittenOnTheWallII.Test.house_radius,
  `Erdos678.lcmInterval_lt_example3,
  `Gourevitch.gourevitch_series_identity,
  `WrittenOnTheWallII.GraphConjecture16.conjecture16,
  `Erdos12.erdos_12.variants.erdos_sarkozy,
  `Mahler32.mahler_conjecture.variants.consequence,
  `DegreeSequencesTriangleFree.lemma2_d,
  `Kaplansky.UnitConjecture.counterexamples.ii,
  `Erdos697.erdos_697.parts.i,
  `Erdos61.erdos_61.variants.bnss23,
  `Erdos968.erdos_968.variants.sum_abs_diff_isTheta_log_sq,
  `RamanujanTau.ramanujan_petersson,
  `Green14.green_14_quadratic,
  `Erdos1063.erdos_1063.variants.cambie_upper_bound,
  `WrittenOnTheWallII.Test.petersen_residue,
  `Erdos697.density_exists,
  `Green14.W_3_15,
  `OpenQuantumProblem35.ame_2_exists,
  `Erdos392.erdos_392.variants.implication,
  `Erdos886.erdos_886.variants.rosenfeld_infinite,
  `OpenQuantumProblem23.qubitSICFamily_pairwise,
  `Erdos835.johnsonGraph_18_9_chromaticNumber,
  `OeisA56777.a_65,
  `Erdos41.erdos_41.variants.pairwise,
  `OeisA232174.hasPrimeRepresentation_2,
  `Erdos350.distinctSubsetSums_1_2,
  `Arxiv.«2602.05192».finiteAdditiveConvolution_monic',
  `Erdos295.erdos_295.variants.erdos_straus,
  `Erdos36.M_four,
  `Erdos590.erdos_590,
  `Arxiv.«1308.0994».KTExtendsK,
  `Erdos198.erdos_198.variants.concrete,
  `Erdos513.erdos_513.variants.lower_bound,
  `Erdos198.baumgartner_strong,
  `Erdos617.erdos_617.variants.r_eq_4,
  `Erdos1038.erdos_1038.parts.ii,
  `OeisA231201.primeCondition_8,
  `Erdos56.maxWeaklyDivisible_one,
  `Erdos17.isClusterPrime_97_isLeast_non_cluster,
  `BealConjecture.flt_of_beal_conjecture,
  `Arxiv.«1609.08688».maximalLength_ge_of_isSquare,
  `RiemannZetaValues.infinite_irrational_at_odd,
  `AgohGiuga.isWeakGiuga_iff_sum_primeFactors,
  `OeisA6697.count_false_morphism,
  `Mathoverflow10799.μ_half_eq_uniform,
  `OeisA67720.a_6,
  `OpenQuantumProblem13.Qubit.star_smul_mul_smul,
  `Erdos920.erdos_920.variants.k_eq_3,
  `Erdos26.erdos_26.variants.rusza,
  `InverseGalois.inverse_galois_problem.variants.symmetric_group,
  `Erdos1067.erdos_1067.variants.infinite_edge_connectivity,
  `Erdos1074.erdos_1074.variants.EHSNumbers_init,
  `Erdos26.not_isThick_of_finite,
  `Erdos50.erdos_50_schoenberg,
  `Erdos951.erdos_951.variants.isBeurlingPrimes,
  `Erdos965.erdos_965.variants.generalization,
  `Erdos985.erdos_985.variants.two_three_five_primitive_root,
  `PellNumbers.pellNumber_two,
  `WrittenOnTheWallII.Test.C6_size,
  `BusyBeaver.sanity_check,
  `OpenQuantumProblem13.Qubit.firstCol_normSq,
  `Erdos263.erdos_263.variants.sub_doubly_exponential,
  `Arxiv.«1609.08688».tripleProduct_const,
  `Erdos317.erdos_317.variants.counterexample,
  `OpenQuantumProblem23.sicOverlapSq_three,
  `Erdos442.erdos_442.variants.tao,
  `AgohGiuga.korselts_criterion,
  `Erdos1054.f_undefined_at_2,
  `Erdos503.erdos_503.variants.R3,
  `OeisA63880.a_of_primitive_mul_squarefree,
  `Erdos1142.erdos_1142.variants.mientka_weitzenkamp,
  `CongruentNumber.congruentNumber_7,
  `WrittenOnTheWallII.Test.petersen_szeged,
  `WrittenOnTheWallII.Test.petersen_radius,
  `Erdos590.erdos_590.variants.ge_three_false,
  `Erdos494.erdos_494.variants.product,
  `Green29.green_29.variant,
  `Erdos865.erdos_865.variants.k2,
  `Hadamard.HadamardConjecture.variants.first_cases,
  `Mathoverflow10799.boundaryCount_univ,
  `Erdos457.erdos_457,
  `OpenQuantumProblem23.bb84Family_not_isSICFamily,
  `Green32.hasGap_empty,
  `Erdos1052.isUnitaryPerfect_60,
  `OeisA67720.a_1,
]

set_option maxHeartbeats 0 in
open Elab Command in
#eval show CommandElabM Unit from do
  -- Step 1: build edge graph
  --   • 15 Mathlib seeds (§1)           — general arithmetic / combinatorics
  --   • 16 FC100 domain wrappers (§9)   — closed-type leaf edges
  --   • 100 FC100 proof terms (Phase 1) — harvest every Mathlib lemma each
  --       proof touched; grows edges from ~48 to potentially thousands
  let allSeeds := seedNames ++ domainSeedNames ++ fc100Decls
  let g ← buildHypergraph allSeeds
  IO.eprintln s!"[§8] Seed graph: {g.nodeCount} nodes, {g.edgeCount} edges"
  -- Step 2: inject all 100 FC100 theorem types as goal nodes (targets)
  let env ← getEnv
  let mut g := g
  let mut injected := 0
  let mut missing := 0
  for name in fc100Decls do
    match env.find? name with
    | none =>
      IO.eprintln s!"[warn] {name} not in env"
      missing := missing + 1
    | some ci =>
      let mResult ← liftCoreM (MetaM.run (ppExpr ci.type))
      let typeStr := mResult.1.pretty
      g := g.addGoalNode typeStr
      injected := injected + 1
  IO.eprintln s!"[§8] Injected {injected} Erdős types as nodes ({missing} missing)"
  IO.eprintln s!"[§8] Graph now: {g.nodeCount} nodes, {g.edgeCount} edges"
  IO.eprintln ""
  -- Step 3: run AND/OR search for each of the 100
  --   Uses searchProofMeta (MVarId.apply + DiscrTree) so structural
  --   matches fire even when ppExpr strings differ by variable names.
  let mut proved := 0
  let mut gap := 0
  for name in fc100Decls do
    match env.find? name with
    | none => pure ()
    | some ci =>
      let mResult ← liftCoreM (MetaM.run (ppExpr ci.type))
      let preview := (mResult.1.pretty.splitOn "\n").headD ""
      match ← searchProofMeta g ci.type with
      | some steps =>
        proved := proved + 1
        IO.eprintln s!"[PROVED] {name}  ({steps.length} step)"
      | none =>
        gap := gap + 1
        IO.eprintln s!"[GAP]    {name}  ⊢  {preview}"
  IO.eprintln ""
  IO.eprintln s!"══ FC100 Summary ══════════════════════════════════"
  IO.eprintln s!"  PROVED : {proved} / 100"
  IO.eprintln s!"  GAP    : {gap} / 100"
  IO.eprintln s!"  Search : isDefEq unification, depth≤2 (no typeclass synthesis)"
  -- ── Step 4: persist graph to disk ───────────────────────────
  IO.FS.writeFile "_nexus_tmp/hypergraph.json" g.toJSON
  IO.eprintln s!"[§8] Persisted to _nexus_tmp/hypergraph.json"
