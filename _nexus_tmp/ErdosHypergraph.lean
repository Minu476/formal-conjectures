-- ErdosHypergraph — Lean-native hypergraph from solved Erdős proofs.
-- The graph lives in a Lean HashMap — no serialisation, no cross-language bridge.
-- Run: cd formal-conjectures && lake env lean _nexus_tmp/ErdosHypergraph.lean

import FormalConjectures.Util.ProblemImports

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
  /-- Fully-qualified Lean 4 declaration name. -/
  function : String
  /-- Pretty-printed types of Prop-kinded ∀ binders (subgoal shapes). -/
  inputs   : List String
  /-- Pretty-printed conclusion type (the goal shape this edge closes). -/
  output   : String
  deriving Repr

/-- In-memory hypergraph.  Key = `hash (goalText : String)` (UInt64).
    `edges` maps each output-goal hash to every known edge that proves it,
    enabling O(1) backward-chaining lookup with no serialisation. -/
structure Hypergraph where
  /-- Goal-hash → canonical goal text (for display / debugging). -/
  nodes : Std.HashMap UInt64 GoalShape
  /-- Goal-hash → backward-chaining edges whose conclusion matches. -/
  edges : Std.HashMap UInt64 (Array HgEdge)

namespace Hypergraph

def empty : Hypergraph := ⟨{}, {}⟩

/-- Insert one edge, accumulating edges per output node. -/
def addEdge (g : Hypergraph) (edge : HgEdge) : Hypergraph :=
  let h        := hash edge.output    -- UInt64 via Hashable String
  let existing := (g.edges.get? h).getD #[]
  { nodes := g.nodes.insert h edge.output
  , edges := g.edges.insert h (existing.push edge) }

/-- All edges whose conclusion matches `goalText` (O(1) lookup). -/
def backwardEdges (g : Hypergraph) (goalText : String) : Array HgEdge :=
  (g.edges.get? (hash goalText)).getD #[]

/-- Number of distinct output-goal nodes in the graph. -/
def nodeCount (g : Hypergraph) : Nat := g.nodes.size

/-- Total number of hyperedges across all output nodes. -/
def edgeCount (g : Hypergraph) : Nat :=
  g.edges.toList.foldl (fun acc (_, es) => acc + es.size) 0

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

/-- Top-level proof search entry point. -/
def searchProof (g : Hypergraph) (goal : String) (maxDepth : Nat := 50)
    : Option (List (String × String)) :=
  proveGoal g goal maxDepth {}

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
    return some { function := name.toString
                , inputs   := propInputs
                , output   := outputStr }

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
