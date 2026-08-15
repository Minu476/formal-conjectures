/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib
public import Mathlib.Data.Finset.Sym
public import FormalConjecturesForMathlib
public import FormalConjecturesUtil.Answer
public import FormalConjecturesUtil.Linters.AMSLinter
public import FormalConjecturesUtil.Linters.AnswerLinter
public import FormalConjecturesUtil.Linters.CategoryDocstringLinter
public import FormalConjecturesUtil.Linters.CategoryLinter
public import FormalConjecturesUtil.Linters.CopyrightLinter
public import FormalConjecturesUtil.Linters.ExistsImplicationLinter
public import FormalConjecturesUtil.Linters.FormalProofLinter
public import FormalConjecturesUtil.Linters.LatexDocstringLinter
public import FormalConjecturesUtil.Linters.ModuleDocstringLinter
public import FormalConjecturesUtil.Linters.NamespaceLinter

/-!
# Standard imports for open problems

This file provides a standard set of imports used by problem files throughout the project.
-/

/-! ## v4.33 port compatibility instances

Mathlib v4.33 made `SimpleGraph.edgeFinset` require `[Fintype G.edgeSet]` and moved the
`Fintype (Sym2 α)` instance to `Mathlib.Data.Finset.Sym`. For a universally quantified
graph those instances only exist classically. These low-priority instances restore the
v4.27 elaboration behavior for problem statements; the computable instances
(`SimpleGraph.fintypeEdgeSet` under `[DecidableRel G.Adj]`) still win whenever they apply.
-/

section V433Compat

variable {V : Type*}

open SimpleGraph

noncomputable instance (priority := low) instFiniteSym2OfFinite {V : Type*} [Finite V] :
    Finite (Sym2 V) :=
  Finite.of_surjective (Quot.mk (Sym2.Rel V)) fun q => Quot.exists_rep q

noncomputable instance (priority := low) instFintypeEdgeSetOfFinite {V : Type*} [Finite V]
    {G : SimpleGraph V} : Fintype G.edgeSet := by
  have hfin : G.edgeSet.Finite :=
    Set.Finite.subset (Set.finite_univ (α := Sym2 V)) (fun _ _ => Set.mem_univ _)
  exact hfin.fintype

theorem subgraph_top_verts_eq (G : SimpleGraph V) :
    (⊤ : G.Subgraph).verts = Set.univ := rfl

noncomputable instance (priority := low) instFintypeVertsTopOfFinite {V : Type*} [Finite V]
    {G : SimpleGraph V} : Fintype (⊤ : G.Subgraph).verts := by
  rw [subgraph_top_verts_eq]
  exact Set.Finite.fintype (Set.finite_univ (α := V))

end V433Compat
