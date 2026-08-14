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

public import Mathlib.Computability.Encoding
public import Mathlib.Data.List.SplitOn

@[expose] public section

open Computability

section Encodings
/-
These encodings are used in the formalization of complexity classes such as P and NP.

Note that in a Zulip discussion thread, Daniel Weber contributed some more general encodings.
We might eventually want to replace these with his more general versions.

see: https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Formalise.20the.20proposition.20P.20.E2.89.A0NP/with/453031558
-/

def finEncodingListBool : Computability.Encoding (List Bool) Bool where
  encode := id
  decode := Option.some
  decode_encode _ := rfl

/-- Port note (v4.33): `List.splitOnP` moved to Lean core with new unfolding lemmas;
both simp lemmas below are rebuilt on a single-chunk helper. -/
private lemma splitOnP_eq_single {α : Type} (P : α → Bool) (l : List α)
    (h : ∀ x ∈ l, P x = false) : List.splitOnP P l = [l] := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.splitOnP_cons_eq_if_splitOnPPrepend,
      if_neg (by simp [h hd (by simp)]),
      List.splitOnPPrepend_eq_modifyHead,
      ih (fun x hx => h x (by simp [hx]))]
    simp

@[simp]
lemma splitOnP_isNone_map_some {α : Type} (l : List α) :
    List.splitOnP Option.isNone (l.map some) = [l.map some] :=
  splitOnP_eq_single _ _ (by simp)

@[simp]
lemma splitOnP_append_cons {α : Type} (l1 l2 : List α)
    (a : α) (P : α → Bool) (hPa : P a = true) :
    List.splitOnP P (l1 ++ a :: l2)
    = List.splitOnP P l1 ++ List.splitOnP P l2 := by
  induction l1 with
  | nil =>
    rw [List.nil_append, List.splitOnP_cons_eq_if_splitOnPPrepend, if_pos hPa]
    simp
  | cons hd tl ih =>
    rw [List.cons_append, List.splitOnP_cons_eq_if_splitOnPPrepend]
    by_cases hPh : P hd = true
    · rw [List.splitOnP_cons_eq_if_splitOnPPrepend, if_pos hPh, ih, if_pos hPh]
      simp
    · rw [if_neg hPh, List.splitOnPPrepend_eq_modifyHead,
        List.splitOnP_cons_eq_if_splitOnPPrepend, if_neg hPh,
        List.splitOnPPrepend_eq_modifyHead, ih]
      obtain ⟨hd1, tl1, h1'⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil P tl)
      rw [h1']
      simp

def finEncodingListBoolProdListBool : Computability.Encoding (List Bool × List Bool) (Option Bool) where
  encode := fun ⟨l1, l2⟩ ↦ (l1.map some) ++ [none] ++ (l2.map some)
  decode := fun l ↦
    match l.splitOnP Option.isNone with
    | [l1, l2] => some (l1.map (Option.getD · false), l2.map (Option.getD · false))
    | _ => none
  decode_encode := by
    intro (l1, l2)
    simp

end Encodings
