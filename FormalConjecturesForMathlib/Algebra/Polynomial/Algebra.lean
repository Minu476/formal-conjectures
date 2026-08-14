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


public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.RingTheory.Algebraic.Pi

@[expose] public section

/-!
# Algebra over the Ring of Polynomials

-/

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

namespace Polynomial

-- Port note (v4.33): `Pi.ringHom …toAlgebra` now routes through a noncomputable
-- `CommSemiring.toCommMonoid`-derived datum; the instance must be noncomputable.
noncomputable instance instAlgebraPi : Algebra R[X] (S → S) :=
  (Pi.ringHom fun x ↦ (Polynomial.aeval x).toRingHom).toAlgebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

-- Port note (v4.33): `aeval_polynomial_pi` is commented out — its proof relied on
-- the old `aeval = eval₂` definitional unfolding; v4.33's `aevalEquiv` refactoring
-- changed the definitional shape and the simp cascade no longer closes. It has no
-- users in this repository. Restore with a proof against `aevalEquiv` if needed.
/- @[simp] lemma aeval_polynomial_pi (p : R[X][X]) (f : S → S) (x : S) :
    p.aeval f x = aevalAeval x (f x) p := by
  simp [instAlgebraPi, aeval, eval₂, sum] -/

end Polynomial
