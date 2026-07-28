/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerScalarUnits
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# Scalar identification of a one-dimensional Brauer quotient

If an algebra Brauer quotient is one-dimensional over its coefficient
field, its canonical scalar map is an algebra equivalence.  Consequently
its unit group has the canonical scalar identification required by the
normalizer-correction construction.
-/

noncomputable section

namespace Representation

variable {k P A : Type}
variable [Field k] [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

/-- The canonical scalar algebra map into a one-dimensional Brauer
quotient is an algebra equivalence. -/
def scalarBrauerAlgEquiv
    (hfin :
      Module.finrank k
          (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) =
        1) :
    k ≃ₐ[k]
      BrauerQuotientAlgebra (k := k) (P := P) (A := A) :=
  by
    letI :
        Nontrivial
          (BrauerQuotientAlgebra
            (k := k) (P := P) (A := A)) :=
      Module.nontrivial_of_finrank_pos (by
        rw [hfin]
        exact Nat.zero_lt_one)
    exact
      AlgEquiv.ofBijective
        (Algebra.ofId k
          (BrauerQuotientAlgebra
            (k := k) (P := P) (A := A)))
        (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfin)

@[simp]
theorem scalarBrauerAlgEquiv_apply
    (hfin :
      Module.finrank k
          (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) =
        1)
    (a : k) :
    scalarBrauerAlgEquiv
        (k := k) (P := P) (A := A) hfin a =
      algebraMap k
        (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) a :=
  rfl

/-- A one-dimensional nonzero Brauer quotient has the canonical scalar
unit identification. -/
def brauerScalarIdentificationOfFinrankOne
    (hfin :
      Module.finrank k
          (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) =
        1) :
    BrauerScalarIdentification (k := k) (P := P) (A := A) := by
  let e :=
    scalarBrauerAlgEquiv (k := k) (P := P) (A := A) hfin
  exact BrauerScalarIdentification.ofRingEquiv
    e.symm.toRingEquiv
    (fun z ↦ by
      apply Units.ext
      change
        e.symm
            (scalarBrauerUnit
              (k := k) (P := P) (A := A) z :
              BrauerQuotientAlgebra
                (k := k) (P := P) (A := A)) =
          (z : k)
      apply e.injective
      rw [e.apply_symm_apply]
      rfl)

end Representation
