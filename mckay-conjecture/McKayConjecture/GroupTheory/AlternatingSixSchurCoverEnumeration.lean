/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import McKayConjecture.GroupTheory.AlternatingSixHopfKernelProof

/-!
# Exact enumeration of the `A₆` Schur cover

The weighted rewrite certificate supplies a surjection from the `360 * 6`
selected normal representatives to the presented sixfold cover.  The
independent lower-bound argument proves that the cover has exactly `2160`
elements.  Hence the normal-representative map is an equivalence.

This file records that consequence separately.  It is the finite enumeration
interface used by later character-table certificates: sums over the abstract
presented group can be checked on the explicit normal representatives without
introducing a second group model.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- The `360 * 6` normal representatives are pairwise distinct as well as
exhaustive. -/
theorem alternatingSixSchurNormalRepresentative_bijective :
    Function.Bijective alternatingSixSchurNormalRepresentative := by
  apply
    alternatingSixSchurNormalRepresentative_surjective
      |>.bijective_of_nat_card_le
  rw [natCard_alternatingSixSchurPresentedGroup]
  simp

/-- Exact enumeration of the presented Schur cover by a noncentral normal
word and a power of the central generator. -/
def alternatingSixSchurNormalRepresentativeEquiv :
    (Fin 360 × Fin 6) ≃ AlternatingSixSchurPresentedGroup :=
  Equiv.ofBijective
    alternatingSixSchurNormalRepresentative
    alternatingSixSchurNormalRepresentative_bijective

@[simp]
theorem alternatingSixSchurNormalRepresentativeEquiv_apply
    (index : Fin 360 × Fin 6) :
    alternatingSixSchurNormalRepresentativeEquiv index =
      alternatingSixSchurNormalRepresentative index :=
  rfl

/-- The exact normal-form equivalence supplies a computationally indexed
fintype structure on the abstract presented group. -/
noncomputable instance alternatingSixSchurPresentedGroupFintype :
    Fintype AlternatingSixSchurPresentedGroup :=
  Fintype.ofEquiv
    (Fin 360 × Fin 6)
    alternatingSixSchurNormalRepresentativeEquiv

/-- A finite sum over the presented cover is exactly the sum over the checked
normal representatives. -/
theorem sum_alternatingSixSchurNormalRepresentative
    {M : Type*} [AddCommMonoid M]
    (f : AlternatingSixSchurPresentedGroup → M) :
    ∑ g, f g =
      ∑ index : Fin 360 × Fin 6,
        f (alternatingSixSchurNormalRepresentative index) := by
  classical
  symm
  exact
    alternatingSixSchurNormalRepresentativeEquiv.sum_comp f

/-- The exact normal-form enumeration transported to the canonical
free-presentation universal cover. -/
def alternatingSixUniversalCoverNormalRepresentativeEquiv :
    (Fin 360 × Fin 6) ≃ AlternatingSixUniversalCover :=
  alternatingSixSchurNormalRepresentativeEquiv.trans
    (alternatingSixSchurUniversalCentralExtension.sourceEquiv
      alternatingSixUniversalCentralExtension).toEquiv

end GroupTheory
end McKayConjecture
