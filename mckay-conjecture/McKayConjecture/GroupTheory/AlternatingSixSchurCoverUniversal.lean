/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverLift

/-!
# Universality of the explicit sixfold-cover presentation

The corrected-lift construction supplies existence of a map to every
central extension of `A₆`.  Perfectness of the explicit source supplies
uniqueness.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- The explicit Schur-cover presentation is a universal central
extension of `A₆`. -/
def alternatingSixSchurUniversalCentralExtension :
    UniversalCentralExtension
      AlternatingSixSchurPresentedGroup AlternatingSix where
  toCentralExtension :=
    alternatingSixSchurCentralExtension
  sourcePerfect :=
    alternatingSixSchurPresentedGroup_isPerfect
  lift := by
    intro V _ F
    obtain ⟨σ, hσ⟩ :=
      alternatingSixSchur_exists_lift F
    refine ⟨σ, hσ, ?_⟩
    intro τ hτ
    exact
      F.hom_ext_of_domain_perfect
        alternatingSixSchurPresentedGroup_isPerfect
        τ σ (hτ.trans hσ.symm)

end GroupTheory
end McKayConjecture
