/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.CentralExtensionUniversalityCriterion
import McKayConjecture.GroupTheory.FreePresentationHopfKernel
import McKayConjecture.GroupTheory.FreePresentationUniversalCentralExtension

/-!
# Central closedness from a free presentation

For a perfect group, the free-presentation cover is a universal central
extension.  Consequently, injectivity of its projection implies central
closedness.  The second theorem packages the same criterion in terms of the
project's Hopf-kernel model of the Schur multiplier.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- A perfect group is centrally closed if its free-presentation cover
projects injectively to it. -/
theorem isCentrallyClosed_of_coverProjection_injective
    {U : Type*} [Group U]
    (hperfect : Group.IsPerfect U)
    (hinjective :
      Function.Injective (FreePresentation.coverProjection U)) :
    IsCentrallyClosed U := by
  intro V _ F
  let E : UniversalCentralExtension (FreePresentation.Cover U) U :=
    FreePresentation.universalCentralExtension hperfect
  let e : FreePresentation.Cover U ≃* U :=
    MulEquiv.ofBijective (FreePresentation.coverProjection U)
      ⟨hinjective,
        FreePresentation.coverProjection_surjective U hperfect⟩
  obtain ⟨f, hf, _⟩ := E.lift V F
  refine ⟨f.comp e.symm.toMonoidHom, ?_⟩
  ext u
  have hu := DFunLike.congr_fun hf (e.symm u)
  change F.projection (f (e.symm u)) = u
  exact hu.trans (e.apply_symm_apply u)

/-- A perfect group is centrally closed when its free-presentation Hopf
kernel has cardinality one. -/
theorem isCentrallyClosed_of_hopfKernel_card_one
    {U : Type*} [Group U]
    (hperfect : Group.IsPerfect U)
    (hcard : Nat.card (FreePresentation.HopfKernel U) = 1) :
    IsCentrallyClosed U := by
  apply isCentrallyClosed_of_coverProjection_injective hperfect
  apply
    (MonoidHom.ker_eq_bot_iff
      (FreePresentation.coverProjection U)).mp
  apply Subgroup.eq_bot_of_card_eq
  rw [← FreePresentation.natCard_hopfKernel_eq_natCard_coverProjection_ker]
  exact hcard

end GroupTheory
end McKayConjecture
