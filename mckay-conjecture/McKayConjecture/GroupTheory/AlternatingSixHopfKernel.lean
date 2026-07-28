/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Data.Nat.Squarefree
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import McKayConjecture.GroupTheory.AlternatingSixSylowFiveNormalizer
import McKayConjecture.GroupTheory.AlternatingSixUniversalCoverKernel
import McKayConjecture.GroupTheory.FreePresentationHopfKernel
import McKayConjecture.GroupTheory.UniversalCentralExtensionSourceEquiv

/-!
# The exact Hopf-formula obstruction for the universal cover of `A₆`

For the canonical free presentation `F → A₆`, put `R = ker(F → A₆)` and
`D = [F,F]`.  The only group-theoretic cardinality calculation still needed
to identify the canonical universal cover with `6.A₆` is

`|(R ∩ D) / [F,R]| = 6`.

This file names that precise proposition, proves that it is equivalent to
the order-six center statement, and routes its consequences through the
already checked universal-cover and Sylow calculations.
-/

noncomputable section

open scoped IsMulCommutative

namespace McKayConjecture
namespace GroupTheory

local instance alternatingSixHopfFactPrimeThree :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

local instance alternatingSixHopfFactPrimeFive :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- The Hopf-formula quotient `(R ∩ [F,F]) / [F,R]` for the canonical free
presentation of `A₆`. -/
abbrev AlternatingSixHopfKernel :=
  FreePresentation.HopfKernel AlternatingSix

/-- The Hopf quotient is canonically the center of the chosen universal
cover, as a group and not merely at the level of cardinalities. -/
def alternatingSixHopfKernelEquivCenter :
    AlternatingSixHopfKernel ≃*
      Subgroup.center AlternatingSixUniversalCover :=
  (FreePresentation.hopfKernelEquivCoverProjectionKer AlternatingSix).trans
    (MulEquiv.subgroupCongr
      alternatingSixUniversalCentralExtension_ker_eq_center)

instance alternatingSixHopfKernelFinite :
    Finite AlternatingSixHopfKernel :=
  Finite.of_equiv
    (Subgroup.center AlternatingSixUniversalCover)
    alternatingSixHopfKernelEquivCenter.symm.toEquiv

/-- The exact remaining Schur-multiplier computation for the canonical
free-presentation model of `A₆`. -/
def AlternatingSixHopfKernelHasOrderSix : Prop :=
  Nat.card AlternatingSixHopfKernel = 6

/-- The Hopf quotient and the center of the canonical universal cover have
the same cardinality. -/
theorem natCard_alternatingSixHopfKernel_eq_center :
    Nat.card AlternatingSixHopfKernel =
      Nat.card (Subgroup.center AlternatingSixUniversalCover) :=
  Nat.card_congr alternatingSixHopfKernelEquivCenter.toEquiv

/-- Computing the Hopf quotient to have order six is exactly the missing
center-order statement; there is no further group-theoretic gap between
these formulations. -/
theorem alternatingSixHopfKernelHasOrderSix_iff_center :
    AlternatingSixHopfKernelHasOrderSix ↔
      Nat.card (Subgroup.center AlternatingSixUniversalCover) = 6 := by
  unfold AlternatingSixHopfKernelHasOrderSix
  rw [natCard_alternatingSixHopfKernel_eq_center]

namespace AlternatingSixHopfKernelHasOrderSix

/-- The named Hopf computation gives the center order of the fixed cover. -/
theorem center
    (h : AlternatingSixHopfKernelHasOrderSix) :
    Nat.card (Subgroup.center AlternatingSixUniversalCover) = 6 :=
  alternatingSixHopfKernelHasOrderSix_iff_center.mp h

/-- The canonical cover projection has kernel of order six. -/
theorem projectionKernel
    (h : AlternatingSixHopfKernelHasOrderSix) :
    Nat.card (FreePresentation.coverProjection AlternatingSix).ker = 6 := by
  rw [← FreePresentation.natCard_hopfKernel_eq_natCard_coverProjection_ker]
  exact h

/-- The canonical universal cover has order `360 · 6 = 2160`. -/
theorem cover
    (h : AlternatingSixHopfKernelHasOrderSix) :
    Nat.card AlternatingSixUniversalCover = 2160 := by
  rw [natCard_alternatingSixUniversalCover, h.center]

/-- The center is cyclic once the Hopf quotient has order six. -/
theorem centerIsCyclic
    (h : AlternatingSixHopfKernelHasOrderSix) :
    IsCyclic (Subgroup.center AlternatingSixUniversalCover) := by
  letI :
    IsZGroup (Subgroup.center AlternatingSixUniversalCover) :=
    IsZGroup.of_squarefree (by
      rw [h.center]
      simpa using
        (Nat.squarefree_mul
          (m := 2) (n := 3) (by norm_num)).mpr
            ⟨Nat.prime_two.squarefree,
              Nat.prime_three.squarefree⟩)
  infer_instance

/-- The Hopf quotient itself is cyclic once its order has been computed. -/
theorem hopfKernelIsCyclic
    (h : AlternatingSixHopfKernelHasOrderSix) :
    IsCyclic AlternatingSixHopfKernel :=
  alternatingSixHopfKernelEquivCenter.isCyclic.mpr h.centerIsCyclic

/-- The fixed Sylow `2`-subgroup of the canonical cover has order sixteen. -/
theorem sylowTwo
    (h : AlternatingSixHopfKernelHasOrderSix) :
    Nat.card (alternatingSixUniversalCoverSylow 2) = 16 :=
  natCard_alternatingSixUniversalCoverSylowTwo_of_center_eq_six h.center

/-- The fixed Sylow `3`-subgroup of the canonical cover has order
twenty-seven. -/
theorem sylowThree
    (h : AlternatingSixHopfKernelHasOrderSix) :
    Nat.card (alternatingSixUniversalCoverSylow 3) = 27 :=
  natCard_alternatingSixUniversalCoverSylowThree_of_center_eq_six h.center

/-- The fixed Sylow `5`-subgroup of the canonical cover has order five. -/
theorem sylowFive
    (h : AlternatingSixHopfKernelHasOrderSix) :
    Nat.card (alternatingSixUniversalCoverSylow 5) = 5 :=
  natCard_alternatingSixUniversalCoverSylowFive_of_center_eq_six h.center

/-- The fixed Sylow `5`-projection is an isomorphism onto its image in
`A₆`. -/
def sylowFiveEquivTarget
    (h : AlternatingSixHopfKernelHasOrderSix) :
    alternatingSixUniversalCoverSylow 5 ≃*
      alternatingSixUniversalCoverTargetSylow 5 :=
  alternatingSixUniversalCoverSylowFiveEquivTarget_of_center_eq_six h.center

/-- The fixed Sylow `5`-subgroup of the canonical cover is cyclic. -/
theorem sylowFiveIsCyclic
    (h : AlternatingSixHopfKernelHasOrderSix) :
    IsCyclic (alternatingSixUniversalCoverSylow 5) :=
  alternatingSixUniversalCoverSylowFive_isCyclic_of_center_eq_six h.center

/-- The fixed Sylow `5`-normalizer in the canonical cover has order sixty. -/
theorem sylowFiveNormalizer
    (h : AlternatingSixHopfKernelHasOrderSix) :
    Nat.card
        (Subgroup.normalizer
          (alternatingSixUniversalCoverSylow 5 :
            Set AlternatingSixUniversalCover)) =
      60 :=
  natCard_normalizer_alternatingSixUniversalCoverSylowFive_of_center_eq_six
    h.center

/-- Every universal central extension of `A₆`, not only the chosen
free-presentation model, has center of order six. -/
theorem centerOfUniversalCentralExtension
    {U : Type} [Group U]
    (h : AlternatingSixHopfKernelHasOrderSix)
    (E : UniversalCentralExtension U AlternatingSix) :
    Nat.card (Subgroup.center U) = 6 := by
  rw [Nat.card_congr
    (Subgroup.centerCongr
      (E.sourceEquiv alternatingSixUniversalCentralExtension)).toEquiv]
  exact h.center

/-- Every universal central extension of `A₆` has source order `2160`. -/
theorem sourceOfUniversalCentralExtension
    {U : Type} [Group U]
    (h : AlternatingSixHopfKernelHasOrderSix)
    (E : UniversalCentralExtension U AlternatingSix) :
    Nat.card U = 2160 := by
  rw [Nat.card_congr
    (E.sourceEquiv alternatingSixUniversalCentralExtension).toEquiv]
  exact h.cover

/-- For any perfect sixfold central cover of `A₆`, the canonical comparison
from a universal cover is injective. -/
theorem comparisonInjective
    {U A : Type} [Group U] [Group A] [Finite A]
    (h : AlternatingSixHopfKernelHasOrderSix)
    (E : UniversalCentralExtension U AlternatingSix)
    (F : CentralExtension A AlternatingSix)
    (hperfect : Group.IsPerfect A)
    (hkernel : Nat.card F.projection.ker = 6) :
    Function.Injective (E.mapToCentralExtension F) := by
  apply
    (natCard_universalCenter_alternatingSix_eq_six_iff_comparison_injective
      E F hperfect hkernel).mp
  exact h.centerOfUniversalCentralExtension E

end AlternatingSixHopfKernelHasOrderSix

end GroupTheory
end McKayConjecture
