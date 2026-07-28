/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSix
import McKayConjecture.GroupTheory.PerfectCentralExtensionFinite
import McKayConjecture.GroupTheory.UniversalCoverPerfectCoverKernel

/-!
# Comparing kernels of covers of `A₆`

The missing Schur-multiplier calculation for `A₆` can be separated into
explicit upper- and lower-bound tasks.  This file proves the lower-bound
bridge without assuming a model for `6.A₆`: every finite perfect central
cover of `A₆` is a quotient of every universal central extension, and its
kernel is a quotient of the universal center.

Consequently, either one perfect sixfold cover, or a perfect double cover
and a perfect triple cover, proves that the center of every universal
central extension of `A₆` has order divisible by six.  The proofs below
include the restriction-to-kernels check; they do not merely compare total
group orders.
-/

noncomputable section

open scoped IsMulCommutative

namespace McKayConjecture
namespace GroupTheory

variable {U A : Type}
variable [Group U] [Group A]

/-- The kernel order of a finite perfect central cover of `A₆` divides the
center order of every universal central extension of `A₆`.  Finiteness of
the universal source is derived rather than assumed. -/
theorem natCard_perfectCentralCoverKernel_dvd_universalCenter_alternatingSix
    [Finite A]
    (E : UniversalCentralExtension U AlternatingSix)
    (F : CentralExtension A AlternatingSix)
    (hperfect : Group.IsPerfect A) :
    Nat.card F.projection.ker ∣
      Nat.card (Subgroup.center U) := by
  letI : Finite U :=
    E.toCentralExtension.finite_source E.sourcePerfect
  rw [← E.toCentralExtension.ker_eq_center
    (inferInstance : IsSimpleGroup AlternatingSix)
    alternatingSix_not_isMulCommutative]
  exact
    E.natCard_perfectCoverKernel_dvd_natCard_universalKernel
      F hperfect

/-- Exact cardinality comparison: the only gap between a perfect central
cover of `A₆` and the universal center is the kernel of the canonical map
from the universal source to that cover. -/
theorem natCard_universalCenter_alternatingSix_eq_comparisonKernel_mul_coverKernel
    [Finite A]
    (E : UniversalCentralExtension U AlternatingSix)
    (F : CentralExtension A AlternatingSix)
    (hperfect : Group.IsPerfect A) :
    Nat.card (Subgroup.center U) =
      Nat.card (E.mapToCentralExtension F).ker *
        Nat.card F.projection.ker := by
  letI : Finite U :=
    E.toCentralExtension.finite_source E.sourcePerfect
  rw [← E.toCentralExtension.ker_eq_center
    (inferInstance : IsSimpleGroup AlternatingSix)
    alternatingSix_not_isMulCommutative]
  exact
    E.natCard_universalKernel_eq_natCard_comparisonKernel_mul_perfectCoverKernel
      F hperfect

/-- A concrete perfect sixfold cover gives the divisibility half of the
Schur-multiplier computation for every universal cover of `A₆`. -/
theorem six_dvd_natCard_universalCenter_alternatingSix_of_perfectCover
    [Finite A]
    (E : UniversalCentralExtension U AlternatingSix)
    (F : CentralExtension A AlternatingSix)
    (hperfect : Group.IsPerfect A)
    (hkernel : Nat.card F.projection.ker = 6) :
    6 ∣ Nat.card (Subgroup.center U) := by
  rw [← hkernel]
  exact
    natCard_perfectCentralCoverKernel_dvd_universalCenter_alternatingSix
      E F hperfect

/-- It is enough to construct separate perfect double and triple covers:
their coprime kernel orders force the product `6` to divide the universal
center order. -/
theorem six_dvd_natCard_universalCenter_alternatingSix_of_double_and_triple_covers
    {A₂ A₃ : Type}
    [Group A₂] [Group A₃] [Finite A₂] [Finite A₃]
    (E : UniversalCentralExtension U AlternatingSix)
    (F₂ : CentralExtension A₂ AlternatingSix)
    (F₃ : CentralExtension A₃ AlternatingSix)
    (hperfect₂ : Group.IsPerfect A₂)
    (hperfect₃ : Group.IsPerfect A₃)
    (hkernel₂ : Nat.card F₂.projection.ker = 2)
    (hkernel₃ : Nat.card F₃.projection.ker = 3) :
    6 ∣ Nat.card (Subgroup.center U) := by
  have htwo :
      2 ∣ Nat.card (Subgroup.center U) := by
    rw [← hkernel₂]
    exact
      natCard_perfectCentralCoverKernel_dvd_universalCenter_alternatingSix
        E F₂ hperfect₂
  have hthree :
      3 ∣ Nat.card (Subgroup.center U) := by
    rw [← hkernel₃]
    exact
      natCard_perfectCentralCoverKernel_dvd_universalCenter_alternatingSix
        E F₃ hperfect₃
  have hproduct :=
    (show Nat.Coprime 2 3 by norm_num).mul_dvd_of_dvd_of_dvd
      htwo hthree
  norm_num at hproduct
  exact hproduct

/-- The preceding divisibility result also gives the numerical lower bound
on the universal center. -/
theorem six_le_natCard_universalCenter_alternatingSix_of_perfectCover
    [Finite A]
    (E : UniversalCentralExtension U AlternatingSix)
    (F : CentralExtension A AlternatingSix)
    (hperfect : Group.IsPerfect A)
    (hkernel : Nat.card F.projection.ker = 6) :
    6 ≤ Nat.card (Subgroup.center U) := by
  letI : Finite U :=
    E.toCentralExtension.finite_source E.sourcePerfect
  exact Nat.le_of_dvd Nat.card_pos
    (six_dvd_natCard_universalCenter_alternatingSix_of_perfectCover
      E F hperfect hkernel)

/-- For a perfect sixfold cover, proving the Schur-multiplier order is now
exactly the injectivity of the canonical comparison map. -/
theorem natCard_universalCenter_alternatingSix_eq_six_iff_comparison_injective
    [Finite A]
    (E : UniversalCentralExtension U AlternatingSix)
    (F : CentralExtension A AlternatingSix)
    (hperfect : Group.IsPerfect A)
    (hkernel : Nat.card F.projection.ker = 6) :
    Nat.card (Subgroup.center U) = 6 ↔
      Function.Injective (E.mapToCentralExtension F) := by
  letI : Finite U :=
    E.toCentralExtension.finite_source E.sourcePerfect
  have hcard :
      Nat.card (Subgroup.center U) =
        Nat.card (E.mapToCentralExtension F).ker * 6 := by
    rw [natCard_universalCenter_alternatingSix_eq_comparisonKernel_mul_coverKernel
      E F hperfect, hkernel]
  constructor
  · intro hcenter
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply Subgroup.card_eq_one.mp
    omega
  · intro hinjective
    have hker :
        (E.mapToCentralExtension F).ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff _).mpr hinjective
    rw [hcard, hker]
    simp

/-- Specialization of the kernel divisibility bridge to the fixed
free-presentation universal cover used elsewhere in the `A₆` reduction. -/
theorem natCard_perfectCentralCoverKernel_dvd_center_alternatingSixUniversalCover
    [Finite A]
    (F : CentralExtension A AlternatingSix)
    (hperfect : Group.IsPerfect A) :
    Nat.card F.projection.ker ∣
      Nat.card (Subgroup.center AlternatingSixUniversalCover) :=
  natCard_perfectCentralCoverKernel_dvd_universalCenter_alternatingSix
    alternatingSixUniversalCentralExtension F hperfect

end GroupTheory
end McKayConjecture
