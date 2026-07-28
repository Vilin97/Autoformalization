/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Index
import McKayConjecture.GroupTheory.CentralExtensionSylowNormalizer
import McKayConjecture.GroupTheory.QuasisimpleSylow

/-!
# Prime support in central extensions

Let `U → Q` be a finite central extension.  If a prime `p` does not divide
the order of the target, then every Sylow `p`-subgroup of `U` is contained
in the central kernel.  Thus primes contributed only by a central covering
kernel never produce a nonnormal Sylow case upstairs.

This elementary observation is useful when the source is a universal cover:
the classification-dependent local McKay verification only has to consider
primes occurring in the underlying nonabelian simple target, not all primes
occurring in its Schur multiplier.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace GroupTheory
namespace CentralExtension

variable {U : Type u} {Q : Type v}
variable [Group U] [Group Q] [Finite U] [Finite Q]
variable {p : ℕ} [Fact p.Prime]

/-- A Sylow subgroup at a prime absent from the target of a finite central
extension maps trivially to that target. -/
theorem sylow_map_eq_bot_of_prime_not_dvd_card
    (E : CentralExtension U Q)
    (P : Sylow p U)
    (hp : ¬p ∣ Nat.card Q) :
    (P : Subgroup U).map E.projection = ⊥ := by
  have htarget :
      ((P.mapSurjective E.surjective : Sylow p Q) :
          Subgroup Q) = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rw [Sylow.card_eq_multiplicity,
      Nat.factorization_eq_zero_of_not_dvd hp, pow_zero]
  exact htarget

/-- A Sylow subgroup at a prime absent from the target lies in the kernel
of a finite central extension. -/
theorem sylow_le_ker_of_prime_not_dvd_card
    (E : CentralExtension U Q)
    (P : Sylow p U)
    (hp : ¬p ∣ Nat.card Q) :
    (P : Subgroup U) ≤ E.projection.ker :=
  (Subgroup.map_eq_bot_iff _).mp
    (E.sylow_map_eq_bot_of_prime_not_dvd_card P hp)

/-- A Sylow subgroup at a prime absent from the target is central in the
source of a finite central extension. -/
theorem sylow_le_center_of_prime_not_dvd_card
    (E : CentralExtension U Q)
    (P : Sylow p U)
    (hp : ¬p ∣ Nat.card Q) :
    (P : Subgroup U) ≤ Subgroup.center U :=
  (E.sylow_le_ker_of_prime_not_dvd_card P hp).trans
    E.ker_le_center

/-- In particular, a Sylow subgroup at a prime absent from the target is
normal in the source of a finite central extension. -/
theorem sylow_normal_of_prime_not_dvd_card
    (E : CentralExtension U Q)
    (P : Sylow p U)
    (hp : ¬p ∣ Nat.card Q) :
    (P : Subgroup U).Normal :=
  by
    refine ⟨?_⟩
    intro x hx g
    have hcomm :
        g * x = x * g :=
      Subgroup.mem_center_iff.mp
        (E.sylow_le_center_of_prime_not_dvd_card P hp hx) g
    rw [hcomm]
    simpa using hx

/-- At a prime occurring in the target, a source Sylow subgroup cannot be
contained in the kernel of a surjective homomorphism. -/
theorem sylow_not_le_ker_of_prime_dvd_card
    (E : CentralExtension U Q)
    (P : Sylow p U)
    (hp : p ∣ Nat.card Q) :
    ¬(P : Subgroup U) ≤ E.projection.ker := by
  intro hP
  have hmap :
      (P : Subgroup U).map E.projection = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr hP
  have htarget :
      ((P.mapSurjective E.surjective : Sylow p Q) :
          Subgroup Q) = ⊥ :=
    hmap
  exact
    (P.mapSurjective E.surjective).ne_bot_of_dvd_card hp
      htarget

/-- Over a nonabelian simple target, a source Sylow subgroup at a target
prime is noncentral. -/
theorem sylow_not_le_center_of_prime_dvd_card
    (E : CentralExtension U Q)
    (hQ : IsSimpleGroup Q)
    (hnoncomm : ¬IsMulCommutative Q)
    (P : Sylow p U)
    (hp : p ∣ Nat.card Q) :
    ¬(P : Subgroup U) ≤ Subgroup.center U := by
  rw [← E.ker_eq_center hQ hnoncomm]
  exact E.sylow_not_le_ker_of_prime_dvd_card P hp

/-- For a perfect central cover of a nonabelian simple group, a Sylow
subgroup at a target prime is necessarily nonnormal. -/
theorem sylow_not_normal_of_prime_dvd_card
    (E : CentralExtension U Q)
    (hperfect : Group.IsPerfect U)
    (hQ : IsSimpleGroup Q)
    (hnoncomm : ¬IsMulCommutative Q)
    (P : Sylow p U)
    (hp : p ∣ Nat.card Q) :
    ¬(P : Subgroup U).Normal := by
  intro hnormal
  have hquasisimple : IsQuasisimple U :=
    E.source_isQuasisimple hperfect hQ hnoncomm
  exact
    E.sylow_not_le_center_of_prime_dvd_card
      hQ hnoncomm P hp
      (hquasisimple.normal_sylow_le_center P hnormal)

end CentralExtension
end GroupTheory
end McKayConjecture
