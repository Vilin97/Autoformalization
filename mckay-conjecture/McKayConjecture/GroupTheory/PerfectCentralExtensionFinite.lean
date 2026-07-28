/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Schreier
import McKayConjecture.GroupTheory.PerfectCentralExtensionCenter

/-!
# Finiteness of perfect central extensions

A perfect central extension of a finite group is finite.  This is the
finiteness step needed in the classical free-presentation construction of a
finite universal central extension.
-/

noncomputable section

open scoped commutatorElement

universe u v

namespace McKayConjecture
namespace GroupTheory
namespace CentralExtension

variable {A : Type u} {Q : Type v}
variable [Group A] [Group Q]

/-- A surjective group homomorphism maps central elements to central
elements. -/
theorem center_le_comap_center
    (E : CentralExtension A Q) :
    Subgroup.center A ≤
      (Subgroup.center Q).comap E.projection := by
  intro a ha
  exact
    map_center_le_center_of_surjective E.surjective
      ⟨a, ha, rfl⟩

/-- The map on quotients by the centers induced by a perfect central
extension. -/
def quotientCenterMap
    (E : CentralExtension A Q) :
    (A ⧸ Subgroup.center A) →*
      (Q ⧸ Subgroup.center Q) :=
  QuotientGroup.map
    (Subgroup.center A)
    (Subgroup.center Q)
    E.projection
    E.center_le_comap_center

/-- A perfect central extension induces an injection after quotienting both
source and target by their centers. -/
theorem quotientCenterMap_injective
    (E : CentralExtension A Q)
    (hperfect : Group.IsPerfect A) :
    Function.Injective E.quotientCenterMap := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [quotientCenterMap, QuotientGroup.ker_map]
  have hcomap :
      (Subgroup.center Q).comap E.projection =
        Subgroup.center A := by
    apply le_antisymm
    · intro a ha
      exact E.mem_center_of_projection_mem_center hperfect ha
    · exact E.center_le_comap_center
  rw [hcomap, QuotientGroup.map_mk'_self]

/-- The quotient of the source by its center is finite when the target is
finite. -/
theorem finite_quotientCenter
    (E : CentralExtension A Q)
    [Finite Q]
    (hperfect : Group.IsPerfect A) :
    Finite (A ⧸ Subgroup.center A) :=
  Finite.of_injective E.quotientCenterMap
    (E.quotientCenterMap_injective hperfect)

/-- Multiplying the first entry of a commutator on the right by a central
element does not change the commutator. -/
private theorem commutatorElement_mul_center_left
    (a b z : A)
    (hz : z ∈ Subgroup.center A) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hzb : ⁅z, b⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp hz b).symm
  simp [hzb]

/-- Multiplying the second entry of a commutator on the right by a central
element does not change the commutator. -/
private theorem commutatorElement_mul_center_right
    (a b z : A)
    (hz : z ∈ Subgroup.center A) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have haz : ⁅a, z⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp hz a)
  rw [haz, mul_one, mul_inv_cancel_right]

/-- A choice of representatives realizes every commutator using a pair of
cosets modulo the center. -/
private def quotientPairCommutator :
    ((A ⧸ Subgroup.center A) ×
        (A ⧸ Subgroup.center A)) →
      commutatorSet A :=
  fun q =>
    ⟨⁅q.1.out, q.2.out⁆,
      commutator_mem_commutatorSet q.1.out q.2.out⟩

/-- Every commutator is obtained from a pair of coset representatives
modulo the center. -/
private theorem quotientPairCommutator_surjective :
    Function.Surjective
      (quotientPairCommutator (A := A)) := by
  intro c
  obtain ⟨a, b, hab⟩ := c.2
  refine
    ⟨((a : A ⧸ Subgroup.center A),
        (b : A ⧸ Subgroup.center A)), ?_⟩
  apply Subtype.ext
  change
    ⁅(a : A ⧸ Subgroup.center A).out,
      (b : A ⧸ Subgroup.center A).out⁆ = c.1
  obtain ⟨za, hza⟩ :=
    QuotientGroup.mk_out_eq_mul
      (Subgroup.center A) a
  obtain ⟨zb, hzb⟩ :=
    QuotientGroup.mk_out_eq_mul
      (Subgroup.center A) b
  rw [hza, hzb,
    commutatorElement_mul_center_left _ _ _ za.2,
    commutatorElement_mul_center_right _ _ _ zb.2,
    hab]

/-- A perfect central extension of a finite group has only finitely many
commutators. -/
theorem finite_commutatorSet
    (E : CentralExtension A Q)
    [Finite Q]
    (hperfect : Group.IsPerfect A) :
    Finite (commutatorSet A) := by
  letI : Finite (A ⧸ Subgroup.center A) :=
    E.finite_quotientCenter hperfect
  exact
    Finite.of_surjective
      (quotientPairCommutator (A := A))
      quotientPairCommutator_surjective

/-- A perfect central extension of a finite group has finite source. -/
theorem finite_source
    (E : CentralExtension A Q)
    [Finite Q]
    (hperfect : Group.IsPerfect A) :
    Finite A := by
  letI : Group.IsPerfect A := hperfect
  letI : Finite (commutatorSet A) :=
    E.finite_commutatorSet hperfect
  letI : Finite (_root_.commutator A) :=
    inferInstance
  exact
    Finite.of_injective
      (fun a : A =>
        (⟨a, Group.IsPerfect.mem_commutator⟩ :
          _root_.commutator A))
      (fun _ _ h => Subtype.ext_iff.mp h)

end CentralExtension
end GroupTheory
end McKayConjecture
