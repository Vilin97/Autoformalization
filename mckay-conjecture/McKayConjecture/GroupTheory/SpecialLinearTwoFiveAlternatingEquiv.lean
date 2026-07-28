/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.SpecificGroups.Alternating
import McKayConjecture.GroupTheory.SpecialLinearTwoFiveCentralCover

/-!
# The exceptional isomorphism `PSL(2, 𝔽₅) ≅ A₅`

We construct the exceptional isomorphism through the faithful five-point
action of `PSL(2, 𝔽₅)`.

The concrete quaternion Sylow subgroup of `SL(2, 𝔽₅)` has normalizer of
order `24`, hence has five conjugates.  We enumerate those conjugate
eight-element tables directly and let `SL(2, 𝔽₅)` act on them.  A finite
calculation identifies the kernel with the two-element center.  Since the
source is perfect, every permutation in the image is even.  The resulting
map to `A₅` has kernel the center and image of order `60`, so it is
surjective and descends to the required isomorphism.
-/

noncomputable section

open Matrix
open scoped MatrixGroups

namespace McKayConjecture
namespace GroupTheory

/-- Conjugate every entry of a finite group table by `g`. -/
def conjugateFinset
    {G : Type*} [Group G] [DecidableEq G]
    (g : G) (s : Finset G) : Finset G :=
  s.image fun x ↦ g * x * g⁻¹

@[simp]
theorem mem_conjugateFinset
    {G : Type*} [Group G] [DecidableEq G]
    (g x : G) (s : Finset G) :
    x ∈ conjugateFinset g s ↔
      g⁻¹ * x * g ∈ s := by
  constructor
  · rw [conjugateFinset, Finset.mem_image]
    rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    refine Finset.mem_image.mpr
      ⟨g⁻¹ * x * g, hx, ?_⟩
    simp [mul_assoc]

@[simp]
theorem conjugateFinset_one
    {G : Type*} [Group G] [DecidableEq G]
    (s : Finset G) :
    conjugateFinset 1 s = s := by
  ext x
  simp

theorem conjugateFinset_mul
    {G : Type*} [Group G] [DecidableEq G]
    (g h : G) (s : Finset G) :
    conjugateFinset (g * h) s =
      conjugateFinset g (conjugateFinset h s) := by
  ext x
  simp [mul_assoc]

/-- The five conjugate quaternion-subgroup tables. -/
def specialLinearTwoFiveQuaternionConjugates :
    Finset (Finset SpecialLinearTwoFive) :=
  Finset.univ.image fun g : SpecialLinearTwoFive ↦
    conjugateFinset g specialLinearTwoFiveQuaternionElements

/-- There are exactly five conjugates of the quaternion Sylow subgroup. -/
theorem card_specialLinearTwoFiveQuaternionConjugates :
    specialLinearTwoFiveQuaternionConjugates.card = 5 := by
  native_decide

/-- A point of the concrete five-point action is one of the five conjugate
quaternion tables. -/
abbrev SpecialLinearTwoFiveQuaternionConjugate :=
  ↥specialLinearTwoFiveQuaternionConjugates

/-- Conjugation acts on the five quaternion tables. -/
instance specialLinearTwoFiveQuaternionConjugateMulAction :
    MulAction SpecialLinearTwoFive
      SpecialLinearTwoFiveQuaternionConjugate where
  smul g s :=
    ⟨conjugateFinset g s.1, by
      obtain ⟨h, _, hs⟩ :=
        Finset.mem_image.mp s.2
      refine Finset.mem_image.mpr
        ⟨g * h, Finset.mem_univ _, ?_⟩
      rw [conjugateFinset_mul, hs]⟩
  one_smul s := by
    apply Subtype.ext
    exact conjugateFinset_one s.1
  mul_smul g h s := by
    apply Subtype.ext
    exact conjugateFinset_mul g h s.1

/-- Coordinate the five conjugate quaternion tables by `Fin 5`. -/
def specialLinearTwoFiveQuaternionConjugatesEquivFinFive :
    SpecialLinearTwoFiveQuaternionConjugate ≃ Fin 5 :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_coe,
      card_specialLinearTwoFiveQuaternionConjugates])

/-- The raw permutation action on the five quaternion tables. -/
def specialLinearTwoFiveQuaternionAction :
    SpecialLinearTwoFive →*
      Equiv.Perm SpecialLinearTwoFiveQuaternionConjugate :=
  MulAction.toPermHom _ _

/-- The same action in fixed `Fin 5` coordinates. -/
def specialLinearTwoFivePermutationAction :
    SpecialLinearTwoFive →* Equiv.Perm (Fin 5) :=
  specialLinearTwoFiveQuaternionConjugatesEquivFinFive
    |>.permCongrHom.toMonoidHom.comp
      specialLinearTwoFiveQuaternionAction

/-- An executable list of the kernel of the raw five-point action. -/
def specialLinearTwoFiveQuaternionActionKernelElements :
    Finset SpecialLinearTwoFive :=
  Finset.univ.filter fun g ↦
    specialLinearTwoFiveQuaternionAction g = 1

theorem coe_specialLinearTwoFiveQuaternionAction_ker :
    (specialLinearTwoFiveQuaternionAction.ker :
      Set SpecialLinearTwoFive) =
      specialLinearTwoFiveQuaternionActionKernelElements := by
  ext g
  simp [specialLinearTwoFiveQuaternionActionKernelElements,
    MonoidHom.mem_ker]

/-- The raw five-point action has a two-element kernel. -/
theorem card_specialLinearTwoFiveQuaternionActionKernelElements :
    specialLinearTwoFiveQuaternionActionKernelElements.card = 2 := by
  native_decide

theorem natCard_specialLinearTwoFiveQuaternionAction_ker :
    Nat.card specialLinearTwoFiveQuaternionAction.ker = 2 := by
  change
    (specialLinearTwoFiveQuaternionAction.ker :
      Set SpecialLinearTwoFive).ncard = 2
  rw [coe_specialLinearTwoFiveQuaternionAction_ker]
  simpa using
    card_specialLinearTwoFiveQuaternionActionKernelElements

/-- Every central matrix fixes every quaternion conjugate. -/
theorem center_le_specialLinearTwoFiveQuaternionAction_ker :
    Subgroup.center SpecialLinearTwoFive ≤
      specialLinearTwoFiveQuaternionAction.ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  apply Equiv.ext
  intro s
  apply Subtype.ext
  change conjugateFinset z s.1 = s.1
  ext x
  rw [mem_conjugateFinset]
  have hcommute :
      z * x = x * z :=
    (Subgroup.mem_center_iff.mp hz x).symm
  have hconj : z⁻¹ * x * z = x := by
    calc
      z⁻¹ * x * z = z⁻¹ * (x * z) := by
        rw [mul_assoc]
      _ = z⁻¹ * (z * x) := by
        rw [← hcommute]
      _ = x := by simp
  calc
    z⁻¹ * x * z ∈ s.1 ↔ x ∈ s.1 := by rw [hconj]
    _ ↔ x ∈ s.1 := Iff.rfl

/-- The kernel of the five-point action is exactly the center. -/
theorem specialLinearTwoFiveQuaternionAction_ker :
    specialLinearTwoFiveQuaternionAction.ker =
      Subgroup.center SpecialLinearTwoFive := by
  letI : Fintype
      (Subgroup.center SpecialLinearTwoFive) :=
    Fintype.ofFinite _
  letI : Fintype
      specialLinearTwoFiveQuaternionAction.ker :=
    Fintype.ofFinite _
  apply SetLike.coe_injective
  symm
  apply Set.eq_of_subset_of_card_le
    center_le_specialLinearTwoFiveQuaternionAction_ker
  have hker :
      Fintype.card
        specialLinearTwoFiveQuaternionAction.ker = 2 := by
    simpa only [Nat.card_eq_fintype_card] using
      natCard_specialLinearTwoFiveQuaternionAction_ker
  have hcenter :
      Fintype.card
        (Subgroup.center SpecialLinearTwoFive) = 2 := by
    simpa only [Nat.card_eq_fintype_card] using
      natCard_center_specialLinearTwoFive
  exact le_of_eq (hker.trans hcenter.symm)

/-- Changing coordinates from the five quaternion tables to `Fin 5` does
not change the kernel. -/
theorem specialLinearTwoFivePermutationAction_ker :
    specialLinearTwoFivePermutationAction.ker =
      Subgroup.center SpecialLinearTwoFive := by
  rw [← specialLinearTwoFiveQuaternionAction_ker]
  ext g
  constructor
  · intro hg
    rw [MonoidHom.mem_ker]
    exact
      specialLinearTwoFiveQuaternionConjugatesEquivFinFive
        |>.permCongrHom.injective (by
          simpa only [specialLinearTwoFivePermutationAction,
            MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
            Function.comp_apply, map_one] using
            (MonoidHom.mem_ker.mp hg))
  · intro hg
    rw [MonoidHom.mem_ker] at hg ⊢
    change
      (specialLinearTwoFiveQuaternionConjugatesEquivFinFive
        |>.permCongrHom)
          (specialLinearTwoFiveQuaternionAction g) = 1
    rw [hg, map_one]

/-- Perfectness of `SL(2, 𝔽₅)` forces every permutation arising from the
five-point action to be even. -/
theorem specialLinearTwoFivePermutationAction_mem_alternatingGroup
    (g : SpecialLinearTwoFive) :
    specialLinearTwoFivePermutationAction g ∈
      alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  apply MonoidHom.mem_ker.mp
  exact
    Abelianization.commutator_subset_ker
      (Equiv.Perm.sign.comp
        specialLinearTwoFivePermutationAction)
      Group.IsPerfect.mem_commutator

/-- The concrete action of `SL(2, 𝔽₅)` on five quaternion conjugates,
regarded as a homomorphism to `A₅`. -/
def specialLinearTwoFiveAlternatingAction :
    SpecialLinearTwoFive →* alternatingGroup (Fin 5) :=
  specialLinearTwoFivePermutationAction.codRestrict
    (alternatingGroup (Fin 5))
    specialLinearTwoFivePermutationAction_mem_alternatingGroup

/-- The kernel of the concrete `A₅` action is the center. -/
theorem specialLinearTwoFiveAlternatingAction_ker :
    specialLinearTwoFiveAlternatingAction.ker =
      Subgroup.center SpecialLinearTwoFive := by
  rw [← specialLinearTwoFivePermutationAction_ker]
  ext g
  simp [specialLinearTwoFiveAlternatingAction,
    MonoidHom.mem_ker]

/-- The concrete alternating group on five letters has order `60`. -/
theorem natCard_alternatingGroupFinFive :
    Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup]
  norm_num

/-- The concrete action onto `A₅` is surjective. -/
theorem specialLinearTwoFiveAlternatingAction_surjective :
    Function.Surjective
      specialLinearTwoFiveAlternatingAction := by
  apply MonoidHom.surjective_of_card_ker_le_div
  rw [specialLinearTwoFiveAlternatingAction_ker,
    natCard_center_specialLinearTwoFive,
    natCard_specialLinearTwoFive,
    natCard_alternatingGroupFinFive]

/-- The exceptional isomorphism
`PSL(2, ZMod 5) ≃* alternatingGroup (Fin 5)`, constructed from the action
on the five quaternion Sylow subgroups of `SL(2, ZMod 5)`. -/
def projectiveSpecialLinearTwoFiveEquivAlternatingGroup :
    ProjectiveSpecialLinearTwoFive ≃*
      alternatingGroup (Fin 5) :=
  (QuotientGroup.quotientMulEquivOfEq
      specialLinearTwoFiveAlternatingAction_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      specialLinearTwoFiveAlternatingAction
      specialLinearTwoFiveAlternatingAction_surjective)

end GroupTheory
end McKayConjecture
