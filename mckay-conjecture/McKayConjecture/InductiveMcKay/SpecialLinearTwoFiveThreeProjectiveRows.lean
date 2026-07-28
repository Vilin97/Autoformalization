/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.InnerSemidirectProjective
import McKayConjecture.Character.CentralScalar
import McKayConjecture.InductiveMcKay.ExactNormalizerInnerProjectiveCompatibility
import McKayConjecture.InductiveMcKay.HonestExtensionProjectiveCompatibility
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveThreeEquivariantTable

/-!
# Exact projective rows for `SL(2, 𝔽₅)` at `p = 3`

This file constructs the six projective comparison rows for the explicit
equivariant McKay correspondence.  The faithful pair is treated first.
Its character stabilizer contains only inner automorphisms, so a normalized
lift into the exact normalizer gives both associated projective
representations with literally the same central-defect factor.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple GroupTheory

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The two faithful rows, packaged as `3'`-rows. -/
def specialLinearTwoFiveThreeFaithfulRow
    (k : Fin 2) :
    SpecialLinearTwoFivePPrimeCharacterRow 3 :=
  ⟨.faithful k, by
    fin_cases k <;> decide⟩

/-- The chosen outer automorphism exchanges, rather than fixes, the two
faithful rows. -/
theorem specialLinearTwoFiveThreeOuterFaithfulRow_ne
    (k : Fin 2) :
    specialLinearTwoFiveThreeOuterPPrimeRow
        (specialLinearTwoFiveThreeFaithfulRow k) ≠
      specialLinearTwoFiveThreeFaithfulRow k := by
  fin_cases k <;> native_decide

/-- Every automorphism in the inertia group of a faithful row is inner by
an element of the exact Sylow-three normalizer. -/
theorem
    specialLinearTwoFiveThreeFaithfulStabilizer_exists_innerLift
    (k : Fin 2)
    (a :
      PPrimeCharacterStabilizer
        specialLinearTwoFiveSylowThree
        (specialLinearTwoFivePPrimeCharacterEquiv 3
          (specialLinearTwoFiveThreeFaithfulRow k))) :
    ∃ g : SpecialLinearTwoFiveSylowThreeNormalizer,
      a.1.1 = MulAut.conj g.1 := by
  obtain ⟨g, hinner | houter⟩ :=
    specialLinearTwoFive_sylowThreeStabilizer_eq_inner_or_outer_inner
      a.1
  · exact ⟨g, hinner⟩
  · have haction :=
      specialLinearTwoFive_sylowThreeOuterInner_smul_ambient
        a.1 g houter
        (specialLinearTwoFiveThreeFaithfulRow k)
    have hfix :
        a.1 •
            specialLinearTwoFivePPrimeCharacterEquiv 3
              (specialLinearTwoFiveThreeFaithfulRow k) =
          specialLinearTwoFivePPrimeCharacterEquiv 3
            (specialLinearTwoFiveThreeFaithfulRow k) :=
      MulAction.mem_stabilizer_iff.mp a.2
    have hrows :
        specialLinearTwoFiveThreeOuterPPrimeRow
            (specialLinearTwoFiveThreeFaithfulRow k) =
          specialLinearTwoFiveThreeFaithfulRow k := by
      apply (specialLinearTwoFivePPrimeCharacterEquiv 3).injective
      exact haction.symm.trans hfix
    exact
      (specialLinearTwoFiveThreeOuterFaithfulRow_ne k hrows).elim

/-- A normalized set-theoretic lift of the faithful inertia group into the
exact normalizer. -/
def specialLinearTwoFiveThreeFaithfulStabilizerLift
    (k : Fin 2)
    (a :
      PPrimeCharacterStabilizer
        specialLinearTwoFiveSylowThree
        (specialLinearTwoFivePPrimeCharacterEquiv 3
          (specialLinearTwoFiveThreeFaithfulRow k))) :
    SpecialLinearTwoFiveSylowThreeNormalizer := by
  classical
  exact
    if ha : a = 1 then 1
    else
      Classical.choose
        (specialLinearTwoFiveThreeFaithfulStabilizer_exists_innerLift
          k a)

@[simp]
theorem specialLinearTwoFiveThreeFaithfulStabilizerLift_one
    (k : Fin 2) :
    specialLinearTwoFiveThreeFaithfulStabilizerLift k 1 = 1 := by
  simp [specialLinearTwoFiveThreeFaithfulStabilizerLift]

theorem specialLinearTwoFiveThreeFaithfulStabilizerLift_spec
    (k : Fin 2)
    (a :
      PPrimeCharacterStabilizer
        specialLinearTwoFiveSylowThree
        (specialLinearTwoFivePPrimeCharacterEquiv 3
          (specialLinearTwoFiveThreeFaithfulRow k))) :
    PPrimeCharacterStabilizer.ambientAction a =
      MulAut.conj
        (specialLinearTwoFiveThreeFaithfulStabilizerLift k a).1 := by
  by_cases ha : a = 1
  · subst a
    simp
  · change a.1.1 =
      MulAut.conj
        (specialLinearTwoFiveThreeFaithfulStabilizerLift k a).1
    rw [specialLinearTwoFiveThreeFaithfulStabilizerLift, dif_neg ha]
    exact
      Classical.choose_spec
        (specialLinearTwoFiveThreeFaithfulStabilizer_exists_innerLift
          k a)

/-- The same lift realizes the restricted action on the exact normalizer. -/
theorem
    specialLinearTwoFiveThreeFaithfulStabilizerLift_local_spec
    (k : Fin 2)
    (a :
      PPrimeCharacterStabilizer
        specialLinearTwoFiveSylowThree
        (specialLinearTwoFivePPrimeCharacterEquiv 3
          (specialLinearTwoFiveThreeFaithfulRow k))) :
    (specialLinearTwoFiveThreeEquivariantMcKayEquiv
      |>.toExactNormalizerLocalCorrespondence).stabilizerIntermediateAction
          (specialLinearTwoFivePPrimeCharacterEquiv 3
            (specialLinearTwoFiveThreeFaithfulRow k)) a =
      MulAut.conj
        (specialLinearTwoFiveThreeFaithfulStabilizerLift k a) := by
  apply DFunLike.ext _ _
  intro x
  apply Subtype.ext
  change
    a.1.1 x.1 =
      specialLinearTwoFiveThreeFaithfulStabilizerLift k a * x *
        (specialLinearTwoFiveThreeFaithfulStabilizerLift k a)⁻¹
  rw [
    show
      a.1.1 =
        MulAut.conj
          (specialLinearTwoFiveThreeFaithfulStabilizerLift k a).1 by
      exact
        specialLinearTwoFiveThreeFaithfulStabilizerLift_spec k a]
  rfl

/-- The common scalar attached to a central lift defect. -/
def specialLinearTwoFiveThreeCentralUnit
    (z : SpecialLinearTwoFive) : ℂˣ :=
  if z = 1 then 1 else -1

/-- The center of the ambient binary icosahedral group is `{±1}`. -/
theorem specialLinearTwoFive_mem_center_eq_one_or_neg_one
    (z : SpecialLinearTwoFive)
    (hz : z ∈ Subgroup.center SpecialLinearTwoFive) :
    z = 1 ∨ z = -1 := by
  revert z
  native_decide

/-- The center of the exact Sylow-three normalizer is the same central
involution. -/
theorem
    specialLinearTwoFiveSylowThreeNormalizer_mem_center_eq_one_or_neg_one
    (z : SpecialLinearTwoFiveSylowThreeNormalizer)
    (hz :
      z ∈
        Subgroup.center
          SpecialLinearTwoFiveSylowThreeNormalizer) :
    z.1 = 1 ∨ z.1 = -1 := by
  obtain ⟨q, rfl⟩ :=
    quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer.surjective
      z
  have hqcenter : q ∈ Subgroup.center (QuaternionGroup 3) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro x
    apply
      quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer.injective
    simpa only [map_mul] using
      hz
        (quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer
          x)
  have hq :
      q = QuaternionGroup.a 0 ∨
        q = QuaternionGroup.a 3 := by
    rw [Subgroup.mem_center_iff] at hqcenter
    rcases q with i | i
    · fin_cases i
      · exact Or.inl (by native_decide)
      · exfalso
        apply
          (show
            (QuaternionGroup.xa 0 : QuaternionGroup 3) *
                QuaternionGroup.a 1 ≠
              QuaternionGroup.a 1 * QuaternionGroup.xa 0 by
            native_decide)
        exact hqcenter (QuaternionGroup.xa 0)
      · exfalso
        apply
          (show
            (QuaternionGroup.xa 0 : QuaternionGroup 3) *
                QuaternionGroup.a 2 ≠
              QuaternionGroup.a 2 * QuaternionGroup.xa 0 by
            native_decide)
        exact hqcenter (QuaternionGroup.xa 0)
      · exact Or.inr (by native_decide)
      · exfalso
        apply
          (show
            (QuaternionGroup.xa 0 : QuaternionGroup 3) *
                QuaternionGroup.a 4 ≠
              QuaternionGroup.a 4 * QuaternionGroup.xa 0 by
            native_decide)
        exact hqcenter (QuaternionGroup.xa 0)
      · exfalso
        apply
          (show
            (QuaternionGroup.xa 0 : QuaternionGroup 3) *
                QuaternionGroup.a 5 ≠
              QuaternionGroup.a 5 * QuaternionGroup.xa 0 by
            native_decide)
        exact hqcenter (QuaternionGroup.xa 0)
    · have hnoncentral :
          ∀ j : ZMod 6,
            (QuaternionGroup.a 1 : QuaternionGroup 3) *
                QuaternionGroup.xa j ≠
              QuaternionGroup.xa j * QuaternionGroup.a 1 := by
          intro j
          fin_cases j <;> native_decide
      exfalso
      exact
        hnoncentral i
          (hqcenter (QuaternionGroup.a 1))
  rcases hq with rfl | rfl
  · rw [
      quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer_apply_a]
    exact Or.inl (by native_decide)
  · rw [
      quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer_apply_a]
    exact Or.inr (by native_decide)

/-- A character taking the value `-degree` on the central involution has
the sign scalar action on every central element. -/
theorem irreducibleCharacter_realizationAction_eq_centralUnit
    {G : Type} [Group G] [Finite G]
    (χ : IrreducibleCharacter G)
    (centralInvolution : G)
    (centralUnit : G → ℂˣ)
    (hcenter :
      ∀ z : G, z ∈ Subgroup.center G →
        z = 1 ∨ z = centralInvolution)
    (hunit_one : centralUnit 1 = 1)
    (hunit_neg : centralUnit centralInvolution = -1)
    (hneg :
      χ.values centralInvolution = -(χ.degree : ℂ))
    (z : G) (hz : z ∈ Subgroup.center G) :
    AssociatedExistence.realizationAction χ z =
      scalarLinearEquiv ℂ χ.realization
        (centralUnit z) := by
  rcases hcenter z hz with hz_one | hz_neg
  · subst z
    rw [hunit_one]
    simp
  · rw [hz_neg, hunit_neg]
    have hcentral :
        centralInvolution ∈ Subgroup.center G := by
      simpa only [hz_neg] using hz
    obtain ⟨c, hc⟩ :=
      χ.exists_realization_scalar_of_mem_center
        centralInvolution hcentral
    have hvalue :=
      χ.values_eq_scalar_mul_degree centralInvolution c hc
    rw [hneg] at hvalue
    have hcneg : c = -1 := by
      apply
        mul_right_cancel₀
          (Nat.cast_ne_zero.mpr χ.degree_ne_zero)
      simpa using hvalue.symm
    ext v
    change
      χ.realization.ρ centralInvolution v =
        (-1 : ℂ) • v
    have hv := LinearMap.congr_fun hc v
    change
      χ.realization.ρ centralInvolution v = c • v
        at hv
    rw [hv, hcneg]

/-- The central involution, regarded as an element of the exact
Sylow-three normalizer. -/
def specialLinearTwoFiveSylowThreeNormalizerNegOne :
    SpecialLinearTwoFiveSylowThreeNormalizer :=
  quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer
    (QuaternionGroup.a 3)

@[simp]
theorem specialLinearTwoFiveSylowThreeNormalizerNegOne_val :
    (specialLinearTwoFiveSylowThreeNormalizerNegOne :
      SpecialLinearTwoFive) = -1 := by
  rw [
    specialLinearTwoFiveSylowThreeNormalizerNegOne,
    quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer_apply_a]
  native_decide

/-- A central element of the exact normalizer is either the identity or
the chosen central involution. -/
theorem
    specialLinearTwoFiveSylowThreeNormalizer_mem_center_eq_one_or_negOne
    (z : SpecialLinearTwoFiveSylowThreeNormalizer)
    (hz :
      z ∈
        Subgroup.center
          SpecialLinearTwoFiveSylowThreeNormalizer) :
    z = 1 ∨
      z = specialLinearTwoFiveSylowThreeNormalizerNegOne := by
  rcases
      specialLinearTwoFiveSylowThreeNormalizer_mem_center_eq_one_or_neg_one
        z hz with hz_one | hz_neg
  · exact Or.inl (Subtype.ext hz_one)
  · right
    apply Subtype.ext
    simpa using hz_neg

/-- Both faithful ambient characters have central character `-1`. -/
theorem specialLinearTwoFiveThreeFaithfulAmbient_values_neg_one
    (k : Fin 2) :
    (specialLinearTwoFivePPrimeCharacterEquiv 3
        (specialLinearTwoFiveThreeFaithfulRow k)).1.values (-1) =
      -((specialLinearTwoFivePPrimeCharacterEquiv 3
          (specialLinearTwoFiveThreeFaithfulRow k)).1.degree : ℂ) := by
  change
    (specialLinearTwoFiveIrreducibleCharacter (.faithful k)).values
        (specialLinearTwoFiveConjugacyRepresentative 1) =
      -((specialLinearTwoFiveIrreducibleCharacter
        (.faithful k)).degree : ℂ)
  rw [
    specialLinearTwoFiveIrreducibleCharacter_values_representative,
    specialLinearTwoFiveIrreducibleCharacter_degree]
  fin_cases k <;>
    norm_num [specialLinearTwoFiveCharacterTableValue,
      binaryIcosahedralDefiningTrace,
      specialLinearTwoFiveCharacterRowDegree]

/-- The local character paired with a faithful row is the corresponding
odd linear normalizer character. -/
theorem specialLinearTwoFiveThreeFaithfulLocalCharacter_eq
    (k : Fin 2) :
    (specialLinearTwoFiveThreeEquivariantMcKayEquiv
      |>.toExactNormalizerLocalCorrespondence).localCharacter
        (specialLinearTwoFivePPrimeCharacterEquiv 3
          (specialLinearTwoFiveThreeFaithfulRow k)) =
      specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
        (.linear (if k = 0 then 1 else 3)) := by
  change
    specialLinearTwoFiveThreeEquivariantMcKayEquiv
        (specialLinearTwoFivePPrimeCharacterEquiv 3
          (specialLinearTwoFiveThreeFaithfulRow k)) =
      _
  rw [specialLinearTwoFiveThreeEquivariantMcKayEquiv_apply]
  fin_cases k <;> rfl

/-- The order-four circle character takes the central residue `2` to `-1`. -/
private theorem zmodFourToCircle_two :
    ((ZMod.toCircle (2 : ZMod 4) : Circle) : ℂ) = -1 := by
  calc
    _ = Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * (2 : ℂ) / (4 : ℂ)) :=
      ZMod.toCircle_natCast (N := 4) 2
    _ = -1 := by
      convert Complex.exp_pi_mul_I using 1 <;> ring_nf

/-- The paired odd linear normalizer characters have the same central
character `-1`. -/
theorem specialLinearTwoFiveThreeFaithfulLocal_values_neg_one
    (k : Fin 2) :
    ((specialLinearTwoFiveThreeEquivariantMcKayEquiv
      |>.toExactNormalizerLocalCorrespondence).localCharacter
        (specialLinearTwoFivePPrimeCharacterEquiv 3
          (specialLinearTwoFiveThreeFaithfulRow k))).1.values
            specialLinearTwoFiveSylowThreeNormalizerNegOne =
      -(((specialLinearTwoFiveThreeEquivariantMcKayEquiv
        |>.toExactNormalizerLocalCorrespondence).localCharacter
          (specialLinearTwoFivePPrimeCharacterEquiv 3
            (specialLinearTwoFiveThreeFaithfulRow k))).1.degree : ℂ) := by
  rw [specialLinearTwoFiveThreeFaithfulLocalCharacter_eq]
  change
    (specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
      (.linear (if k = 0 then 1 else 3))).1.values
        (quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer
          (QuaternionGroup.a 3)) =
      -((specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
        (.linear (if k = 0 then 1 else 3))).1.degree : ℂ)
  rw [
    specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv_values,
    specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv_degree_linear,
    quaternionGroupThreePPrimeCharacterEquiv_apply]
  fin_cases k
  · rw [if_pos (by native_decide)]
    rw [quaternionGroupThreePPrimeCharacter]
    rw [quaternionGroupThreeLinearPPrimeCharacter_values_a]
    norm_num only [Nat.cast_one]
    rw [show (3 : ZMod 6).val = 3 by native_decide]
    rw [show
      (1 : ZMod 4) * (2 * ((3 : ℕ) : ZMod 4)) = 2 by
        native_decide]
    exact zmodFourToCircle_two
  · rw [if_neg (by native_decide)]
    rw [quaternionGroupThreePPrimeCharacter]
    rw [quaternionGroupThreeLinearPPrimeCharacter_values_a]
    norm_num only [Nat.cast_one]
    rw [show (3 : ZMod 6).val = 3 by native_decide]
    rw [show
      (3 : ZMod 4) * (2 * ((3 : ℕ) : ZMod 4)) = 2 by
        native_decide]
    exact zmodFourToCircle_two

/-- The common normalized inner lift and central sign give exact
projective compatibility for each faithful `p = 3` row. -/
theorem specialLinearTwoFiveThreeFaithfulRow_tripleCompatible
    (k : Fin 2) :
    specialLinearTwoFiveThreeEquivariantMcKayEquiv
      |>.toExactNormalizerLocalCorrespondence.TripleCompatible
        (specialLinearTwoFivePPrimeCharacterEquiv 3
          (specialLinearTwoFiveThreeFaithfulRow k)) := by
  let e := specialLinearTwoFiveThreeEquivariantMcKayEquiv
  let χ :=
    specialLinearTwoFivePPrimeCharacterEquiv 3
      (specialLinearTwoFiveThreeFaithfulRow k)
  apply e.tripleCompatible_of_innerNormalizerLift χ
    (specialLinearTwoFiveThreeFaithfulStabilizerLift k)
    (specialLinearTwoFiveThreeFaithfulStabilizerLift_one k)
    (specialLinearTwoFiveThreeFaithfulStabilizerLift_spec k)
    specialLinearTwoFiveThreeCentralUnit
  · intro z hz
    apply
      irreducibleCharacter_realizationAction_eq_centralUnit
        χ.1 (-1) specialLinearTwoFiveThreeCentralUnit
        specialLinearTwoFive_mem_center_eq_one_or_neg_one
        (by simp [specialLinearTwoFiveThreeCentralUnit])
        (by
          simp [specialLinearTwoFiveThreeCentralUnit,
            show (-1 : SpecialLinearTwoFive) ≠ 1 by native_decide])
        (specialLinearTwoFiveThreeFaithfulAmbient_values_neg_one k)
        z hz
  · intro z hz
    apply
      irreducibleCharacter_realizationAction_eq_centralUnit
        (e χ).1 specialLinearTwoFiveSylowThreeNormalizerNegOne
        (fun n => specialLinearTwoFiveThreeCentralUnit n.1)
        specialLinearTwoFiveSylowThreeNormalizer_mem_center_eq_one_or_negOne
        (by simp [specialLinearTwoFiveThreeCentralUnit])
        (by
          simp [specialLinearTwoFiveThreeCentralUnit,
            show (-1 : SpecialLinearTwoFive) ≠ 1 by native_decide])
        (specialLinearTwoFiveThreeFaithfulLocal_values_neg_one k)
        z hz

/-- Concrete exact-normalizer projective data for the two faithful
`p = 3` rows. -/
def specialLinearTwoFiveThreeFaithfulProjectiveRowData
    (k : Fin 2) :
    ExactNormalizerProjectiveRowData
      specialLinearTwoFiveThreeEquivariantMcKayEquiv
      (specialLinearTwoFivePPrimeCharacterEquiv 3
        (specialLinearTwoFiveThreeFaithfulRow k)) :=
  ExactNormalizerProjectiveRowData.ofTripleCompatible
    specialLinearTwoFiveThreeEquivariantMcKayEquiv
    (specialLinearTwoFivePPrimeCharacterEquiv 3
      (specialLinearTwoFiveThreeFaithfulRow k))
    (specialLinearTwoFiveThreeFaithfulRow_tripleCompatible k)

end InductiveMcKay
end McKayConjecture
