/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.TwoPointCenterScalar
import McKayConjecture.InductiveMcKay.ExactNormalizerInnerProjectiveCompatibility
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveFiveTrivialProjectiveRow

/-!
# Inner-stabilizer projective rows at `p = 5`

The four two-dimensional normalizer rows correspond to the two faithful
and two symmetric-square ambient rows.  The diagonal outer automorphism
exchanges each row with its opposite partner, so each inertia group is
implemented entirely by the exact Sylow-five normalizer.  A common
normalized inner lift and the common central sign then give literally
equal projective factors.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple GroupTheory
open QuaternionGroupFive

local instance factPrimeFiveForInnerProjectiveRows :
    Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The ambient row paired with the `k`-th two-dimensional normalizer
character. -/
def specialLinearTwoFiveFiveTwoDimensionalPPrimeRow
    (k : Fin 4) :
    SpecialLinearTwoFivePPrimeCharacterRow 5 :=
  specialLinearTwoFiveFiveCharacterRowEquiv.symm
    (.twoDimensional k)

@[simp]
theorem specialLinearTwoFiveFiveCharacterRowEquiv_twoDimensionalRow
    (k : Fin 4) :
    specialLinearTwoFiveFiveCharacterRowEquiv
        (specialLinearTwoFiveFiveTwoDimensionalPPrimeRow k) =
      .twoDimensional k :=
  Equiv.apply_symm_apply _ _

@[simp]
theorem specialLinearTwoFiveFiveTwoDimensionalPPrimeRow_zero_val :
    (specialLinearTwoFiveFiveTwoDimensionalPPrimeRow 0).1 =
      .faithful 0 := by
  rfl

@[simp]
theorem specialLinearTwoFiveFiveTwoDimensionalPPrimeRow_one_val :
    (specialLinearTwoFiveFiveTwoDimensionalPPrimeRow 1).1 =
      .symmetricSquare 0 := by
  rfl

@[simp]
theorem specialLinearTwoFiveFiveTwoDimensionalPPrimeRow_two_val :
    (specialLinearTwoFiveFiveTwoDimensionalPPrimeRow 2).1 =
      .faithful 1 := by
  rfl

@[simp]
theorem specialLinearTwoFiveFiveTwoDimensionalPPrimeRow_three_val :
    (specialLinearTwoFiveFiveTwoDimensionalPPrimeRow 3).1 =
      .symmetricSquare 1 := by
  rfl

/-- The outer row permutation has no fixed point on these four rows. -/
theorem specialLinearTwoFiveFiveOuter_twoDimensionalRow_ne
    (k : Fin 4) :
    specialLinearTwoFiveFiveOuterPPrimeRow
        (specialLinearTwoFiveFiveTwoDimensionalPPrimeRow k) ≠
      specialLinearTwoFiveFiveTwoDimensionalPPrimeRow k := by
  intro h
  have hrows :=
    congrArg specialLinearTwoFiveFiveCharacterRowEquiv h
  rw [specialLinearTwoFiveFiveCharacterRowEquiv_map_outer,
    specialLinearTwoFiveFiveCharacterRowEquiv_twoDimensionalRow]
      at hrows
  injection hrows with hk
  fin_cases k <;> contradiction

/-- Every automorphism stabilizing one of the four moved ambient rows is
inner by an element of the exact Sylow-five normalizer. -/
theorem
    specialLinearTwoFiveFiveTwoDimensionalStabilizer_exists_innerLift
    (k : Fin 4)
    (a :
      PPrimeCharacterStabilizer
        specialLinearTwoFiveSylowFive
        (specialLinearTwoFivePPrimeCharacterEquiv 5
          (specialLinearTwoFiveFiveTwoDimensionalPPrimeRow k))) :
    ∃ g : SylowNormalizer specialLinearTwoFiveSylowFive,
      a.1.1 = MulAut.conj g.1 := by
  obtain ⟨g, hinner | houter⟩ :=
    specialLinearTwoFive_sylowFiveStabilizer_eq_inner_or_outer_inner
      a.1
  · exact ⟨g, hinner⟩
  · have haction :=
      specialLinearTwoFive_sylowFiveOuterInner_smul_ambient
        a.1 g houter
        (specialLinearTwoFiveFiveTwoDimensionalPPrimeRow k)
    have hfix :
        a.1 •
            specialLinearTwoFivePPrimeCharacterEquiv 5
              (specialLinearTwoFiveFiveTwoDimensionalPPrimeRow k) =
          specialLinearTwoFivePPrimeCharacterEquiv 5
            (specialLinearTwoFiveFiveTwoDimensionalPPrimeRow k) :=
      MulAction.mem_stabilizer_iff.mp a.2
    have hrows :
        specialLinearTwoFiveFiveOuterPPrimeRow
            (specialLinearTwoFiveFiveTwoDimensionalPPrimeRow k) =
          specialLinearTwoFiveFiveTwoDimensionalPPrimeRow k := by
      apply (specialLinearTwoFivePPrimeCharacterEquiv 5).injective
      exact haction.symm.trans hfix
    exact
      (specialLinearTwoFiveFiveOuter_twoDimensionalRow_ne k hrows).elim

/-- A normalized set-theoretic lift of a moved-row inertia group into the
exact normalizer. -/
def specialLinearTwoFiveFiveTwoDimensionalStabilizerLift
    (k : Fin 4)
    (a :
      PPrimeCharacterStabilizer
        specialLinearTwoFiveSylowFive
        (specialLinearTwoFivePPrimeCharacterEquiv 5
          (specialLinearTwoFiveFiveTwoDimensionalPPrimeRow k))) :
    SylowNormalizer specialLinearTwoFiveSylowFive := by
  classical
  exact
    if ha : a = 1 then 1
    else
      Classical.choose
        (specialLinearTwoFiveFiveTwoDimensionalStabilizer_exists_innerLift
          k a)

@[simp]
theorem
    specialLinearTwoFiveFiveTwoDimensionalStabilizerLift_one
    (k : Fin 4) :
    specialLinearTwoFiveFiveTwoDimensionalStabilizerLift k 1 = 1 := by
  simp [specialLinearTwoFiveFiveTwoDimensionalStabilizerLift]

theorem
    specialLinearTwoFiveFiveTwoDimensionalStabilizerLift_spec
    (k : Fin 4)
    (a :
      PPrimeCharacterStabilizer
        specialLinearTwoFiveSylowFive
        (specialLinearTwoFivePPrimeCharacterEquiv 5
          (specialLinearTwoFiveFiveTwoDimensionalPPrimeRow k))) :
    PPrimeCharacterStabilizer.ambientAction a =
      MulAut.conj
        (specialLinearTwoFiveFiveTwoDimensionalStabilizerLift k a).1 := by
  by_cases ha : a = 1
  · subst a
    simp
  · change
      a.1.1 =
        MulAut.conj
          (specialLinearTwoFiveFiveTwoDimensionalStabilizerLift k a).1
    rw [specialLinearTwoFiveFiveTwoDimensionalStabilizerLift,
      dif_neg ha]
    exact
      Classical.choose_spec
        (specialLinearTwoFiveFiveTwoDimensionalStabilizer_exists_innerLift
          k a)

/-- The sign by which the central involution acts in the `k`-th matched
pair. -/
def specialLinearTwoFiveFiveTwoDimensionalCentralSign
    (k : Fin 4) : ℂˣ :=
  if k.val % 2 = 0 then -1 else 1

/-- The common central-unit function for the ambient and local rows. -/
def specialLinearTwoFiveFiveTwoDimensionalCentralUnit
    (k : Fin 4) (z : SpecialLinearTwoFive) : ℂˣ :=
  if z = 1 then 1
  else specialLinearTwoFiveFiveTwoDimensionalCentralSign k

/-- The ambient binary icosahedral group has center `{1,-1}`. -/
theorem specialLinearTwoFiveFive_mem_center_eq_one_or_neg_one
    (z : SpecialLinearTwoFive)
    (hz : z ∈ Subgroup.center SpecialLinearTwoFive) :
    z = 1 ∨ z = -1 := by
  have h :
      ∀ zc : Subgroup.center SpecialLinearTwoFive,
        (zc : SpecialLinearTwoFive) = 1 ∨
          (zc : SpecialLinearTwoFive) = -1 := by
    native_decide
  exact h ⟨z, hz⟩

/-- The central involution as an element of the exact Sylow-five
normalizer. -/
def specialLinearTwoFiveSylowFiveNormalizerNegOne :
    SylowNormalizer specialLinearTwoFiveSylowFive :=
  quaternionFiveEquivSylowFiveNormalizer
    (QuaternionGroup.a 5)

@[simp]
theorem specialLinearTwoFiveSylowFiveNormalizerNegOne_val :
    (specialLinearTwoFiveSylowFiveNormalizerNegOne :
      SpecialLinearTwoFive) = -1 := by
  change
    specialLinearTwoFiveSylowFiveNormalizerA ^ 5 = -1
  decide

/-- The exact Sylow-five normalizer also has center `{1,-1}`. -/
theorem
    specialLinearTwoFiveSylowFiveNormalizer_mem_center_eq_one_or_negOne
    (z : SylowNormalizer specialLinearTwoFiveSylowFive)
    (hz :
      z ∈
        Subgroup.center
          (SylowNormalizer specialLinearTwoFiveSylowFive)) :
    z = 1 ∨
      z = specialLinearTwoFiveSylowFiveNormalizerNegOne := by
  obtain ⟨q, rfl⟩ :=
    quaternionFiveEquivSylowFiveNormalizer.surjective z
  have hqcenter :
      q ∈ Subgroup.center (QuaternionGroup 5) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro x
    apply quaternionFiveEquivSylowFiveNormalizer.injective
    simpa only [map_mul] using
      hz (quaternionFiveEquivSylowFiveNormalizer x)
  have quaternion_center :
      ∀ q : QuaternionGroup 5,
        q ∈ Subgroup.center (QuaternionGroup 5) →
          q = QuaternionGroup.a 0 ∨
            q = QuaternionGroup.a 5 := by
    native_decide
  rcases quaternion_center q hqcenter with hq | hq
  · subst q
    left
    simp
  · subst q
    right
    rfl

/-- The fixed primitive tenth root has fifth power `-1`. -/
theorem primitiveTenthRoot_pow_five :
    primitiveTenthRoot ^ 5 = -1 := by
  rw [primitiveTenthRoot, ← Complex.exp_nat_mul]
  convert Complex.exp_pi_mul_I using 1 <;> ring

/-- The ambient moved row has the displayed central sign. -/
theorem specialLinearTwoFiveFiveTwoDimensionalAmbient_values_neg_one
    (k : Fin 4) :
    (specialLinearTwoFivePPrimeCharacterEquiv 5
        (specialLinearTwoFiveFiveTwoDimensionalPPrimeRow k)).1.values
          (-1) =
      (specialLinearTwoFiveFiveTwoDimensionalCentralUnit k (-1) : ℂ) *
        ((specialLinearTwoFivePPrimeCharacterEquiv 5
          (specialLinearTwoFiveFiveTwoDimensionalPPrimeRow k)).1.degree :
          ℂ) := by
  change
    (specialLinearTwoFiveIrreducibleCharacter
      (specialLinearTwoFiveFiveTwoDimensionalPPrimeRow k).1).values
        (specialLinearTwoFiveConjugacyRepresentative 1) =
      (specialLinearTwoFiveFiveTwoDimensionalCentralUnit k (-1) : ℂ) *
        ((specialLinearTwoFiveIrreducibleCharacter
          (specialLinearTwoFiveFiveTwoDimensionalPPrimeRow k).1).degree :
          ℂ)
  rw [
    specialLinearTwoFiveIrreducibleCharacter_values_representative,
    specialLinearTwoFiveIrreducibleCharacter_degree]
  have hneg : (-1 : SpecialLinearTwoFive) ≠ 1 := by
    decide
  fin_cases k
  · change
      specialLinearTwoFiveCharacterTableValue
          binaryIcosahedralGoldenRootPlus (.faithful 0) 1 =
        (specialLinearTwoFiveFiveTwoDimensionalCentralUnit
          0 (-1) : ℂ) * 2
    norm_num [
      specialLinearTwoFiveFiveTwoDimensionalCentralUnit,
      specialLinearTwoFiveFiveTwoDimensionalCentralSign,
      hneg, specialLinearTwoFiveCharacterTableValue,
      binaryIcosahedralDefiningTrace]
  · change
      specialLinearTwoFiveCharacterTableValue
          binaryIcosahedralGoldenRootPlus (.symmetricSquare 0) 1 =
        (specialLinearTwoFiveFiveTwoDimensionalCentralUnit
          1 (-1) : ℂ) * 3
    norm_num [
      specialLinearTwoFiveFiveTwoDimensionalCentralUnit,
      specialLinearTwoFiveFiveTwoDimensionalCentralSign,
      hneg, specialLinearTwoFiveCharacterTableValue,
      binaryIcosahedralDefiningTrace,
      binaryIcosahedralSymmetricSquareValue]
  · change
      specialLinearTwoFiveCharacterTableValue
          binaryIcosahedralGoldenRootPlus (.faithful 1) 1 =
        (specialLinearTwoFiveFiveTwoDimensionalCentralUnit
          2 (-1) : ℂ) * 2
    norm_num [
      specialLinearTwoFiveFiveTwoDimensionalCentralUnit,
      specialLinearTwoFiveFiveTwoDimensionalCentralSign,
      hneg, specialLinearTwoFiveCharacterTableValue,
      binaryIcosahedralDefiningTrace]
  · change
      specialLinearTwoFiveCharacterTableValue
          binaryIcosahedralGoldenRootPlus (.symmetricSquare 1) 1 =
        (specialLinearTwoFiveFiveTwoDimensionalCentralUnit
          3 (-1) : ℂ) * 3
    norm_num [
      specialLinearTwoFiveFiveTwoDimensionalCentralUnit,
      specialLinearTwoFiveFiveTwoDimensionalCentralSign,
      hneg,
      specialLinearTwoFiveCharacterTableValue,
      binaryIcosahedralDefiningTrace,
      binaryIcosahedralSymmetricSquareValue]

/-- The local character in the `k`-th moved pair is exactly the `k`-th
two-dimensional dicyclic row. -/
theorem specialLinearTwoFiveFiveTwoDimensionalLocalCharacter_eq
    (k : Fin 4) :
    (specialLinearTwoFiveFiveEquivariantMcKayEquiv
      |>.toExactNormalizerLocalCorrespondence).localCharacter
        (specialLinearTwoFivePPrimeCharacterEquiv 5
          (specialLinearTwoFiveFiveTwoDimensionalPPrimeRow k)) =
      specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv
        (.twoDimensional k) := by
  change
    specialLinearTwoFiveFiveEquivariantMcKayEquiv
        (specialLinearTwoFivePPrimeCharacterEquiv 5
          (specialLinearTwoFiveFiveTwoDimensionalPPrimeRow k)) =
      _
  rw [specialLinearTwoFiveFiveEquivariantMcKayEquiv_apply,
    specialLinearTwoFiveFiveCharacterRowEquiv_twoDimensionalRow]

/-- The matched local row has the same central sign. -/
theorem specialLinearTwoFiveFiveTwoDimensionalLocal_values_neg_one
    (k : Fin 4) :
    ((specialLinearTwoFiveFiveEquivariantMcKayEquiv
      |>.toExactNormalizerLocalCorrespondence).localCharacter
        (specialLinearTwoFivePPrimeCharacterEquiv 5
          (specialLinearTwoFiveFiveTwoDimensionalPPrimeRow k))).1.values
            specialLinearTwoFiveSylowFiveNormalizerNegOne =
      (specialLinearTwoFiveFiveTwoDimensionalCentralUnit k
          specialLinearTwoFiveSylowFiveNormalizerNegOne.1 : ℂ) *
        (((specialLinearTwoFiveFiveEquivariantMcKayEquiv
          |>.toExactNormalizerLocalCorrespondence).localCharacter
            (specialLinearTwoFivePPrimeCharacterEquiv 5
              (specialLinearTwoFiveFiveTwoDimensionalPPrimeRow k))).1.degree :
          ℂ) := by
  rw [specialLinearTwoFiveFiveTwoDimensionalLocalCharacter_eq]
  change
    (specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv
      (.twoDimensional k)).1.values
        (quaternionFiveEquivSylowFiveNormalizer
          (QuaternionGroup.a 5)) =
      (specialLinearTwoFiveFiveTwoDimensionalCentralUnit k
          specialLinearTwoFiveSylowFiveNormalizerNegOne.1 : ℂ) *
        ((specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv
          (.twoDimensional k)).1.degree : ℂ)
  rw [
    specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv_values,
    specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv_degree_twoDimensional]
  change
    (twoDimensionalCharacter k).values
        (QuaternionGroup.a ((5 : ℕ) : ZMod 10)) =
      (specialLinearTwoFiveFiveTwoDimensionalCentralUnit k
          specialLinearTwoFiveSylowFiveNormalizerNegOne.1 : ℂ) * 2
  rw [twoDimensionalCharacter_values_a_natCast]
  rw [specialLinearTwoFiveSylowFiveNormalizerNegOne_val]
  have hneg : (-1 : SpecialLinearTwoFive) ≠ 1 := by
    decide
  have h10 : primitiveTenthRoot ^ 10 = 1 :=
    primitiveTenthRoot_isPrimitive.pow_eq_one
  have h15 : primitiveTenthRoot ^ 15 = -1 := by
    rw [show 15 = 5 * 3 by norm_num, pow_mul,
      primitiveTenthRoot_pow_five]
    norm_num
  have h20 : primitiveTenthRoot ^ 20 = 1 := by
    rw [show 20 = 10 * 2 by norm_num, pow_mul, h10]
    norm_num
  fin_cases k <;>
    norm_num [
      twoDimensionalParameter,
      specialLinearTwoFiveFiveTwoDimensionalCentralUnit,
      specialLinearTwoFiveFiveTwoDimensionalCentralSign,
      hneg, ← pow_mul, primitiveTenthRoot_pow_five,
      h10, h15, h20]

/-- The common inner lift and common central sign give exact projective
compatibility for each moved `p = 5` row. -/
theorem
    specialLinearTwoFiveFiveTwoDimensionalRow_tripleCompatible
    (k : Fin 4) :
    specialLinearTwoFiveFiveEquivariantMcKayEquiv
      |>.toExactNormalizerLocalCorrespondence.TripleCompatible
        (specialLinearTwoFivePPrimeCharacterEquiv 5
          (specialLinearTwoFiveFiveTwoDimensionalPPrimeRow k)) := by
  let e := specialLinearTwoFiveFiveEquivariantMcKayEquiv
  let χ :=
    specialLinearTwoFivePPrimeCharacterEquiv 5
      (specialLinearTwoFiveFiveTwoDimensionalPPrimeRow k)
  apply e.tripleCompatible_of_innerNormalizerLift χ
    (specialLinearTwoFiveFiveTwoDimensionalStabilizerLift k)
    (specialLinearTwoFiveFiveTwoDimensionalStabilizerLift_one k)
    (specialLinearTwoFiveFiveTwoDimensionalStabilizerLift_spec k)
    (specialLinearTwoFiveFiveTwoDimensionalCentralUnit k)
  · intro z hz
    apply
      irreducibleCharacter_realizationAction_eq_of_twoPointCenter
        χ.1 (-1)
        (specialLinearTwoFiveFiveTwoDimensionalCentralUnit k)
        specialLinearTwoFiveFive_mem_center_eq_one_or_neg_one
        (by simp [
          specialLinearTwoFiveFiveTwoDimensionalCentralUnit])
        (specialLinearTwoFiveFiveTwoDimensionalAmbient_values_neg_one k)
        z hz
  · intro z hz
    apply
      irreducibleCharacter_realizationAction_eq_of_twoPointCenter
        (e χ).1
        specialLinearTwoFiveSylowFiveNormalizerNegOne
        (fun n =>
          specialLinearTwoFiveFiveTwoDimensionalCentralUnit k n.1)
        specialLinearTwoFiveSylowFiveNormalizer_mem_center_eq_one_or_negOne
        (by simp [
          specialLinearTwoFiveFiveTwoDimensionalCentralUnit])
        (specialLinearTwoFiveFiveTwoDimensionalLocal_values_neg_one k)
        z hz

/-- Concrete exact-normalizer projective data for the four moved rows. -/
def specialLinearTwoFiveFiveTwoDimensionalProjectiveRowData
    (k : Fin 4) :
    ExactNormalizerProjectiveRowData
      specialLinearTwoFiveFiveEquivariantMcKayEquiv
      (specialLinearTwoFivePPrimeCharacterEquiv 5
        (specialLinearTwoFiveFiveTwoDimensionalPPrimeRow k)) :=
  ExactNormalizerProjectiveRowData.ofTripleCompatible
    specialLinearTwoFiveFiveEquivariantMcKayEquiv
    (specialLinearTwoFivePPrimeCharacterEquiv 5
      (specialLinearTwoFiveFiveTwoDimensionalPPrimeRow k))
    (specialLinearTwoFiveFiveTwoDimensionalRow_tripleCompatible k)

end InductiveMcKay
end McKayConjecture
