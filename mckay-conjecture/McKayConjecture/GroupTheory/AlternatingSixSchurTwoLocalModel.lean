/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverExact
import McKayConjecture.GroupTheory.QuaternionGroupLiftInjective

/-!
# A generalized-quaternion Sylow subgroup in the sixfold cover of `A₆`

This file constructs explicit corrected lifts of the rotation and reflection
in a dihedral Sylow `2`-subgroup of `A₆`.  The weighted rewrite certificate
checks the generalized-quaternion relations between the lifts.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-! ### Elementary presentation relations -/

/-- The distinguished central generator of the presented cover. -/
abbrev alternatingSixSchurTwoCentral :
    AlternatingSixSchurPresentedGroup :=
  alternatingSixSchurPresentedK 0

/-- The distinguished kernel generator is central. -/
theorem alternatingSixSchurTwoCentral_mem_center :
    alternatingSixSchurTwoCentral ∈
      Subgroup.center AlternatingSixSchurPresentedGroup :=
  alternatingSixSchurPresentedK_mem_center 0

/-- The distinguished kernel generator commutes with every element. -/
theorem alternatingSixSchurTwoCentral_commute
    (g : AlternatingSixSchurPresentedGroup) :
    Commute alternatingSixSchurTwoCentral g :=
  (Subgroup.mem_center_iff.mp
    alternatingSixSchurTwoCentral_mem_center g).symm

/-- The square of the first presentation generator is `k₀`. -/
theorem alternatingSixSchurTwo_presentedA_sq :
    alternatingSixSchurPresentedA ^ 2 =
      alternatingSixSchurTwoCentral := by
  simpa [alternatingSixSchurBaseRelator,
    alternatingSixSchurFreeA, alternatingSixSchurPresentedA,
    alternatingSixSchurGenerator,
    alternatingSixSchurPresentedGenerator, PresentedGroup.of,
    alternatingSixSchurTwoCentral] using
      alternatingSixSchurPresented_baseRelator 0

/-! ### A local evaluator for the weighted rewrite table -/

/-- The table state and accumulated central weight after reading a
two-local word. -/
structure AlternatingSixSchurTwoTrace where
  state : Fin 360
  weight : Fin 4 → ℤ

/-- The initial table state. -/
def alternatingSixSchurTwoInitialTrace :
    AlternatingSixSchurTwoTrace where
  state := 0
  weight := fun _ => 0

/-- Read one signed noncentral letter. -/
def alternatingSixSchurTwoTraceStep
    (trace : AlternatingSixSchurTwoTrace)
    (letter : AlternatingSixRewriteLetter) :
    AlternatingSixSchurTwoTrace :=
  let column :=
    alternatingSixRewriteTransitionLetter letter
  let transition :=
    alternatingSixRewriteTransitions trace.state column
  {
    state := transition.target
    weight :=
      alternatingSixRewriteAddWeight
        (alternatingSixSchurTransitionWeight trace.state column)
        trace.weight
  }

/-- Evaluate a word from a specified table state. -/
def alternatingSixSchurTwoTraceFrom
    (trace : AlternatingSixSchurTwoTrace)
    (word : AlternatingSixRewriteWord) :
    AlternatingSixSchurTwoTrace :=
  word.foldl alternatingSixSchurTwoTraceStep trace

/-- Evaluate a word from the identity state. -/
def alternatingSixSchurTwoTrace
    (word : AlternatingSixRewriteWord) :
    AlternatingSixSchurTwoTrace :=
  alternatingSixSchurTwoTraceFrom
    alternatingSixSchurTwoInitialTrace word

/-- The two-local trace computes a valid weighted normal form. -/
theorem alternatingSixSchurTwoTraceFrom_sound
    (trace : AlternatingSixSchurTwoTrace)
    (word : AlternatingSixRewriteWord) :
    (alternatingSixSchurNormalElement trace.state *
          alternatingSixSchurWeight trace.weight) *
        alternatingSixSchurWord word =
      alternatingSixSchurNormalElement
          (alternatingSixSchurTwoTraceFrom trace word).state *
        alternatingSixSchurWeight
          (alternatingSixSchurTwoTraceFrom trace word).weight := by
  induction word generalizing trace with
  | nil =>
      simp [alternatingSixSchurTwoTraceFrom,
        alternatingSixSchurWord_nil]
  | cons letter word ih =>
      rw [show letter :: word = [letter] ++ word by rfl,
        alternatingSixSchurWord_append, ← mul_assoc]
      let column :=
        alternatingSixRewriteTransitionLetter letter
      have hletter :
          alternatingSixSchurWord [letter] =
            alternatingSixSchurWord
              (alternatingSixRewriteLetterWord column) := by
        rw [alternatingSixRewriteLetterWord_transitionLetter]
      rw [hletter,
        alternatingSixSchurNormal_mul_letter_weight]
      simpa [alternatingSixSchurTwoTraceFrom,
        alternatingSixSchurTwoTraceStep, column] using
        (ih (alternatingSixSchurTwoTraceStep trace letter))

/-- A trace from the initial state gives a normal form for the word. -/
theorem alternatingSixSchurTwoTrace_sound
    (word : AlternatingSixRewriteWord) :
    alternatingSixSchurWord word =
      alternatingSixSchurNormalElement
          (alternatingSixSchurTwoTrace word).state *
        alternatingSixSchurWeight
          (alternatingSixSchurTwoTrace word).weight := by
  have h :=
    alternatingSixSchurTwoTraceFrom_sound
      alternatingSixSchurTwoInitialTrace word
  have hnormal :
      alternatingSixSchurNormalElement 0 = 1 := by
    rfl
  simpa [alternatingSixSchurTwoTrace,
    alternatingSixSchurTwoInitialTrace, hnormal] using h

/-- Reduce a central rewrite weight to a power of `k₀`. -/
theorem alternatingSixSchurTwoWeight_eq_k0_zpow
    (weight : Fin 4 → ℤ) :
    alternatingSixSchurWeight weight =
      alternatingSixSchurPresentedK 0 ^
        (weight 0 + 3 * weight 1 - weight 2 + weight 3 : ℤ) := by
  have h :=
    congrArg Additive.toMul
      (alternatingSixSchurWeightAdditive_reduce weight)
  have hv := congrArg Subtype.val h
  simpa [alternatingSixSchurWeight,
    alternatingSixSchurCentralKAdditive,
    alternatingSixSchurCentralK] using hv

/-- A word lifting the chosen order-four rotation in `A₆`. -/
def alternatingSixSchurTwoRotationWord :
    AlternatingSixRewriteWord :=
  [(0, true), (1, true), (0, true), (1, false)]

/-- The raw lift of the chosen order-four rotation. -/
def alternatingSixSchurRawTwoRotation :
    AlternatingSixSchurPresentedGroup :=
  alternatingSixSchurWord alternatingSixSchurTwoRotationWord

private theorem alternatingSixSchurRawTwoRotationFourthTrace_state :
    (alternatingSixSchurTwoTrace
    (alternatingSixSchurTwoRotationWord ++
      alternatingSixSchurTwoRotationWord ++
      alternatingSixSchurTwoRotationWord ++
      alternatingSixSchurTwoRotationWord)).state = 0 := by
  decide

private theorem alternatingSixSchurRawTwoRotationFourthTrace_weight :
    (alternatingSixSchurTwoTrace
      (alternatingSixSchurTwoRotationWord ++
        alternatingSixSchurTwoRotationWord ++
        alternatingSixSchurTwoRotationWord ++
        alternatingSixSchurTwoRotationWord)).weight =
      ![(-16 : ℤ), -5, 12, -4] := by
  funext i
  fin_cases i <;> decide

private theorem alternatingSixSchurRawTwoConjugationTrace_state :
    (alternatingSixSchurTwoTrace
    (alternatingSixSchurTwoRotationWord ++
      [(0, true)] ++
      alternatingSixSchurTwoRotationWord ++
      [(0, false)])).state = 0 := by
  decide

private theorem alternatingSixSchurRawTwoConjugationTrace_weight :
    (alternatingSixSchurTwoTrace
      (alternatingSixSchurTwoRotationWord ++
        [(0, true)] ++
        alternatingSixSchurTwoRotationWord ++
        [(0, false)])).weight =
      ![(2 : ℤ), 0, 0, 0] := by
  funext i
  fin_cases i <;> decide

/-- The fourth power of the raw rotation lift is `k₀`. -/
theorem alternatingSixSchurRawTwoRotation_pow_four :
    alternatingSixSchurRawTwoRotation ^ 4 =
      alternatingSixSchurTwoCentral := by
  have h :=
    alternatingSixSchurTwoTrace_sound
      (alternatingSixSchurTwoRotationWord ++
        alternatingSixSchurTwoRotationWord ++
        alternatingSixSchurTwoRotationWord ++
        alternatingSixSchurTwoRotationWord)
  rw [alternatingSixSchurRawTwoRotationFourthTrace_state,
    alternatingSixSchurRawTwoRotationFourthTrace_weight] at h
  have hweight :
      alternatingSixSchurWeight ![(-16 : ℤ), -5, 12, -4] =
        alternatingSixSchurTwoCentral := by
    rw [alternatingSixSchurTwoWeight_eq_k0_zpow]
    norm_num
    calc
      alternatingSixSchurTwoCentral ^ (-47 : ℤ) =
          alternatingSixSchurTwoCentral ^ ((-47 : ℤ) % 6) :=
        zpow_eq_zpow_emod (-47) (by
          simpa [alternatingSixSchurTwoCentral] using
            alternatingSixSchurPresentedK0_pow_six)
      _ = alternatingSixSchurTwoCentral := by norm_num
  have hnormal :
      alternatingSixSchurNormalElement 0 = 1 := by
    rfl
  rw [hnormal, one_mul, hweight] at h
  simp only [alternatingSixSchurWord_append] at h
  change
    alternatingSixSchurRawTwoRotation *
          (alternatingSixSchurRawTwoRotation *
            (alternatingSixSchurRawTwoRotation *
              alternatingSixSchurRawTwoRotation)) =
        alternatingSixSchurTwoCentral at h
  simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using h

/-- The raw rotation and raw reflection satisfy the inversion relation
up to the central error `k₀²`. -/
theorem alternatingSixSchurRawTwoConjugation :
    alternatingSixSchurRawTwoRotation *
          alternatingSixSchurPresentedA *
          alternatingSixSchurRawTwoRotation *
          alternatingSixSchurPresentedA⁻¹ =
      alternatingSixSchurTwoCentral ^ 2 := by
  have h :=
    alternatingSixSchurTwoTrace_sound
      (alternatingSixSchurTwoRotationWord ++
        [(0, true)] ++
        alternatingSixSchurTwoRotationWord ++
        [(0, false)])
  rw [alternatingSixSchurRawTwoConjugationTrace_state,
    alternatingSixSchurRawTwoConjugationTrace_weight] at h
  have hweight :
      alternatingSixSchurWeight ![(2 : ℤ), 0, 0, 0] =
        alternatingSixSchurTwoCentral ^ 2 := by
    rw [alternatingSixSchurTwoWeight_eq_k0_zpow]
    change
      alternatingSixSchurTwoCentral ^
          (2 + 3 * 0 - 0 + 0 : ℤ) =
        alternatingSixSchurTwoCentral ^ 2
    norm_num
  have hnormal :
      alternatingSixSchurNormalElement 0 = 1 := by
    rfl
  rw [hnormal, one_mul, hweight] at h
  simp only [alternatingSixSchurWord_append] at h
  change
    alternatingSixSchurRawTwoRotation *
          alternatingSixSchurPresentedA *
          alternatingSixSchurRawTwoRotation *
          alternatingSixSchurPresentedA⁻¹ =
        alternatingSixSchurTwoCentral ^ 2 at h
  exact h

/-! ### Corrected generalized-quaternion generators -/

/-- Multiplication of two noncentral factors with powers of `k₀`
separates into its noncentral and central parts. -/
theorem alternatingSixSchurTwo_mul_central_zpow
    (x y : AlternatingSixSchurPresentedGroup)
    (m n : ℤ) :
    (x * alternatingSixSchurTwoCentral ^ m) *
        (y * alternatingSixSchurTwoCentral ^ n) =
      (x * y) *
        alternatingSixSchurTwoCentral ^ (m + n) := by
  rw [alternatingSix_mul_mul_central_factors
    x y
    (alternatingSixSchurTwoCentral ^ m)
    (alternatingSixSchurTwoCentral ^ n)
    ((Subgroup.center AlternatingSixSchurPresentedGroup).zpow_mem
      alternatingSixSchurTwoCentral_mem_center m)]
  rw [← zpow_add]

/-- Correct the raw rotation by `k₀²`; the result has order eight. -/
def alternatingSixSchurTwoRotation :
    AlternatingSixSchurPresentedGroup :=
  alternatingSixSchurRawTwoRotation *
    alternatingSixSchurTwoCentral ^ (2 : ℤ)

/-- Correct the raw reflection by `k₀`; the result has order four. -/
def alternatingSixSchurTwoReflection :
    AlternatingSixSchurPresentedGroup :=
  alternatingSixSchurPresentedA *
    alternatingSixSchurTwoCentral

/-- The corrected rotation has fourth power equal to the central
involution. -/
theorem alternatingSixSchurTwoRotation_pow_four :
    alternatingSixSchurTwoRotation ^ 4 =
      alternatingSixSchurTwoCentral ^ 3 := by
  unfold alternatingSixSchurTwoRotation
  have hcommute :
      Commute alternatingSixSchurRawTwoRotation
        (alternatingSixSchurTwoCentral ^ 2) :=
    ((alternatingSixSchurTwoCentral_commute
      alternatingSixSchurRawTwoRotation).pow_left 2).symm
  calc
    (alternatingSixSchurRawTwoRotation *
          alternatingSixSchurTwoCentral ^ 2) ^ 4 =
        alternatingSixSchurRawTwoRotation ^ 4 *
          (alternatingSixSchurTwoCentral ^ 2) ^ 4 :=
      hcommute.mul_pow 4
    _ =
        alternatingSixSchurTwoCentral *
          (alternatingSixSchurTwoCentral ^ 2) ^ 4 := by
      rw [alternatingSixSchurRawTwoRotation_pow_four]
    _ =
        alternatingSixSchurTwoCentral *
          alternatingSixSchurTwoCentral ^ 8 := by
      rw [← pow_mul]
    _ =
        alternatingSixSchurTwoCentral ^ 9 := by group
    _ =
        alternatingSixSchurTwoCentral ^ 3 *
          alternatingSixSchurTwoCentral ^ 6 := by
      rw [← pow_add]
    _ = alternatingSixSchurTwoCentral ^ 3 := by
      rw [alternatingSixSchurPresentedK0_pow_six,
        mul_one]

/-- The corrected rotation has eighth power one. -/
theorem alternatingSixSchurTwoRotation_pow_eight :
    alternatingSixSchurTwoRotation ^ 8 = 1 := by
  calc
    alternatingSixSchurTwoRotation ^ 8 =
        (alternatingSixSchurTwoRotation ^ 4) ^ 2 := by
      rw [← pow_mul]
    _ = (alternatingSixSchurTwoCentral ^ 3) ^ 2 := by
      rw [alternatingSixSchurTwoRotation_pow_four]
    _ = alternatingSixSchurTwoCentral ^ 6 := by
      rw [← pow_mul]
    _ = 1 := alternatingSixSchurPresentedK0_pow_six

/-- The central involution `k₀³` is nontrivial. -/
theorem alternatingSixSchurTwoCentral_pow_three_ne_one :
    alternatingSixSchurTwoCentral ^ 3 ≠ 1 := by
  intro h
  have hdvd :
      orderOf alternatingSixSchurTwoCentral ∣ 3 :=
    orderOf_dvd_iff_pow_eq_one.mpr h
  rw [show
      orderOf alternatingSixSchurTwoCentral = 6 by
        exact orderOf_alternatingSixSchurPresentedK0]
    at hdvd
  norm_num at hdvd

/-- The corrected rotation has exact order eight. -/
theorem orderOf_alternatingSixSchurTwoRotation :
    orderOf alternatingSixSchurTwoRotation = 8 := by
  have hdvd :
      orderOf alternatingSixSchurTwoRotation ∣ 2 ^ 3 := by
    norm_num
    exact
      orderOf_dvd_of_pow_eq_one
        alternatingSixSchurTwoRotation_pow_eight
  obtain ⟨k, hk, horder⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hnotDvdFour :
      ¬orderOf alternatingSixSchurTwoRotation ∣ 4 := by
    rw [orderOf_dvd_iff_pow_eq_one,
      alternatingSixSchurTwoRotation_pow_four]
    exact alternatingSixSchurTwoCentral_pow_three_ne_one
  interval_cases k
  · norm_num at horder
    exact False.elim (hnotDvdFour (horder ▸ by norm_num))
  · norm_num at horder
    exact False.elim (hnotDvdFour (horder ▸ by norm_num))
  · norm_num at horder
    exact False.elim (hnotDvdFour (horder ▸ by norm_num))
  · norm_num at horder ⊢
    exact horder

/-- The corrected reflection squares to the same central involution. -/
theorem alternatingSixSchurTwoReflection_sq :
    alternatingSixSchurTwoReflection ^ 2 =
      alternatingSixSchurTwoCentral ^ 3 := by
  rw [alternatingSixSchurTwoReflection,
    Commute.mul_pow
      (alternatingSixSchurTwoCentral_commute
        alternatingSixSchurPresentedA).symm,
    alternatingSixSchurTwo_presentedA_sq]
  group

/-- The inverse of the corrected reflection separates its central
factor. -/
theorem alternatingSixSchurTwoReflection_inv :
    alternatingSixSchurTwoReflection⁻¹ =
      alternatingSixSchurPresentedA⁻¹ *
        alternatingSixSchurTwoCentral ^ (-1 : ℤ) := by
  rw [alternatingSixSchurTwoReflection, mul_inv_rev]
  change
    alternatingSixSchurTwoCentral⁻¹ *
        alternatingSixSchurPresentedA⁻¹ =
      alternatingSixSchurPresentedA⁻¹ *
        alternatingSixSchurTwoCentral⁻¹
  exact
    ((alternatingSixSchurTwoCentral_commute
      alternatingSixSchurPresentedA⁻¹).inv_left).eq

/-- The corrected generators satisfy the cyclically written inversion
relation. -/
theorem alternatingSixSchurTwoRotation_reflection_cycle :
    alternatingSixSchurTwoRotation *
          alternatingSixSchurTwoReflection *
          alternatingSixSchurTwoRotation *
          alternatingSixSchurTwoReflection⁻¹ =
      1 := by
  have hfirst :=
    alternatingSixSchurTwo_mul_central_zpow
      alternatingSixSchurRawTwoRotation
      alternatingSixSchurPresentedA 2 1
  have hsecond :=
    alternatingSixSchurTwo_mul_central_zpow
      (alternatingSixSchurRawTwoRotation *
        alternatingSixSchurPresentedA)
      alternatingSixSchurRawTwoRotation 3 2
  have hthird :=
    alternatingSixSchurTwo_mul_central_zpow
      (alternatingSixSchurRawTwoRotation *
        alternatingSixSchurPresentedA *
        alternatingSixSchurRawTwoRotation)
        alternatingSixSchurPresentedA⁻¹ 5 (-1)
  norm_num at hfirst hsecond hthird
  rw [alternatingSixSchurTwoReflection_inv,
    alternatingSixSchurTwoRotation,
    alternatingSixSchurTwoReflection]
  change
    (alternatingSixSchurRawTwoRotation *
          alternatingSixSchurTwoCentral ^ (2 : ℤ)) *
        (alternatingSixSchurPresentedA *
          alternatingSixSchurTwoCentral ^ (1 : ℤ)) *
        (alternatingSixSchurRawTwoRotation *
          alternatingSixSchurTwoCentral ^ (2 : ℤ)) *
        (alternatingSixSchurPresentedA⁻¹ *
          alternatingSixSchurTwoCentral ^ (-1 : ℤ)) =
      1
  norm_num
  rw [hfirst]
  rw [hsecond]
  rw [hthird]
  rw [alternatingSixSchurRawTwoConjugation]
  calc
    alternatingSixSchurTwoCentral ^ 2 *
          alternatingSixSchurTwoCentral ^ 4 =
        alternatingSixSchurTwoCentral ^ 6 := by
      rw [← pow_add]
    _ = 1 := alternatingSixSchurPresentedK0_pow_six

/-- Conjugation by the corrected reflection inverts the corrected
rotation. -/
theorem alternatingSixSchurTwoRotation_mul_reflection :
    alternatingSixSchurTwoRotation *
        alternatingSixSchurTwoReflection =
      alternatingSixSchurTwoReflection *
        alternatingSixSchurTwoRotation⁻¹ := by
  have h :
      (alternatingSixSchurTwoRotation *
          alternatingSixSchurTwoReflection) *
        (alternatingSixSchurTwoRotation *
          alternatingSixSchurTwoReflection⁻¹) =
      1 := by
    simpa only [mul_assoc] using
      alternatingSixSchurTwoRotation_reflection_cycle
  have hinverse :=
    (mul_eq_one_iff_eq_inv).mp h
  simpa only [mul_inv_rev, inv_inv] using hinverse

/-! ### The explicit generalized-quaternion subgroup -/

/-- The square relation in the form required by `QuaternionGroup.lift`. -/
theorem alternatingSixSchurTwoReflection_mul_self :
    alternatingSixSchurTwoReflection *
        alternatingSixSchurTwoReflection =
      QuaternionGroup.zmodPower
        alternatingSixSchurTwoRotation
        alternatingSixSchurTwoRotation_pow_eight
        (4 : ZMod 8) := by
  calc
    alternatingSixSchurTwoReflection *
          alternatingSixSchurTwoReflection =
        alternatingSixSchurTwoReflection ^ 2 := by
      rw [pow_two]
    _ = alternatingSixSchurTwoCentral ^ 3 :=
      alternatingSixSchurTwoReflection_sq
    _ = alternatingSixSchurTwoRotation ^ 4 :=
      alternatingSixSchurTwoRotation_pow_four.symm
    _ =
        QuaternionGroup.zmodPower
          alternatingSixSchurTwoRotation
          alternatingSixSchurTwoRotation_pow_eight
          (4 : ZMod 8) := by
      symm
      exact
        QuaternionGroup.zmodPower_natCast
          alternatingSixSchurTwoRotation
          alternatingSixSchurTwoRotation_pow_eight 4

/-- The inversion relation for every indexed power of the rotation. -/
theorem alternatingSixSchurTwo_zmodPower_mul_reflection
    (i : ZMod 8) :
    QuaternionGroup.zmodPower
          alternatingSixSchurTwoRotation
          alternatingSixSchurTwoRotation_pow_eight i *
        alternatingSixSchurTwoReflection =
      alternatingSixSchurTwoReflection *
        QuaternionGroup.zmodPower
          alternatingSixSchurTwoRotation
          alternatingSixSchurTwoRotation_pow_eight (-i) :=
  QuaternionGroup.zmodPower_mul_eq_mul_zmodPower_neg
    alternatingSixSchurTwoRotation
    alternatingSixSchurTwoReflection
    alternatingSixSchurTwoRotation_pow_eight
    alternatingSixSchurTwoRotation_mul_reflection i

/-- The generalized quaternion group of order sixteen maps to the
presented sixfold cover through the corrected generators. -/
def quaternionFourToAlternatingSixSchur :
    QuaternionGroup 4 →*
      AlternatingSixSchurPresentedGroup :=
  QuaternionGroup.lift
    alternatingSixSchurTwoRotation
    alternatingSixSchurTwoReflection
    alternatingSixSchurTwoRotation_pow_eight
    alternatingSixSchurTwoReflection_mul_self
    alternatingSixSchurTwo_zmodPower_mul_reflection

/-- The corrected reflection is not a power of the corrected rotation. -/
theorem alternatingSixSchurTwoReflection_not_mem_zpowers :
    alternatingSixSchurTwoReflection ∉
      Subgroup.zpowers alternatingSixSchurTwoRotation := by
  intro hreflection
  obtain ⟨z, hz⟩ :=
    Subgroup.mem_zpowers_iff.mp hreflection
  have hcommute :
      Commute alternatingSixSchurTwoRotation
        alternatingSixSchurTwoReflection := by
    rw [← hz]
    exact
      (Commute.refl alternatingSixSchurTwoRotation).zpow_right z
  have hright :
      alternatingSixSchurTwoReflection *
          alternatingSixSchurTwoRotation =
        alternatingSixSchurTwoReflection *
          alternatingSixSchurTwoRotation⁻¹ :=
    hcommute.eq.symm.trans
      alternatingSixSchurTwoRotation_mul_reflection
  have hselfInverse :
      alternatingSixSchurTwoRotation =
        alternatingSixSchurTwoRotation⁻¹ :=
    mul_left_cancel hright
  have hsquare :
      alternatingSixSchurTwoRotation ^ 2 = 1 := by
    rw [pow_two]
    exact
      (congrArg
        (fun x =>
          x * alternatingSixSchurTwoRotation)
        hselfInverse).trans
          (inv_mul_cancel alternatingSixSchurTwoRotation)
  have hdvd :
      orderOf alternatingSixSchurTwoRotation ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr hsquare
  rw [orderOf_alternatingSixSchurTwoRotation] at hdvd
  norm_num at hdvd

/-- The explicit generalized-quaternion map is faithful. -/
theorem quaternionFourToAlternatingSixSchur_injective :
    Function.Injective quaternionFourToAlternatingSixSchur :=
  QuaternionGroup.lift_injective_of_orderOf_eq
    alternatingSixSchurTwoRotation
    alternatingSixSchurTwoReflection
    alternatingSixSchurTwoRotation_pow_eight
    alternatingSixSchurTwoReflection_mul_self
    alternatingSixSchurTwo_zmodPower_mul_reflection
    orderOf_alternatingSixSchurTwoRotation
    alternatingSixSchurTwoReflection_not_mem_zpowers

end GroupTheory
end McKayConjecture
