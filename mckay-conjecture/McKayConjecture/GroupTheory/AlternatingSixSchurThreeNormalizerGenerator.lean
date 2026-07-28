/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverSylowThreeStructure

/-!
# An explicit order-eight element in the three-normalizer of `6.A₆`

The order-four element used to describe the Sylow-three normalizer in
`A₆` has a distinguished word in the two ATLAS generators.  Evaluating
the same word in the sixfold Schur cover gives an element `t` satisfying

* `t⁴ = k₀³`, so `t` has exact order eight;
* `t x t⁻¹ = z y`; and
* `t y t⁻¹ = x²`.

Here `x`, `y`, and `z` are the exponent-three Heisenberg generators of
the explicit Sylow subgroup.  In particular, `t` normalizes that Sylow
subgroup.  The checked equalities are obtained from the existing
weighted rewrite table, without increasing the default heartbeat or
recursion limits.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-! ### The lifted normalizer word -/

/-- A word in the ATLAS generators projecting to the displayed
order-four normalizer generator in `A₆`. -/
def alternatingSixSchurThreeNormalizerWord :
    AlternatingSixRewriteWord :=
  [(0, true), (1, true), (0, true), (1, false), (0, true),
    (1, false), (0, true), (1, true), (0, true), (1, false)]

/-- The normalizer word has the advertised projection to `A₆`. -/
@[simp]
theorem alternatingSixSchurProjection_threeNormalizerWord :
    alternatingSixSchurProjection
        (alternatingSixSchurWord
          alternatingSixSchurThreeNormalizerWord) =
      alternatingSixSylowThreeNormalizerGenerator := by
  rw [alternatingSixSchurProjection_word]
  apply Subtype.ext
  simp only [alternatingSixPresentedWord,
    alternatingSixPresentationToAlternatingSix]
  change
    (FreeGroup.lift
      (fun i : Fin 2 =>
        if i = 0 then alternatingSixPresentationA
        else alternatingSixPresentationB)
      (FreeGroup.mk alternatingSixSchurThreeNormalizerWord)).1 =
        alternatingSixSylowThreeNormalizerGeneratorPerm
  decide

/-- The explicit lift of the order-four target normalizer generator. -/
def alternatingSixSchurThreeNormalizerElement :
    AlternatingSixSchurPresentedGroup :=
  alternatingSixSchurWord
    alternatingSixSchurThreeNormalizerWord

@[simp]
theorem alternatingSixSchurProjection_threeNormalizerElement :
    alternatingSixSchurProjection
        alternatingSixSchurThreeNormalizerElement =
      alternatingSixSylowThreeNormalizerGenerator :=
  alternatingSixSchurProjection_threeNormalizerWord

/-! ### Exact order of the lift -/

private def alternatingSixSchurThreeNormalizerFourthTrace :
    AlternatingSixSchurWordTrace :=
  ⟨0, ![(65 : ℤ), 4, -40, 18]⟩

private def alternatingSixSchurThreeNormalizerFirstTrace :
    AlternatingSixSchurWordTrace :=
  ⟨224, ![(0 : ℤ), 0, 0, 0]⟩

private def alternatingSixSchurThreeNormalizerSecondTrace :
    AlternatingSixSchurWordTrace :=
  ⟨293, ![(8 : ℤ), -5, -7, 5]⟩

private def alternatingSixSchurThreeNormalizerThirdTrace :
    AlternatingSixSchurWordTrace :=
  ⟨241, ![(58 : ℤ), 2, -39, 18]⟩

private theorem alternatingSixSchurThreeNormalizerFirstTrace_eq :
    alternatingSixSchurTraceFrom
        alternatingSixSchurInitialTrace
        alternatingSixSchurThreeNormalizerWord =
      alternatingSixSchurThreeNormalizerFirstTrace := by
  apply AlternatingSixSchurWordTrace.ext
  · decide
  · funext i
    fin_cases i <;> decide

private theorem alternatingSixSchurThreeNormalizerSecondTrace_eq :
    alternatingSixSchurTraceFrom
        alternatingSixSchurThreeNormalizerFirstTrace
        alternatingSixSchurThreeNormalizerWord =
      alternatingSixSchurThreeNormalizerSecondTrace := by
  apply AlternatingSixSchurWordTrace.ext
  · decide
  · funext i
    fin_cases i <;> decide

private theorem alternatingSixSchurThreeNormalizerThirdTrace_eq :
    alternatingSixSchurTraceFrom
        alternatingSixSchurThreeNormalizerSecondTrace
        alternatingSixSchurThreeNormalizerWord =
      alternatingSixSchurThreeNormalizerThirdTrace := by
  apply AlternatingSixSchurWordTrace.ext
  · decide
  · funext i
    fin_cases i <;> decide

private theorem alternatingSixSchurThreeNormalizerFourthTraceFrom_eq :
    alternatingSixSchurTraceFrom
        alternatingSixSchurThreeNormalizerThirdTrace
        alternatingSixSchurThreeNormalizerWord =
      alternatingSixSchurThreeNormalizerFourthTrace := by
  apply AlternatingSixSchurWordTrace.ext
  · decide
  · funext i
    fin_cases i <;> decide

private theorem alternatingSixSchurThreeNormalizerFourthTrace_eq :
    alternatingSixSchurTrace
      (alternatingSixSchurThreeNormalizerWord ++
        alternatingSixSchurThreeNormalizerWord ++
        alternatingSixSchurThreeNormalizerWord ++
        alternatingSixSchurThreeNormalizerWord) =
      alternatingSixSchurThreeNormalizerFourthTrace := by
  rw [alternatingSixSchurTrace,
    alternatingSixSchurTraceFrom_append,
    alternatingSixSchurTraceFrom_append,
    alternatingSixSchurTraceFrom_append,
    alternatingSixSchurThreeNormalizerFirstTrace_eq,
    alternatingSixSchurThreeNormalizerSecondTrace_eq,
    alternatingSixSchurThreeNormalizerThirdTrace_eq,
    alternatingSixSchurThreeNormalizerFourthTraceFrom_eq]

/-- The fourth power of the lifted generator is the central involution. -/
theorem alternatingSixSchurThreeNormalizerElement_pow_four :
    alternatingSixSchurThreeNormalizerElement ^ 4 =
      alternatingSixSchurPresentedK 0 ^ 3 := by
  have h :=
    alternatingSixSchurTrace_sound
      (alternatingSixSchurThreeNormalizerWord ++
        alternatingSixSchurThreeNormalizerWord ++
        alternatingSixSchurThreeNormalizerWord ++
        alternatingSixSchurThreeNormalizerWord)
  rw [alternatingSixSchurThreeNormalizerFourthTrace_eq] at h
  simp only [alternatingSixSchurThreeNormalizerFourthTrace] at h
  change
    alternatingSixSchurWord
        (alternatingSixSchurThreeNormalizerWord ++
          alternatingSixSchurThreeNormalizerWord ++
          alternatingSixSchurThreeNormalizerWord ++
          alternatingSixSchurThreeNormalizerWord) =
      alternatingSixSchurNormalElement 0 *
        alternatingSixSchurWeight ![(65 : ℤ), 4, -40, 18] at h
  have hweight :
      alternatingSixSchurWeight ![(65 : ℤ), 4, -40, 18] =
        alternatingSixSchurPresentedK 0 ^ 3 := by
    rw [alternatingSixSchurWeight_eq_k0_zpow]
    norm_num
    calc
      alternatingSixSchurPresentedK 0 ^ (135 : ℤ) =
          alternatingSixSchurPresentedK 0 ^ ((135 : ℤ) % 6) :=
        zpow_eq_zpow_emod 135 (by
          simpa using alternatingSixSchurPresentedK0_pow_six)
      _ = alternatingSixSchurPresentedK 0 ^ 3 := by norm_num
  have hnormal :
      alternatingSixSchurNormalElement 0 = 1 := by
    rfl
  rw [hnormal, one_mul, hweight] at h
  rw [alternatingSixSchurWord_append,
    alternatingSixSchurWord_append,
    alternatingSixSchurWord_append] at h
  simpa [alternatingSixSchurThreeNormalizerElement,
    pow_succ, mul_assoc] using h

/-- The lifted normalizer generator has eighth power one. -/
@[simp]
theorem alternatingSixSchurThreeNormalizerElement_pow_eight :
    alternatingSixSchurThreeNormalizerElement ^ 8 = 1 := by
  calc
    alternatingSixSchurThreeNormalizerElement ^ 8 =
        (alternatingSixSchurThreeNormalizerElement ^ 4) ^ 2 := by
      rw [← pow_mul]
    _ = (alternatingSixSchurPresentedK 0 ^ 3) ^ 2 := by
      rw [alternatingSixSchurThreeNormalizerElement_pow_four]
    _ = alternatingSixSchurPresentedK 0 ^ 6 := by
      rw [← pow_mul]
    _ = 1 := alternatingSixSchurPresentedK0_pow_six

private theorem alternatingSixSchurPresentedK0_pow_three_ne_one :
    alternatingSixSchurPresentedK 0 ^ 3 ≠ 1 := by
  intro h
  have hdvd :
      orderOf (alternatingSixSchurPresentedK 0) ∣ 3 :=
    orderOf_dvd_iff_pow_eq_one.mpr h
  rw [orderOf_alternatingSixSchurPresentedK0] at hdvd
  norm_num at hdvd

/-- The lift has exact order eight, rather than merely order dividing
eight. -/
theorem orderOf_alternatingSixSchurThreeNormalizerElement :
    orderOf alternatingSixSchurThreeNormalizerElement = 8 := by
  have hdvd :
      orderOf alternatingSixSchurThreeNormalizerElement ∣ 2 ^ 3 := by
    norm_num
    exact
      orderOf_dvd_of_pow_eq_one
        alternatingSixSchurThreeNormalizerElement_pow_eight
  obtain ⟨k, hk, horder⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hnotDvdFour :
      ¬orderOf alternatingSixSchurThreeNormalizerElement ∣ 4 := by
    rw [orderOf_dvd_iff_pow_eq_one,
      alternatingSixSchurThreeNormalizerElement_pow_four]
    exact alternatingSixSchurPresentedK0_pow_three_ne_one
  interval_cases k
  · norm_num at horder
    exact False.elim (hnotDvdFour (horder ▸ by norm_num))
  · norm_num at horder
    exact False.elim (hnotDvdFour (horder ▸ by norm_num))
  · norm_num at horder
    exact False.elim (hnotDvdFour (horder ▸ by norm_num))
  · norm_num at horder ⊢
    exact horder

/-! ### Conjugation on the Heisenberg generators -/

private def alternatingSixSchurThreeNormalizerConjLeftWord :
    AlternatingSixRewriteWord :=
  alternatingSixSchurThreeNormalizerWord ++
    alternatingSixSchurLeftThreeCycleWord ++
      alternatingSixRewriteInverseWord
        alternatingSixSchurThreeNormalizerWord

private def alternatingSixSchurThreeNormalizerConjRightWord :
    AlternatingSixRewriteWord :=
  alternatingSixSchurThreeNormalizerWord ++
    alternatingSixSchurRightThreeCycleWord ++
      alternatingSixRewriteInverseWord
        alternatingSixSchurThreeNormalizerWord

private def alternatingSixSchurThreeNormalizerConjLeftTrace :
    AlternatingSixSchurWordTrace :=
  ⟨200, ![(-39 : ℤ), -13, 22, -6]⟩

private def alternatingSixSchurThreeNormalizerConjRightTrace :
    AlternatingSixSchurWordTrace :=
  ⟨283, ![(4 : ℤ), -6, -5, 5]⟩

private def alternatingSixSchurRawRightTrace :
    AlternatingSixSchurWordTrace :=
  ⟨200, ![(25 : ℤ), 7, -11, 3]⟩

private def alternatingSixSchurRawLeftSquareTrace :
    AlternatingSixSchurWordTrace :=
  ⟨283, ![(35 : ℤ), 9, -18, 5]⟩

private def alternatingSixSchurThreeNormalizerConjLeftMiddleTrace :
    AlternatingSixSchurWordTrace :=
  ⟨92, ![(-9 : ℤ), -5, 7, -2]⟩

private def alternatingSixSchurRawRightFirstHalfTrace :
    AlternatingSixSchurWordTrace :=
  ⟨208, ![(19 : ℤ), 2, -13, 6]⟩

private def alternatingSixSchurThreeNormalizerConjRightFirstHalfTrace :
    AlternatingSixSchurWordTrace :=
  ⟨57, ![(-8 : ℤ), -2, 8, -3]⟩

private def alternatingSixSchurThreeNormalizerConjRightMiddleTrace :
    AlternatingSixSchurWordTrace :=
  ⟨296, ![(-26 : ℤ), -9, 18, -5]⟩

private def alternatingSixSchurRawLeftTrace :
    AlternatingSixSchurWordTrace :=
  ⟨276, ![(0 : ℤ), 0, 0, 0]⟩

private theorem alternatingSixSchurThreeNormalizerConjLeftMiddleTrace_eq :
    alternatingSixSchurTraceFrom
        alternatingSixSchurThreeNormalizerFirstTrace
        alternatingSixSchurLeftThreeCycleWord =
      alternatingSixSchurThreeNormalizerConjLeftMiddleTrace := by
  apply AlternatingSixSchurWordTrace.ext
  · decide
  · funext i
    fin_cases i <;> decide

private theorem alternatingSixSchurThreeNormalizerConjLeftFinalTrace_eq :
    alternatingSixSchurTraceFrom
        alternatingSixSchurThreeNormalizerConjLeftMiddleTrace
        (alternatingSixRewriteInverseWord
          alternatingSixSchurThreeNormalizerWord) =
      alternatingSixSchurThreeNormalizerConjLeftTrace := by
  apply AlternatingSixSchurWordTrace.ext
  · decide
  · funext i
    fin_cases i <;> decide

private theorem alternatingSixSchurThreeNormalizerConjLeftTrace_eq :
    alternatingSixSchurTrace
        alternatingSixSchurThreeNormalizerConjLeftWord =
      alternatingSixSchurThreeNormalizerConjLeftTrace := by
  rw [alternatingSixSchurThreeNormalizerConjLeftWord,
    alternatingSixSchurTrace,
    alternatingSixSchurTraceFrom_append,
    alternatingSixSchurTraceFrom_append,
    alternatingSixSchurThreeNormalizerFirstTrace_eq,
    alternatingSixSchurThreeNormalizerConjLeftMiddleTrace_eq,
    alternatingSixSchurThreeNormalizerConjLeftFinalTrace_eq]

private theorem alternatingSixSchurThreeNormalizerConjRightFirstHalfTrace_eq :
    alternatingSixSchurTraceFrom
        alternatingSixSchurThreeNormalizerFirstTrace
        (alternatingSixSchurRightThreeCycleWord.take 15) =
      alternatingSixSchurThreeNormalizerConjRightFirstHalfTrace := by
  apply AlternatingSixSchurWordTrace.ext
  · decide
  · funext i
    fin_cases i <;> decide

private theorem alternatingSixSchurThreeNormalizerConjRightMiddleTrace_eq :
    alternatingSixSchurTraceFrom
        alternatingSixSchurThreeNormalizerConjRightFirstHalfTrace
        (alternatingSixSchurRightThreeCycleWord.drop 15) =
      alternatingSixSchurThreeNormalizerConjRightMiddleTrace := by
  apply AlternatingSixSchurWordTrace.ext
  · decide
  · funext i
    fin_cases i <;> decide

private theorem alternatingSixSchurThreeNormalizerConjRightFinalTrace_eq :
    alternatingSixSchurTraceFrom
        alternatingSixSchurThreeNormalizerConjRightMiddleTrace
        (alternatingSixRewriteInverseWord
          alternatingSixSchurThreeNormalizerWord) =
      alternatingSixSchurThreeNormalizerConjRightTrace := by
  apply AlternatingSixSchurWordTrace.ext
  · decide
  · funext i
    fin_cases i <;> decide

private theorem alternatingSixSchurThreeNormalizerConjRightTrace_eq :
    alternatingSixSchurTrace
        alternatingSixSchurThreeNormalizerConjRightWord =
      alternatingSixSchurThreeNormalizerConjRightTrace := by
  rw [alternatingSixSchurThreeNormalizerConjRightWord,
    show alternatingSixSchurRightThreeCycleWord =
      alternatingSixSchurRightThreeCycleWord.take 15 ++
        alternatingSixSchurRightThreeCycleWord.drop 15 by
          exact
            (List.take_append_drop 15
              alternatingSixSchurRightThreeCycleWord).symm,
    alternatingSixSchurTrace,
    alternatingSixSchurTraceFrom_append,
    alternatingSixSchurTraceFrom_append,
    alternatingSixSchurTraceFrom_append,
    alternatingSixSchurThreeNormalizerFirstTrace_eq,
    alternatingSixSchurThreeNormalizerConjRightFirstHalfTrace_eq,
    alternatingSixSchurThreeNormalizerConjRightMiddleTrace_eq,
    alternatingSixSchurThreeNormalizerConjRightFinalTrace_eq]

private theorem alternatingSixSchurRawRightFirstHalfTrace_eq :
    alternatingSixSchurTraceFrom
        alternatingSixSchurInitialTrace
        (alternatingSixSchurRightThreeCycleWord.take 15) =
      alternatingSixSchurRawRightFirstHalfTrace := by
  apply AlternatingSixSchurWordTrace.ext
  · decide
  · funext i
    fin_cases i <;> decide

private theorem alternatingSixSchurRawRightSecondHalfTrace_eq :
    alternatingSixSchurTraceFrom
        alternatingSixSchurRawRightFirstHalfTrace
        (alternatingSixSchurRightThreeCycleWord.drop 15) =
      alternatingSixSchurRawRightTrace := by
  apply AlternatingSixSchurWordTrace.ext
  · decide
  · funext i
    fin_cases i <;> decide

private theorem alternatingSixSchurRawRightTrace_eq :
    alternatingSixSchurTrace
        alternatingSixSchurRightThreeCycleWord =
      alternatingSixSchurRawRightTrace := by
  rw [show alternatingSixSchurRightThreeCycleWord =
      alternatingSixSchurRightThreeCycleWord.take 15 ++
        alternatingSixSchurRightThreeCycleWord.drop 15 by
          exact
            (List.take_append_drop 15
              alternatingSixSchurRightThreeCycleWord).symm,
    alternatingSixSchurTrace,
    alternatingSixSchurTraceFrom_append,
    alternatingSixSchurRawRightFirstHalfTrace_eq,
    alternatingSixSchurRawRightSecondHalfTrace_eq]

private theorem alternatingSixSchurRawLeftTrace_eq :
    alternatingSixSchurTraceFrom
        alternatingSixSchurInitialTrace
        alternatingSixSchurLeftThreeCycleWord =
      alternatingSixSchurRawLeftTrace := by
  apply AlternatingSixSchurWordTrace.ext
  · decide
  · funext i
    fin_cases i <;> decide

private theorem alternatingSixSchurRawLeftSquareTraceFrom_eq :
    alternatingSixSchurTraceFrom
        alternatingSixSchurRawLeftTrace
        alternatingSixSchurLeftThreeCycleWord =
      alternatingSixSchurRawLeftSquareTrace := by
  apply AlternatingSixSchurWordTrace.ext
  · decide
  · funext i
    fin_cases i <;> decide

private theorem alternatingSixSchurRawLeftSquareTrace_eq :
    alternatingSixSchurTrace
      (alternatingSixSchurLeftThreeCycleWord ++
        alternatingSixSchurLeftThreeCycleWord) =
      alternatingSixSchurRawLeftSquareTrace := by
  rw [alternatingSixSchurTrace,
    alternatingSixSchurTraceFrom_append,
    alternatingSixSchurRawLeftTrace_eq,
    alternatingSixSchurRawLeftSquareTraceFrom_eq]

private theorem alternatingSixSchurRawRightThreeCycleLift_normalForm :
    alternatingSixSchurRawRightThreeCycleLift =
      alternatingSixSchurNormalElement 200 := by
  have h :=
    alternatingSixSchurTrace_sound
      alternatingSixSchurRightThreeCycleWord
  rw [alternatingSixSchurRawRightTrace_eq] at h
  simp only [alternatingSixSchurRawRightTrace] at h
  have hweight :
      alternatingSixSchurWeight ![(25 : ℤ), 7, -11, 3] = 1 := by
    rw [alternatingSixSchurWeight_eq_k0_zpow]
    change alternatingSixSchurPresentedK 0 ^ (60 : ℤ) = 1
    calc
      alternatingSixSchurPresentedK 0 ^ (60 : ℤ) =
          alternatingSixSchurPresentedK 0 ^ ((60 : ℤ) % 6) :=
        zpow_eq_zpow_emod 60 (by
          simpa using alternatingSixSchurPresentedK0_pow_six)
      _ = 1 := by norm_num
  rw [hweight, mul_one] at h
  exact h

private theorem alternatingSixSchurRawLeftThreeCycleLift_sq_normalForm :
    alternatingSixSchurRawLeftThreeCycleLift ^ 2 =
      alternatingSixSchurNormalElement 283 *
        alternatingSixSchurPresentedK 0 := by
  have h :=
    alternatingSixSchurTrace_sound
      (alternatingSixSchurLeftThreeCycleWord ++
        alternatingSixSchurLeftThreeCycleWord)
  rw [alternatingSixSchurRawLeftSquareTrace_eq] at h
  simp only [alternatingSixSchurRawLeftSquareTrace] at h
  have hweight :
      alternatingSixSchurWeight ![(35 : ℤ), 9, -18, 5] =
        alternatingSixSchurPresentedK 0 := by
    rw [alternatingSixSchurWeight_eq_k0_zpow]
    norm_num
    calc
      alternatingSixSchurPresentedK 0 ^ (85 : ℤ) =
          alternatingSixSchurPresentedK 0 ^ ((85 : ℤ) % 6) :=
        zpow_eq_zpow_emod 85 (by
          simpa using alternatingSixSchurPresentedK0_pow_six)
      _ = alternatingSixSchurPresentedK 0 := by norm_num
  rw [hweight] at h
  rw [alternatingSixSchurWord_append] at h
  simpa [alternatingSixSchurRawLeftThreeCycleLift, pow_two] using h

private theorem alternatingSixSchurThreeNormalizerElement_conj_rawLeft :
    alternatingSixSchurThreeNormalizerElement *
          alternatingSixSchurRawLeftThreeCycleLift *
        alternatingSixSchurThreeNormalizerElement⁻¹ =
      alternatingSixSchurPresentedK 0 ^ 2 *
        alternatingSixSchurRawRightThreeCycleLift := by
  have h :=
    alternatingSixSchurTrace_sound
      alternatingSixSchurThreeNormalizerConjLeftWord
  rw [alternatingSixSchurThreeNormalizerConjLeftTrace_eq] at h
  simp only [alternatingSixSchurThreeNormalizerConjLeftTrace] at h
  have hweight :
      alternatingSixSchurWeight ![(-39 : ℤ), -13, 22, -6] =
        alternatingSixSchurPresentedK 0 ^ 2 := by
    rw [alternatingSixSchurWeight_eq_k0_zpow]
    norm_num
    calc
      alternatingSixSchurPresentedK 0 ^ (-106 : ℤ) =
          alternatingSixSchurPresentedK 0 ^ ((-106 : ℤ) % 6) :=
        zpow_eq_zpow_emod (-106) (by
          simpa using alternatingSixSchurPresentedK0_pow_six)
      _ = alternatingSixSchurPresentedK 0 ^ 2 := by norm_num
  rw [hweight] at h
  rw [alternatingSixSchurThreeNormalizerConjLeftWord,
    alternatingSixSchurWord_append,
    alternatingSixSchurWord_append,
    alternatingSixSchurWord_inverse] at h
  rw [alternatingSixSchurRawRightThreeCycleLift_normalForm]
  have hcentral :
      Commute
        (alternatingSixSchurPresentedK 0 ^ 2)
        (alternatingSixSchurNormalElement 200) :=
    (alternatingSixSchurPresentedK0_commute
      (alternatingSixSchurNormalElement 200)).pow_left 2
  simpa [alternatingSixSchurThreeNormalizerElement,
    alternatingSixSchurRawLeftThreeCycleLift,
    hcentral.eq] using h

private theorem alternatingSixSchurThreeNormalizerElement_conj_rawRight :
    alternatingSixSchurThreeNormalizerElement *
          alternatingSixSchurRawRightThreeCycleLift *
        alternatingSixSchurThreeNormalizerElement⁻¹ =
      alternatingSixSchurRawLeftThreeCycleLift ^ 2 *
        alternatingSixSchurPresentedK 0 := by
  have h :=
    alternatingSixSchurTrace_sound
      alternatingSixSchurThreeNormalizerConjRightWord
  rw [alternatingSixSchurThreeNormalizerConjRightTrace_eq] at h
  simp only [alternatingSixSchurThreeNormalizerConjRightTrace] at h
  have hweight :
      alternatingSixSchurWeight ![(4 : ℤ), -6, -5, 5] =
        alternatingSixSchurPresentedK 0 ^ 2 := by
    rw [alternatingSixSchurWeight_eq_k0_zpow]
    norm_num
    calc
      alternatingSixSchurPresentedK 0 ^ (-4 : ℤ) =
          alternatingSixSchurPresentedK 0 ^ ((-4 : ℤ) % 6) :=
        zpow_eq_zpow_emod (-4) (by
          simpa using alternatingSixSchurPresentedK0_pow_six)
      _ = alternatingSixSchurPresentedK 0 ^ 2 := by norm_num
  rw [hweight] at h
  rw [alternatingSixSchurThreeNormalizerConjRightWord,
    alternatingSixSchurWord_append,
    alternatingSixSchurWord_append,
    alternatingSixSchurWord_inverse] at h
  calc
    alternatingSixSchurThreeNormalizerElement *
          alternatingSixSchurRawRightThreeCycleLift *
        alternatingSixSchurThreeNormalizerElement⁻¹ =
        alternatingSixSchurNormalElement 283 *
          alternatingSixSchurPresentedK 0 ^ 2 := by
      simpa [alternatingSixSchurThreeNormalizerElement,
        alternatingSixSchurRawRightThreeCycleLift] using h
    _ =
        (alternatingSixSchurNormalElement 283 *
          alternatingSixSchurPresentedK 0) *
            alternatingSixSchurPresentedK 0 := by
      rw [pow_two, mul_assoc]
    _ =
        alternatingSixSchurRawLeftThreeCycleLift ^ 2 *
          alternatingSixSchurPresentedK 0 := by
      rw [alternatingSixSchurRawLeftThreeCycleLift_sq_normalForm]

/-- Conjugation by the order-eight lift sends `x` to `z y`. -/
theorem alternatingSixSchurThreeNormalizerElement_conj_X :
    alternatingSixSchurThreeNormalizerElement *
          alternatingSixSchurSylowThreeX *
        alternatingSixSchurThreeNormalizerElement⁻¹ =
      alternatingSixSchurSylowThreeZ *
        alternatingSixSchurSylowThreeY := by
  rw [alternatingSixSchurSylowThreeX,
    alternatingSixSchurSylowThreeY,
    alternatingSixSchurSylowThreeZ]
  calc
    alternatingSixSchurThreeNormalizerElement *
          (alternatingSixSchurRawLeftThreeCycleLift *
            alternatingSixSchurPresentedK 0) *
        alternatingSixSchurThreeNormalizerElement⁻¹ =
        alternatingSixSchurThreeNormalizerElement *
          alternatingSixSchurRawLeftThreeCycleLift *
            (alternatingSixSchurPresentedK 0 *
              alternatingSixSchurThreeNormalizerElement⁻¹) := by
      simp only [mul_assoc]
    _ =
        alternatingSixSchurThreeNormalizerElement *
          alternatingSixSchurRawLeftThreeCycleLift *
            (alternatingSixSchurThreeNormalizerElement⁻¹ *
              alternatingSixSchurPresentedK 0) := by
      rw [(alternatingSixSchurPresentedK0_commute
        alternatingSixSchurThreeNormalizerElement⁻¹).eq]
    _ =
        (alternatingSixSchurThreeNormalizerElement *
            alternatingSixSchurRawLeftThreeCycleLift *
              alternatingSixSchurThreeNormalizerElement⁻¹) *
          alternatingSixSchurPresentedK 0 := by
      simp only [mul_assoc]
    _ =
        (alternatingSixSchurPresentedK 0 ^ 2 *
            alternatingSixSchurRawRightThreeCycleLift) *
          alternatingSixSchurPresentedK 0 := by
      rw [alternatingSixSchurThreeNormalizerElement_conj_rawLeft]
    _ =
        alternatingSixSchurPresentedK 0 ^ 2 *
          (alternatingSixSchurRawRightThreeCycleLift *
            alternatingSixSchurPresentedK 0) := by
      simp only [mul_assoc]

/-- Conjugation by the order-eight lift sends `y` to `x²`. -/
theorem alternatingSixSchurThreeNormalizerElement_conj_Y :
    alternatingSixSchurThreeNormalizerElement *
          alternatingSixSchurSylowThreeY *
        alternatingSixSchurThreeNormalizerElement⁻¹ =
      alternatingSixSchurSylowThreeX ^ 2 := by
  rw [alternatingSixSchurSylowThreeY,
    alternatingSixSchurSylowThreeX]
  have hcentral :
      Commute
        (alternatingSixSchurPresentedK 0)
        alternatingSixSchurRawLeftThreeCycleLift :=
    alternatingSixSchurPresentedK0_commute
      alternatingSixSchurRawLeftThreeCycleLift
  calc
    alternatingSixSchurThreeNormalizerElement *
          (alternatingSixSchurRawRightThreeCycleLift *
            alternatingSixSchurPresentedK 0) *
        alternatingSixSchurThreeNormalizerElement⁻¹ =
        alternatingSixSchurThreeNormalizerElement *
          alternatingSixSchurRawRightThreeCycleLift *
            (alternatingSixSchurPresentedK 0 *
              alternatingSixSchurThreeNormalizerElement⁻¹) := by
      simp only [mul_assoc]
    _ =
        alternatingSixSchurThreeNormalizerElement *
          alternatingSixSchurRawRightThreeCycleLift *
            (alternatingSixSchurThreeNormalizerElement⁻¹ *
              alternatingSixSchurPresentedK 0) := by
      rw [(alternatingSixSchurPresentedK0_commute
        alternatingSixSchurThreeNormalizerElement⁻¹).eq]
    _ =
        (alternatingSixSchurThreeNormalizerElement *
            alternatingSixSchurRawRightThreeCycleLift *
              alternatingSixSchurThreeNormalizerElement⁻¹) *
          alternatingSixSchurPresentedK 0 := by
      simp only [mul_assoc]
    _ =
        (alternatingSixSchurRawLeftThreeCycleLift ^ 2 *
            alternatingSixSchurPresentedK 0) *
          alternatingSixSchurPresentedK 0 := by
      rw [alternatingSixSchurThreeNormalizerElement_conj_rawRight]
    _ =
        alternatingSixSchurRawLeftThreeCycleLift ^ 2 *
          alternatingSixSchurPresentedK 0 ^ 2 := by
      simp only [pow_two, mul_assoc]
    _ =
        (alternatingSixSchurRawLeftThreeCycleLift *
          alternatingSixSchurPresentedK 0) ^ 2 := by
      rw [hcentral.symm.mul_pow]

/-- The order-eight lift fixes the central Heisenberg generator. -/
theorem alternatingSixSchurThreeNormalizerElement_conj_Z :
    alternatingSixSchurThreeNormalizerElement *
          alternatingSixSchurSylowThreeZ *
        alternatingSixSchurThreeNormalizerElement⁻¹ =
      alternatingSixSchurSylowThreeZ := by
  exact
    (alternatingSixSchurSylowThreeZ_commute
      alternatingSixSchurThreeNormalizerElement).symm.mul_inv_cancel

end GroupTheory
end McKayConjecture
