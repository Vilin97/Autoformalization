/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverExact
import McKayConjecture.GroupTheory.AlternatingSixSylowThreeNormalizer

/-!
# Explicit lifts of the two Sylow-three generators in `6.A₆`

The checked Schur-cover rewrite table can evaluate an arbitrary word while
retaining its central weight.  We package that evaluation once, then apply it
to words for the disjoint three-cycles `(0 1 2)` and `(3 4 5)`.

The raw word lifts both have cube `k₀³`.  After multiplying each by `k₀`,
they have order three, and their commutator is `k₀⁴`.  Thus the central
three-part `k₀²` and the corrected lifts satisfy the exponent-three
Heisenberg relations.
-/

noncomputable section

open scoped commutatorElement

namespace McKayConjecture
namespace GroupTheory

/-! ### A reusable evaluator for the weighted rewrite table -/

/-- The table state and accumulated central weight after reading a word. -/
structure AlternatingSixSchurWordTrace where
  state : Fin 360
  weight : Fin 4 → ℤ

@[ext]
theorem AlternatingSixSchurWordTrace.ext
    {left right : AlternatingSixSchurWordTrace}
    (hstate : left.state = right.state)
    (hweight : left.weight = right.weight) :
    left = right := by
  cases left
  cases right
  simp_all

/-- The initial rewrite state represents the identity with zero weight. -/
def alternatingSixSchurInitialTrace :
    AlternatingSixSchurWordTrace where
  state := 0
  weight := fun _ => 0

/-- Read one signed noncentral letter in the weighted rewrite table. -/
def alternatingSixSchurTraceStep
    (trace : AlternatingSixSchurWordTrace)
    (letter : AlternatingSixRewriteLetter) :
    AlternatingSixSchurWordTrace :=
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

/-- Evaluate a word starting from a specified weighted table state. -/
def alternatingSixSchurTraceFrom
    (trace : AlternatingSixSchurWordTrace)
    (word : AlternatingSixRewriteWord) :
    AlternatingSixSchurWordTrace :=
  word.foldl alternatingSixSchurTraceStep trace

/-- Evaluate a word from the identity state. -/
def alternatingSixSchurTrace
    (word : AlternatingSixRewriteWord) :
    AlternatingSixSchurWordTrace :=
  alternatingSixSchurTraceFrom alternatingSixSchurInitialTrace word

/-- The executable trace computes a valid weighted normal form. -/
theorem alternatingSixSchurTraceFrom_sound
    (trace : AlternatingSixSchurWordTrace)
    (word : AlternatingSixRewriteWord) :
    (alternatingSixSchurNormalElement trace.state *
          alternatingSixSchurWeight trace.weight) *
        alternatingSixSchurWord word =
      alternatingSixSchurNormalElement
          (alternatingSixSchurTraceFrom trace word).state *
        alternatingSixSchurWeight
          (alternatingSixSchurTraceFrom trace word).weight := by
  induction word generalizing trace with
  | nil =>
      simp [alternatingSixSchurTraceFrom,
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
      simpa [alternatingSixSchurTraceFrom,
        alternatingSixSchurTraceStep, column] using
        (ih (alternatingSixSchurTraceStep trace letter))

/-- A trace from the initial state gives a normal form for the word itself. -/
theorem alternatingSixSchurTrace_sound
    (word : AlternatingSixRewriteWord) :
    alternatingSixSchurWord word =
      alternatingSixSchurNormalElement
          (alternatingSixSchurTrace word).state *
        alternatingSixSchurWeight
          (alternatingSixSchurTrace word).weight := by
  have h :=
    alternatingSixSchurTraceFrom_sound
      alternatingSixSchurInitialTrace word
  have hnormal :
      alternatingSixSchurNormalElement 0 = 1 := by
    rfl
  simpa [alternatingSixSchurTrace,
    alternatingSixSchurInitialTrace, hnormal] using h

/-- Reduce an arbitrary central rewrite weight to a power of `k₀`. -/
theorem alternatingSixSchurWeight_eq_k0_zpow
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

/-! ### Concrete words and their projections -/

/-- A certified word for the left block cycle `(0 1 2)`. -/
def alternatingSixSchurLeftThreeCycleWord :
    AlternatingSixRewriteWord :=
  [(0, true), (1, false), (0, true), (1, true), (0, true),
    (1, false), (0, true), (1, true), (1, true), (0, true),
    (1, false)]

/-- The first half of the certified right block-cycle word. -/
private def alternatingSixSchurRightThreeCycleWordFirst :
    AlternatingSixRewriteWord :=
  [(0, true), (1, false), (0, true), (1, true), (0, true),
    (1, true), (1, true), (0, true), (1, false),
    (0, true), (1, false), (0, true), (1, true), (0, true),
    (1, true)]

/-- The second half of the certified right block-cycle word. -/
private def alternatingSixSchurRightThreeCycleWordSecond :
    AlternatingSixRewriteWord :=
  [(1, true), (0, true), (1, false),
    (1, true), (0, true), (1, true), (1, true), (0, true),
    (1, false), (0, true), (1, true), (1, true), (0, true),
    (1, false), (0, true)]

/-- A certified word for the right block cycle `(3 4 5)`.

It is the product of the square of the star cycle `(0 3 4)` and the
star cycle `(0 5 4)`. -/
def alternatingSixSchurRightThreeCycleWord :
    AlternatingSixRewriteWord :=
  alternatingSixSchurRightThreeCycleWordFirst ++
    alternatingSixSchurRightThreeCycleWordSecond

/-- The left word projects to `(0 1 2)`. -/
@[simp]
theorem alternatingSixSchurProjection_leftThreeCycleWord :
    alternatingSixSchurProjection
        (alternatingSixSchurWord
          alternatingSixSchurLeftThreeCycleWord) =
      alternatingSixLeftThreeCycle := by
  rw [alternatingSixSchurProjection_word]
  apply Subtype.ext
  simp only [alternatingSixPresentedWord,
    alternatingSixPresentationToAlternatingSix]
  change
    (FreeGroup.lift
      (fun i : Fin 2 =>
        if i = 0 then alternatingSixPresentationA
        else alternatingSixPresentationB)
      (FreeGroup.mk alternatingSixSchurLeftThreeCycleWord)).1 =
        alternatingSixLeftThreeCyclePerm
  decide

/-- The right word projects to `(3 4 5)`. -/
@[simp]
theorem alternatingSixSchurProjection_rightThreeCycleWord :
    alternatingSixSchurProjection
        (alternatingSixSchurWord
          alternatingSixSchurRightThreeCycleWord) =
      alternatingSixRightThreeCycle := by
  rw [alternatingSixSchurProjection_word]
  apply Subtype.ext
  simp only [alternatingSixPresentedWord,
    alternatingSixPresentationToAlternatingSix]
  change
    (FreeGroup.lift
      (fun i : Fin 2 =>
        if i = 0 then alternatingSixPresentationA
        else alternatingSixPresentationB)
      (FreeGroup.mk alternatingSixSchurRightThreeCycleWord)).1 =
        alternatingSixRightThreeCyclePerm
  decide

/-! ### Checked cubes and commutator -/

/-- The raw left lift. -/
def alternatingSixSchurRawLeftThreeCycleLift :
    AlternatingSixSchurPresentedGroup :=
  alternatingSixSchurWord alternatingSixSchurLeftThreeCycleWord

/-- The raw right lift. -/
def alternatingSixSchurRawRightThreeCycleLift :
    AlternatingSixSchurPresentedGroup :=
  alternatingSixSchurWord alternatingSixSchurRightThreeCycleWord

/-- The word whose value is the commutator of the two raw lifts. -/
def alternatingSixSchurThreeCycleCommutatorWord :
    AlternatingSixRewriteWord :=
  alternatingSixSchurLeftThreeCycleWord ++
    alternatingSixSchurRightThreeCycleWord ++
    alternatingSixRewriteInverseWord
      alternatingSixSchurLeftThreeCycleWord ++
    alternatingSixRewriteInverseWord
      alternatingSixSchurRightThreeCycleWord

/-- Tracing a concatenation is the same as tracing the two pieces in
sequence. -/
theorem alternatingSixSchurTraceFrom_append
    (trace : AlternatingSixSchurWordTrace)
    (left right : AlternatingSixRewriteWord) :
    alternatingSixSchurTraceFrom trace (left ++ right) =
      alternatingSixSchurTraceFrom
        (alternatingSixSchurTraceFrom trace left) right := by
  simp [alternatingSixSchurTraceFrom, List.foldl_append]

private def alternatingSixSchurLeftTraceOne :
    AlternatingSixSchurWordTrace :=
  ⟨276, ![(0 : ℤ), 0, 0, 0]⟩

private def alternatingSixSchurLeftTraceTwo :
    AlternatingSixSchurWordTrace :=
  ⟨283, ![(35 : ℤ), 9, -18, 5]⟩

private def alternatingSixSchurLeftTraceThree :
    AlternatingSixSchurWordTrace :=
  ⟨0, ![(40 : ℤ), 10, -18, 5]⟩

private def alternatingSixSchurRightTraceOne :
    AlternatingSixSchurWordTrace :=
  ⟨200, ![(25 : ℤ), 7, -11, 3]⟩

private def alternatingSixSchurRightTraceTwo :
    AlternatingSixSchurWordTrace :=
  ⟨180, ![(91 : ℤ), 11, -57, 25]⟩

private def alternatingSixSchurRightTraceThree :
    AlternatingSixSchurWordTrace :=
  ⟨0, ![(82 : ℤ), 10, -45, 20]⟩

private def alternatingSixSchurCommutatorTraceTwo :
    AlternatingSixSchurWordTrace :=
  ⟨263, ![(6 : ℤ), 1, 0, 0]⟩

private def alternatingSixSchurCommutatorTraceThree :
    AlternatingSixSchurWordTrace :=
  ⟨200, ![(-5 : ℤ), -3, 5, -1]⟩

private def alternatingSixSchurCommutatorTraceFour :
    AlternatingSixSchurWordTrace :=
  ⟨0, ![(60 : ℤ), 20, -32, 8]⟩

private def alternatingSixSchurRightTraceOneHalf :
    AlternatingSixSchurWordTrace :=
  ⟨208, ![(19 : ℤ), 2, -13, 6]⟩

private def alternatingSixSchurRightTraceTwoHalf :
    AlternatingSixSchurWordTrace :=
  ⟨343, ![(37 : ℤ), -3, -28, 16]⟩

private def alternatingSixSchurRightTraceThreeHalf :
    AlternatingSixSchurWordTrace :=
  ⟨160, ![(74 : ℤ), 8, -44, 20]⟩

private def alternatingSixSchurCommutatorTraceTwoHalf :
    AlternatingSixSchurWordTrace :=
  ⟨273, ![(29 : ℤ), 8, -13, 3]⟩

private def alternatingSixSchurCommutatorTraceFourHalf :
    AlternatingSixSchurWordTrace :=
  ⟨208, ![(39 : ℤ), 12, -21, 6]⟩

private def alternatingSixSchurRightTraceTwoThreeQuarter :
    AlternatingSixSchurWordTrace :=
  ⟨359, ![(83 : ℤ), 12, -52, 22]⟩

private def alternatingSixSchurCommutatorTraceTwoQuarter :
    AlternatingSixSchurWordTrace :=
  ⟨279, ![(9 : ℤ), 5, -2, -1]⟩

private theorem alternatingSixSchurLeftTraceOne_eq :
    alternatingSixSchurTraceFrom
        alternatingSixSchurInitialTrace
        alternatingSixSchurLeftThreeCycleWord =
      alternatingSixSchurLeftTraceOne := by
  apply AlternatingSixSchurWordTrace.ext
  · decide
  · funext i
    fin_cases i <;> decide

private theorem alternatingSixSchurLeftTraceTwo_eq :
    alternatingSixSchurTraceFrom
        alternatingSixSchurLeftTraceOne
        alternatingSixSchurLeftThreeCycleWord =
      alternatingSixSchurLeftTraceTwo := by
  apply AlternatingSixSchurWordTrace.ext
  · decide
  · funext i
    fin_cases i <;> decide

private theorem alternatingSixSchurLeftTraceThree_eq :
    alternatingSixSchurTraceFrom
        alternatingSixSchurLeftTraceTwo
        alternatingSixSchurLeftThreeCycleWord =
      alternatingSixSchurLeftTraceThree := by
  apply AlternatingSixSchurWordTrace.ext
  · decide
  · funext i
    fin_cases i <;> decide

private theorem alternatingSixSchurRightTraceOne_eq :
    alternatingSixSchurTraceFrom
        alternatingSixSchurInitialTrace
        alternatingSixSchurRightThreeCycleWord =
      alternatingSixSchurRightTraceOne := by
  rw [alternatingSixSchurRightThreeCycleWord,
    alternatingSixSchurTraceFrom_append]
  have hfirst :
      alternatingSixSchurTraceFrom
          alternatingSixSchurInitialTrace
          alternatingSixSchurRightThreeCycleWordFirst =
        alternatingSixSchurRightTraceOneHalf := by
    apply AlternatingSixSchurWordTrace.ext
    · decide
    · funext i
      fin_cases i <;> decide
  rw [hfirst]
  apply AlternatingSixSchurWordTrace.ext
  · decide
  · funext i
    fin_cases i <;> decide

private theorem alternatingSixSchurRightTraceTwo_eq :
    alternatingSixSchurTraceFrom
        alternatingSixSchurRightTraceOne
        alternatingSixSchurRightThreeCycleWord =
      alternatingSixSchurRightTraceTwo := by
  rw [alternatingSixSchurRightThreeCycleWord,
    alternatingSixSchurTraceFrom_append]
  have hfirst :
      alternatingSixSchurTraceFrom
          alternatingSixSchurRightTraceOne
          alternatingSixSchurRightThreeCycleWordFirst =
        alternatingSixSchurRightTraceTwoHalf := by
    apply AlternatingSixSchurWordTrace.ext
    · decide
    · funext i
      fin_cases i <;> decide
  rw [hfirst]
  rw [show alternatingSixSchurRightThreeCycleWordSecond =
      alternatingSixSchurRightThreeCycleWordSecond.take 7 ++
        alternatingSixSchurRightThreeCycleWordSecond.drop 7 by
          exact
            (List.take_append_drop 7
              alternatingSixSchurRightThreeCycleWordSecond).symm,
    alternatingSixSchurTraceFrom_append]
  have hsecondFirst :
      alternatingSixSchurTraceFrom
          alternatingSixSchurRightTraceTwoHalf
          (alternatingSixSchurRightThreeCycleWordSecond.take 7) =
        alternatingSixSchurRightTraceTwoThreeQuarter := by
    apply AlternatingSixSchurWordTrace.ext
    · decide
    · funext i
      fin_cases i <;> decide
  rw [hsecondFirst]
  apply AlternatingSixSchurWordTrace.ext
  · decide
  · funext i
    fin_cases i <;> decide

private theorem alternatingSixSchurRightTraceThree_eq :
    alternatingSixSchurTraceFrom
        alternatingSixSchurRightTraceTwo
        alternatingSixSchurRightThreeCycleWord =
      alternatingSixSchurRightTraceThree := by
  rw [alternatingSixSchurRightThreeCycleWord,
    alternatingSixSchurTraceFrom_append]
  have hfirst :
      alternatingSixSchurTraceFrom
          alternatingSixSchurRightTraceTwo
          alternatingSixSchurRightThreeCycleWordFirst =
        alternatingSixSchurRightTraceThreeHalf := by
    apply AlternatingSixSchurWordTrace.ext
    · decide
    · funext i
      fin_cases i <;> decide
  rw [hfirst]
  apply AlternatingSixSchurWordTrace.ext
  · decide
  · funext i
    fin_cases i <;> decide

private theorem alternatingSixSchurCommutatorTraceTwo_eq :
    alternatingSixSchurTraceFrom
        alternatingSixSchurLeftTraceOne
        alternatingSixSchurRightThreeCycleWord =
      alternatingSixSchurCommutatorTraceTwo := by
  rw [alternatingSixSchurRightThreeCycleWord,
    alternatingSixSchurTraceFrom_append]
  rw [show alternatingSixSchurRightThreeCycleWordFirst =
      alternatingSixSchurRightThreeCycleWordFirst.take 7 ++
        alternatingSixSchurRightThreeCycleWordFirst.drop 7 by
          exact
            (List.take_append_drop 7
              alternatingSixSchurRightThreeCycleWordFirst).symm,
    alternatingSixSchurTraceFrom_append]
  have hfirstFirst :
      alternatingSixSchurTraceFrom
          alternatingSixSchurLeftTraceOne
          (alternatingSixSchurRightThreeCycleWordFirst.take 7) =
        alternatingSixSchurCommutatorTraceTwoQuarter := by
    apply AlternatingSixSchurWordTrace.ext
    · decide
    · funext i
      fin_cases i <;> decide
  rw [hfirstFirst]
  have hfirst :
      alternatingSixSchurTraceFrom
          alternatingSixSchurCommutatorTraceTwoQuarter
          (alternatingSixSchurRightThreeCycleWordFirst.drop 7) =
        alternatingSixSchurCommutatorTraceTwoHalf := by
    apply AlternatingSixSchurWordTrace.ext
    · decide
    · funext i
      fin_cases i <;> decide
  rw [hfirst]
  apply AlternatingSixSchurWordTrace.ext
  · decide
  · funext i
    fin_cases i <;> decide

private theorem alternatingSixSchurCommutatorTraceThree_eq :
    alternatingSixSchurTraceFrom
        alternatingSixSchurCommutatorTraceTwo
        (alternatingSixRewriteInverseWord
          alternatingSixSchurLeftThreeCycleWord) =
      alternatingSixSchurCommutatorTraceThree := by
  apply AlternatingSixSchurWordTrace.ext
  · decide
  · funext i
    fin_cases i <;> decide

private theorem alternatingSixSchurCommutatorTraceFour_eq :
    alternatingSixSchurTraceFrom
        alternatingSixSchurCommutatorTraceThree
        (alternatingSixRewriteInverseWord
          alternatingSixSchurRightThreeCycleWord) =
      alternatingSixSchurCommutatorTraceFour := by
  have hinverse :
      alternatingSixRewriteInverseWord
          alternatingSixSchurRightThreeCycleWord =
        alternatingSixRewriteInverseWord
            alternatingSixSchurRightThreeCycleWordSecond ++
          alternatingSixRewriteInverseWord
            alternatingSixSchurRightThreeCycleWordFirst := by
    simp [alternatingSixSchurRightThreeCycleWord,
      alternatingSixRewriteInverseWord,
      List.reverse_append, List.map_append]
  rw [hinverse, alternatingSixSchurTraceFrom_append]
  have hsecond :
      alternatingSixSchurTraceFrom
          alternatingSixSchurCommutatorTraceThree
          (alternatingSixRewriteInverseWord
            alternatingSixSchurRightThreeCycleWordSecond) =
        alternatingSixSchurCommutatorTraceFourHalf := by
    apply AlternatingSixSchurWordTrace.ext
    · decide
    · funext i
      fin_cases i <;> decide
  rw [hsecond]
  apply AlternatingSixSchurWordTrace.ext
  · decide
  · funext i
    fin_cases i <;> decide

private theorem alternatingSixSchurLeftThreeCycleCubeTrace :
    alternatingSixSchurTrace
      (alternatingSixSchurLeftThreeCycleWord ++
        alternatingSixSchurLeftThreeCycleWord ++
        alternatingSixSchurLeftThreeCycleWord) =
      alternatingSixSchurLeftTraceThree := by
  rw [alternatingSixSchurTrace,
    alternatingSixSchurTraceFrom_append,
    alternatingSixSchurTraceFrom_append,
    alternatingSixSchurLeftTraceOne_eq,
    alternatingSixSchurLeftTraceTwo_eq,
    alternatingSixSchurLeftTraceThree_eq]

private theorem alternatingSixSchurRightThreeCycleCubeTrace :
    alternatingSixSchurTrace
      (alternatingSixSchurRightThreeCycleWord ++
        alternatingSixSchurRightThreeCycleWord ++
        alternatingSixSchurRightThreeCycleWord) =
      alternatingSixSchurRightTraceThree := by
  rw [alternatingSixSchurTrace,
    alternatingSixSchurTraceFrom_append,
    alternatingSixSchurTraceFrom_append,
    alternatingSixSchurRightTraceOne_eq,
    alternatingSixSchurRightTraceTwo_eq,
    alternatingSixSchurRightTraceThree_eq]

private theorem alternatingSixSchurThreeCycleCommutatorTrace :
    alternatingSixSchurTrace
      alternatingSixSchurThreeCycleCommutatorWord =
      alternatingSixSchurCommutatorTraceFour := by
  rw [alternatingSixSchurThreeCycleCommutatorWord,
    alternatingSixSchurTrace,
    alternatingSixSchurTraceFrom_append,
    alternatingSixSchurTraceFrom_append,
    alternatingSixSchurTraceFrom_append,
    alternatingSixSchurLeftTraceOne_eq,
    alternatingSixSchurCommutatorTraceTwo_eq,
    alternatingSixSchurCommutatorTraceThree_eq,
    alternatingSixSchurCommutatorTraceFour_eq]

/-- The raw left lift cubes to the central involution `k₀³`. -/
theorem alternatingSixSchurRawLeftThreeCycleLift_cube :
    alternatingSixSchurRawLeftThreeCycleLift ^ 3 =
      alternatingSixSchurPresentedK 0 ^ 3 := by
  have h :=
    alternatingSixSchurTrace_sound
      (alternatingSixSchurLeftThreeCycleWord ++
        alternatingSixSchurLeftThreeCycleWord ++
        alternatingSixSchurLeftThreeCycleWord)
  rw [alternatingSixSchurLeftThreeCycleCubeTrace] at h
  simp only [alternatingSixSchurLeftTraceThree] at h
  change
    alternatingSixSchurWord
          (alternatingSixSchurLeftThreeCycleWord ++
            alternatingSixSchurLeftThreeCycleWord ++
            alternatingSixSchurLeftThreeCycleWord) =
      alternatingSixSchurNormalElement 0 *
        alternatingSixSchurWeight ![(40 : ℤ), 10, -18, 5] at h
  have hweight :
      alternatingSixSchurWeight ![(40 : ℤ), 10, -18, 5] =
        alternatingSixSchurPresentedK 0 ^ 3 := by
    rw [alternatingSixSchurWeight_eq_k0_zpow]
    norm_num
    calc
      alternatingSixSchurPresentedK 0 ^ (93 : ℤ) =
          alternatingSixSchurPresentedK 0 ^ ((93 : ℤ) % 6) :=
        zpow_eq_zpow_emod 93 (by
          simpa using alternatingSixSchurPresentedK0_pow_six)
      _ = alternatingSixSchurPresentedK 0 ^ 3 := by norm_num
  have hnormal :
      alternatingSixSchurNormalElement 0 = 1 := by
    rfl
  rw [hnormal, one_mul, hweight] at h
  rw [alternatingSixSchurWord_append,
    alternatingSixSchurWord_append] at h
  simpa [alternatingSixSchurRawLeftThreeCycleLift,
    pow_succ, mul_assoc] using h

/-- The raw right lift cubes to the same central involution `k₀³`. -/
theorem alternatingSixSchurRawRightThreeCycleLift_cube :
    alternatingSixSchurRawRightThreeCycleLift ^ 3 =
      alternatingSixSchurPresentedK 0 ^ 3 := by
  have h :=
    alternatingSixSchurTrace_sound
      (alternatingSixSchurRightThreeCycleWord ++
        alternatingSixSchurRightThreeCycleWord ++
        alternatingSixSchurRightThreeCycleWord)
  rw [alternatingSixSchurRightThreeCycleCubeTrace] at h
  simp only [alternatingSixSchurRightTraceThree] at h
  change
    alternatingSixSchurWord
          (alternatingSixSchurRightThreeCycleWord ++
            alternatingSixSchurRightThreeCycleWord ++
            alternatingSixSchurRightThreeCycleWord) =
      alternatingSixSchurNormalElement 0 *
        alternatingSixSchurWeight ![(82 : ℤ), 10, -45, 20] at h
  have hweight :
      alternatingSixSchurWeight ![(82 : ℤ), 10, -45, 20] =
        alternatingSixSchurPresentedK 0 ^ 3 := by
    rw [alternatingSixSchurWeight_eq_k0_zpow]
    norm_num
    calc
      alternatingSixSchurPresentedK 0 ^ (177 : ℤ) =
          alternatingSixSchurPresentedK 0 ^ ((177 : ℤ) % 6) :=
        zpow_eq_zpow_emod 177 (by
          simpa using alternatingSixSchurPresentedK0_pow_six)
      _ = alternatingSixSchurPresentedK 0 ^ 3 := by norm_num
  have hnormal :
      alternatingSixSchurNormalElement 0 = 1 := by
    rfl
  rw [hnormal, one_mul, hweight] at h
  rw [alternatingSixSchurWord_append,
    alternatingSixSchurWord_append] at h
  simpa [alternatingSixSchurRawRightThreeCycleLift,
    pow_succ, mul_assoc] using h

/-- The two raw lifts have commutator `k₀⁴`, which generates the
central three-part. -/
theorem alternatingSixSchurRawThreeCycleLifts_commutator :
    ⁅alternatingSixSchurRawLeftThreeCycleLift,
      alternatingSixSchurRawRightThreeCycleLift⁆ =
        alternatingSixSchurPresentedK 0 ^ 4 := by
  have h :=
    alternatingSixSchurTrace_sound
      alternatingSixSchurThreeCycleCommutatorWord
  rw [alternatingSixSchurThreeCycleCommutatorTrace] at h
  simp only [alternatingSixSchurCommutatorTraceFour] at h
  have hweight :
      alternatingSixSchurWeight ![(60 : ℤ), 20, -32, 8] =
        alternatingSixSchurPresentedK 0 ^ 4 := by
    rw [alternatingSixSchurWeight_eq_k0_zpow]
    norm_num
    calc
      alternatingSixSchurPresentedK 0 ^ (160 : ℤ) =
          alternatingSixSchurPresentedK 0 ^ ((160 : ℤ) % 6) :=
        zpow_eq_zpow_emod 160 (by
          simpa using alternatingSixSchurPresentedK0_pow_six)
      _ = alternatingSixSchurPresentedK 0 ^ 4 := by norm_num
  have hnormal :
      alternatingSixSchurNormalElement 0 = 1 := by
    rfl
  rw [hnormal, one_mul, hweight] at h
  simpa [alternatingSixSchurThreeCycleCommutatorWord,
    alternatingSixSchurRawLeftThreeCycleLift,
    alternatingSixSchurRawRightThreeCycleLift,
    alternatingSixSchurWord_append,
    alternatingSixSchurWord_inverse,
    commutatorElement_def, mul_assoc] using h

end GroupTheory
end McKayConjecture
