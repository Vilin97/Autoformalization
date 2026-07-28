/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverKernelRelations

/-!
# Normal forms in the sixfold-cover presentation

The checked 360-state rewrite table is reused with its central weights.
The lattice calculation reduces every such weight to one of six powers
of `k₀`, giving a finite set of at most `360 * 6` representatives.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- The six selected powers of the first central relator value. -/
def alternatingSixSchurCentralRepresentative
    (n : Fin 6) :
    AlternatingSixSchurPresentedGroup :=
  (Additive.toMul
    ((n.val : ℤ) •
      alternatingSixSchurCentralKAdditive 0)).1

/-- An arbitrary integer multiple of `k₀` has a representative with
exponent between zero and five. -/
theorem alternatingSixSchurCentralKAdditive_exists_finSix
    (z : ℤ) :
    ∃ n : Fin 6,
      z • alternatingSixSchurCentralKAdditive 0 =
        (n.val : ℤ) •
          alternatingSixSchurCentralKAdditive 0 := by
  let remainder := z % 6
  have hnonnegative : 0 ≤ remainder := by
    dsimp [remainder]
    exact Int.emod_nonneg z (by norm_num)
  have hless : remainder < 6 := by
    dsimp [remainder]
    exact Int.emod_lt_of_pos z (by norm_num)
  let n : Fin 6 :=
    ⟨remainder.toNat, by omega⟩
  refine ⟨n, ?_⟩
  have hsix :
      (6 : ℤ) • alternatingSixSchurCentralKAdditive 0 = 0 :=
    alternatingSixSchurCentralKAdditive_reduce.2.2.2
  have hdecompose : remainder + 6 * (z / 6) = z := by
    dsimp [remainder]
    omega
  rw [← hdecompose, add_smul]
  have hmultiple :
      (6 * (z / 6)) •
          alternatingSixSchurCentralKAdditive 0 = 0 := by
    rw [mul_comm, mul_smul, hsix, smul_zero]
  rw [hmultiple, add_zero]
  change
    remainder • alternatingSixSchurCentralKAdditive 0 =
      (remainder.toNat : ℤ) •
        alternatingSixSchurCentralKAdditive 0
  rw [Int.toNat_of_nonneg hnonnegative]

/-- Every checked central weight is one of the six selected powers of
`k₀`. -/
theorem alternatingSixSchurWeight_exists_finSix
    (weight : Fin 4 → ℤ) :
    ∃ n : Fin 6,
      alternatingSixSchurWeight weight =
        alternatingSixSchurCentralRepresentative n := by
  obtain ⟨n, hn⟩ :=
    alternatingSixSchurCentralKAdditive_exists_finSix
      (weight 0 + 3 * weight 1 - weight 2 + weight 3)
  refine ⟨n, ?_⟩
  apply congrArg
    (fun value :
        Additive
          (Subgroup.center AlternatingSixSchurPresentedGroup) =>
      (Additive.toMul value).1)
  rw [alternatingSixSchurWeightAdditive_reduce]
  exact hn

/-- The element represented by one of the 360 noncentral normal words. -/
def alternatingSixSchurNormalElement
    (i : Fin 360) :
    AlternatingSixSchurPresentedGroup :=
  alternatingSixSchurWord
    (alternatingSixRewriteNormalWords i)

/-- The central weight carried by one transition of the checked table. -/
def alternatingSixSchurTransitionWeight
    (i : Fin 360) (letter : Fin 4) :
    Fin 4 → ℤ :=
  alternatingSixRewriteProofWeight
    alternatingSixRewriteRules
    (alternatingSixRewriteTransitions i letter).proof

/-- The checked transition equation in normal-element notation. -/
theorem alternatingSixSchurNormalElement_mul_letter
    (i : Fin 360) (letter : Fin 4) :
    alternatingSixSchurNormalElement i *
        alternatingSixSchurWord
          (alternatingSixRewriteLetterWord letter) =
      alternatingSixSchurNormalElement
          (alternatingSixRewriteTransitions i letter).target *
        alternatingSixSchurWeight
          (alternatingSixSchurTransitionWeight i letter) := by
  simpa [alternatingSixSchurNormalElement,
    alternatingSixSchurTransitionWeight,
    alternatingSixSchurWord_append] using
      alternatingSixSchurRewriteTransition_sound i letter

/-- A central weight commutes with every element of the presented group. -/
theorem alternatingSixSchurWeight_commute
    (weight : Fin 4 → ℤ)
    (g : AlternatingSixSchurPresentedGroup) :
    alternatingSixSchurWeight weight * g =
      g * alternatingSixSchurWeight weight :=
  (Subgroup.mem_center_iff.mp
    (alternatingSixSchurWeight_mem_center weight) g).symm

/-- Appending a noncentral signed letter updates the table state and
adds its checked central weight. -/
theorem alternatingSixSchurNormal_mul_letter_weight
    (i : Fin 360) (letter : Fin 4)
    (oldWeight : Fin 4 → ℤ) :
    (alternatingSixSchurNormalElement i *
          alternatingSixSchurWeight oldWeight) *
        alternatingSixSchurWord
          (alternatingSixRewriteLetterWord letter) =
      alternatingSixSchurNormalElement
          (alternatingSixRewriteTransitions i letter).target *
        alternatingSixSchurWeight
          (alternatingSixRewriteAddWeight
            (alternatingSixSchurTransitionWeight i letter)
            oldWeight) := by
  calc
    _ =
        (alternatingSixSchurNormalElement i *
            alternatingSixSchurWord
              (alternatingSixRewriteLetterWord letter)) *
          alternatingSixSchurWeight oldWeight := by
            rw [mul_assoc,
              alternatingSixSchurWeight_commute oldWeight]
            simp only [← mul_assoc]
    _ =
        (alternatingSixSchurNormalElement
              (alternatingSixRewriteTransitions i letter).target *
            alternatingSixSchurWeight
              (alternatingSixSchurTransitionWeight i letter)) *
          alternatingSixSchurWeight oldWeight := by
            rw [alternatingSixSchurNormalElement_mul_letter]
    _ =
        alternatingSixSchurNormalElement
            (alternatingSixRewriteTransitions i letter).target *
          alternatingSixSchurWeight
            (alternatingSixRewriteAddWeight
              (alternatingSixSchurTransitionWeight i letter)
              oldWeight) := by
            rw [alternatingSixSchurWeight_add]
            simp only [mul_assoc]

/-- Multiplying a normal representative by another central weight just
adds the exponent vectors. -/
theorem alternatingSixSchurNormal_mul_central_weight
    (i : Fin 360) (oldWeight newWeight : Fin 4 → ℤ) :
    (alternatingSixSchurNormalElement i *
          alternatingSixSchurWeight oldWeight) *
        alternatingSixSchurWeight newWeight =
      alternatingSixSchurNormalElement i *
        alternatingSixSchurWeight
          (alternatingSixRewriteAddWeight oldWeight newWeight) := by
  rw [alternatingSixSchurWeight_add]
  simp only [mul_assoc]

/-- Embed one of the two noncentral signed letters among the six
presentation generators. -/
def alternatingSixSchurNoncentralLetter
    (letter : AlternatingSixRewriteLetter) :
    Fin 6 × Bool :=
  (⟨letter.1.val, by omega⟩, letter.2)

/-- The transition-table interpretation of a noncentral letter agrees
with its value in the six-generator presentation. -/
theorem alternatingSixSchurWord_transitionLetter
    (letter : AlternatingSixRewriteLetter) :
    alternatingSixSchurWord
        (alternatingSixRewriteLetterWord
          (alternatingSixRewriteTransitionLetter letter)) =
      PresentedGroup.mk alternatingSixSchurRelators
        (FreeGroup.mk
          [alternatingSixSchurNoncentralLetter letter]) := by
  rw [alternatingSixRewriteLetterWord_transitionLetter]
  rcases letter with ⟨generator, positive⟩
  fin_cases generator <;>
    cases positive <;>
    rfl

/-- The signed standard-basis weight belonging to a central generator. -/
def alternatingSixSchurSignedBasisWeight
    (i : Fin 4) (positive : Bool) :
    Fin 4 → ℤ :=
  fun j =>
    if j = i then
      if positive then 1 else -1
    else 0

/-- A signed central presentation letter is its signed basis weight. -/
theorem alternatingSixSchurWeight_signedBasis
    (i : Fin 4) (positive : Bool) :
    alternatingSixSchurWeight
        (alternatingSixSchurSignedBasisWeight i positive) =
      PresentedGroup.mk alternatingSixSchurRelators
        (FreeGroup.mk
          [((⟨i.val + 2, by omega⟩ : Fin 6), positive)]) := by
  cases positive
  · have hneg :
        alternatingSixSchurSignedBasisWeight i false =
          alternatingSixRewriteNegWeight
            (fun j => if j = i then 1 else 0) := by
        funext j
        simp only [alternatingSixSchurSignedBasisWeight,
          alternatingSixRewriteNegWeight]
        split <;> simp_all
    rw [hneg, alternatingSixSchurWeight_neg,
      alternatingSixSchurWeight_basis]
    rfl
  · rw [show
      alternatingSixSchurSignedBasisWeight i true =
        (fun j => if j = i then 1 else 0) by
          funext j
          simp [alternatingSixSchurSignedBasisWeight]]
    rw [alternatingSixSchurWeight_basis]
    rfl

/-- The class of table-normal element times a central weight is closed
under right multiplication by any signed presentation generator. -/
theorem alternatingSixSchurNormal_exists_mul_signedGenerator
    (i : Fin 360) (oldWeight : Fin 4 → ℤ)
    (letter : Fin 6 × Bool) :
    ∃ j : Fin 360, ∃ newWeight : Fin 4 → ℤ,
      (alternatingSixSchurNormalElement i *
          alternatingSixSchurWeight oldWeight) *
          PresentedGroup.mk alternatingSixSchurRelators
            (FreeGroup.mk [letter]) =
        alternatingSixSchurNormalElement j *
          alternatingSixSchurWeight newWeight := by
  rcases letter with ⟨generator, positive⟩
  fin_cases generator
  · let tableLetter : AlternatingSixRewriteLetter :=
      (0, positive)
    refine
      ⟨(alternatingSixRewriteTransitions i
          (alternatingSixRewriteTransitionLetter tableLetter)).target,
        alternatingSixRewriteAddWeight
          (alternatingSixSchurTransitionWeight i
            (alternatingSixRewriteTransitionLetter tableLetter))
          oldWeight, ?_⟩
    have heval :
        alternatingSixSchurWord
            (alternatingSixRewriteLetterWord
              (alternatingSixRewriteTransitionLetter tableLetter)) =
          PresentedGroup.mk alternatingSixSchurRelators
            (FreeGroup.mk [(0, positive)]) := by
      simpa [tableLetter,
        alternatingSixSchurNoncentralLetter] using
          alternatingSixSchurWord_transitionLetter tableLetter
    change
      (alternatingSixSchurNormalElement i *
          alternatingSixSchurWeight oldWeight) *
          PresentedGroup.mk alternatingSixSchurRelators
            (FreeGroup.mk [((0 : Fin 6), positive)]) =
        _
    rw [← heval]
    exact
      alternatingSixSchurNormal_mul_letter_weight i
        (alternatingSixRewriteTransitionLetter tableLetter)
        oldWeight
  · let tableLetter : AlternatingSixRewriteLetter :=
      (1, positive)
    refine
      ⟨(alternatingSixRewriteTransitions i
          (alternatingSixRewriteTransitionLetter tableLetter)).target,
        alternatingSixRewriteAddWeight
          (alternatingSixSchurTransitionWeight i
            (alternatingSixRewriteTransitionLetter tableLetter))
          oldWeight, ?_⟩
    have heval :
        alternatingSixSchurWord
            (alternatingSixRewriteLetterWord
              (alternatingSixRewriteTransitionLetter tableLetter)) =
          PresentedGroup.mk alternatingSixSchurRelators
            (FreeGroup.mk [(1, positive)]) := by
      simpa [tableLetter,
        alternatingSixSchurNoncentralLetter] using
          alternatingSixSchurWord_transitionLetter tableLetter
    change
      (alternatingSixSchurNormalElement i *
          alternatingSixSchurWeight oldWeight) *
          PresentedGroup.mk alternatingSixSchurRelators
            (FreeGroup.mk [((1 : Fin 6), positive)]) =
        _
    rw [← heval]
    exact
      alternatingSixSchurNormal_mul_letter_weight i
        (alternatingSixRewriteTransitionLetter tableLetter)
        oldWeight
  · refine
      ⟨i,
        alternatingSixRewriteAddWeight oldWeight
          (alternatingSixSchurSignedBasisWeight 0 positive), ?_⟩
    have heval :
        alternatingSixSchurWeight
            (alternatingSixSchurSignedBasisWeight 0 positive) =
          PresentedGroup.mk alternatingSixSchurRelators
            (FreeGroup.mk [(2, positive)]) := by
      simpa using
        alternatingSixSchurWeight_signedBasis 0 positive
    change
      (alternatingSixSchurNormalElement i *
          alternatingSixSchurWeight oldWeight) *
          PresentedGroup.mk alternatingSixSchurRelators
            (FreeGroup.mk [((2 : Fin 6), positive)]) =
        _
    rw [← heval]
    exact
      alternatingSixSchurNormal_mul_central_weight i oldWeight
        (alternatingSixSchurSignedBasisWeight 0 positive)
  · refine
      ⟨i,
        alternatingSixRewriteAddWeight oldWeight
          (alternatingSixSchurSignedBasisWeight 1 positive), ?_⟩
    have heval :
        alternatingSixSchurWeight
            (alternatingSixSchurSignedBasisWeight 1 positive) =
          PresentedGroup.mk alternatingSixSchurRelators
            (FreeGroup.mk [(3, positive)]) := by
      simpa using
        alternatingSixSchurWeight_signedBasis 1 positive
    change
      (alternatingSixSchurNormalElement i *
          alternatingSixSchurWeight oldWeight) *
          PresentedGroup.mk alternatingSixSchurRelators
            (FreeGroup.mk [((3 : Fin 6), positive)]) =
        _
    rw [← heval]
    exact
      alternatingSixSchurNormal_mul_central_weight i oldWeight
        (alternatingSixSchurSignedBasisWeight 1 positive)
  · refine
      ⟨i,
        alternatingSixRewriteAddWeight oldWeight
          (alternatingSixSchurSignedBasisWeight 2 positive), ?_⟩
    have heval :
        alternatingSixSchurWeight
            (alternatingSixSchurSignedBasisWeight 2 positive) =
          PresentedGroup.mk alternatingSixSchurRelators
            (FreeGroup.mk [(4, positive)]) := by
      simpa using
        alternatingSixSchurWeight_signedBasis 2 positive
    change
      (alternatingSixSchurNormalElement i *
          alternatingSixSchurWeight oldWeight) *
          PresentedGroup.mk alternatingSixSchurRelators
            (FreeGroup.mk [((4 : Fin 6), positive)]) =
        _
    rw [← heval]
    exact
      alternatingSixSchurNormal_mul_central_weight i oldWeight
        (alternatingSixSchurSignedBasisWeight 2 positive)
  · refine
      ⟨i,
        alternatingSixRewriteAddWeight oldWeight
          (alternatingSixSchurSignedBasisWeight 3 positive), ?_⟩
    have heval :
        alternatingSixSchurWeight
            (alternatingSixSchurSignedBasisWeight 3 positive) =
          PresentedGroup.mk alternatingSixSchurRelators
            (FreeGroup.mk [(5, positive)]) := by
      simpa using
        alternatingSixSchurWeight_signedBasis 3 positive
    change
      (alternatingSixSchurNormalElement i *
          alternatingSixSchurWeight oldWeight) *
          PresentedGroup.mk alternatingSixSchurRelators
            (FreeGroup.mk [((5 : Fin 6), positive)]) =
        _
    rw [← heval]
    exact
      alternatingSixSchurNormal_mul_central_weight i oldWeight
        (alternatingSixSchurSignedBasisWeight 3 positive)

/-- Every element of the six-generator presentation is a table-normal
word followed by an integral central weight. -/
theorem alternatingSixSchurPresented_exists_weightedNormalForm
    (g : AlternatingSixSchurPresentedGroup) :
    ∃ i : Fin 360, ∃ weight : Fin 4 → ℤ,
      g =
        alternatingSixSchurNormalElement i *
          alternatingSixSchurWeight weight := by
  apply PresentedGroup.induction_on g
  intro z
  refine Quot.inductionOn z ?_
  intro word
  induction word using List.reverseRecOn with
  | nil =>
      refine ⟨0, fun _ => 0, ?_⟩
      rfl
  | append_singleton word letter ih =>
      rcases ih with ⟨i, oldWeight, hi⟩
      rw [FreeGroup.quot_mk_eq_mk] at hi
      obtain ⟨j, newWeight, hmul⟩ :=
        alternatingSixSchurNormal_exists_mul_signedGenerator
          i oldWeight letter
      refine ⟨j, newWeight, ?_⟩
      change
        PresentedGroup.mk alternatingSixSchurRelators
            (FreeGroup.mk word * FreeGroup.mk [letter]) =
          alternatingSixSchurNormalElement j *
            alternatingSixSchurWeight newWeight
      rw [map_mul, hi]
      exact hmul

/-- Every element has one of `360 * 6` selected representatives. -/
theorem alternatingSixSchurPresented_exists_normalForm
    (g : AlternatingSixSchurPresentedGroup) :
    ∃ i : Fin 360, ∃ n : Fin 6,
      g =
        alternatingSixSchurNormalElement i *
          alternatingSixSchurCentralRepresentative n := by
  obtain ⟨i, weight, hi⟩ :=
    alternatingSixSchurPresented_exists_weightedNormalForm g
  obtain ⟨n, hn⟩ :=
    alternatingSixSchurWeight_exists_finSix weight
  exact ⟨i, n, hi.trans (congrArg
    (alternatingSixSchurNormalElement i * ·) hn)⟩

/-- The selected `360 * 6` normal representatives as a single map. -/
def alternatingSixSchurNormalRepresentative
    (index : Fin 360 × Fin 6) :
    AlternatingSixSchurPresentedGroup :=
  alternatingSixSchurNormalElement index.1 *
    alternatingSixSchurCentralRepresentative index.2

/-- The selected normal-representative map is onto. -/
theorem alternatingSixSchurNormalRepresentative_surjective :
    Function.Surjective
      alternatingSixSchurNormalRepresentative := by
  intro g
  obtain ⟨i, n, hi⟩ :=
    alternatingSixSchurPresented_exists_normalForm g
  exact ⟨(i, n), hi.symm⟩

noncomputable instance alternatingSixSchurPresentedGroup_finite :
    Finite AlternatingSixSchurPresentedGroup :=
  Finite.of_surjective
    alternatingSixSchurNormalRepresentative
    alternatingSixSchurNormalRepresentative_surjective

/-- The sixfold-cover presentation has order at most `2160`. -/
theorem natCard_alternatingSixSchurPresentedGroup_le :
    Nat.card AlternatingSixSchurPresentedGroup ≤ 2160 := by
  calc
    Nat.card AlternatingSixSchurPresentedGroup ≤
        Nat.card (Fin 360 × Fin 6) :=
      Nat.card_le_card_of_surjective
        alternatingSixSchurNormalRepresentative
        alternatingSixSchurNormalRepresentative_surjective
    _ = 2160 := by
      rw [Nat.card_prod, Nat.card_fin, Nat.card_fin]

end GroupTheory
end McKayConjecture
