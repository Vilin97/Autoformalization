/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormRuleChecks
import McKayConjecture.GroupTheory.BinaryIcosahedralNormalFormTransitionChecks

/-!
# An exact normal form for the binary-icosahedral presentation

This file checks a finite rewriting certificate for

`⟨a,b | (ab)² = a³ = b⁵⟩`.

The certificate first derives `a⁶ = 1` as a product of conjugates of the
two defining relators.  It then checks 120 shortlex normal forms and their
four right-multiplication transitions.  Thus the proof does not assume
finiteness or identify the presented group with a pre-existing finite
model.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- Appending a signed generator followed by its inverse does not change a
free-group word. -/
theorem binaryIcosahedralMk_append_cancel
    (wordPrefix : List (Fin 2 × Bool))
    (generator : Fin 2) (positive : Bool) :
    FreeGroup.mk
        (wordPrefix ++
          [(generator, positive), (generator, !positive)]) =
      FreeGroup.mk wordPrefix := by
  apply Quot.sound
  simpa using
    (@FreeGroup.Red.Step.not
      (Fin 2) wordPrefix [] generator positive)

/-- Pushing one letter onto the reversed reduction stack represents right
multiplication by that letter. -/
theorem binaryIcosahedralMk_reducePush_reverse
    (stack : List (Fin 2 × Bool))
    (x : Fin 2 × Bool) :
    FreeGroup.mk
        (binaryIcosahedralReducePush stack x).reverse =
      FreeGroup.mk stack.reverse *
        FreeGroup.mk [x] := by
  cases stack with
  | nil =>
      simp [binaryIcosahedralReducePush]
  | cons y ys =>
      rcases x with ⟨x, xb⟩
      rcases y with ⟨y, yb⟩
      fin_cases x <;>
        fin_cases y <;>
        cases xb <;>
        cases yb <;>
        simp [binaryIcosahedralReducePush,
          binaryIcosahedralLettersCancel,
          List.reverse_cons, List.append_assoc]
      all_goals
        symm
        apply binaryIcosahedralMk_append_cancel

/-- The accumulator invariant for the tail-recursive reducer. -/
theorem binaryIcosahedralMk_foldl_reducePush_reverse
    (stack word : List (Fin 2 × Bool)) :
    FreeGroup.mk
        (word.foldl
          binaryIcosahedralReducePush stack).reverse =
      FreeGroup.mk stack.reverse *
        FreeGroup.mk word := by
  induction word generalizing stack with
  | nil =>
      simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih,
        binaryIcosahedralMk_reducePush_reverse]
    rw [mul_assoc, FreeGroup.mul_mk]
    rfl

/-- The executable reduction used by the certificates preserves the
represented free-group element. -/
theorem binaryIcosahedralMk_fastReduce
    (word : List (Fin 2 × Bool)) :
    FreeGroup.mk
        (binaryIcosahedralFastReduce word) =
      FreeGroup.mk word := by
  simpa [binaryIcosahedralFastReduce] using
    binaryIcosahedralMk_foldl_reducePush_reverse
      ([] : List (Fin 2 × Bool)) word

/-- The raw conjugate word evaluates to the corresponding conjugate in the
free group. -/
theorem binaryIcosahedralMk_relatorConjugateWord
    (relatorWords : Nat → String)
    (c : BinaryIcosahedralRelatorConjugate) :
    FreeGroup.mk
        (binaryIcosahedralRelatorConjugateWord
          relatorWords c) =
      binaryIcosahedralEvaluateRelatorConjugate
        relatorWords c := by
  cases hc : c.inverted <;>
    simp [binaryIcosahedralRelatorConjugateWord,
      binaryIcosahedralEvaluateRelatorConjugate,
      binaryIcosahedralFreeWord, FreeGroup.inv_mk,
      List.append_assoc, hc]

/-- The raw certificate word evaluates to the product of conjugates used by
the abstract soundness proof. -/
theorem binaryIcosahedralMk_certificateWord
    (relatorWords : Nat → String)
    (certificate : String) :
    FreeGroup.mk
        (binaryIcosahedralCertificateWord
          relatorWords certificate) =
      binaryIcosahedralEvaluateCertificate
        relatorWords certificate := by
  unfold binaryIcosahedralCertificateWord
  unfold binaryIcosahedralEvaluateCertificate
  generalize
    binaryIcosahedralDecodeCertificate certificate =
      decoded
  induction decoded with
  | nil =>
      rfl
  | cons c cs ih =>
      rw [binaryIcosahedralCertificateWordList,
        binaryIcosahedralEvaluateCertificateList,
        ← FreeGroup.mul_mk,
        binaryIcosahedralMk_relatorConjugateWord,
        ih]

/-- The printed first relator is exactly `a³b⁻⁵`. -/
theorem binaryIcosahedralFreeWord_powerRelator :
    binaryIcosahedralFreeWord "aaaBBBBB" =
      binaryIcosahedralTwoRelatorPower := by
  native_decide

/-- The printed second relator is exactly `(ab)²a⁻³`. -/
theorem binaryIcosahedralFreeWord_productRelator :
    binaryIcosahedralFreeWord "ababAAA" =
      binaryIcosahedralTwoRelatorProduct := by
  native_decide

/-- Every printed defining relator lies in the normal closure of the
presentation relators. -/
theorem binaryIcosahedralDefiningRelator_mem_normalClosure
    (i : Nat) :
    binaryIcosahedralFreeWord
        (binaryIcosahedralDefiningRelatorWords i) ∈
      Subgroup.normalClosure
        binaryIcosahedralTwoRelators := by
  cases i with
  | zero =>
    change
      binaryIcosahedralFreeWord "aaaBBBBB" ∈
        Subgroup.normalClosure
          binaryIcosahedralTwoRelators
    rw [binaryIcosahedralFreeWord_powerRelator]
    exact
      Subgroup.subset_normalClosure
        (by simp [binaryIcosahedralTwoRelators])
  | succ i =>
    change
      binaryIcosahedralFreeWord "ababAAA" ∈
        Subgroup.normalClosure
          binaryIcosahedralTwoRelators
    rw [binaryIcosahedralFreeWord_productRelator]
    exact
      Subgroup.subset_normalClosure
        (by simp [binaryIcosahedralTwoRelators])

/-- A product-of-conjugates certificate evaluates into the normal closure
as soon as each named relator does. -/
theorem binaryIcosahedralEvaluateCertificate_mem_normalClosure
    (relatorWords : Nat → String)
    (hrelator :
      ∀ i,
        binaryIcosahedralFreeWord (relatorWords i) ∈
          Subgroup.normalClosure
            binaryIcosahedralTwoRelators)
    (certificate : String) :
    binaryIcosahedralEvaluateCertificate
        relatorWords certificate ∈
      Subgroup.normalClosure
        binaryIcosahedralTwoRelators := by
  unfold binaryIcosahedralEvaluateCertificate
  generalize
    binaryIcosahedralDecodeCertificate certificate =
      decoded
  induction decoded with
  | nil =>
      exact
        (Subgroup.normalClosure
          binaryIcosahedralTwoRelators).one_mem
  | cons c cs ih =>
      apply
        (Subgroup.normalClosure
          binaryIcosahedralTwoRelators).mul_mem
      · unfold binaryIcosahedralEvaluateRelatorConjugate
        dsimp only
        apply
          Subgroup.normalClosure_normal.conj_mem
        cases hc : c.inverted
        · simpa [binaryIcosahedralEvaluateRelatorConjugate,
            hc] using hrelator c.relation
        · simpa [binaryIcosahedralEvaluateRelatorConjugate,
            hc] using
              (Subgroup.normalClosure
                binaryIcosahedralTwoRelators).inv_mem
                (hrelator c.relation)
      · simpa [binaryIcosahedralEvaluateCertificateList] using ih

/-- The generated order-six certificate is a literal equality in the free
group. -/
theorem binaryIcosahedralOrderSixCertificate_valid :
    binaryIcosahedralFreeWord "aaaaaa" =
      binaryIcosahedralEvaluateCertificate
        binaryIcosahedralDefiningRelatorWords
        binaryIcosahedralOrderSixCertificate := by
  calc
    binaryIcosahedralFreeWord "aaaaaa" =
        FreeGroup.mk
          (binaryIcosahedralDecodedWord "aaaaaa") := rfl
    _ = FreeGroup.mk
        (binaryIcosahedralFastReduce
          (binaryIcosahedralDecodedWord "aaaaaa")) :=
      (binaryIcosahedralMk_fastReduce _).symm
    _ = FreeGroup.mk
        (binaryIcosahedralFastReduce
          (binaryIcosahedralCertificateWord
            binaryIcosahedralDefiningRelatorWords
            binaryIcosahedralOrderSixCertificate)) := by
      apply congrArg FreeGroup.mk
      native_decide
    _ = FreeGroup.mk
        (binaryIcosahedralCertificateWord
          binaryIcosahedralDefiningRelatorWords
          binaryIcosahedralOrderSixCertificate) :=
      binaryIcosahedralMk_fastReduce _
    _ = _ :=
      binaryIcosahedralMk_certificateWord
        binaryIcosahedralDefiningRelatorWords
        binaryIcosahedralOrderSixCertificate

/-- The relation `a⁶ = 1` follows from the two defining relators. -/
theorem binaryIcosahedralFreeWord_orderSix_mem_normalClosure :
    binaryIcosahedralFreeWord "aaaaaa" ∈
      Subgroup.normalClosure
        binaryIcosahedralTwoRelators := by
  rw [binaryIcosahedralOrderSixCertificate_valid]
  exact
    binaryIcosahedralEvaluateCertificate_mem_normalClosure
      binaryIcosahedralDefiningRelatorWords
      binaryIcosahedralDefiningRelator_mem_normalClosure
      binaryIcosahedralOrderSixCertificate

/-- Every relator available to the normal-form checker is justified by the
original two relations. -/
theorem binaryIcosahedralExtendedRelator_mem_normalClosure
    (i : Nat) :
    binaryIcosahedralFreeWord
        (binaryIcosahedralExtendedRelatorWords i) ∈
      Subgroup.normalClosure
        binaryIcosahedralTwoRelators := by
  rcases i with (_ | _ | i)
  · simpa [binaryIcosahedralExtendedRelatorWords,
      binaryIcosahedralDefiningRelatorWords] using
        binaryIcosahedralDefiningRelator_mem_normalClosure 0
  · simpa [binaryIcosahedralExtendedRelatorWords,
      binaryIcosahedralDefiningRelatorWords] using
        binaryIcosahedralDefiningRelator_mem_normalClosure 1
  · simpa [binaryIcosahedralExtendedRelatorWords] using
      binaryIcosahedralFreeWord_orderSix_mem_normalClosure

/-- Convert a signed free-group letter to its transition-table column. -/
def binaryIcosahedralTransitionLetter
    (letter : Fin 2 × Bool) :
    Fin 4 :=
  if letter.1 = 0 then
    if letter.2 then 0 else 1
  else
    if letter.2 then 2 else 3

/-- The printed transition letter evaluates to the given signed letter. -/
theorem binaryIcosahedralFreeWord_transitionLetter
    (letter : Fin 2 × Bool) :
    binaryIcosahedralFreeWord
        (binaryIcosahedralNormalFormLetterWords
          (binaryIcosahedralTransitionLetter letter)) =
      FreeGroup.mk [letter] := by
  rcases letter with ⟨generator, positive⟩
  fin_cases generator <;>
    cases positive <;>
    native_decide

/-- The element represented by the `i`th certified normal word. -/
def binaryIcosahedralNormalFormElement
    (i : Fin 120) :
    BinaryIcosahedralTwoPresentedGroup :=
  PresentedGroup.mk
    binaryIcosahedralTwoRelators
    (binaryIcosahedralFreeWord
      (binaryIcosahedralNormalFormWords i))

/-- The presented element represented by a transition-table letter. -/
def binaryIcosahedralNormalFormLetterElement
    (letter : Fin 4) :
    BinaryIcosahedralTwoPresentedGroup :=
  PresentedGroup.mk
    binaryIcosahedralTwoRelators
    (binaryIcosahedralFreeWord
      (binaryIcosahedralNormalFormLetterWords letter))

/-- The difference between the two sides of every certified rewrite rule
lies in the normal closure of the two defining relators. -/
theorem binaryIcosahedralRewriteRuleDifference_mem
    (ruleIndex : Fin 122) :
    binaryIcosahedralFreeWord
          (binaryIcosahedralRewritePatterns ruleIndex).lhs *
        (binaryIcosahedralFreeWord
          (binaryIcosahedralRewritePatterns ruleIndex).rhs)⁻¹ ∈
      Subgroup.normalClosure
        binaryIcosahedralTwoRelators := by
  have hvalid :
      binaryIcosahedralFastReduce
          (binaryIcosahedralDecodedWord
              (binaryIcosahedralRewritePatterns ruleIndex).lhs ++
            FreeGroup.invRev
              (binaryIcosahedralDecodedWord
                (binaryIcosahedralRewritePatterns ruleIndex).rhs)) =
        binaryIcosahedralFastReduce
          (binaryIcosahedralCertificateWord
            binaryIcosahedralExtendedRelatorWords
            (binaryIcosahedralRewriteRules
              ruleIndex).certificate) := by
    have h :=
      binaryIcosahedralRewriteRules_valid ruleIndex
    unfold binaryIcosahedralRewriteRuleValid at h
    rw [binaryIcosahedralRewriteRules_pattern] at h
    exact h
  have hfree :
      binaryIcosahedralFreeWord
            (binaryIcosahedralRewritePatterns ruleIndex).lhs *
          (binaryIcosahedralFreeWord
            (binaryIcosahedralRewritePatterns ruleIndex).rhs)⁻¹ =
        binaryIcosahedralEvaluateCertificate
          binaryIcosahedralExtendedRelatorWords
          (binaryIcosahedralRewriteRules
            ruleIndex).certificate := by
    calc
      _ = FreeGroup.mk
          (binaryIcosahedralDecodedWord
              (binaryIcosahedralRewritePatterns ruleIndex).lhs ++
            FreeGroup.invRev
              (binaryIcosahedralDecodedWord
                (binaryIcosahedralRewritePatterns
                  ruleIndex).rhs)) := by
          simp [binaryIcosahedralFreeWord,
            FreeGroup.inv_mk]
      _ = FreeGroup.mk
          (binaryIcosahedralFastReduce
            (binaryIcosahedralDecodedWord
                (binaryIcosahedralRewritePatterns
                  ruleIndex).lhs ++
              FreeGroup.invRev
                (binaryIcosahedralDecodedWord
                  (binaryIcosahedralRewritePatterns
                    ruleIndex).rhs))) :=
        (binaryIcosahedralMk_fastReduce _).symm
      _ = FreeGroup.mk
          (binaryIcosahedralFastReduce
            (binaryIcosahedralCertificateWord
              binaryIcosahedralExtendedRelatorWords
              (binaryIcosahedralRewriteRules
                ruleIndex).certificate)) :=
        congrArg FreeGroup.mk hvalid
      _ = FreeGroup.mk
          (binaryIcosahedralCertificateWord
            binaryIcosahedralExtendedRelatorWords
            (binaryIcosahedralRewriteRules
              ruleIndex).certificate) :=
        binaryIcosahedralMk_fastReduce _
      _ = _ :=
        binaryIcosahedralMk_certificateWord
          binaryIcosahedralExtendedRelatorWords
          (binaryIcosahedralRewriteRules
            ruleIndex).certificate
  rw [hfree]
  exact
    binaryIcosahedralEvaluateCertificate_mem_normalClosure
      binaryIcosahedralExtendedRelatorWords
      binaryIcosahedralExtendedRelator_mem_normalClosure
      (binaryIcosahedralRewriteRules
        ruleIndex).certificate

/-- Every oriented rewrite rule is an equality in the presented group. -/
theorem binaryIcosahedralRewriteRule_presented_eq
    (ruleIndex : Fin 122) :
    PresentedGroup.mk
          binaryIcosahedralTwoRelators
          (binaryIcosahedralFreeWord
            (binaryIcosahedralRewritePatterns ruleIndex).lhs) =
      PresentedGroup.mk
          binaryIcosahedralTwoRelators
          (binaryIcosahedralFreeWord
            (binaryIcosahedralRewritePatterns ruleIndex).rhs) := by
  apply eq_of_mul_inv_eq_one
  have hmk :
      PresentedGroup.mk
          binaryIcosahedralTwoRelators
          (binaryIcosahedralFreeWord
              (binaryIcosahedralRewritePatterns ruleIndex).lhs *
            (binaryIcosahedralFreeWord
              (binaryIcosahedralRewritePatterns
                ruleIndex).rhs)⁻¹) =
        1 :=
    PresentedGroup.mk_eq_one_iff.mpr
      (binaryIcosahedralRewriteRuleDifference_mem ruleIndex)
  simpa using hmk

/-- Interpret an arbitrary signed word in the two-generator presented
group. -/
def binaryIcosahedralPresentedWord
    (word : List (Fin 2 × Bool)) :
    BinaryIcosahedralTwoPresentedGroup :=
  PresentedGroup.mk
    binaryIcosahedralTwoRelators
    (FreeGroup.mk word)

/-- Interpreting an append is multiplication in the presented group. -/
theorem binaryIcosahedralPresentedWord_append
    (u v : List (Fin 2 × Bool)) :
    binaryIcosahedralPresentedWord (u ++ v) =
      binaryIcosahedralPresentedWord u *
        binaryIcosahedralPresentedWord v := by
  simp [binaryIcosahedralPresentedWord,
    ← FreeGroup.mul_mk]

/-- Replaying one certified contextual rewrite preserves the represented
element of the presented group. -/
theorem binaryIcosahedralApplyRewriteStep_sound
    (word next : List (Fin 2 × Bool))
    (step : BinaryIcosahedralRewriteStep)
    (hstep :
      binaryIcosahedralApplyRewriteStep
          binaryIcosahedralRewritePatterns word step =
        some next) :
    binaryIcosahedralPresentedWord word =
      binaryIcosahedralPresentedWord next := by
  unfold binaryIcosahedralApplyRewriteStep at hstep
  dsimp only at hstep
  split at hstep
  next hword =>
    simp only [Option.some.injEq] at hstep
    subst next
    rw [hword]
    simp only [List.append_assoc,
      binaryIcosahedralPresentedWord_append]
    have hrule :
        binaryIcosahedralPresentedWord
              (binaryIcosahedralDecodedWord
                (binaryIcosahedralRewritePatterns
                  step.rule).lhs) =
          binaryIcosahedralPresentedWord
            (binaryIcosahedralDecodedWord
              (binaryIcosahedralRewritePatterns
                step.rule).rhs) := by
      simpa [binaryIcosahedralPresentedWord,
        binaryIcosahedralFreeWord] using
          binaryIcosahedralRewriteRule_presented_eq
            step.rule
    rw [hrule]
  next hword =>
    contradiction

/-- Replaying a whole certified rewrite trace preserves the represented
element of the presented group. -/
theorem binaryIcosahedralApplyRewriteTrace_sound
    (word next : List (Fin 2 × Bool))
    (trace : List BinaryIcosahedralRewriteStep)
    (htrace :
      binaryIcosahedralApplyRewriteTrace
          binaryIcosahedralRewritePatterns word trace =
        some next) :
    binaryIcosahedralPresentedWord word =
      binaryIcosahedralPresentedWord next := by
  induction trace generalizing word with
  | nil =>
      simp only [binaryIcosahedralApplyRewriteTrace,
        Option.some.injEq] at htrace
      subst next
      rfl
  | cons step trace ih =>
      simp only [binaryIcosahedralApplyRewriteTrace] at htrace
      cases hstep :
          binaryIcosahedralApplyRewriteStep
            binaryIcosahedralRewritePatterns word step with
      | none =>
          simp [hstep] at htrace
      | some middle =>
          rw [hstep] at htrace
          exact
            (binaryIcosahedralApplyRewriteStep_sound
                word middle step hstep).trans
              (ih middle htrace)

/-- Each table transition is a genuine equality in the two-generator
presented group. -/
theorem binaryIcosahedralNormalFormTransition_presentedWord
    (i : Fin 120) (letter : Fin 4) :
    binaryIcosahedralPresentedWord
          (binaryIcosahedralDecodedWord
              (binaryIcosahedralNormalFormWords i) ++
            binaryIcosahedralDecodedWord
              (binaryIcosahedralNormalFormLetterWords letter)) =
      binaryIcosahedralPresentedWord
        (binaryIcosahedralDecodedWord
          (binaryIcosahedralNormalFormWords
            (binaryIcosahedralNormalFormTransitions
              i letter).target)) := by
  apply binaryIcosahedralApplyRewriteTrace_sound
  exact
    binaryIcosahedralNormalFormTransitions_valid i letter

/-- Right multiplication by any signed generator stays in the certified
120-element normal-form table. -/
theorem binaryIcosahedralNormalFormElement_mul_letter
    (i : Fin 120) (letter : Fin 4) :
    binaryIcosahedralNormalFormElement i *
        binaryIcosahedralNormalFormLetterElement letter =
      binaryIcosahedralNormalFormElement
        (binaryIcosahedralNormalFormTransitions
          i letter).target := by
  simpa [binaryIcosahedralNormalFormElement,
    binaryIcosahedralNormalFormLetterElement,
    binaryIcosahedralPresentedWord,
    binaryIcosahedralFreeWord,
    ← FreeGroup.mul_mk] using
      binaryIcosahedralNormalFormTransition_presentedWord
        i letter

/-- Every element of the two-generator presentation has one of the 120
certified normal forms. -/
theorem binaryIcosahedralTwoPresented_exists_normalForm
    (g : BinaryIcosahedralTwoPresentedGroup) :
    ∃ i : Fin 120,
      g = binaryIcosahedralNormalFormElement i := by
  apply PresentedGroup.induction_on g
  intro z
  refine Quot.inductionOn z ?_
  intro word
  induction word using List.reverseRecOn with
  | nil =>
      refine ⟨0, ?_⟩
      change
        PresentedGroup.mk
            binaryIcosahedralTwoRelators
            (FreeGroup.mk []) =
          PresentedGroup.mk
            binaryIcosahedralTwoRelators
            (FreeGroup.mk [])
      rfl
  | append_singleton word letter ih =>
      rcases ih with ⟨i, hi⟩
      rw [FreeGroup.quot_mk_eq_mk] at hi
      let tableLetter :=
        binaryIcosahedralTransitionLetter letter
      refine
        ⟨(binaryIcosahedralNormalFormTransitions
            i tableLetter).target, ?_⟩
      change
        PresentedGroup.mk
            binaryIcosahedralTwoRelators
            (FreeGroup.mk word *
              FreeGroup.mk [letter]) =
          binaryIcosahedralNormalFormElement
            (binaryIcosahedralNormalFormTransitions
              i tableLetter).target
      rw [map_mul, hi,
        ← binaryIcosahedralFreeWord_transitionLetter]
      exact
        binaryIcosahedralNormalFormElement_mul_letter
          i tableLetter

/-- The certified 120 normal words map onto the two-generator presented
group. -/
theorem binaryIcosahedralNormalFormElement_surjective :
    Function.Surjective
      binaryIcosahedralNormalFormElement := by
  intro g
  obtain ⟨i, hi⟩ :=
    binaryIcosahedralTwoPresented_exists_normalForm g
  exact ⟨i, hi.symm⟩

noncomputable instance binaryIcosahedralTwoPresentedGroup_finite :
    Finite BinaryIcosahedralTwoPresentedGroup :=
  Finite.of_surjective
    binaryIcosahedralNormalFormElement
    binaryIcosahedralNormalFormElement_surjective

/-- The two-generator binary-icosahedral presentation has order at most
`120`. -/
theorem natCard_binaryIcosahedralTwoPresentedGroup_le :
    Nat.card BinaryIcosahedralTwoPresentedGroup ≤ 120 := by
  simpa using
    Nat.card_le_card_of_surjective
      binaryIcosahedralNormalFormElement
      binaryIcosahedralNormalFormElement_surjective

noncomputable instance binaryIcosahedralPresentedGroup_finite :
    Finite BinaryIcosahedralPresentedGroup :=
  Finite.of_surjective
    binaryIcosahedralTwoPresentationToBalanced
    binaryIcosahedralTwoPresentationToBalanced_surjective

/-- The balanced binary-icosahedral presentation also has order at most
`120`. -/
theorem natCard_binaryIcosahedralPresentedGroup_le :
    Nat.card BinaryIcosahedralPresentedGroup ≤ 120 :=
  (Nat.card_le_card_of_surjective
      binaryIcosahedralTwoPresentationToBalanced
      binaryIcosahedralTwoPresentationToBalanced_surjective).trans
    natCard_binaryIcosahedralTwoPresentedGroup_le

/-- The surjection from the balanced presentation onto `SL(2, 𝔽₅)` is
bijective. -/
theorem binaryIcosahedralPresentationToSpecialLinearTwoFive_bijective :
    Function.Bijective
      binaryIcosahedralPresentationToSpecialLinearTwoFive :=
  Function.Surjective.bijective_of_nat_card_le
    binaryIcosahedralPresentationToSpecialLinearTwoFive_surjective (by
      rw [natCard_specialLinearTwoFive]
      exact natCard_binaryIcosahedralPresentedGroup_le)

/-- The balanced binary-icosahedral presentation is exactly
`SL(2, 𝔽₅)`. -/
def binaryIcosahedralPresentedGroupEquivSpecialLinearTwoFive :
    BinaryIcosahedralPresentedGroup ≃*
      SpecialLinearTwoFive :=
  MulEquiv.ofBijective
    binaryIcosahedralPresentationToSpecialLinearTwoFive
    binaryIcosahedralPresentationToSpecialLinearTwoFive_bijective

end GroupTheory
end McKayConjecture
