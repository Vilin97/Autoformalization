/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.Abel
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverPresentation
import McKayConjecture.GroupTheory.AlternatingSixRewriteRuleChecks
import McKayConjecture.GroupTheory.AlternatingSixRewriteTransitionChecks

/-!
# Weighted rewrite soundness in the sixfold cover

The same short rewrite paths used for the order-360 presentation are
replayed without killing the four relators.  Their accumulated weights
are monomials in the four central elements `k₀,…,k₃`.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- The center, equipped with its canonical commutative group structure. -/
instance alternatingSixSchurCenterCommGroup :
    CommGroup
      (Subgroup.center AlternatingSixSchurPresentedGroup) where
  mul_comm left right := by
    apply Subtype.ext
    exact
      (Subgroup.mem_center_iff.mp
        left.2 right.1).symm

/-- The four central relator values as elements of the center. -/
def alternatingSixSchurCentralK (i : Fin 4) :
    Subgroup.center AlternatingSixSchurPresentedGroup :=
  ⟨alternatingSixSchurPresentedK i,
    alternatingSixSchurPresentedK_mem_center i⟩

/-- Additive notation for a central monomial with four integer
exponents. -/
def alternatingSixSchurWeightAdditive
    (weight : Fin 4 → ℤ) :
    Additive
      (Subgroup.center AlternatingSixSchurPresentedGroup) :=
  weight 0 • Additive.ofMul (alternatingSixSchurCentralK 0) +
    weight 1 • Additive.ofMul (alternatingSixSchurCentralK 1) +
      weight 2 • Additive.ofMul (alternatingSixSchurCentralK 2) +
        weight 3 • Additive.ofMul (alternatingSixSchurCentralK 3)

/-- The ambient group element represented by a central weight. -/
def alternatingSixSchurWeight
    (weight : Fin 4 → ℤ) :
    AlternatingSixSchurPresentedGroup :=
  (Additive.toMul
    (alternatingSixSchurWeightAdditive weight)).1

@[simp]
theorem alternatingSixSchurWeight_zero :
    alternatingSixSchurWeight (fun _ => 0) = 1 := by
  rfl

/-- Central weights turn coordinatewise addition into multiplication. -/
theorem alternatingSixSchurWeight_add
    (left right : Fin 4 → ℤ) :
    alternatingSixSchurWeight
        (alternatingSixRewriteAddWeight left right) =
      alternatingSixSchurWeight left *
        alternatingSixSchurWeight right := by
  have h :
      alternatingSixSchurWeightAdditive
          (alternatingSixRewriteAddWeight left right) =
        alternatingSixSchurWeightAdditive left +
          alternatingSixSchurWeightAdditive right := by
    simp only [alternatingSixSchurWeightAdditive,
      alternatingSixRewriteAddWeight, Pi.add_apply,
      add_smul]
    abel
  exact congrArg
    (fun value :
        Additive
          (Subgroup.center AlternatingSixSchurPresentedGroup) =>
      (Additive.toMul value).1) h

/-- Negating a weight gives the inverse monomial. -/
theorem alternatingSixSchurWeight_neg
    (weight : Fin 4 → ℤ) :
    alternatingSixSchurWeight
        (alternatingSixRewriteNegWeight weight) =
      (alternatingSixSchurWeight weight)⁻¹ := by
  have h :
      alternatingSixSchurWeightAdditive
          (alternatingSixRewriteNegWeight weight) =
        -alternatingSixSchurWeightAdditive weight := by
    simp only [alternatingSixSchurWeightAdditive,
      alternatingSixRewriteNegWeight, neg_smul]
    abel
  exact congrArg
    (fun value :
        Additive
          (Subgroup.center AlternatingSixSchurPresentedGroup) =>
      (Additive.toMul value).1) h

/-- A central monomial is central in the ambient presented group. -/
theorem alternatingSixSchurWeight_mem_center
    (weight : Fin 4 → ℤ) :
    alternatingSixSchurWeight weight ∈
      Subgroup.center AlternatingSixSchurPresentedGroup :=
  (Additive.toMul
    (alternatingSixSchurWeightAdditive weight)).2

/-- The weight of a standard basis vector is the corresponding `kᵢ`. -/
theorem alternatingSixSchurWeight_basis
    (i : Fin 4) :
    alternatingSixSchurWeight
        (fun j => if j = i then 1 else 0) =
      alternatingSixSchurPresentedK i := by
  fin_cases i <;>
    simp [alternatingSixSchurWeight,
      alternatingSixSchurWeightAdditive,
      alternatingSixSchurCentralK]

/-- Evaluate a signed word in the two noncentral generators of the Schur
presentation. -/
def alternatingSixSchurWord
    (word : AlternatingSixRewriteWord) :
    AlternatingSixSchurPresentedGroup :=
  FreeGroup.lift
      (fun i : Fin 2 =>
        if i = 0 then alternatingSixSchurPresentedA
        else alternatingSixSchurPresentedB)
    (FreeGroup.mk word)

/-- Evaluation of an append is multiplication. -/
theorem alternatingSixSchurWord_append
    (left right : AlternatingSixRewriteWord) :
    alternatingSixSchurWord (left ++ right) =
      alternatingSixSchurWord left *
        alternatingSixSchurWord right := by
  simp [alternatingSixSchurWord, ← FreeGroup.mul_mk]

@[simp]
theorem alternatingSixSchurWord_nil :
    alternatingSixSchurWord [] = 1 := by
  change
    FreeGroup.lift
        (fun i : Fin 2 =>
          if i = 0 then alternatingSixSchurPresentedA
          else alternatingSixSchurPresentedB)
        (FreeGroup.mk []) = 1
  rw [← FreeGroup.one_eq_mk]
  exact map_one _

/-- The four checker relator words evaluate to the four central
generators. -/
theorem alternatingSixSchurWord_relator
    (i : Fin 4) :
    alternatingSixSchurWord
        (alternatingSixRewriteRelatorWord i) =
      alternatingSixSchurPresentedK i := by
  have h := alternatingSixSchurPresented_baseRelator i
  fin_cases i
  · simpa [alternatingSixSchurWord,
      alternatingSixRewriteRelatorWord,
      alternatingSixSchurBaseRelator,
      alternatingSixSchurFreeA,
      alternatingSixSchurFreeB,
      alternatingSixSchurPresentedA,
      alternatingSixSchurPresentedB,
      alternatingSixSchurPresentedGenerator,
      PresentedGroup.of,
      alternatingSixSchurGenerator,
      pow_two] using h
  · simpa [alternatingSixSchurWord,
      alternatingSixRewriteRelatorWord,
      alternatingSixSchurBaseRelator,
      alternatingSixSchurFreeA,
      alternatingSixSchurFreeB,
      alternatingSixSchurPresentedA,
      alternatingSixSchurPresentedB,
      alternatingSixSchurPresentedGenerator,
      PresentedGroup.of,
      alternatingSixSchurGenerator,
      pow_succ, mul_assoc] using h
  · simpa [alternatingSixSchurWord,
      alternatingSixRewriteRelatorWord,
      alternatingSixSchurBaseRelator,
      alternatingSixSchurFreeA,
      alternatingSixSchurFreeB,
      alternatingSixSchurPresentedA,
      alternatingSixSchurPresentedB,
      alternatingSixSchurPresentedGenerator,
      PresentedGroup.of,
      alternatingSixSchurGenerator,
      pow_succ, mul_assoc] using h
  · simpa [alternatingSixSchurWord,
      alternatingSixRewriteRelatorWord,
      alternatingSixSchurBaseRelator,
      alternatingSixSchurFreeA,
      alternatingSixSchurFreeB,
      alternatingSixSchurPresentedA,
      alternatingSixSchurPresentedB,
      alternatingSixSchurPresentedGenerator,
      PresentedGroup.of,
      alternatingSixSchurGenerator,
      pow_succ, mul_assoc] using h

/-- Free cancellation remains sound in the Schur presentation. -/
theorem alternatingSixSchurWord_cancel
    (generator : Fin 2) (positive : Bool) :
    alternatingSixSchurWord
        [(generator, positive), (generator, !positive)] = 1 := by
  unfold alternatingSixSchurWord
  rw [show
    FreeGroup.mk
        [(generator, positive), (generator, !positive)] =
      1 by
        apply Quot.sound
        simpa using
          (@FreeGroup.Red.Step.not
            (Fin 2) [] [] generator positive)]
  exact map_one _

/-- The checker inverse word evaluates to the group inverse. -/
theorem alternatingSixSchurWord_inverse
    (word : AlternatingSixRewriteWord) :
    alternatingSixSchurWord
        (alternatingSixRewriteInverseWord word) =
      (alternatingSixSchurWord word)⁻¹ := by
  simp only [alternatingSixSchurWord,
    alternatingSixFreeGroupMk_inverseWord, map_inv]

/-- Reverse a weighted equality. -/
theorem alternatingSixSchurWeightedEq_symm
    {left right : AlternatingSixSchurPresentedGroup}
    {weight : Fin 4 → ℤ}
    (h :
      left =
        right * alternatingSixSchurWeight weight) :
    right =
      left *
        alternatingSixSchurWeight
          (alternatingSixRewriteNegWeight weight) := by
  rw [alternatingSixSchurWeight_neg]
  calc
    right =
        (right * alternatingSixSchurWeight weight) *
          (alternatingSixSchurWeight weight)⁻¹ := by
      group
    _ = left *
          (alternatingSixSchurWeight weight)⁻¹ := by
      rw [h]

/-- One contextual weighted replacement is sound once its bare pattern is
sound. -/
theorem alternatingSixSchurApplyAtom_sound_of_pattern
    (word next : AlternatingSixRewriteWord)
    (atom : AlternatingSixRewriteAtom)
    (hpattern :
      alternatingSixSchurWord
          (alternatingSixRewriteAtomPattern
            alternatingSixRewriteRules atom).1 =
        alternatingSixSchurWord
            (alternatingSixRewriteAtomPattern
              alternatingSixRewriteRules atom).2 *
          alternatingSixSchurWeight
            (alternatingSixRewriteAtomWeight
              alternatingSixRewriteRules atom))
    (happly :
      alternatingSixRewriteApplyAtom
          alternatingSixRewriteRules word atom =
        some next) :
    alternatingSixSchurWord word =
      alternatingSixSchurWord next *
        alternatingSixSchurWeight
          (alternatingSixRewriteAtomWeight
            alternatingSixRewriteRules atom) := by
  unfold alternatingSixRewriteApplyAtom at happly
  dsimp only at happly
  split at happly
  next hword =>
    simp only [Option.some.injEq] at happly
    subst next
    rw [hword]
    simp only [List.append_assoc,
      alternatingSixSchurWord_append]
    rw [hpattern]
    have hcentral :=
      Subgroup.mem_center_iff.mp
        (alternatingSixSchurWeight_mem_center
          (alternatingSixRewriteAtomWeight
            alternatingSixRewriteRules atom))
        (alternatingSixSchurWord atom.rightContext)
    calc
      alternatingSixSchurWord atom.leftContext *
            ((alternatingSixSchurWord
                  (alternatingSixRewriteAtomPattern
                    alternatingSixRewriteRules atom).2 *
                alternatingSixSchurWeight
                  (alternatingSixRewriteAtomWeight
                    alternatingSixRewriteRules atom)) *
              alternatingSixSchurWord atom.rightContext) =
          alternatingSixSchurWord atom.leftContext *
            (alternatingSixSchurWord
                (alternatingSixRewriteAtomPattern
                  alternatingSixRewriteRules atom).2 *
              (alternatingSixSchurWeight
                  (alternatingSixRewriteAtomWeight
                    alternatingSixRewriteRules atom) *
                alternatingSixSchurWord atom.rightContext)) := by
            group
      _ = alternatingSixSchurWord atom.leftContext *
            (alternatingSixSchurWord
                (alternatingSixRewriteAtomPattern
                  alternatingSixRewriteRules atom).2 *
              (alternatingSixSchurWord atom.rightContext *
                alternatingSixSchurWeight
                  (alternatingSixRewriteAtomWeight
                    alternatingSixRewriteRules atom))) := by
            rw [hcentral.symm]
      _ = (alternatingSixSchurWord atom.leftContext *
              (alternatingSixSchurWord
                  (alternatingSixRewriteAtomPattern
                    alternatingSixRewriteRules atom).2 *
                alternatingSixSchurWord atom.rightContext)) *
            alternatingSixSchurWeight
              (alternatingSixRewriteAtomWeight
                alternatingSixRewriteRules atom) := by
            group
  next hword =>
    contradiction

/-- A whole checked path has the sum of the weights of its atoms. -/
theorem alternatingSixSchurApplyProof_sound
    (word next : AlternatingSixRewriteWord)
    (proof : List AlternatingSixRewriteAtom)
    (hatom :
      ∀ atom ∈ proof,
        alternatingSixSchurWord
            (alternatingSixRewriteAtomPattern
              alternatingSixRewriteRules atom).1 =
          alternatingSixSchurWord
              (alternatingSixRewriteAtomPattern
                alternatingSixRewriteRules atom).2 *
            alternatingSixSchurWeight
              (alternatingSixRewriteAtomWeight
                alternatingSixRewriteRules atom))
    (happly :
      alternatingSixRewriteApplyProof
          alternatingSixRewriteRules word proof =
        some next) :
    alternatingSixSchurWord word =
      alternatingSixSchurWord next *
        alternatingSixSchurWeight
          (alternatingSixRewriteProofWeight
            alternatingSixRewriteRules proof) := by
  induction proof generalizing word with
  | nil =>
      simp only [alternatingSixRewriteApplyProof,
        Option.some.injEq] at happly
      subst next
      simp [alternatingSixRewriteProofWeight]
  | cons atom proof ih =>
      simp only [alternatingSixRewriteApplyProof] at happly
      cases hstep :
          alternatingSixRewriteApplyAtom
            alternatingSixRewriteRules word atom with
      | none =>
          simp [hstep] at happly
      | some middle =>
          rw [hstep] at happly
          have hfirst :=
            alternatingSixSchurApplyAtom_sound_of_pattern
              word middle atom
              (hatom atom (by simp)) hstep
          have hrest :=
            ih middle
              (fun later hlater =>
                hatom later (by simp [hlater]))
              happly
          rw [hfirst, hrest]
          rw [alternatingSixRewriteProofWeight,
            alternatingSixSchurWeight_add]
          have hcentral :=
            Subgroup.mem_center_iff.mp
              (alternatingSixSchurWeight_mem_center
                (alternatingSixRewriteAtomWeight
                  alternatingSixRewriteRules atom))
              (alternatingSixSchurWeight
                (alternatingSixRewriteProofWeight
                  alternatingSixRewriteRules proof))
          rw [mul_assoc, hcentral, ← mul_assoc]

/-- Soundness of one atom whose rule citations are already known
sound. -/
theorem alternatingSixSchurAtomPattern_sound
    (bound : Nat)
    (hbound : bound ≤ 188)
    (hrules :
      ∀ j : Fin 188, j.val < bound →
        alternatingSixSchurWord
            (alternatingSixRewriteRules j).lhs =
          alternatingSixSchurWord
              (alternatingSixRewriteRules j).rhs *
            alternatingSixSchurWeight
              (alternatingSixRewriteRules j).weight)
    (atom : AlternatingSixRewriteAtom)
    (hearlier :
      atom.kind = .rule → atom.index < bound) :
    alternatingSixSchurWord
        (alternatingSixRewriteAtomPattern
          alternatingSixRewriteRules atom).1 =
      alternatingSixSchurWord
          (alternatingSixRewriteAtomPattern
            alternatingSixRewriteRules atom).2 *
        alternatingSixSchurWeight
          (alternatingSixRewriteAtomWeight
            alternatingSixRewriteRules atom) := by
  cases hkind : atom.kind <;>
    cases hforward : atom.forward
  case rule.false =>
    have hindex := hearlier hkind
    have hindexBound :
        (Fin.ofNat 188 atom.index).val < bound := by
      simpa [Fin.ofNat,
        Nat.mod_eq_of_lt (hindex.trans_le hbound)] using hindex
    simpa only [alternatingSixRewriteAtomPattern,
      alternatingSixRewriteAtomWeight, hkind, hforward, Bool.false_eq_true,
      ↓reduceIte] using
        alternatingSixSchurWeightedEq_symm
          (hrules (Fin.ofNat 188 atom.index)
            hindexBound)
  case rule.true =>
    have hindex := hearlier hkind
    have hindexBound :
        (Fin.ofNat 188 atom.index).val < bound := by
      simpa [Fin.ofNat,
        Nat.mod_eq_of_lt (hindex.trans_le hbound)] using hindex
    simpa only [alternatingSixRewriteAtomPattern,
      alternatingSixRewriteAtomWeight, hkind, hforward, Bool.false_eq_true,
      ↓reduceIte] using
        hrules (Fin.ofNat 188 atom.index)
          hindexBound
  case cancel.false =>
    simp only [alternatingSixRewriteAtomPattern,
      alternatingSixRewriteAtomWeight, hkind, hforward, Bool.false_eq_true,
      ↓reduceIte]
    apply alternatingSixSchurWeightedEq_symm
    rw [alternatingSixSchurWord_cancel,
      alternatingSixSchurWord_nil,
      alternatingSixSchurWeight_zero, mul_one]
  case cancel.true =>
    simp only [alternatingSixRewriteAtomPattern,
      alternatingSixRewriteAtomWeight, hkind, hforward, Bool.false_eq_true,
      ↓reduceIte]
    rw [alternatingSixSchurWord_cancel,
      alternatingSixSchurWord_nil,
      alternatingSixSchurWeight_zero, mul_one]
  case relator.false =>
    simp only [alternatingSixRewriteAtomPattern,
      alternatingSixRewriteAtomWeight, hkind, hforward, Bool.false_eq_true,
      ↓reduceIte]
    apply alternatingSixSchurWeightedEq_symm
    rw [alternatingSixSchurWord_nil, one_mul,
      alternatingSixSchurWeight_basis]
    exact
      alternatingSixSchurWord_relator
        (Fin.ofNat 4 atom.index)
  case relator.true =>
    simp only [alternatingSixRewriteAtomPattern,
      alternatingSixRewriteAtomWeight, hkind, hforward, Bool.false_eq_true,
      ↓reduceIte]
    rw [alternatingSixSchurWord_nil, one_mul,
      alternatingSixSchurWeight_basis]
    exact
      alternatingSixSchurWord_relator
        (Fin.ofNat 4 atom.index)
  case inverseRelator.false =>
    simp only [alternatingSixRewriteAtomPattern,
      alternatingSixRewriteAtomWeight, hkind, hforward, Bool.false_eq_true,
      ↓reduceIte]
    apply alternatingSixSchurWeightedEq_symm
    rw [alternatingSixSchurWord_inverse,
      alternatingSixSchurWord_relator,
      alternatingSixSchurWord_nil, one_mul]
    have hbasis :=
      alternatingSixSchurWeight_basis
        (Fin.ofNat 4 atom.index)
    rw [show
      (fun i =>
        if i = Fin.ofNat 4 atom.index then (-1 : ℤ) else 0) =
        alternatingSixRewriteNegWeight
          (fun i =>
            if i = Fin.ofNat 4 atom.index then 1 else 0) by
          funext i
          change
            (if i = Fin.ofNat 4 atom.index then (-1 : ℤ) else 0) =
              -(if i = Fin.ofNat 4 atom.index then 1 else 0)
          split <;> rfl,
      alternatingSixSchurWeight_neg, hbasis]
  case inverseRelator.true =>
    simp only [alternatingSixRewriteAtomPattern,
      alternatingSixRewriteAtomWeight, hkind, hforward, Bool.false_eq_true,
      ↓reduceIte]
    rw [alternatingSixSchurWord_inverse,
      alternatingSixSchurWord_relator,
      alternatingSixSchurWord_nil, one_mul]
    have hbasis :=
      alternatingSixSchurWeight_basis
        (Fin.ofNat 4 atom.index)
    rw [show
      (fun i =>
        if i = Fin.ofNat 4 atom.index then (-1 : ℤ) else 0) =
        alternatingSixRewriteNegWeight
          (fun i =>
            if i = Fin.ofNat 4 atom.index then 1 else 0) by
          funext i
          change
            (if i = Fin.ofNat 4 atom.index then (-1 : ℤ) else 0) =
              -(if i = Fin.ofNat 4 atom.index then 1 else 0)
          split <;> rfl,
      alternatingSixSchurWeight_neg, hbasis]

/-- Every generated rule is sound with its stored central weight. -/
theorem alternatingSixSchurRewriteRule_sound
    (ruleIndex : Fin 188) :
    alternatingSixSchurWord
        (alternatingSixRewriteRules ruleIndex).lhs =
      alternatingSixSchurWord
          (alternatingSixRewriteRules ruleIndex).rhs *
        alternatingSixSchurWeight
          (alternatingSixRewriteRules ruleIndex).weight := by
  rcases ruleIndex with ⟨n, hn⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hvalid :=
        alternatingSixRewriteRules_valid
          (⟨n, hn⟩ : Fin 188)
      simp only [AlternatingSixRewriteRule.Valid] at hvalid
      obtain ⟨hpathBool, hweightBool⟩ :=
        Bool.and_eq_true_iff.mp hvalid
      obtain ⟨happlyBool, hearlierBool⟩ :=
        Bool.and_eq_true_iff.mp hpathBool
      have happly :=
        of_decide_eq_true happlyBool
      have hweight :=
        of_decide_eq_true hweightBool
      have hsound :=
        alternatingSixSchurApplyProof_sound
          (alternatingSixRewriteRules
            (⟨n, hn⟩ : Fin 188)).lhs
          (alternatingSixRewriteRules
            (⟨n, hn⟩ : Fin 188)).rhs
          (alternatingSixRewriteRules
            (⟨n, hn⟩ : Fin 188)).proof
          (fun atom hatom => by
            apply alternatingSixSchurAtomPattern_sound n
              (Nat.le_of_lt hn)
            · intro j hj
              exact ih j.val hj j.isLt
            · intro hkind
              have hearlierEntry :=
                List.all_eq_true.mp hearlierBool atom hatom
              rcases Bool.or_eq_true_iff.mp hearlierEntry with
                hne | hlt
              · exact False.elim
                  ((of_decide_eq_true hne) hkind)
              · exact of_decide_eq_true hlt)
          happly
      rw [hweight] at hsound
      exact hsound

/-- Every transition is sound with the weight computed from its trace. -/
theorem alternatingSixSchurRewriteTransition_sound
    (wordIndex : Fin 360) (letter : Fin 4) :
    alternatingSixSchurWord
          (alternatingSixRewriteNormalWords wordIndex ++
            alternatingSixRewriteLetterWord letter) =
      alternatingSixSchurWord
          (alternatingSixRewriteNormalWords
            (alternatingSixRewriteTransitions
              wordIndex letter).target) *
        alternatingSixSchurWeight
          (alternatingSixRewriteProofWeight
            alternatingSixRewriteRules
            (alternatingSixRewriteTransitions
              wordIndex letter).proof) := by
  apply alternatingSixSchurApplyProof_sound
  · intro atom _
    cases hkind : atom.kind <;>
      cases hforward : atom.forward
    all_goals
      simp only [alternatingSixRewriteAtomPattern,
        alternatingSixRewriteAtomWeight, hkind, hforward, Bool.false_eq_true,
        ↓reduceIte]
    · exact
        alternatingSixSchurWeightedEq_symm
          (alternatingSixSchurRewriteRule_sound
            (Fin.ofNat 188 atom.index))
    · exact
        alternatingSixSchurRewriteRule_sound
          (Fin.ofNat 188 atom.index)
    · apply alternatingSixSchurWeightedEq_symm
      rw [alternatingSixSchurWord_cancel,
        alternatingSixSchurWord_nil,
        alternatingSixSchurWeight_zero, mul_one]
    · rw [alternatingSixSchurWord_cancel,
        alternatingSixSchurWord_nil,
        alternatingSixSchurWeight_zero, mul_one]
    · apply alternatingSixSchurWeightedEq_symm
      rw [alternatingSixSchurWord_nil, one_mul,
        alternatingSixSchurWeight_basis]
      exact alternatingSixSchurWord_relator _
    · rw [alternatingSixSchurWord_nil, one_mul,
        alternatingSixSchurWeight_basis]
      exact alternatingSixSchurWord_relator _
    · apply alternatingSixSchurWeightedEq_symm
      rw [alternatingSixSchurWord_inverse,
        alternatingSixSchurWord_relator,
        alternatingSixSchurWord_nil, one_mul]
      rw [show
        (fun i =>
          if i = Fin.ofNat 4 atom.index then (-1 : ℤ) else 0) =
          alternatingSixRewriteNegWeight
            (fun i =>
              if i = Fin.ofNat 4 atom.index then 1 else 0) by
            funext i
            change
              (if i = Fin.ofNat 4 atom.index then (-1 : ℤ) else 0) =
                -(if i = Fin.ofNat 4 atom.index then 1 else 0)
            split <;> rfl,
        alternatingSixSchurWeight_neg,
        alternatingSixSchurWeight_basis]
    · rw [alternatingSixSchurWord_inverse,
        alternatingSixSchurWord_relator,
        alternatingSixSchurWord_nil, one_mul]
      rw [show
        (fun i =>
          if i = Fin.ofNat 4 atom.index then (-1 : ℤ) else 0) =
          alternatingSixRewriteNegWeight
            (fun i =>
              if i = Fin.ofNat 4 atom.index then 1 else 0) by
            funext i
            change
              (if i = Fin.ofNat 4 atom.index then (-1 : ℤ) else 0) =
                -(if i = Fin.ofNat 4 atom.index then 1 else 0)
            split <;> rfl,
        alternatingSixSchurWeight_neg,
        alternatingSixSchurWeight_basis]
  · have hvalid :=
      alternatingSixRewriteTransitions_valid wordIndex
    simp only [AlternatingSixRewriteTransition.Valid] at hvalid
    apply of_decide_eq_true
    apply List.all_eq_true.mp hvalid
    exact List.mem_ofFn.mpr ⟨letter, rfl⟩

end GroupTheory
end McKayConjecture
