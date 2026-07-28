/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixGeneration
import McKayConjecture.GroupTheory.AlternatingSixRewriteRuleChecks
import McKayConjecture.GroupTheory.AlternatingSixRewriteTransitionChecks

/-!
# A certified normal form for the ATLAS presentation of `A₆`

The generated certificate consists of 188 acyclic rewrite rules and a
closed table of 360 shortlex normal words.  This file proves the semantic
soundness of the executable checker and deduces that

`⟨a,b | a², b⁴, (ab)⁵, (ab²)⁵⟩`

is exactly `A₆`.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- Interpret a signed word in the four-relator presented group. -/
def alternatingSixPresentedWord
    (word : AlternatingSixRewriteWord) :
    AlternatingSixPresentedGroup :=
  PresentedGroup.mk
    alternatingSixPresentationRelators
    (FreeGroup.mk word)

@[simp]
theorem alternatingSixPresentedWord_nil :
    alternatingSixPresentedWord [] = 1 := by
  change
    PresentedGroup.mk
        alternatingSixPresentationRelators
        (FreeGroup.mk []) = 1
  rw [← FreeGroup.one_eq_mk]
  exact map_one _

/-- Interpreting an append is multiplication in the presented group. -/
theorem alternatingSixPresentedWord_append
    (left right : AlternatingSixRewriteWord) :
    alternatingSixPresentedWord (left ++ right) =
      alternatingSixPresentedWord left *
        alternatingSixPresentedWord right := by
  simp [alternatingSixPresentedWord, ← FreeGroup.mul_mk]

/-- A positive free word evaluates to the product of its generators. -/
theorem alternatingSixFreeGroupMk_positiveWord
    (word : List (Fin 2)) :
    FreeGroup.mk (word.map fun i => (i, true)) =
      (word.map FreeGroup.of).prod := by
  induction word with
  | nil =>
      rfl
  | cons i word ih =>
      simp only [List.map_cons, List.prod_cons]
      change
        FreeGroup.mk
            ([(i, true)] ++
              word.map fun j => (j, true)) =
          FreeGroup.of i *
            (word.map FreeGroup.of).prod
      rw [← FreeGroup.mul_mk, ih]
      rfl

/-- Each of the four checker relators is one of the presentation
relators. -/
theorem alternatingSixPresentedWord_relator
    (i : Fin 4) :
    alternatingSixPresentedWord
        (alternatingSixRewriteRelatorWord i) = 1 := by
  apply PresentedGroup.mk_eq_one_iff.mpr
  apply Subgroup.subset_normalClosure
  fin_cases i
  · left
    change
      FreeGroup.mk [(0, true), (0, true)] =
        alternatingSixPresentationRelatorA
    rw [show
      ([(0, true), (0, true)] :
        AlternatingSixRewriteWord) =
        [0, 0].map fun j : Fin 2 => (j, true) by rfl,
      alternatingSixFreeGroupMk_positiveWord]
    simp [alternatingSixPresentationRelatorA,
      alternatingSixPresentationGenerator, pow_two]
  · right; left
    change
      FreeGroup.mk [(1, true), (1, true), (1, true), (1, true)] =
        alternatingSixPresentationRelatorB
    rw [show
      ([(1, true), (1, true), (1, true), (1, true)] :
        AlternatingSixRewriteWord) =
        [1, 1, 1, 1].map fun j : Fin 2 => (j, true) by rfl,
      alternatingSixFreeGroupMk_positiveWord]
    simp [alternatingSixPresentationRelatorB,
      alternatingSixPresentationGenerator, pow_succ, mul_assoc]
  · right; right; left
    change
      FreeGroup.mk
        [(0, true), (1, true), (0, true), (1, true), (0, true),
          (1, true), (0, true), (1, true), (0, true), (1, true)] =
        alternatingSixPresentationRelatorAB
    rw [show
      ([(0, true), (1, true), (0, true), (1, true), (0, true),
          (1, true), (0, true), (1, true), (0, true), (1, true)] :
          AlternatingSixRewriteWord) =
        ([0, 1, 0, 1, 0, 1, 0, 1, 0, 1] :
          List (Fin 2)).map
            fun j => (j, true) by rfl,
      alternatingSixFreeGroupMk_positiveWord]
    simp [alternatingSixPresentationRelatorAB,
      alternatingSixPresentationGenerator, pow_succ, mul_assoc]
  · right; right; right
    change
      FreeGroup.mk
        [(0, true), (1, true), (1, true), (0, true), (1, true),
          (1, true), (0, true), (1, true), (1, true), (0, true),
          (1, true), (1, true), (0, true), (1, true), (1, true)] =
        alternatingSixPresentationRelatorABSq
    rw [show
      ([(0, true), (1, true), (1, true), (0, true), (1, true),
          (1, true), (0, true), (1, true), (1, true), (0, true),
          (1, true), (1, true), (0, true), (1, true), (1, true)] :
          AlternatingSixRewriteWord) =
        ([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] :
          List (Fin 2)).map
            fun j => (j, true) by rfl,
      alternatingSixFreeGroupMk_positiveWord]
    simp [alternatingSixPresentationRelatorABSq,
      alternatingSixPresentationGenerator, pow_succ, mul_assoc]

/-- A signed generator followed by its inverse represents the identity. -/
theorem alternatingSixPresentedWord_cancel
    (generator : Fin 2) (positive : Bool) :
    alternatingSixPresentedWord
        [(generator, positive), (generator, !positive)] =
      alternatingSixPresentedWord [] := by
  apply congrArg
    (PresentedGroup.mk alternatingSixPresentationRelators)
  apply Quot.sound
  simpa using
    (@FreeGroup.Red.Step.not
      (Fin 2) [] [] generator positive)

/-- The checker inverse of a word evaluates to the group inverse. -/
theorem alternatingSixFreeGroupMk_inverseWord
    (word : AlternatingSixRewriteWord) :
    FreeGroup.mk
        (alternatingSixRewriteInverseWord word) =
      (FreeGroup.mk word)⁻¹ := by
  simpa [alternatingSixRewriteInverseWord,
    FreeGroup.invRev] using
      (FreeGroup.inv_mk word).symm

/-- An inverse defining relator also evaluates to the identity. -/
theorem alternatingSixPresentedWord_inverseRelator
    (i : Fin 4) :
    alternatingSixPresentedWord
        (alternatingSixRewriteInverseWord
          (alternatingSixRewriteRelatorWord i)) = 1 := by
  rw [alternatingSixPresentedWord,
    alternatingSixFreeGroupMk_inverseWord, map_inv]
  simpa [alternatingSixPresentedWord] using
    congrArg Inv.inv (alternatingSixPresentedWord_relator i)

/-- One contextual replacement is sound once its uncontextualized pattern
is sound. -/
theorem alternatingSixRewriteApplyAtom_sound_of_pattern
    (word next : AlternatingSixRewriteWord)
    (atom : AlternatingSixRewriteAtom)
    (hpattern :
      alternatingSixPresentedWord
          (alternatingSixRewriteAtomPattern
            alternatingSixRewriteRules atom).1 =
        alternatingSixPresentedWord
          (alternatingSixRewriteAtomPattern
            alternatingSixRewriteRules atom).2)
    (happly :
      alternatingSixRewriteApplyAtom
          alternatingSixRewriteRules word atom =
        some next) :
    alternatingSixPresentedWord word =
      alternatingSixPresentedWord next := by
  unfold alternatingSixRewriteApplyAtom at happly
  dsimp only at happly
  split at happly
  next hword =>
    simp only [Option.some.injEq] at happly
    subst next
    rw [hword]
    simp only [List.append_assoc,
      alternatingSixPresentedWord_append]
    rw [hpattern]
  next hword =>
    contradiction

/-- A whole checked path is sound if every cited atom is sound. -/
theorem alternatingSixRewriteApplyProof_sound
    (word next : AlternatingSixRewriteWord)
    (proof : List AlternatingSixRewriteAtom)
    (hatom :
      ∀ atom ∈ proof,
        alternatingSixPresentedWord
            (alternatingSixRewriteAtomPattern
              alternatingSixRewriteRules atom).1 =
          alternatingSixPresentedWord
            (alternatingSixRewriteAtomPattern
              alternatingSixRewriteRules atom).2)
    (happly :
      alternatingSixRewriteApplyProof
          alternatingSixRewriteRules word proof =
        some next) :
    alternatingSixPresentedWord word =
      alternatingSixPresentedWord next := by
  induction proof generalizing word with
  | nil =>
      simp only [alternatingSixRewriteApplyProof,
        Option.some.injEq] at happly
      subst next
      rfl
  | cons atom proof ih =>
      simp only [alternatingSixRewriteApplyProof] at happly
      cases hstep :
          alternatingSixRewriteApplyAtom
            alternatingSixRewriteRules word atom with
      | none =>
          simp [hstep] at happly
      | some middle =>
          rw [hstep] at happly
          exact
            (alternatingSixRewriteApplyAtom_sound_of_pattern
                word middle atom
                (hatom atom (by simp)) hstep).trans
              (ih middle
                (fun later hlater =>
                  hatom later (by simp [hlater]))
                happly)

/-- Every acyclic generated rewrite rule is an equality in the presented
group. -/
theorem alternatingSixRewriteRule_presented_eq
    (ruleIndex : Fin 188) :
    alternatingSixPresentedWord
        (alternatingSixRewriteRules ruleIndex).lhs =
      alternatingSixPresentedWord
        (alternatingSixRewriteRules ruleIndex).rhs := by
  rcases ruleIndex with ⟨n, hn⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hvalid :=
        alternatingSixRewriteRules_valid
          (⟨n, hn⟩ : Fin 188)
      simp only [AlternatingSixRewriteRule.Valid] at hvalid
      obtain ⟨hpathBool, _hweightBool⟩ :=
        Bool.and_eq_true_iff.mp hvalid
      obtain ⟨happlyBool, hearlierBool⟩ :=
        Bool.and_eq_true_iff.mp hpathBool
      have happly :
          alternatingSixRewriteApplyProof
              alternatingSixRewriteRules
              (alternatingSixRewriteRules
                (⟨n, hn⟩ : Fin 188)).lhs
              (alternatingSixRewriteRules
                (⟨n, hn⟩ : Fin 188)).proof =
            some
              (alternatingSixRewriteRules
                (⟨n, hn⟩ : Fin 188)).rhs :=
        of_decide_eq_true happlyBool
      apply alternatingSixRewriteApplyProof_sound _ _ _ _ happly
      intro atom hatom
      have hearlierEntry :=
        List.all_eq_true.mp hearlierBool atom hatom
      cases hkind : atom.kind <;>
        cases hforward : atom.forward
      all_goals
        simp only [alternatingSixRewriteAtomPattern,
          hkind, hforward, Bool.false_eq_true,
          Bool.true_eq_false, ↓reduceIte]
      case rule.false =>
        have hatomIndex : atom.index < n := by
          rcases Bool.or_eq_true_iff.mp hearlierEntry with
            hne | hlt
          · exact False.elim
              ((of_decide_eq_true hne) hkind)
          · exact of_decide_eq_true hlt
        have hindex :
            (Fin.ofNat 188 atom.index).val =
              atom.index := by
          simp [Fin.ofNat,
            Nat.mod_eq_of_lt
              (hatomIndex.trans hn)]
        have hfin :
            Fin.ofNat 188 atom.index =
              (⟨atom.index,
                hatomIndex.trans hn⟩ : Fin 188) :=
          Fin.ext hindex
        rw [hfin]
        exact
          (ih atom.index hatomIndex
            (hatomIndex.trans hn)).symm
      case rule.true =>
        have hatomIndex : atom.index < n := by
          rcases Bool.or_eq_true_iff.mp hearlierEntry with
            hne | hlt
          · exact False.elim
              ((of_decide_eq_true hne) hkind)
          · exact of_decide_eq_true hlt
        have hindex :
            (Fin.ofNat 188 atom.index).val =
              atom.index := by
          simp [Fin.ofNat,
            Nat.mod_eq_of_lt
              (hatomIndex.trans hn)]
        have hfin :
            Fin.ofNat 188 atom.index =
              (⟨atom.index,
                hatomIndex.trans hn⟩ : Fin 188) :=
          Fin.ext hindex
        rw [hfin]
        exact
          ih atom.index hatomIndex
            (hatomIndex.trans hn)
      case cancel.false =>
        exact
          (alternatingSixPresentedWord_cancel
            (alternatingSixRewriteIndexedLetter atom.index).1
            (alternatingSixRewriteIndexedLetter atom.index).2).symm
      case cancel.true =>
        exact
          alternatingSixPresentedWord_cancel
            (alternatingSixRewriteIndexedLetter atom.index).1
            (alternatingSixRewriteIndexedLetter atom.index).2
      case relator.false =>
        simpa only [alternatingSixPresentedWord_nil] using
          (alternatingSixPresentedWord_relator
            (Fin.ofNat 4 atom.index)).symm
      case relator.true =>
        simpa only [alternatingSixPresentedWord_nil] using
          alternatingSixPresentedWord_relator
            (Fin.ofNat 4 atom.index)
      case inverseRelator.false =>
        simpa only [alternatingSixPresentedWord_nil] using
          (alternatingSixPresentedWord_inverseRelator
            (Fin.ofNat 4 atom.index)).symm
      case inverseRelator.true =>
        simpa only [alternatingSixPresentedWord_nil] using
          alternatingSixPresentedWord_inverseRelator
            (Fin.ofNat 4 atom.index)

/-- Every checked transition is an equality in the presented group. -/
theorem alternatingSixRewriteTransition_presented_eq
    (wordIndex : Fin 360) (letter : Fin 4) :
    alternatingSixPresentedWord
          (alternatingSixRewriteNormalWords wordIndex ++
            alternatingSixRewriteLetterWord letter) =
      alternatingSixPresentedWord
        (alternatingSixRewriteNormalWords
          (alternatingSixRewriteTransitions
            wordIndex letter).target) := by
  apply alternatingSixRewriteApplyProof_sound
  · intro atom hatom
    cases hkind : atom.kind <;>
      cases hforward : atom.forward
    all_goals
      simp only [alternatingSixRewriteAtomPattern,
        hkind, hforward, Bool.false_eq_true,
        Bool.true_eq_false, ↓reduceIte]
    · exact
        (alternatingSixRewriteRule_presented_eq
          (Fin.ofNat 188 atom.index)).symm
    · exact
        alternatingSixRewriteRule_presented_eq
          (Fin.ofNat 188 atom.index)
    · exact
        (alternatingSixPresentedWord_cancel
          (alternatingSixRewriteIndexedLetter atom.index).1
          (alternatingSixRewriteIndexedLetter atom.index).2).symm
    · exact
        alternatingSixPresentedWord_cancel
          (alternatingSixRewriteIndexedLetter atom.index).1
          (alternatingSixRewriteIndexedLetter atom.index).2
    · simpa only [alternatingSixPresentedWord_nil] using
        (alternatingSixPresentedWord_relator
          (Fin.ofNat 4 atom.index)).symm
    · simpa only [alternatingSixPresentedWord_nil] using
        alternatingSixPresentedWord_relator
          (Fin.ofNat 4 atom.index)
    · simpa only [alternatingSixPresentedWord_nil] using
        (alternatingSixPresentedWord_inverseRelator
          (Fin.ofNat 4 atom.index)).symm
    · simpa only [alternatingSixPresentedWord_nil] using
        alternatingSixPresentedWord_inverseRelator
          (Fin.ofNat 4 atom.index)
  · have hvalid :=
      alternatingSixRewriteTransitions_valid wordIndex
    simp only [AlternatingSixRewriteTransition.Valid] at hvalid
    have hall := List.all_eq_true.mp hvalid
    apply of_decide_eq_true
    apply hall
    exact List.mem_ofFn.mpr ⟨letter, rfl⟩

/-- Convert a signed free-group letter to its transition-table column. -/
def alternatingSixRewriteTransitionLetter
    (letter : AlternatingSixRewriteLetter) :
    Fin 4 :=
  if letter.1 = 0 then
    if letter.2 then 0 else 1
  else
    if letter.2 then 2 else 3

/-- The selected transition column is exactly the supplied signed
letter. -/
theorem alternatingSixRewriteLetterWord_transitionLetter
    (letter : AlternatingSixRewriteLetter) :
    alternatingSixRewriteLetterWord
        (alternatingSixRewriteTransitionLetter letter) =
      [letter] := by
  rcases letter with ⟨generator, positive⟩
  fin_cases generator <;>
    cases positive <;>
    rfl

/-- The element represented by one certified normal word. -/
def alternatingSixRewriteNormalElement
    (i : Fin 360) :
    AlternatingSixPresentedGroup :=
  alternatingSixPresentedWord
    (alternatingSixRewriteNormalWords i)

/-- Right multiplication by a signed generator remains in the table. -/
theorem alternatingSixRewriteNormalElement_mul_letter
    (i : Fin 360) (letter : Fin 4) :
    alternatingSixRewriteNormalElement i *
        alternatingSixPresentedWord
          (alternatingSixRewriteLetterWord letter) =
      alternatingSixRewriteNormalElement
        (alternatingSixRewriteTransitions i letter).target := by
  simpa [alternatingSixRewriteNormalElement,
    alternatingSixPresentedWord_append] using
      alternatingSixRewriteTransition_presented_eq i letter

/-- Every element of the presentation has a certified normal form. -/
theorem alternatingSixPresented_exists_rewriteNormalForm
    (g : AlternatingSixPresentedGroup) :
    ∃ i : Fin 360,
      g = alternatingSixRewriteNormalElement i := by
  apply PresentedGroup.induction_on g
  intro z
  refine Quot.inductionOn z ?_
  intro word
  induction word using List.reverseRecOn with
  | nil =>
      refine ⟨0, ?_⟩
      rfl
  | append_singleton word letter ih =>
      rcases ih with ⟨i, hi⟩
      rw [FreeGroup.quot_mk_eq_mk] at hi
      let tableLetter :=
        alternatingSixRewriteTransitionLetter letter
      refine
        ⟨(alternatingSixRewriteTransitions
            i tableLetter).target, ?_⟩
      change
        PresentedGroup.mk
            alternatingSixPresentationRelators
            (FreeGroup.mk word *
              FreeGroup.mk [letter]) =
          alternatingSixRewriteNormalElement
            (alternatingSixRewriteTransitions
              i tableLetter).target
      rw [map_mul, hi]
      have hletter :
          alternatingSixPresentedWord
              (alternatingSixRewriteLetterWord tableLetter) =
            PresentedGroup.mk
              alternatingSixPresentationRelators
              (FreeGroup.mk [letter]) := by
        rw [alternatingSixRewriteLetterWord_transitionLetter]
        rfl
      rw [← hletter]
      exact
        alternatingSixRewriteNormalElement_mul_letter
          i tableLetter

/-- The 360 certified words map onto the presented group. -/
theorem alternatingSixRewriteNormalElement_surjective :
    Function.Surjective
      alternatingSixRewriteNormalElement := by
  intro g
  obtain ⟨i, hi⟩ :=
    alternatingSixPresented_exists_rewriteNormalForm g
  exact ⟨i, hi.symm⟩

noncomputable instance alternatingSixPresentedGroup_finite :
    Finite AlternatingSixPresentedGroup :=
  Finite.of_surjective
    alternatingSixRewriteNormalElement
    alternatingSixRewriteNormalElement_surjective

/-- The ATLAS presentation has order at most 360. -/
theorem natCard_alternatingSixPresentedGroup_le :
    Nat.card AlternatingSixPresentedGroup ≤ 360 := by
  simpa using
    Nat.card_le_card_of_surjective
      alternatingSixRewriteNormalElement
      alternatingSixRewriteNormalElement_surjective

/-- The standard surjection from the presentation to `A₆` is bijective. -/
theorem alternatingSixPresentationToAlternatingSix_bijective :
    Function.Bijective
      alternatingSixPresentationToAlternatingSix :=
  Function.Surjective.bijective_of_nat_card_le
    alternatingSixPresentationToAlternatingSix_surjective (by
      rw [natCard_alternatingSix]
      exact natCard_alternatingSixPresentedGroup_le)

/-- The four-relator ATLAS presentation is exactly `A₆`. -/
def alternatingSixPresentedGroupEquivAlternatingSix :
    AlternatingSixPresentedGroup ≃* AlternatingSix :=
  MulEquiv.ofBijective
    alternatingSixPresentationToAlternatingSix
    alternatingSixPresentationToAlternatingSix_bijective

end GroupTheory
end McKayConjecture
