/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.AlternatingSixThreeNormalizerDegreeFourRows
import McKayConjecture.Character.AlternatingSixThreeNormalizerDegreeThreeExtensions
import McKayConjecture.Character.FiniteCharacterTableCertificate
import McKayConjecture.Character.AlternatingSixThreeNormalizerOrdinaryCharacterCount

/-!
# Complete character table of the coordinate three-normalizer

The table consists of eight linear rows, sixteen degree-three rows, and
four degree-four rows.  The three families are disjoint by degree; the
within-family separation was proved from quotient parameters, central
values, and the two degree-four diagnostic values.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace AlternatingSixThreeNormalizer

open GroupTheory

/-- The eight linear characters of the coordinate normalizer. -/
def coordinateLinearCharacter (j : Fin 8) :
    IrreducibleCharacter AlternatingSixThreeNormalizerCoordinates :=
  IrreducibleCharacter.linear (coordinateQuotientLinearHom j)

@[simp]
theorem coordinateLinearCharacter_degree (j : Fin 8) :
    (coordinateLinearCharacter j).degree = 1 :=
  IrreducibleCharacter.linear_degree
    (coordinateQuotientLinearHom j)

theorem coordinateQuotientLinearHom_injective :
    Function.Injective coordinateQuotientLinearHom := by
  intro i j hij
  apply CyclicEight.linearHom_injective
  apply MonoidHom.ext
  intro c
  have h :=
    DFunLike.congr_fun hij
      (SemidirectProduct.inr c :
        AlternatingSixThreeNormalizerCoordinates)
  simpa [coordinateQuotientLinearHom] using h

theorem coordinateLinearCharacter_injective :
    Function.Injective coordinateLinearCharacter :=
  IrreducibleCharacter.linear_injective.comp
    coordinateQuotientLinearHom_injective

/-- Row indices, ordered by degrees `1`, `3`, and `4`. -/
abbrev CharacterRow :=
  Fin 8 ⊕ ((Fin 2 × Fin 8) ⊕ (Fin 2 × Fin 2))

/-- The irreducible character represented by a table row. -/
def rowCharacter (r : CharacterRow) :
    IrreducibleCharacter AlternatingSixThreeNormalizerCoordinates :=
  match r with
  | Sum.inl j => coordinateLinearCharacter j
  | Sum.inr (Sum.inl r) => degreeThreeCharacter r.1 r.2
  | Sum.inr (Sum.inr r) => degreeFourCharacter r.1 r.2

@[simp]
theorem rowCharacter_linear (j : Fin 8) :
    rowCharacter (Sum.inl j) = coordinateLinearCharacter j :=
  rfl

@[simp]
theorem rowCharacter_degreeThree (r : Fin 2 × Fin 8) :
    rowCharacter (Sum.inr (Sum.inl r)) =
      degreeThreeCharacter r.1 r.2 :=
  rfl

@[simp]
theorem rowCharacter_degreeFour (r : Fin 2 × Fin 2) :
    rowCharacter (Sum.inr (Sum.inr r)) =
      degreeFourCharacter r.1 r.2 :=
  rfl

@[simp]
theorem rowCharacter_degree (r : CharacterRow) :
    (rowCharacter r).degree =
      match r with
      | Sum.inl _ => 1
      | Sum.inr (Sum.inl _) => 3
      | Sum.inr (Sum.inr _) => 4 := by
  rcases r with j | r
  · exact coordinateLinearCharacter_degree j
  · rcases r with r | r
    · exact degreeThreeCharacter_degree r.1 r.2
    · exact degreeFourCharacter_degree r.1 r.2

/-- All twenty-eight displayed irreducible characters are distinct. -/
theorem rowCharacter_injective :
    Function.Injective rowCharacter := by
  intro r s hrs
  rcases r with j | r
  · rcases s with k | s
    · exact congrArg Sum.inl
        (coordinateLinearCharacter_injective hrs)
    · rcases s with s | s
      · have hdegree := congrArg IrreducibleCharacter.degree hrs
        simp at hdegree
      · have hdegree := congrArg IrreducibleCharacter.degree hrs
        simp at hdegree
  · rcases r with r | r
    · rcases s with k | s
      · have hdegree := congrArg IrreducibleCharacter.degree hrs
        simp at hdegree
      · rcases s with s | s
        · have hindex :
              r = s :=
            degreeThreeCharacter_injective hrs
          exact congrArg (fun t => Sum.inr (Sum.inl t)) hindex
        · have hdegree := congrArg IrreducibleCharacter.degree hrs
          simp at hdegree
    · rcases s with k | s
      · have hdegree := congrArg IrreducibleCharacter.degree hrs
        simp at hdegree
      · rcases s with s | s
        · have hdegree := congrArg IrreducibleCharacter.degree hrs
          simp at hdegree
        · have hindex :
              r = s :=
            degreeFourCharacter_injective hrs
          exact congrArg (fun t => Sum.inr (Sum.inr t)) hindex

/-- Every row is certified using its already-simple realization. -/
def rowCertificate (r : CharacterRow) :
    CharacterRowCertificate
      AlternatingSixThreeNormalizerCoordinates :=
  CharacterRowCertificate.ofSimple (rowCharacter r).realization

@[simp]
theorem rowCertificate_irreducibleCharacter
    (r : CharacterRow) :
    (rowCertificate r).irreducibleCharacter =
      rowCharacter r := by
  change
    IrreducibleCharacter.ofSimple
        (rowCharacter r).realization =
      rowCharacter r
  exact IrreducibleCharacter.ofSimple_realization (rowCharacter r)

/-- The complete finite character-table certificate for the coordinate
normalizer. -/
def finiteCharacterTableCertificate :
    FiniteCharacterTableCertificate
      AlternatingSixThreeNormalizerCoordinates CharacterRow where
  row := rowCertificate
  row_injective := by
    intro r s hrs
    apply rowCharacter_injective
    rw [← rowCertificate_irreducibleCharacter r,
      ← rowCertificate_irreducibleCharacter s]
    exact hrs
  row_count := by
    calc
      Nat.card CharacterRow = 28 := by
        rw [Nat.card_sum, Nat.card_sum,
          Nat.card_prod, Nat.card_prod]
        simp
      _ =
          Nat.card
            (ConjClasses
              AlternatingSixThreeNormalizerCoordinates) :=
        natCard_conjClasses_alternatingSixThreeNormalizerCoordinates.symm

/-- Complete ordinary irreducible-character enumeration. -/
def irreducibleCharacterEquiv :
    CharacterRow ≃
      IrreducibleCharacter
        AlternatingSixThreeNormalizerCoordinates :=
  finiteCharacterTableCertificate.irreducibleCharacterEquiv

@[simp]
theorem irreducibleCharacterEquiv_apply (r : CharacterRow) :
    irreducibleCharacterEquiv r = rowCharacter r := by
  rw [irreducibleCharacterEquiv,
    FiniteCharacterTableCertificate.irreducibleCharacterEquiv_apply,
    FiniteCharacterTableCertificate.character]
  change
    (rowCertificate r).irreducibleCharacter =
      rowCharacter r
  exact rowCertificate_irreducibleCharacter r

/-- The twelve prime-to-three rows: eight linear and four
degree-four. -/
abbrev CoordinatePPrimeCharacterRow :=
  Fin 8 ⊕ (Fin 2 × Fin 2)

/-- The explicitly displayed prime-to-three character. -/
def pPrimeCharacter (r : CoordinatePPrimeCharacterRow) :
    PPrimeIrreducibleCharacter
      AlternatingSixThreeNormalizerCoordinates 3 :=
  match r with
  | Sum.inl j =>
      ⟨coordinateLinearCharacter j, by
        rw [IrreducibleCharacter.IsPPrimeDegree,
          coordinateLinearCharacter_degree]
        norm_num⟩
  | Sum.inr r =>
      ⟨degreeFourCharacter r.1 r.2, by
        rw [IrreducibleCharacter.IsPPrimeDegree,
          degreeFourCharacter_degree]
        norm_num⟩

theorem pPrimeCharacter_bijective :
    Function.Bijective pPrimeCharacter := by
  constructor
  · intro r s hrs
    cases r with
    | inl j =>
        cases s with
        | inl k =>
            exact congrArg Sum.inl
              (coordinateLinearCharacter_injective
                (congrArg Subtype.val hrs))
        | inr s =>
            have hdegree :=
              congrArg
                (fun χ :
                  PPrimeIrreducibleCharacter
                    AlternatingSixThreeNormalizerCoordinates 3 =>
                  χ.1.degree)
                hrs
            simp [pPrimeCharacter] at hdegree
    | inr r =>
        cases s with
        | inl k =>
            have hdegree :=
              congrArg
                (fun χ :
                  PPrimeIrreducibleCharacter
                    AlternatingSixThreeNormalizerCoordinates 3 =>
                  χ.1.degree)
                hrs
            simp [pPrimeCharacter] at hdegree
        | inr s =>
            exact congrArg Sum.inr
              (degreeFourCharacter_injective
                (congrArg Subtype.val hrs))
  · intro χ
    let r : CharacterRow :=
      irreducibleCharacterEquiv.symm χ.1
    have hr : irreducibleCharacterEquiv r = χ.1 :=
      irreducibleCharacterEquiv.apply_symm_apply χ.1
    rcases r with j | r
    · refine ⟨Sum.inl j, ?_⟩
      apply Subtype.ext
      change coordinateLinearCharacter j = χ.1
      simpa only [irreducibleCharacterEquiv_apply,
        rowCharacter_linear] using hr
    · rcases r with r | r
      · exfalso
        apply χ.2
        rw [← hr, irreducibleCharacterEquiv_apply,
          rowCharacter_degreeThree,
          degreeThreeCharacter_degree]
      · refine ⟨Sum.inr r, ?_⟩
        apply Subtype.ext
        change degreeFourCharacter r.1 r.2 = χ.1
        simpa only [irreducibleCharacterEquiv_apply,
          rowCharacter_degreeFour] using hr

/-- Complete explicit enumeration of the twelve `3'`-degree rows. -/
def pPrimeIrreducibleCharacterEquiv :
    CoordinatePPrimeCharacterRow ≃
      PPrimeIrreducibleCharacter
        AlternatingSixThreeNormalizerCoordinates 3 :=
  Equiv.ofBijective pPrimeCharacter pPrimeCharacter_bijective

@[simp]
theorem pPrimeIrreducibleCharacterEquiv_apply
    (r : CoordinatePPrimeCharacterRow) :
    pPrimeIrreducibleCharacterEquiv r = pPrimeCharacter r :=
  rfl

@[simp]
theorem natCard_pPrimeIrreducibleCharacter :
    Nat.card
        (PPrimeIrreducibleCharacter
          AlternatingSixThreeNormalizerCoordinates 3) =
      12 := by
  calc
    Nat.card
        (PPrimeIrreducibleCharacter
          AlternatingSixThreeNormalizerCoordinates 3) =
        Nat.card CoordinatePPrimeCharacterRow :=
      Nat.card_congr pPrimeIrreducibleCharacterEquiv.symm
    _ = 12 := by
      rw [Nat.card_sum, Nat.card_prod]
      simp

end AlternatingSixThreeNormalizer
end McKayConjecture
