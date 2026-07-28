/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Construction
import McKayConjecture.Character.TableEnumeration
import McKayConjecture.GroupTheory.SpecialLinearTwoFiveConjugacyClassEquiv
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveCharacterNorm
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveThreeAmbientTransport
import Mathlib.RepresentationTheory.FinGroupCharZero

/-!
# The ordinary character table of `SL(2, 𝔽₅)`

This file realizes all nine symbolic rows by honest complex
representations.  The certified conjugacy-class decomposition turns the
symbolic weighted orthogonality calculation into character norms, proving
that every displayed representation is simple.  The nine rows therefore
give the complete ordinary table and, by degree filtering, the complete
`p'`-tables.
-/

noncomputable section

open CategoryTheory Matrix
open scoped MatrixGroups

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory
open SpecialLinearTwoRepresentation

/-- The two concrete faithful homomorphisms, indexed in the same order as
the symbolic table. -/
def specialLinearTwoFiveComplexHomChoice
    (k : Fin 2) :
    SpecialLinearTwoFive →* SL(2, ℂ) :=
  Fin.cases specialLinearTwoFiveComplexHomPlus
    (fun _ : Fin 1 => specialLinearTwoFiveComplexHomMinus) k

@[simp]
theorem specialLinearTwoFiveComplexHomChoice_zero :
    specialLinearTwoFiveComplexHomChoice 0 =
      specialLinearTwoFiveComplexHomPlus :=
  rfl

@[simp]
theorem specialLinearTwoFiveComplexHomChoice_one :
    specialLinearTwoFiveComplexHomChoice 1 =
      specialLinearTwoFiveComplexHomMinus := by
  rfl

/-- The honest finite-dimensional representation underlying each of the
nine ordinary character rows. -/
def specialLinearTwoFiveCharacterFDRep :
    SpecialLinearTwoFiveCharacterRow →
      FDRep ℂ SpecialLinearTwoFive
  | .trivial =>
      FDRep.of
        (Representation.trivial ℂ SpecialLinearTwoFive ℂ)
  | .faithful k =>
      fdRep (specialLinearTwoFiveComplexHomChoice k)
  | .symmetricSquare k =>
      symmetricSquareFDRep
        (specialLinearTwoFiveComplexHomChoice k)
  | .symmetricCube =>
      symmetricCubeFDRep
        specialLinearTwoFiveComplexHomPlus
  | .tensor =>
      tensorFDRep
        specialLinearTwoFiveComplexHomPlus
        specialLinearTwoFiveComplexHomMinus
  | .symmetricFourthPower =>
      symmetricFourthPowerFDRep
        specialLinearTwoFiveComplexHomPlus
  | .symmetricFifthPower =>
      symmetricFifthPowerFDRep
        specialLinearTwoFiveComplexHomPlus

/-- The defining character with either golden parameter has exactly the
certified symbolic trace row. -/
theorem specialLinearTwoFiveDefiningCharacter_representative
    (k : Fin 2)
    (c : SpecialLinearTwoFiveConjugacyClass) :
    (fdRep
        (specialLinearTwoFiveComplexHomChoice k)).character
        (specialLinearTwoFiveConjugacyRepresentative c) =
      binaryIcosahedralDefiningTrace
        (binaryIcosahedralGoldenRootChoice
          binaryIcosahedralGoldenRootPlus k) c := by
  fin_cases k
  · change
      (fdRep specialLinearTwoFiveComplexHomPlus).character
          (specialLinearTwoFiveConjugacyRepresentative c) =
        binaryIcosahedralDefiningTrace
          binaryIcosahedralGoldenRootPlus c
    change
      (representation
        specialLinearTwoFiveComplexHomPlus).character
          (specialLinearTwoFiveConjugacyRepresentative c) =
        _
    rw [representation_character,
      specialLinearTwoFiveComplexHom_trace_representative]
    fin_cases c <;> rfl
  · change
      (fdRep specialLinearTwoFiveComplexHomMinus).character
          (specialLinearTwoFiveConjugacyRepresentative c) =
        binaryIcosahedralDefiningTrace
          (1 - binaryIcosahedralGoldenRootPlus) c
    change
      (representation
        specialLinearTwoFiveComplexHomMinus).character
          (specialLinearTwoFiveConjugacyRepresentative c) =
        _
    rw [representation_character,
      specialLinearTwoFiveComplexHom_trace_representative]
    rw [one_sub_binaryIcosahedralGoldenRootPlus]
    fin_cases c <;> rfl

/-- Every realized character agrees with its symbolic row on the nine
class representatives. -/
theorem specialLinearTwoFiveCharacterFDRep_character_representative
    (r : SpecialLinearTwoFiveCharacterRow)
    (c : SpecialLinearTwoFiveConjugacyClass) :
    (specialLinearTwoFiveCharacterFDRep r).character
        (specialLinearTwoFiveConjugacyRepresentative c) =
      specialLinearTwoFiveCharacterTableValue
        binaryIcosahedralGoldenRootPlus r c := by
  rcases r with _ | k | k | _ | _ | _ | _
  · change
      LinearMap.trace ℂ ℂ
          (1 : ℂ →ₗ[ℂ] ℂ) =
        1
    simp
  · exact
      specialLinearTwoFiveDefiningCharacter_representative k c
  · change
      (symmetricSquareRepresentation
          (specialLinearTwoFiveComplexHomChoice k)).character
          (specialLinearTwoFiveConjugacyRepresentative c) =
        _
    rw [symmetricSquare_character,
      show
        (representation
          (specialLinearTwoFiveComplexHomChoice k)).character
            (specialLinearTwoFiveConjugacyRepresentative c) =
          binaryIcosahedralDefiningTrace
            (binaryIcosahedralGoldenRootChoice
              binaryIcosahedralGoldenRootPlus k) c by
        exact
          specialLinearTwoFiveDefiningCharacter_representative k c]
    rfl
  · change
      (symmetricCubeRepresentation
          specialLinearTwoFiveComplexHomPlus).character
          (specialLinearTwoFiveConjugacyRepresentative c) =
        _
    rw [symmetricCube_character]
    rw [show
        (representation
          specialLinearTwoFiveComplexHomPlus).character
            (specialLinearTwoFiveConjugacyRepresentative c) =
          binaryIcosahedralDefiningTrace
            binaryIcosahedralGoldenRootPlus c by
      exact
        specialLinearTwoFiveDefiningCharacter_representative 0 c]
    rfl
  · change
      (tensorFDRep
          specialLinearTwoFiveComplexHomPlus
          specialLinearTwoFiveComplexHomMinus).character
          (specialLinearTwoFiveConjugacyRepresentative c) =
        _
    rw [tensorFDRep_character]
    rw [show
        (fdRep specialLinearTwoFiveComplexHomPlus).character
            (specialLinearTwoFiveConjugacyRepresentative c) =
          binaryIcosahedralDefiningTrace
            binaryIcosahedralGoldenRootPlus c by
      exact
        (by simpa using
          specialLinearTwoFiveDefiningCharacter_representative 0 c)]
    rw [show
        (fdRep specialLinearTwoFiveComplexHomMinus).character
            (specialLinearTwoFiveConjugacyRepresentative c) =
          binaryIcosahedralDefiningTrace
            (1 - binaryIcosahedralGoldenRootPlus) c by
      exact
        (by simpa using
          specialLinearTwoFiveDefiningCharacter_representative 1 c)]
    rfl
  · change
      (symmetricFourthPowerRepresentation
          specialLinearTwoFiveComplexHomPlus).character
          (specialLinearTwoFiveConjugacyRepresentative c) =
        _
    rw [symmetricFourthPower_character]
    rw [show
        (representation
          specialLinearTwoFiveComplexHomPlus).character
            (specialLinearTwoFiveConjugacyRepresentative c) =
          binaryIcosahedralDefiningTrace
            binaryIcosahedralGoldenRootPlus c by
      exact
        specialLinearTwoFiveDefiningCharacter_representative 0 c]
    rfl
  · change
      (symmetricFifthPowerRepresentation
          specialLinearTwoFiveComplexHomPlus).character
          (specialLinearTwoFiveConjugacyRepresentative c) =
        _
    rw [symmetricFifthPower_character]
    rw [show
        (representation
          specialLinearTwoFiveComplexHomPlus).character
            (specialLinearTwoFiveConjugacyRepresentative c) =
          binaryIcosahedralDefiningTrace
            binaryIcosahedralGoldenRootPlus c by
      exact
        specialLinearTwoFiveDefiningCharacter_representative 0 c]
    rfl

/-- The dimension of every honest row is its displayed table degree. -/
@[simp]
theorem specialLinearTwoFiveCharacterFDRep_finrank
    (r : SpecialLinearTwoFiveCharacterRow) :
    Module.finrank ℂ
        (specialLinearTwoFiveCharacterFDRep r) =
      specialLinearTwoFiveCharacterRowDegree r := by
  rcases r with _ | k | k | _ | _ | _ | _
  · change Module.finrank ℂ ℂ = 1
    simp
  · exact fdRep_finrank _
  · exact symmetricSquareFDRep_finrank _
  · exact symmetricCubeFDRep_finrank _
  · exact tensorFDRep_finrank _ _
  · exact symmetricFourthPowerFDRep_finrank _
  · exact symmetricFifthPowerFDRep_finrank _

/-- Each realized character has unnormalized squared norm `120`. -/
theorem specialLinearTwoFiveCharacterFDRep_character_norm
    (r : SpecialLinearTwoFiveCharacterRow) :
    (∑ g : SpecialLinearTwoFive,
        (specialLinearTwoFiveCharacterFDRep r).character g *
          (specialLinearTwoFiveCharacterFDRep r).character g⁻¹) =
      (120 : ℂ) := by
  exact
    specialLinearTwoFiveFDRep_character_norm
      binaryIcosahedralGoldenRootPlus
      binaryIcosahedralGoldenRootPlus_sq r
      (specialLinearTwoFiveCharacterFDRep r)
      (specialLinearTwoFiveCharacterFDRep_character_representative r)

/-- All nine displayed representations are simple. -/
theorem specialLinearTwoFiveCharacterFDRep_simple
    (r : SpecialLinearTwoFiveCharacterRow) :
    Simple (specialLinearTwoFiveCharacterFDRep r) := by
  exact
    specialLinearTwoFiveFDRep_simple
      binaryIcosahedralGoldenRootPlus
      binaryIcosahedralGoldenRootPlus_sq r
      (specialLinearTwoFiveCharacterFDRep r)
      (specialLinearTwoFiveCharacterFDRep_character_representative r)

/-- The irreducible character afforded by a displayed row. -/
def specialLinearTwoFiveIrreducibleCharacter
    (r : SpecialLinearTwoFiveCharacterRow) :
    IrreducibleCharacter SpecialLinearTwoFive := by
  letI :
      Simple (specialLinearTwoFiveCharacterFDRep r) :=
    specialLinearTwoFiveCharacterFDRep_simple r
  exact
    IrreducibleCharacter.ofSimple
      (specialLinearTwoFiveCharacterFDRep r)

@[simp]
theorem specialLinearTwoFiveIrreducibleCharacter_degree
    (r : SpecialLinearTwoFiveCharacterRow) :
    (specialLinearTwoFiveIrreducibleCharacter r).degree =
      specialLinearTwoFiveCharacterRowDegree r := by
  change
    Module.finrank ℂ
        (specialLinearTwoFiveCharacterFDRep r) =
      _
  exact specialLinearTwoFiveCharacterFDRep_finrank r

@[simp]
theorem specialLinearTwoFiveIrreducibleCharacter_values_representative
    (r : SpecialLinearTwoFiveCharacterRow)
    (c : SpecialLinearTwoFiveConjugacyClass) :
    (specialLinearTwoFiveIrreducibleCharacter r).values
        (specialLinearTwoFiveConjugacyRepresentative c) =
      specialLinearTwoFiveCharacterTableValue
        binaryIcosahedralGoldenRootPlus r c := by
  change
    (specialLinearTwoFiveCharacterFDRep r).character
        (specialLinearTwoFiveConjugacyRepresentative c) =
      _
  exact
    specialLinearTwoFiveCharacterFDRep_character_representative r c

/-- Orthogonality makes the nine realized irreducible rows distinct. -/
theorem specialLinearTwoFiveIrreducibleCharacter_injective :
    Function.Injective
      specialLinearTwoFiveIrreducibleCharacter := by
  intro r s hrs
  have hvalues
      (c : SpecialLinearTwoFiveConjugacyClass) :
      specialLinearTwoFiveCharacterTableValue
          binaryIcosahedralGoldenRootPlus r c =
        specialLinearTwoFiveCharacterTableValue
          binaryIcosahedralGoldenRootPlus s c := by
    have h :=
      congrArg
        (fun χ : IrreducibleCharacter SpecialLinearTwoFive =>
          χ.values
            (specialLinearTwoFiveConjugacyRepresentative c))
        hrs
    simpa using h
  by_contra hne
  have hrsPair :=
    specialLinearTwoFiveCharacterTableWeightedPairing_eq
      binaryIcosahedralGoldenRootPlus
      binaryIcosahedralGoldenRootPlus_sq r s
  rw [if_neg hne] at hrsPair
  have hrrPair :=
    specialLinearTwoFiveCharacterTableWeightedPairing_eq
      binaryIcosahedralGoldenRootPlus
      binaryIcosahedralGoldenRootPlus_sq r r
  rw [if_pos rfl] at hrrPair
  have hpairs :
      specialLinearTwoFiveCharacterTableWeightedPairing
          binaryIcosahedralGoldenRootPlus r s =
        specialLinearTwoFiveCharacterTableWeightedPairing
          binaryIcosahedralGoldenRootPlus r r := by
    unfold specialLinearTwoFiveCharacterTableWeightedPairing
    apply Finset.sum_congr rfl
    intro c _
    rw [← hvalues c]
  have himpossible : (0 : ℂ) = 120 := by
    calc
      (0 : ℂ) =
          specialLinearTwoFiveCharacterTableWeightedPairing
            binaryIcosahedralGoldenRootPlus r s :=
        hrsPair.symm
      _ =
          specialLinearTwoFiveCharacterTableWeightedPairing
            binaryIcosahedralGoldenRootPlus r r :=
        hpairs
      _ = 120 := hrrPair
  norm_num at himpossible

/-- The nine explicit rows form the complete ordinary character table. -/
def specialLinearTwoFiveIrreducibleCharacterEquiv :
    SpecialLinearTwoFiveCharacterRow ≃
      IrreducibleCharacter SpecialLinearTwoFive :=
  irreducibleCharacterEquivOfInjective
    specialLinearTwoFiveIrreducibleCharacter
    specialLinearTwoFiveIrreducibleCharacter_injective
    (by
      rw [natCard_specialLinearTwoFiveCharacterRow,
        natCard_conjClasses_specialLinearTwoFive])

/-- The explicitly degree-filtered rows give every `p'`-degree
irreducible character. -/
def specialLinearTwoFivePPrimeCharacterEquiv
    (p : ℕ) :
    SpecialLinearTwoFivePPrimeCharacterRow p ≃
      PPrimeIrreducibleCharacter SpecialLinearTwoFive p where
  toFun r :=
    ⟨specialLinearTwoFiveIrreducibleCharacter r.1, by
      rw [IrreducibleCharacter.IsPPrimeDegree,
        specialLinearTwoFiveIrreducibleCharacter_degree]
      exact r.2⟩
  invFun χ :=
    ⟨specialLinearTwoFiveIrreducibleCharacterEquiv.symm χ.1, by
      have hp := χ.2
      rw [IrreducibleCharacter.IsPPrimeDegree] at hp
      rw [← specialLinearTwoFiveIrreducibleCharacter_degree]
      have hirr :
          specialLinearTwoFiveIrreducibleCharacter
              (specialLinearTwoFiveIrreducibleCharacterEquiv.symm χ.1) =
            χ.1 :=
        specialLinearTwoFiveIrreducibleCharacterEquiv.apply_symm_apply χ.1
      rw [hirr]
      exact hp⟩
  left_inv r := by
    apply Subtype.ext
    exact
      specialLinearTwoFiveIrreducibleCharacterEquiv.symm_apply_apply r.1
  right_inv χ := by
    apply Subtype.ext
    exact
      specialLinearTwoFiveIrreducibleCharacterEquiv.apply_symm_apply χ.1

/-- The complete six-row ambient `3'`-character table. -/
abbrev specialLinearTwoFiveThreePPrimeCharacterEquiv :
    SpecialLinearTwoFivePPrimeCharacterRow 3 ≃
      PPrimeIrreducibleCharacter SpecialLinearTwoFive 3 :=
  specialLinearTwoFivePPrimeCharacterEquiv 3

/-- The concrete group has exactly six irreducible characters of degree
prime to three. -/
theorem natCard_specialLinearTwoFiveThreePPrimeIrreducibleCharacter :
    Nat.card
        (PPrimeIrreducibleCharacter
          SpecialLinearTwoFive 3) =
      6 := by
  rw [← Nat.card_congr
    specialLinearTwoFiveThreePPrimeCharacterEquiv]
  exact
    natCard_specialLinearTwoFiveThreePPrimeCharacterRow

end InductiveMcKay
end McKayConjecture
