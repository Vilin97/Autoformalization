/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Linear
import McKayConjecture.Character.Restriction
import McKayConjecture.Character.TableEnumeration
import McKayConjecture.Character.Twist
import McKayConjecture.GroupTheory.SpecialLinearTwoFiveSylowTwoNormalizer
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveCharacterTable
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.RepresentationTheory.FinGroupCharZero

/-!
# Representations of the Sylow-two normalizer in `SL(2, 𝔽₅)`

The exact Sylow-two normalizer is the binary tetrahedral group
`Q₈ ⋊ C₃`.  Its seven ordinary irreducible characters have degrees

`1, 1, 1, 2, 2, 2, 3`.

The three linear rows come from the explicit quotient to `C₃`.  A
two-dimensional row is obtained by restricting the faithful binary
icosahedral representation, and its two nontrivial linear twists give the
other two.  The final row is the restricted symmetric square.  Character
norms are calculated from the exact intersection counts with the ambient
conjugacy classes.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance factPrimeTwoForNormalizerRepresentations :
    Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The seven binary-tetrahedral character rows. -/
inductive SpecialLinearTwoFiveTwoNormalizerCharacterRow
  | linear (j : ZMod 3)
  | twoDimensional (j : ZMod 3)
  | threeDimensional
  deriving DecidableEq, Fintype

/-- The degree displayed by each row. -/
def specialLinearTwoFiveTwoNormalizerCharacterRowDegree :
    SpecialLinearTwoFiveTwoNormalizerCharacterRow → ℕ
  | .linear _ => 1
  | .twoDimensional _ => 2
  | .threeDimensional => 3

/-- The inclusion of the exact normalizer into `SL(2, 𝔽₅)`. -/
abbrev specialLinearTwoFiveSylowTwoNormalizerInclusion :
    SpecialLinearTwoFiveSylowTwoNormalizer →*
      SpecialLinearTwoFive :=
  (Subgroup.normalizer
    (specialLinearTwoFiveSylowTwo :
      Set SpecialLinearTwoFive)).subtype

/-- The complex unit character of `C₃` with frequency `j`. -/
def zmodThreeComplexUnitCharacter (j : ZMod 3) :
    Multiplicative (ZMod 3) →* ℂˣ where
  toFun z :=
    Circle.toUnits
      (ZMod.toCircle (j * Multiplicative.toAdd z))
  map_one' := by
    apply Units.ext
    simp
  map_mul' z w := by
    apply Units.ext
    change
      (ZMod.toCircle
          (j * (Multiplicative.toAdd z +
            Multiplicative.toAdd w)) : ℂ) =
        (ZMod.toCircle
          (j * Multiplicative.toAdd z) : ℂ) *
        (ZMod.toCircle
          (j * Multiplicative.toAdd w) : ℂ)
    rw [mul_add, AddChar.map_add_eq_mul]
    exact map_mul Circle.coeHom _ _

/-- The three linear homomorphisms of the binary tetrahedral normalizer. -/
def specialLinearTwoFiveTwoNormalizerLinearHom (j : ZMod 3) :
    SpecialLinearTwoFiveSylowTwoNormalizer →* ℂˣ :=
  (zmodThreeComplexUnitCharacter j).comp
    specialLinearTwoFiveSylowTwoNormalizerCyclicQuotient

@[simp]
theorem specialLinearTwoFiveTwoNormalizerLinearHom_orderThree
    (j : ZMod 3) :
    specialLinearTwoFiveTwoNormalizerLinearHom j
        specialLinearTwoFiveSylowTwoNormalizerOrderThree =
      Circle.toUnits (ZMod.toCircle j) := by
  apply Units.ext
  simp [specialLinearTwoFiveTwoNormalizerLinearHom,
    zmodThreeComplexUnitCharacter]

theorem
    specialLinearTwoFiveTwoNormalizerLinearHom_orderThree_value_injective :
    Function.Injective
      (fun j : ZMod 3 =>
        (specialLinearTwoFiveTwoNormalizerLinearHom j
          specialLinearTwoFiveSylowTwoNormalizerOrderThree : ℂ)) := by
  intro i j hij
  apply ZMod.injective_stdAddChar
  simpa [ZMod.stdAddChar_apply] using hij

theorem specialLinearTwoFiveTwoNormalizerLinearHom_injective :
    Function.Injective
      specialLinearTwoFiveTwoNormalizerLinearHom := by
  intro i j hij
  apply
    specialLinearTwoFiveTwoNormalizerLinearHom_orderThree_value_injective
  have h :=
    congrArg
      (fun f :
        SpecialLinearTwoFiveSylowTwoNormalizer →* ℂˣ =>
          (f specialLinearTwoFiveSylowTwoNormalizerOrderThree : ℂ))
      hij
  exact h

/-- The three irreducible linear characters. -/
def specialLinearTwoFiveTwoNormalizerLinearCharacter
    (j : ZMod 3) :
    IrreducibleCharacter
      SpecialLinearTwoFiveSylowTwoNormalizer :=
  IrreducibleCharacter.linear
    (specialLinearTwoFiveTwoNormalizerLinearHom j)

@[simp]
theorem specialLinearTwoFiveTwoNormalizerLinearCharacter_degree
    (j : ZMod 3) :
    (specialLinearTwoFiveTwoNormalizerLinearCharacter j).degree =
      1 :=
  IrreducibleCharacter.linear_degree _

@[simp]
theorem specialLinearTwoFiveTwoNormalizerLinearCharacter_values
    (j : ZMod 3)
    (g : SpecialLinearTwoFiveSylowTwoNormalizer) :
    (specialLinearTwoFiveTwoNormalizerLinearCharacter j).values g =
      (specialLinearTwoFiveTwoNormalizerLinearHom j g : ℂ) :=
  IrreducibleCharacter.linear_values _ _

theorem specialLinearTwoFiveTwoNormalizerLinearCharacter_injective :
    Function.Injective
      specialLinearTwoFiveTwoNormalizerLinearCharacter :=
  IrreducibleCharacter.linear_injective.comp
    specialLinearTwoFiveTwoNormalizerLinearHom_injective

/-! ## The restricted two-dimensional row -/

/-- The faithful two-dimensional ambient row restricted to the exact
normalizer. -/
abbrev specialLinearTwoFiveTwoNormalizerBaseFDRep :
    FDRep ℂ SpecialLinearTwoFiveSylowTwoNormalizer :=
  FDRep.res specialLinearTwoFiveSylowTwoNormalizerInclusion
    (specialLinearTwoFiveCharacterFDRep (.faithful 0))

/-- The restricted defining character has norm one. -/
theorem specialLinearTwoFiveTwoNormalizerBaseFDRep_character_norm :
    (∑ g : SpecialLinearTwoFiveSylowTwoNormalizer,
        specialLinearTwoFiveTwoNormalizerBaseFDRep.character g *
          specialLinearTwoFiveTwoNormalizerBaseFDRep.character g⁻¹) =
      (24 : ℂ) := by
  change
    (∑ g : SpecialLinearTwoFiveSylowTwoNormalizer,
      (specialLinearTwoFiveCharacterFDRep (.faithful 0)).character
          (g : SpecialLinearTwoFive) *
        (specialLinearTwoFiveCharacterFDRep (.faithful 0)).character
          ((g : SpecialLinearTwoFive)⁻¹)) =
      (24 : ℂ)
  calc
    _ =
        ∑ c : SpecialLinearTwoFiveConjugacyClass,
          specialLinearTwoFiveSylowTwoNormalizerAmbientClassSize c •
            ((specialLinearTwoFiveCharacterFDRep
                (.faithful 0)).character
                (specialLinearTwoFiveConjugacyRepresentative c) *
              (specialLinearTwoFiveCharacterFDRep
                (.faithful 0)).character
                (specialLinearTwoFiveConjugacyRepresentative c)⁻¹) := by
      exact
        specialLinearTwoFiveSylowTwoNormalizer_sum_by_ambientClasses
          (fun g =>
            (specialLinearTwoFiveCharacterFDRep
                (.faithful 0)).character g *
              (specialLinearTwoFiveCharacterFDRep
                (.faithful 0)).character g⁻¹)
          (by
            intro g h hconj
            obtain ⟨x, rfl⟩ := isConj_iff.mp hconj
            rw [FDRep.char_conj]
            rw [conj_inv, FDRep.char_conj])
    _ = 24 := by
      have hinv
          (c : SpecialLinearTwoFiveConjugacyClass) :
          (specialLinearTwoFiveCharacterFDRep
              (.faithful 0)).character
                (specialLinearTwoFiveConjugacyRepresentative c)⁻¹ =
            (specialLinearTwoFiveCharacterFDRep
              (.faithful 0)).character
                (specialLinearTwoFiveConjugacyRepresentative c) := by
        obtain ⟨z, hz⟩ :=
          isConj_iff.mp
            (specialLinearTwoFiveConjugacyRepresentative_isConj_inv c)
        rw [← hz]
        exact
          FDRep.char_conj
            (specialLinearTwoFiveCharacterFDRep (.faithful 0))
            (specialLinearTwoFiveConjugacyRepresentative c) z
      simp_rw [hinv]
      simp_rw [
        specialLinearTwoFiveCharacterFDRep_character_representative]
      simp [
        specialLinearTwoFiveSylowTwoNormalizerAmbientClassSize,
        specialLinearTwoFiveCharacterTableValue,
        binaryIcosahedralDefiningTrace,
        Fin.sum_univ_succ]
      ring

/-- The restricted defining representation is simple. -/
theorem specialLinearTwoFiveTwoNormalizerBaseFDRep_simple :
    Simple specialLinearTwoFiveTwoNormalizerBaseFDRep := by
  rw [FDRep.simple_iff_char_is_norm_one,
    natCard_specialLinearTwoFiveSylowTwoNormalizer]
  exact
    specialLinearTwoFiveTwoNormalizerBaseFDRep_character_norm

/-- The base two-dimensional irreducible character. -/
def specialLinearTwoFiveTwoNormalizerBaseCharacter :
    IrreducibleCharacter
      SpecialLinearTwoFiveSylowTwoNormalizer := by
  letI :
      Simple specialLinearTwoFiveTwoNormalizerBaseFDRep :=
    specialLinearTwoFiveTwoNormalizerBaseFDRep_simple
  exact
    IrreducibleCharacter.ofSimple
      specialLinearTwoFiveTwoNormalizerBaseFDRep

@[simp]
theorem specialLinearTwoFiveTwoNormalizerBaseCharacter_degree :
    specialLinearTwoFiveTwoNormalizerBaseCharacter.degree = 2 := by
  change
    Module.finrank ℂ
      specialLinearTwoFiveTwoNormalizerBaseFDRep = 2
  rw [FDRep.res_finrank,
    specialLinearTwoFiveCharacterFDRep_finrank]
  rfl

theorem
    specialLinearTwoFiveSylowTwoNormalizerOrderThree_isConj_ambientOrderThree :
    IsConj
      specialLinearTwoFiveSylowTwoNormalizerOrderThreeMatrix
      (specialLinearTwoFiveConjugacyRepresentative 4) := by
  apply
    (specialLinearTwoFiveAreConjugate_iff_isConj _ _).1
  decide

@[simp]
theorem specialLinearTwoFiveTwoNormalizerBaseCharacter_orderThree :
    specialLinearTwoFiveTwoNormalizerBaseCharacter.values
        specialLinearTwoFiveSylowTwoNormalizerOrderThree =
      -1 := by
  change
    (specialLinearTwoFiveCharacterFDRep (.faithful 0)).character
        specialLinearTwoFiveSylowTwoNormalizerOrderThreeMatrix =
      -1
  obtain ⟨x, hx⟩ :=
    isConj_iff.mp
      specialLinearTwoFiveSylowTwoNormalizerOrderThree_isConj_ambientOrderThree
  calc
    _ =
        (specialLinearTwoFiveCharacterFDRep (.faithful 0)).character
          (x *
            specialLinearTwoFiveSylowTwoNormalizerOrderThreeMatrix *
            x⁻¹) := by
      exact
        (FDRep.char_conj
          (specialLinearTwoFiveCharacterFDRep (.faithful 0))
          specialLinearTwoFiveSylowTwoNormalizerOrderThreeMatrix x).symm
    _ =
        (specialLinearTwoFiveCharacterFDRep (.faithful 0)).character
          (specialLinearTwoFiveConjugacyRepresentative 4) := by
      rw [hx]
    _ = -1 := by
      rw [
        specialLinearTwoFiveCharacterFDRep_character_representative]
      rfl

/-- The three two-dimensional rows are the linear twists of the restricted
defining row. -/
def specialLinearTwoFiveTwoNormalizerTwoDimensionalCharacter
    (j : ZMod 3) :
    IrreducibleCharacter
      SpecialLinearTwoFiveSylowTwoNormalizer :=
  IrreducibleCharacter.twist
    (specialLinearTwoFiveTwoNormalizerLinearHom j)
    specialLinearTwoFiveTwoNormalizerBaseCharacter

@[simp]
theorem
    specialLinearTwoFiveTwoNormalizerTwoDimensionalCharacter_degree
    (j : ZMod 3) :
    (specialLinearTwoFiveTwoNormalizerTwoDimensionalCharacter j).degree =
      2 := by
  rw [
    specialLinearTwoFiveTwoNormalizerTwoDimensionalCharacter,
    IrreducibleCharacter.twist_degree,
    specialLinearTwoFiveTwoNormalizerBaseCharacter_degree]

@[simp]
theorem
    specialLinearTwoFiveTwoNormalizerTwoDimensionalCharacter_orderThree
    (j : ZMod 3) :
    (specialLinearTwoFiveTwoNormalizerTwoDimensionalCharacter j).values
        specialLinearTwoFiveSylowTwoNormalizerOrderThree =
      -(ZMod.stdAddChar j) := by
  rw [
    specialLinearTwoFiveTwoNormalizerTwoDimensionalCharacter,
    IrreducibleCharacter.twist_values,
    specialLinearTwoFiveTwoNormalizerBaseCharacter_orderThree]
  rw [show
    (specialLinearTwoFiveTwoNormalizerLinearHom j
        specialLinearTwoFiveSylowTwoNormalizerOrderThree : ℂ) =
      ZMod.stdAddChar j by
    have h :=
      congrArg
        (fun u : ℂˣ => (u : ℂ))
        (specialLinearTwoFiveTwoNormalizerLinearHom_orderThree j)
    simpa [ZMod.stdAddChar_apply] using h]
  ring

theorem
    specialLinearTwoFiveTwoNormalizerTwoDimensionalCharacter_injective :
    Function.Injective
      specialLinearTwoFiveTwoNormalizerTwoDimensionalCharacter := by
  intro i j hij
  apply ZMod.injective_stdAddChar
  have h :=
    congrArg
      (fun χ :
        IrreducibleCharacter
          SpecialLinearTwoFiveSylowTwoNormalizer =>
        χ.values
          specialLinearTwoFiveSylowTwoNormalizerOrderThree)
      hij
  simp only [
    specialLinearTwoFiveTwoNormalizerTwoDimensionalCharacter_orderThree]
    at h
  linear_combination -h

/-! ## The three-dimensional row -/

/-- The ambient symmetric-square row restricted to the exact normalizer. -/
abbrev specialLinearTwoFiveTwoNormalizerThreeFDRep :
    FDRep ℂ SpecialLinearTwoFiveSylowTwoNormalizer :=
  FDRep.res specialLinearTwoFiveSylowTwoNormalizerInclusion
    (specialLinearTwoFiveCharacterFDRep (.symmetricSquare 0))

theorem specialLinearTwoFiveTwoNormalizerThreeFDRep_character_norm :
    (∑ g : SpecialLinearTwoFiveSylowTwoNormalizer,
        specialLinearTwoFiveTwoNormalizerThreeFDRep.character g *
          specialLinearTwoFiveTwoNormalizerThreeFDRep.character g⁻¹) =
      (24 : ℂ) := by
  change
    (∑ g : SpecialLinearTwoFiveSylowTwoNormalizer,
      (specialLinearTwoFiveCharacterFDRep
          (.symmetricSquare 0)).character
          (g : SpecialLinearTwoFive) *
        (specialLinearTwoFiveCharacterFDRep
          (.symmetricSquare 0)).character
          ((g : SpecialLinearTwoFive)⁻¹)) =
      (24 : ℂ)
  calc
    _ =
        ∑ c : SpecialLinearTwoFiveConjugacyClass,
          specialLinearTwoFiveSylowTwoNormalizerAmbientClassSize c •
            ((specialLinearTwoFiveCharacterFDRep
                (.symmetricSquare 0)).character
                (specialLinearTwoFiveConjugacyRepresentative c) *
              (specialLinearTwoFiveCharacterFDRep
                (.symmetricSquare 0)).character
                (specialLinearTwoFiveConjugacyRepresentative c)⁻¹) := by
      exact
        specialLinearTwoFiveSylowTwoNormalizer_sum_by_ambientClasses
          (fun g =>
            (specialLinearTwoFiveCharacterFDRep
                (.symmetricSquare 0)).character g *
              (specialLinearTwoFiveCharacterFDRep
                (.symmetricSquare 0)).character g⁻¹)
          (by
            intro g h hconj
            obtain ⟨x, rfl⟩ := isConj_iff.mp hconj
            rw [FDRep.char_conj]
            rw [conj_inv, FDRep.char_conj])
    _ = 24 := by
      have hinv
          (c : SpecialLinearTwoFiveConjugacyClass) :
          (specialLinearTwoFiveCharacterFDRep
              (.symmetricSquare 0)).character
                (specialLinearTwoFiveConjugacyRepresentative c)⁻¹ =
            (specialLinearTwoFiveCharacterFDRep
              (.symmetricSquare 0)).character
                (specialLinearTwoFiveConjugacyRepresentative c) := by
        obtain ⟨z, hz⟩ :=
          isConj_iff.mp
            (specialLinearTwoFiveConjugacyRepresentative_isConj_inv c)
        rw [← hz]
        exact
          FDRep.char_conj
            (specialLinearTwoFiveCharacterFDRep
              (.symmetricSquare 0))
            (specialLinearTwoFiveConjugacyRepresentative c) z
      simp_rw [hinv]
      simp_rw [
        specialLinearTwoFiveCharacterFDRep_character_representative]
      simp [
        specialLinearTwoFiveSylowTwoNormalizerAmbientClassSize,
        specialLinearTwoFiveCharacterTableValue,
        binaryIcosahedralSymmetricSquareValue,
        binaryIcosahedralDefiningTrace,
        Fin.sum_univ_succ]
      ring

theorem specialLinearTwoFiveTwoNormalizerThreeFDRep_simple :
    Simple specialLinearTwoFiveTwoNormalizerThreeFDRep := by
  rw [FDRep.simple_iff_char_is_norm_one,
    natCard_specialLinearTwoFiveSylowTwoNormalizer]
  exact
    specialLinearTwoFiveTwoNormalizerThreeFDRep_character_norm

/-- The irreducible three-dimensional character. -/
def specialLinearTwoFiveTwoNormalizerThreeDimensionalCharacter :
    IrreducibleCharacter
      SpecialLinearTwoFiveSylowTwoNormalizer := by
  letI :
      Simple specialLinearTwoFiveTwoNormalizerThreeFDRep :=
    specialLinearTwoFiveTwoNormalizerThreeFDRep_simple
  exact
    IrreducibleCharacter.ofSimple
      specialLinearTwoFiveTwoNormalizerThreeFDRep

@[simp]
theorem
    specialLinearTwoFiveTwoNormalizerThreeDimensionalCharacter_degree :
    specialLinearTwoFiveTwoNormalizerThreeDimensionalCharacter.degree =
      3 := by
  change
    Module.finrank ℂ
      specialLinearTwoFiveTwoNormalizerThreeFDRep = 3
  rw [FDRep.res_finrank,
    specialLinearTwoFiveCharacterFDRep_finrank]
  rfl

/-! ## The complete ordinary and `2'` tables -/

/-- The irreducible character represented by each of the seven rows. -/
def specialLinearTwoFiveTwoNormalizerIrreducibleCharacter :
    SpecialLinearTwoFiveTwoNormalizerCharacterRow →
      IrreducibleCharacter
        SpecialLinearTwoFiveSylowTwoNormalizer
  | .linear j =>
      specialLinearTwoFiveTwoNormalizerLinearCharacter j
  | .twoDimensional j =>
      specialLinearTwoFiveTwoNormalizerTwoDimensionalCharacter j
  | .threeDimensional =>
      specialLinearTwoFiveTwoNormalizerThreeDimensionalCharacter

@[simp]
theorem specialLinearTwoFiveTwoNormalizerIrreducibleCharacter_degree
    (r : SpecialLinearTwoFiveTwoNormalizerCharacterRow) :
    (specialLinearTwoFiveTwoNormalizerIrreducibleCharacter r).degree =
      specialLinearTwoFiveTwoNormalizerCharacterRowDegree r := by
  rcases r with j | j | _
  · exact
      specialLinearTwoFiveTwoNormalizerLinearCharacter_degree j
  · exact
      specialLinearTwoFiveTwoNormalizerTwoDimensionalCharacter_degree j
  · exact
      specialLinearTwoFiveTwoNormalizerThreeDimensionalCharacter_degree

theorem
    specialLinearTwoFiveTwoNormalizerIrreducibleCharacter_injective :
    Function.Injective
      specialLinearTwoFiveTwoNormalizerIrreducibleCharacter := by
  intro r s hrs
  rcases r with i | i | _ <;>
    rcases s with j | j | _
  · exact congrArg SpecialLinearTwoFiveTwoNormalizerCharacterRow.linear
      (specialLinearTwoFiveTwoNormalizerLinearCharacter_injective hrs)
  · have hdegree :=
      congrArg
        (fun χ :
          IrreducibleCharacter
            SpecialLinearTwoFiveSylowTwoNormalizer =>
          χ.degree) hrs
    norm_num [
      specialLinearTwoFiveTwoNormalizerCharacterRowDegree]
      at hdegree
  · have hdegree :=
      congrArg
        (fun χ :
          IrreducibleCharacter
            SpecialLinearTwoFiveSylowTwoNormalizer =>
          χ.degree) hrs
    norm_num [
      specialLinearTwoFiveTwoNormalizerCharacterRowDegree]
      at hdegree
  · have hdegree :=
      congrArg
        (fun χ :
          IrreducibleCharacter
            SpecialLinearTwoFiveSylowTwoNormalizer =>
          χ.degree) hrs
    norm_num [
      specialLinearTwoFiveTwoNormalizerCharacterRowDegree]
      at hdegree
  · exact
      congrArg
        SpecialLinearTwoFiveTwoNormalizerCharacterRow.twoDimensional
        (specialLinearTwoFiveTwoNormalizerTwoDimensionalCharacter_injective
          hrs)
  · have hdegree :=
      congrArg
        (fun χ :
          IrreducibleCharacter
            SpecialLinearTwoFiveSylowTwoNormalizer =>
          χ.degree) hrs
    norm_num [
      specialLinearTwoFiveTwoNormalizerCharacterRowDegree]
      at hdegree
  · have hdegree :=
      congrArg
        (fun χ :
          IrreducibleCharacter
            SpecialLinearTwoFiveSylowTwoNormalizer =>
          χ.degree) hrs
    norm_num [
      specialLinearTwoFiveTwoNormalizerCharacterRowDegree]
      at hdegree
  · have hdegree :=
      congrArg
        (fun χ :
          IrreducibleCharacter
            SpecialLinearTwoFiveSylowTwoNormalizer =>
          χ.degree) hrs
    norm_num [
      specialLinearTwoFiveTwoNormalizerCharacterRowDegree]
      at hdegree
  · rfl

theorem natCard_specialLinearTwoFiveTwoNormalizerCharacterRow :
    Nat.card SpecialLinearTwoFiveTwoNormalizerCharacterRow = 7 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- The seven displayed rows form the complete ordinary character table of
the binary tetrahedral normalizer. -/
def specialLinearTwoFiveTwoNormalizerIrreducibleCharacterEquiv :
    SpecialLinearTwoFiveTwoNormalizerCharacterRow ≃
      IrreducibleCharacter
        SpecialLinearTwoFiveSylowTwoNormalizer :=
  irreducibleCharacterEquivOfInjective
    specialLinearTwoFiveTwoNormalizerIrreducibleCharacter
    specialLinearTwoFiveTwoNormalizerIrreducibleCharacter_injective
    (by
      rw [
        natCard_specialLinearTwoFiveTwoNormalizerCharacterRow,
        natCard_conjClasses_specialLinearTwoFiveSylowTwoNormalizer])

/-- The rows of odd degree in the complete normalizer table. -/
abbrev SpecialLinearTwoFiveTwoNormalizerPPrimeCharacterRow :=
  {r : SpecialLinearTwoFiveTwoNormalizerCharacterRow //
    ¬2 ∣ specialLinearTwoFiveTwoNormalizerCharacterRowDegree r}

theorem natCard_specialLinearTwoFiveTwoNormalizerPPrimeCharacterRow :
    Nat.card
        SpecialLinearTwoFiveTwoNormalizerPPrimeCharacterRow =
      4 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- The explicitly filtered odd-degree rows give every `2'`-degree
irreducible character of the exact normalizer. -/
def specialLinearTwoFiveTwoNormalizerPPrimeCharacterEquiv :
    SpecialLinearTwoFiveTwoNormalizerPPrimeCharacterRow ≃
      PPrimeIrreducibleCharacter
        SpecialLinearTwoFiveSylowTwoNormalizer 2 where
  toFun r :=
    ⟨specialLinearTwoFiveTwoNormalizerIrreducibleCharacter r.1, by
      rw [IrreducibleCharacter.IsPPrimeDegree,
        specialLinearTwoFiveTwoNormalizerIrreducibleCharacter_degree]
      exact r.2⟩
  invFun χ :=
    ⟨specialLinearTwoFiveTwoNormalizerIrreducibleCharacterEquiv.symm
        χ.1, by
      have hp := χ.2
      rw [IrreducibleCharacter.IsPPrimeDegree] at hp
      rw [←
        specialLinearTwoFiveTwoNormalizerIrreducibleCharacter_degree]
      have heq :
          specialLinearTwoFiveTwoNormalizerIrreducibleCharacter
              (specialLinearTwoFiveTwoNormalizerIrreducibleCharacterEquiv.symm
                χ.1) =
            χ.1 :=
        specialLinearTwoFiveTwoNormalizerIrreducibleCharacterEquiv
          |>.apply_symm_apply χ.1
      rw [heq]
      exact hp⟩
  left_inv r := by
    apply Subtype.ext
    exact
      specialLinearTwoFiveTwoNormalizerIrreducibleCharacterEquiv
        |>.symm_apply_apply r.1
  right_inv χ := by
    apply Subtype.ext
    exact
      specialLinearTwoFiveTwoNormalizerIrreducibleCharacterEquiv
        |>.apply_symm_apply χ.1

end InductiveMcKay
end McKayConjecture
