/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.FiniteCharacterTableCertificate
import McKayConjecture.Character.QuaternionGroupFiveLinear
import McKayConjecture.Character.QuaternionGroupFiveTwoDimensional
import McKayConjecture.Character.SimpleCharacterRowCertificate
import McKayConjecture.Character.Transport
import McKayConjecture.GroupTheory.CyclicFiveInversionSemidirect

/-!
# The character table of `C₅ ⋊ C₄` with inversion action

The concrete inversion semidirect product is isomorphic to
`QuaternionGroup 5`.  This file transports the four linear and four
two-dimensional representations across that proved equivalence.  It records
complete ordinary and `5'`-character enumerations and packages the eight
explicit transported representations as a generic finite character table.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace CyclicFiveInversionSemidirect

open GroupTheory

abbrev Group :=
  GroupTheory.CyclicFiveInversionSemidirect

/-- Eight-row index: four linear and four two-dimensional rows. -/
inductive CharacterRow
  | linear (j : Fin 4)
  | twoDimensional (k : Fin 4)
  deriving DecidableEq, Fintype

/-- The explicit dicyclic representation attached to a row before
transport to the semidirect-product model. -/
def quaternionRowFDRep :
    CharacterRow → FDRep ℂ (QuaternionGroup 5)
  | .linear j =>
      IrreducibleCharacter.linearFDRep
        (QuaternionGroupFive.linearHom j)
  | .twoDimensional k =>
      QuaternionGroupFive.twoDimensionalFDRep k

theorem quaternionRowFDRep_simple
    (r : CharacterRow) :
    Simple (quaternionRowFDRep r) := by
  cases r with
  | linear j =>
      exact
        IrreducibleCharacter.linearFDRep_simple
          (QuaternionGroupFive.linearHom j)
  | twoDimensional k =>
      exact
        QuaternionGroupFive.twoDimensionalFDRep_simple k

/-- Restriction along the proved equivalence
`C₅ ⋊ C₄ ≃ QuaternionGroup 5`. -/
def restrictionEquivalence :
    FDRep ℂ (QuaternionGroup 5) ≌ FDRep ℂ Group :=
  Action.resEquiv (FGModuleCat ℂ)
    quaternionFiveEquivCyclicFiveInversionSemidirect.symm

/-- The eight explicit representations on the semidirect-product model. -/
def rowFDRep (r : CharacterRow) : FDRep ℂ Group :=
  restrictionEquivalence.functor.obj (quaternionRowFDRep r)

theorem rowFDRep_simple (r : CharacterRow) :
    Simple (rowFDRep r) := by
  letI : Simple (quaternionRowFDRep r) :=
    quaternionRowFDRep_simple r
  exact
    CategoryTheory.simple_obj
      restrictionEquivalence.functor
      (quaternionRowFDRep r)

@[simp]
theorem rowFDRep_character
    (r : CharacterRow) (g : Group) :
    (rowFDRep r).character g =
      (quaternionRowFDRep r).character
        (quaternionFiveEquivCyclicFiveInversionSemidirect.symm g) :=
  rfl

@[simp]
theorem rowFDRep_finrank_linear (j : Fin 4) :
    Module.finrank ℂ (rowFDRep (.linear j)) = 1 := by
  change
    Module.finrank ℂ
      (IrreducibleCharacter.linearFDRep
        (QuaternionGroupFive.linearHom j)) = 1
  exact
    IrreducibleCharacter.linearFDRep_finrank
      (QuaternionGroupFive.linearHom j)

@[simp]
theorem rowFDRep_finrank_twoDimensional (k : Fin 4) :
    Module.finrank ℂ (rowFDRep (.twoDimensional k)) = 2 := by
  change
    Module.finrank ℂ
      (QuaternionGroupFive.twoDimensionalFDRep k) = 2
  simpa only [
    QuaternionGroupFive.twoDimensionalCharacter_degree
  ] using
    (show
      (QuaternionGroupFive.twoDimensionalCharacter k).degree =
        Module.finrank ℂ
          (QuaternionGroupFive.twoDimensionalFDRep k) from rfl).symm

/-- The eight explicit ordinary irreducible characters of the dicyclic
presentation. -/
def quaternionIrreducibleCharacter
    (r : CharacterRow) :
    IrreducibleCharacter (QuaternionGroup 5) :=
  match r with
  | .linear j =>
      QuaternionGroupFive.linearCharacter j
  | .twoDimensional k =>
      QuaternionGroupFive.twoDimensionalCharacter k

/-- The four explicit two-dimensional dicyclic characters are pairwise
distinct.  Evaluating at the standard generator reduces equality to the
elementary identity
`(u - v) * (u - v⁻¹) = 0` for tenth roots of unity. -/
theorem quaternionTwoDimensionalCharacter_injective :
    Function.Injective
      QuaternionGroupFive.twoDimensionalCharacter := by
  intro k l h
  have hvalue :=
    congrArg
      (fun χ : IrreducibleCharacter (QuaternionGroup 5) =>
        χ.values
          (QuaternionGroup.a
            ((1 : ℕ) : ZMod 10))) h
  rw [
    QuaternionGroupFive.twoDimensionalCharacter_values_a_natCast,
    QuaternionGroupFive.twoDimensionalCharacter_values_a_natCast
  ] at hvalue
  have hvalue' :
      QuaternionGroupFive.twoDimensionalParameter k +
          (QuaternionGroupFive.twoDimensionalParameter k)⁻¹ =
        QuaternionGroupFive.twoDimensionalParameter l +
          (QuaternionGroupFive.twoDimensionalParameter l)⁻¹ := by
    simpa only [pow_one] using hvalue
  let u : ℂ :=
    QuaternionGroupFive.twoDimensionalParameter k
  let v : ℂ :=
    QuaternionGroupFive.twoDimensionalParameter l
  have hu : u ≠ 0 :=
    QuaternionGroupFive.twoDimensionalParameter_ne_zero k
  have hv : v ≠ 0 :=
    QuaternionGroupFive.twoDimensionalParameter_ne_zero l
  have huv :
      (u - v) * (u - v⁻¹) = 0 := by
    calc
      (u - v) * (u - v⁻¹) =
          u * (u + u⁻¹ - (v + v⁻¹)) := by
            field_simp [hu, hv]
            ring
      _ = 0 := by
        change
          u *
            (QuaternionGroupFive.twoDimensionalParameter k +
                (QuaternionGroupFive.twoDimensionalParameter k)⁻¹ -
              (QuaternionGroupFive.twoDimensionalParameter l +
                (QuaternionGroupFive.twoDimensionalParameter l)⁻¹)) = 0
        rw [hvalue']
        ring
  rcases mul_eq_zero.mp huv with hsame | hinverse
  · apply Fin.ext
    exact
      Nat.add_right_cancel
        (QuaternionGroupFive.primitiveTenthRoot_isPrimitive.pow_inj
          (by omega)
          (by omega)
          (sub_eq_zero.mp hsame))
  · have hmul : u * v = 1 := by
      have huv' : u = v⁻¹ :=
        sub_eq_zero.mp hinverse
      rw [huv']
      exact inv_mul_cancel₀ hv
    have hpow :
        QuaternionGroupFive.primitiveTenthRoot ^
            ((k.val + 1) + (l.val + 1)) = 1 := by
      rw [pow_add]
      exact hmul
    have hdvd :
        10 ∣ (k.val + 1) + (l.val + 1) :=
      (QuaternionGroupFive.primitiveTenthRoot_isPrimitive.pow_eq_one_iff_dvd
        _).mp hpow
    exact False.elim <|
      (Nat.not_dvd_of_pos_of_lt
        (by omega)
        (by omega)) hdvd

theorem quaternionIrreducibleCharacter_injective :
    Function.Injective quaternionIrreducibleCharacter := by
  intro r s hrs
  rcases r with j | k <;> rcases s with l | m
  · congr 1
    apply QuaternionGroupFive.linearCharacter_injective
    exact hrs
  · exfalso
    have hdegree :=
      congrArg
        (fun χ : IrreducibleCharacter (QuaternionGroup 5) =>
          χ.degree) hrs
    change
      (QuaternionGroupFive.linearCharacter j).degree =
        (QuaternionGroupFive.twoDimensionalCharacter m).degree
      at hdegree
    rw [
      QuaternionGroupFive.linearCharacter_degree,
      QuaternionGroupFive.twoDimensionalCharacter_degree
    ] at hdegree
    omega
  · exfalso
    have hdegree :=
      congrArg
        (fun χ : IrreducibleCharacter (QuaternionGroup 5) =>
          χ.degree) hrs
    change
      (QuaternionGroupFive.twoDimensionalCharacter k).degree =
        (QuaternionGroupFive.linearCharacter l).degree
      at hdegree
    rw [
      QuaternionGroupFive.twoDimensionalCharacter_degree,
      QuaternionGroupFive.linearCharacter_degree
    ] at hdegree
    omega
  · congr 1
    apply quaternionTwoDimensionalCharacter_injective
    exact hrs

/-- The dicyclic group has eight conjugacy classes.  The finite quotient
calculation is checked by the kernel evaluator. -/
theorem natCard_irreducibleCharacter_quaternionGroupFive :
    Nat.card (IrreducibleCharacter (QuaternionGroup 5)) = 8 := by
  rw [ClassFunction.natCard_irreducibleCharacter_eq_conjClasses]
  rw [Nat.card_eq_fintype_card]
  decide

theorem quaternionIrreducibleCharacter_bijective :
    Function.Bijective quaternionIrreducibleCharacter := by
  apply
    quaternionIrreducibleCharacter_injective.bijective_of_nat_card_le
  rw [natCard_irreducibleCharacter_quaternionGroupFive]
  rw [Nat.card_eq_fintype_card]
  decide

/-- Complete ordinary character enumeration of `QuaternionGroup 5`,
extracted from its eight explicit rows. -/
def quaternionIrreducibleCharacterEquiv :
    CharacterRow ≃ IrreducibleCharacter (QuaternionGroup 5) :=
  Equiv.ofBijective quaternionIrreducibleCharacter
    quaternionIrreducibleCharacter_bijective

/-- Complete ordinary character enumeration of the inversion semidirect
product. -/
def irreducibleCharacterEquiv :
    CharacterRow ≃ IrreducibleCharacter Group :=
  quaternionIrreducibleCharacterEquiv.trans
    (IrreducibleCharacter.comapEquiv
      quaternionFiveEquivCyclicFiveInversionSemidirect.symm)

@[simp]
theorem irreducibleCharacterEquiv_degree_linear (j : Fin 4) :
    (irreducibleCharacterEquiv (.linear j)).degree = 1 := by
  change (QuaternionGroupFive.linearCharacter j).degree = 1
  exact QuaternionGroupFive.linearCharacter_degree j

@[simp]
theorem irreducibleCharacterEquiv_degree_twoDimensional (k : Fin 4) :
    (irreducibleCharacterEquiv (.twoDimensional k)).degree = 2 := by
  change
    (QuaternionGroupFive.twoDimensionalCharacter k).degree = 2
  exact QuaternionGroupFive.twoDimensionalCharacter_degree k

/-- A semidirect-product row packaged with its `5'`-degree proof. -/
def pPrimeCharacter
    (r : CharacterRow) :
    PPrimeIrreducibleCharacter Group 5 :=
  ⟨irreducibleCharacterEquiv r, by
    cases r with
    | linear j =>
        rw [IrreducibleCharacter.IsPPrimeDegree,
          irreducibleCharacterEquiv_degree_linear]
        norm_num
    | twoDimensional k =>
        rw [IrreducibleCharacter.IsPPrimeDegree,
          irreducibleCharacterEquiv_degree_twoDimensional]
        norm_num⟩

/-- Complete `5'`-degree character enumeration of the inversion
semidirect product.  Surjectivity follows from the complete ordinary table,
since every row has degree one or two. -/
def pPrimeCharacterEquiv :
    CharacterRow ≃ PPrimeIrreducibleCharacter Group 5 where
  toFun := pPrimeCharacter
  invFun χ := irreducibleCharacterEquiv.symm χ.1
  left_inv r :=
    irreducibleCharacterEquiv.symm_apply_apply r
  right_inv χ := by
    apply Subtype.ext
    exact irreducibleCharacterEquiv.apply_symm_apply χ.1

@[simp]
theorem pPrimeCharacterEquiv_degree_linear (j : Fin 4) :
    (pPrimeCharacterEquiv (.linear j)).1.degree = 1 := by
  exact irreducibleCharacterEquiv_degree_linear j

@[simp]
theorem pPrimeCharacterEquiv_degree_twoDimensional (k : Fin 4) :
    (pPrimeCharacterEquiv (.twoDimensional k)).1.degree = 2 := by
  exact irreducibleCharacterEquiv_degree_twoDimensional k

/-- The normalized certificate attached to a transported semidirect-product
row. -/
def rowCertificate (r : CharacterRow) :
    CharacterRowCertificate Group := by
  letI : Simple (rowFDRep r) := rowFDRep_simple r
  exact CharacterRowCertificate.ofSimple (rowFDRep r)

theorem rowCertificate_irreducibleCharacter
    (r : CharacterRow) :
    (rowCertificate r).irreducibleCharacter =
      irreducibleCharacterEquiv r := by
  apply IrreducibleCharacter.ext
  funext g
  rw [(rowCertificate r).irreducibleCharacter_values_apply]
  change
    (rowFDRep r).character g =
      (irreducibleCharacterEquiv r).values g
  rw [rowFDRep_character]
  change
    (quaternionRowFDRep r).character
        (quaternionFiveEquivCyclicFiveInversionSemidirect.symm g) =
      (quaternionIrreducibleCharacter r).values
        (quaternionFiveEquivCyclicFiveInversionSemidirect.symm g)
  cases r with
  | linear j =>
      change
        (IrreducibleCharacter.linearFDRep
            (QuaternionGroupFive.linearHom j)).character
              (quaternionFiveEquivCyclicFiveInversionSemidirect.symm g) =
          (QuaternionGroupFive.linearCharacter j).values
            (quaternionFiveEquivCyclicFiveInversionSemidirect.symm g)
      rw [IrreducibleCharacter.linearFDRep_character]
      change
        (QuaternionGroupFive.linearHom j
            (quaternionFiveEquivCyclicFiveInversionSemidirect.symm g) : ℂ) =
          (IrreducibleCharacter.linear
            (QuaternionGroupFive.linearHom j)).values
              (quaternionFiveEquivCyclicFiveInversionSemidirect.symm g)
      rw [IrreducibleCharacter.linear_values]
  | twoDimensional k =>
      rfl

/-- Generic finite-table certificate for the eight transported rows. -/
def finiteCharacterTableCertificate :
    FiniteCharacterTableCertificate Group CharacterRow where
  row := rowCertificate
  row_injective := by
    intro r s hrs
    change
      (rowCertificate r).irreducibleCharacter =
        (rowCertificate s).irreducibleCharacter at hrs
    apply irreducibleCharacterEquiv.injective
    rw [← rowCertificate_irreducibleCharacter r,
      ← rowCertificate_irreducibleCharacter s]
    exact hrs
  row_count := by
    calc
      Nat.card CharacterRow =
          Nat.card (IrreducibleCharacter Group) :=
        Nat.card_congr irreducibleCharacterEquiv
      _ = Nat.card (ConjClasses Group) :=
        ClassFunction.natCard_irreducibleCharacter_eq_conjClasses

end CyclicFiveInversionSemidirect
end McKayConjecture
