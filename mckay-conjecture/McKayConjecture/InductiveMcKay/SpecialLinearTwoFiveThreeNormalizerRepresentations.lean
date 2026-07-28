/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Construction
import McKayConjecture.Character.Finiteness
import McKayConjecture.Character.IrreducibleCharacterBasis
import McKayConjecture.Character.Linear
import McKayConjecture.Character.Transport
import McKayConjecture.GroupTheory.SpecialLinearTwoFiveSylowThreeNormalizer
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.RepresentationTheory.FinGroupCharZero

/-!
# Explicit representations of the Sylow-three normalizer

This file constructs the six ordinary irreducible rows of the generalized
quaternion group `QuaternionGroup 3`, hence of the exact Sylow `3`-normalizer
in `SL(2, 𝔽₅)`.

The four linear rows factor through the explicit abelianization map to
`ZMod 4`.  The two remaining rows are the usual two-dimensional dicyclic
representations, with the cyclic generator acting with eigenvalues
`ζ^k, ζ⁻ᵏ` for `k = 1, 2` and `ζ` a primitive sixth root of unity.
-/

noncomputable section

open CategoryTheory Matrix
open scoped MatrixGroups

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The six normalizer character rows, separated into the four linear and
two two-dimensional rows. -/
inductive QuaternionGroupThreeCharacterRow
  | linear (j : ZMod 4)
  | twoDimensional (k : Fin 2)
  deriving DecidableEq, Fintype

/-- The abelianization coordinate `Q₁₂ → C₄` in concrete normal form:
`a ↦ 2` and `x ↦ 1`. -/
def quaternionGroupThreeAbelianization :
    QuaternionGroup 3 →* Multiplicative (ZMod 4) where
  toFun
    | QuaternionGroup.a i =>
        Multiplicative.ofAdd (2 * (i.val : ZMod 4))
    | QuaternionGroup.xa i =>
        Multiplicative.ofAdd (1 + 2 * (i.val : ZMod 4))
  map_one' := by native_decide
  map_mul' := by native_decide

/-- The complex unit character of `C₄` with frequency `j`. -/
def zmodFourComplexUnitCharacter (j : ZMod 4) :
    Multiplicative (ZMod 4) →* ℂˣ where
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

/-- The four explicit linear characters of `QuaternionGroup 3`. -/
def quaternionGroupThreeLinearHom (j : ZMod 4) :
    QuaternionGroup 3 →* ℂˣ :=
  (zmodFourComplexUnitCharacter j).comp
    quaternionGroupThreeAbelianization

/-- The standard primitive sixth-root additive character used in the
two-dimensional matrices. -/
abbrev quaternionGroupThreeSixthRootCharacter :
    AddChar (ZMod 6) ℂ :=
  ZMod.stdAddChar

theorem quaternionGroupThreeSixthRootCharacter_add
    (i j : ZMod 6) :
    quaternionGroupThreeSixthRootCharacter (i + j) =
      quaternionGroupThreeSixthRootCharacter i *
        quaternionGroupThreeSixthRootCharacter j :=
  AddChar.map_add_eq_mul _ _ _

theorem quaternionGroupThreeSixthRootCharacter_neg
    (i : ZMod 6) :
    quaternionGroupThreeSixthRootCharacter (-i) =
      (quaternionGroupThreeSixthRootCharacter i)⁻¹ :=
  AddChar.map_neg_eq_inv _ _

theorem quaternionGroupThreeSixthRootCharacter_sub
    (i j : ZMod 6) :
    quaternionGroupThreeSixthRootCharacter (i - j) =
      quaternionGroupThreeSixthRootCharacter i /
        quaternionGroupThreeSixthRootCharacter j :=
  AddChar.map_sub_eq_div _ _ _

/-- A ring identity between exponents proves the corresponding
multiplicative identity of sixth-root values. -/
theorem quaternionGroupThreeSixthRootCharacter_eq_mul_of_eq_add
    {i j k : ZMod 6} (h : i = j + k) :
    quaternionGroupThreeSixthRootCharacter i =
      quaternionGroupThreeSixthRootCharacter j *
        quaternionGroupThreeSixthRootCharacter k := by
  rw [h]
  exact quaternionGroupThreeSixthRootCharacter_add j k

/-- Multiplication by three in `ZMod 6` is its own additive inverse. -/
theorem zmodSix_neg_mul_three (k : ZMod 6) :
    -(k * 3) = k * 3 := by
  fin_cases k <;> native_decide

/-- The matrix of the dicyclic representation with frequency `k`.

The formula is written directly on the `a i`/`xa i` normal forms. -/
def quaternionGroupThreeTwoMatrix (k : ZMod 6) :
    QuaternionGroup 3 → Matrix (Fin 2) (Fin 2) ℂ
  | QuaternionGroup.a i =>
      !![
        quaternionGroupThreeSixthRootCharacter (k * i), 0;
        0, quaternionGroupThreeSixthRootCharacter (-(k * i))]
  | QuaternionGroup.xa i =>
      !![
        0,
          quaternionGroupThreeSixthRootCharacter
            (3 * k - k * i);
        quaternionGroupThreeSixthRootCharacter (k * i), 0]

/-- The explicit matrices preserve multiplication. -/
theorem quaternionGroupThreeTwoMatrix_mul
    (k : ZMod 6) (g h : QuaternionGroup 3) :
    quaternionGroupThreeTwoMatrix k (g * h) =
      quaternionGroupThreeTwoMatrix k g *
        quaternionGroupThreeTwoMatrix k h := by
  rcases g with i | i <;> rcases h with j | j
  all_goals
    ext r c
    fin_cases r <;> fin_cases c <;>
    simp [quaternionGroupThreeTwoMatrix,
      QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_xa,
      QuaternionGroup.xa_mul_a, QuaternionGroup.xa_mul_xa,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    apply
      quaternionGroupThreeSixthRootCharacter_eq_mul_of_eq_add <;>
      first
      | (ring; done)
      | (ring_nf; rw [zmodSix_neg_mul_three])

/-- The two-dimensional representation with frequency `k`. -/
def quaternionGroupThreeTwoRepresentation (k : ZMod 6) :
    Representation ℂ (QuaternionGroup 3) (Fin 2 → ℂ) where
  toFun g :=
    Matrix.toLin'
      (quaternionGroupThreeTwoMatrix k g)
  map_one' := by
    rw [QuaternionGroup.one_def]
    rw [show
      quaternionGroupThreeTwoMatrix k (QuaternionGroup.a 0) =
          (1 : Matrix (Fin 2) (Fin 2) ℂ) by
        ext r c
        fin_cases r <;> fin_cases c <;>
          simp [quaternionGroupThreeTwoMatrix]]
    exact Matrix.toLin'_one
  map_mul' g h := by
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
      ← quaternionGroupThreeTwoMatrix_mul]

/-- The corresponding finite-dimensional representation object. -/
abbrev quaternionGroupThreeTwoFDRep (k : ZMod 6) :
    FDRep ℂ (QuaternionGroup 3) :=
  FDRep.of (quaternionGroupThreeTwoRepresentation k)

/-- The trace on a cyclic normal-form element. -/
theorem quaternionGroupThreeTwoFDRep_character_a
    (k i : ZMod 6) :
    (quaternionGroupThreeTwoFDRep k).character
        (QuaternionGroup.a i) =
      quaternionGroupThreeSixthRootCharacter (k * i) +
        quaternionGroupThreeSixthRootCharacter (-(k * i)) := by
  rw [show
    (quaternionGroupThreeTwoFDRep k).character
        (QuaternionGroup.a i) =
      LinearMap.trace ℂ (Fin 2 → ℂ)
        (Matrix.toLin'
          (quaternionGroupThreeTwoMatrix k
            (QuaternionGroup.a i))) by rfl,
    Matrix.trace_toLin'_eq]
  simp [quaternionGroupThreeTwoMatrix,
    Matrix.trace, Fin.sum_univ_two]

/-- The trace vanishes on the other normal-form coset. -/
theorem quaternionGroupThreeTwoFDRep_character_xa
    (k i : ZMod 6) :
    (quaternionGroupThreeTwoFDRep k).character
        (QuaternionGroup.xa i) = 0 := by
  rw [show
    (quaternionGroupThreeTwoFDRep k).character
        (QuaternionGroup.xa i) =
      LinearMap.trace ℂ (Fin 2 → ℂ)
        (Matrix.toLin'
          (quaternionGroupThreeTwoMatrix k
            (QuaternionGroup.xa i))) by rfl,
    Matrix.trace_toLin'_eq]
  simp [quaternionGroupThreeTwoMatrix,
    Matrix.trace, Fin.sum_univ_two]

/-- Both explicit matrix representations have dimension two. -/
theorem quaternionGroupThreeTwoFDRep_finrank (k : ZMod 6) :
    Module.finrank ℂ (quaternionGroupThreeTwoFDRep k) = 2 := by
  simp [quaternionGroupThreeTwoFDRep]

/-- The public normal-form equivalence used to split finite sums over
`QuaternionGroup 3`. -/
def quaternionGroupThreeNormalFormEquiv :
    (ZMod 6 ⊕ ZMod 6) ≃ QuaternionGroup 3 where
  toFun
    | Sum.inl i => QuaternionGroup.a i
    | Sum.inr i => QuaternionGroup.xa i
  invFun
    | QuaternionGroup.a i => Sum.inl i
    | QuaternionGroup.xa i => Sum.inr i
  left_inv x := by rcases x with i | i <;> rfl
  right_inv x := by rcases x with i | i <;> rfl

/-- Split a sum over generalized quaternion normal forms into the cyclic
subgroup and its other coset. -/
theorem quaternionGroupThree_sum_normalForms
    {R : Type*} [AddCommMonoid R]
    (f : QuaternionGroup 3 → R) :
    (∑ g : QuaternionGroup 3, f g) =
      (∑ i : ZMod 6, f (QuaternionGroup.a i)) +
        ∑ i : ZMod 6, f (QuaternionGroup.xa i) := by
  calc
    (∑ g : QuaternionGroup 3, f g) =
        ∑ x : ZMod 6 ⊕ ZMod 6,
          f (quaternionGroupThreeNormalFormEquiv x) :=
      (quaternionGroupThreeNormalFormEquiv.sum_comp f).symm
    _ = _ := by
      rw [Fintype.sum_sum_type]
      rfl

@[simp]
theorem quaternionGroupThree_inv_a (i : ZMod 6) :
    (QuaternionGroup.a i : QuaternionGroup 3)⁻¹ =
      QuaternionGroup.a (-i) :=
  rfl

@[simp]
theorem quaternionGroupThree_inv_xa (i : ZMod 6) :
    (QuaternionGroup.xa i : QuaternionGroup 3)⁻¹ =
      QuaternionGroup.xa (3 + i) :=
  rfl

/-- The contribution of one cyclic normal-form element to the character
self-pairing. -/
theorem quaternionGroupThreeTwoFDRep_character_mul_inv_a
    (k i : ZMod 6) :
    (quaternionGroupThreeTwoFDRep k).character
          (QuaternionGroup.a i) *
        (quaternionGroupThreeTwoFDRep k).character
          (QuaternionGroup.a i)⁻¹ =
      quaternionGroupThreeSixthRootCharacter
          ((2 * k) * i) +
        2 +
        quaternionGroupThreeSixthRootCharacter
          ((-(2 * k)) * i) := by
  rw [quaternionGroupThree_inv_a,
    quaternionGroupThreeTwoFDRep_character_a,
    quaternionGroupThreeTwoFDRep_character_a]
  rw [show k * (-i) = -(k * i) by ring, neg_neg]
  let x : ZMod 6 := k * i
  change
    (quaternionGroupThreeSixthRootCharacter x +
        quaternionGroupThreeSixthRootCharacter (-x)) *
      (quaternionGroupThreeSixthRootCharacter (-x) +
        quaternionGroupThreeSixthRootCharacter x) =
      quaternionGroupThreeSixthRootCharacter ((2 * k) * i) +
        2 +
        quaternionGroupThreeSixthRootCharacter
          ((-(2 * k)) * i)
  calc
    _ =
        quaternionGroupThreeSixthRootCharacter x *
            quaternionGroupThreeSixthRootCharacter x +
          quaternionGroupThreeSixthRootCharacter x *
            quaternionGroupThreeSixthRootCharacter (-x) +
          quaternionGroupThreeSixthRootCharacter (-x) *
            quaternionGroupThreeSixthRootCharacter x +
          quaternionGroupThreeSixthRootCharacter (-x) *
            quaternionGroupThreeSixthRootCharacter (-x) := by
          ring
    _ =
        quaternionGroupThreeSixthRootCharacter (x + x) +
          quaternionGroupThreeSixthRootCharacter (x + -x) +
          quaternionGroupThreeSixthRootCharacter (-x + x) +
          quaternionGroupThreeSixthRootCharacter (-x + -x) := by
          rw [quaternionGroupThreeSixthRootCharacter_add,
            quaternionGroupThreeSixthRootCharacter_add,
            quaternionGroupThreeSixthRootCharacter_add,
            quaternionGroupThreeSixthRootCharacter_add]
    _ = _ := by
      rw [show x + x = (2 * k) * i by
          dsimp [x]
          ring,
        show -x + -x = (-(2 * k)) * i by
          dsimp [x]
          ring,
        add_neg_cancel, neg_add_cancel,
        AddChar.map_zero_eq_one]
      ring

/-- The character self-pairing of either two-dimensional row is the group
order whenever its frequency is `1` or `2` modulo inversion. -/
theorem quaternionGroupThreeTwoFDRep_character_norm
    (k : ZMod 6) (hk : 2 * k ≠ 0) :
    (∑ g : QuaternionGroup 3,
        (quaternionGroupThreeTwoFDRep k).character g *
          (quaternionGroupThreeTwoFDRep k).character g⁻¹) =
      (12 : ℂ) := by
  rw [quaternionGroupThree_sum_normalForms]
  simp only [quaternionGroupThreeTwoFDRep_character_mul_inv_a,
    quaternionGroupThreeTwoFDRep_character_xa,
    zero_mul, Finset.sum_const_zero, add_zero]
  have hpos :
      (∑ i : ZMod 6,
        quaternionGroupThreeSixthRootCharacter
          (i * (2 * k))) = 0 := by
    simpa [hk] using
      (AddChar.sum_mulShift (2 * k)
        (ZMod.isPrimitive_stdAddChar 6))
  have hneg :
      (∑ i : ZMod 6,
        quaternionGroupThreeSixthRootCharacter
          (i * (-(2 * k)))) = 0 := by
    have hnegk : -(2 * k) ≠ 0 :=
      neg_ne_zero.mpr hk
    simpa [hnegk] using
      (AddChar.sum_mulShift (-(2 * k))
        (ZMod.isPrimitive_stdAddChar 6))
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp_rw [mul_comm (2 * k), mul_comm (-(2 * k))]
  rw [hpos, hneg]
  norm_num

/-- The explicit frequency-`1` and frequency-`2` representations are
simple. -/
theorem quaternionGroupThreeTwoFDRep_simple
    (k : ZMod 6) (hk : 2 * k ≠ 0) :
    Simple (quaternionGroupThreeTwoFDRep k) := by
  rw [FDRep.simple_iff_char_is_norm_one]
  rw [quaternionGroupThreeTwoFDRep_character_norm k hk]
  norm_num [Nat.card_eq_fintype_card, QuaternionGroup.card]

/-- Frequency attached to the two non-linear row indices. -/
def quaternionGroupThreeTwoFrequency (k : Fin 2) : ZMod 6 :=
  k.val + 1

/-- Both selected frequencies meet the irreducibility criterion. -/
theorem quaternionGroupThreeTwoFrequency_ne
    (k : Fin 2) :
    2 * quaternionGroupThreeTwoFrequency k ≠ 0 := by
  fin_cases k <;> native_decide

/-- The two explicit non-linear irreducible characters. -/
def quaternionGroupThreeTwoIrreducibleCharacter (k : Fin 2) :
    IrreducibleCharacter (QuaternionGroup 3) := by
  letI :
      Simple
        (quaternionGroupThreeTwoFDRep
          (quaternionGroupThreeTwoFrequency k)) :=
    quaternionGroupThreeTwoFDRep_simple _
      (quaternionGroupThreeTwoFrequency_ne k)
  exact
    IrreducibleCharacter.ofSimple
      (quaternionGroupThreeTwoFDRep
        (quaternionGroupThreeTwoFrequency k))

@[simp]
theorem quaternionGroupThreeTwoIrreducibleCharacter_degree
    (k : Fin 2) :
    (quaternionGroupThreeTwoIrreducibleCharacter k).degree = 2 := by
  change
    Module.finrank ℂ
      (quaternionGroupThreeTwoFDRep
        (quaternionGroupThreeTwoFrequency k)) = 2
  exact quaternionGroupThreeTwoFDRep_finrank _

@[simp]
theorem quaternionGroupThreeTwoIrreducibleCharacter_values_a
    (k : Fin 2) (i : ZMod 6) :
    (quaternionGroupThreeTwoIrreducibleCharacter k).values
        (QuaternionGroup.a i) =
      quaternionGroupThreeSixthRootCharacter
          (quaternionGroupThreeTwoFrequency k * i) +
        quaternionGroupThreeSixthRootCharacter
          (-(quaternionGroupThreeTwoFrequency k * i)) := by
  change
    (quaternionGroupThreeTwoFDRep
      (quaternionGroupThreeTwoFrequency k)).character
        (QuaternionGroup.a i) = _
  exact quaternionGroupThreeTwoFDRep_character_a _ _

@[simp]
theorem quaternionGroupThreeTwoIrreducibleCharacter_values_xa
    (k : Fin 2) (i : ZMod 6) :
    (quaternionGroupThreeTwoIrreducibleCharacter k).values
        (QuaternionGroup.xa i) = 0 := by
  change
    (quaternionGroupThreeTwoFDRep
      (quaternionGroupThreeTwoFrequency k)).character
        (QuaternionGroup.xa i) = 0
  exact quaternionGroupThreeTwoFDRep_character_xa _ _

/-- The four linear parameters give four distinct homomorphisms. -/
theorem quaternionGroupThreeLinearHom_injective :
    Function.Injective quaternionGroupThreeLinearHom := by
  intro j l h
  have hx :=
    DFunLike.congr_fun h
      (QuaternionGroup.xa (0 : ZMod 6))
  have hval := congrArg Units.val hx
  have hcircle :
      (ZMod.toCircle j : ℂ) =
        (ZMod.toCircle l : ℂ) := by
    simpa [quaternionGroupThreeLinearHom,
      quaternionGroupThreeAbelianization,
      zmodFourComplexUnitCharacter] using hval
  exact ZMod.injective_toCircle (Circle.ext hcircle)

/-- A linear row, packaged directly as a `3'`-degree irreducible
character. -/
def quaternionGroupThreeLinearPPrimeCharacter (j : ZMod 4) :
    PPrimeIrreducibleCharacter (QuaternionGroup 3) 3 :=
  ⟨IrreducibleCharacter.linear
      (quaternionGroupThreeLinearHom j),
    IrreducibleCharacter.linear_isPPrimeDegree
      (quaternionGroupThreeLinearHom j) 3⟩

@[simp]
theorem quaternionGroupThreeLinearPPrimeCharacter_degree
    (j : ZMod 4) :
    (quaternionGroupThreeLinearPPrimeCharacter j).1.degree = 1 :=
  IrreducibleCharacter.linear_degree _

@[simp]
theorem quaternionGroupThreeLinearPPrimeCharacter_values_a
    (j : ZMod 4) (i : ZMod 6) :
    (quaternionGroupThreeLinearPPrimeCharacter j).1.values
        (QuaternionGroup.a i) =
      (ZMod.toCircle
        (j * (2 * (i.val : ZMod 4))) : ℂ) := by
  change
    (IrreducibleCharacter.linear
        (quaternionGroupThreeLinearHom j)).values
      (QuaternionGroup.a i) = _
  rw [IrreducibleCharacter.linear_values]
  rfl

@[simp]
theorem quaternionGroupThreeLinearPPrimeCharacter_values_xa
    (j : ZMod 4) (i : ZMod 6) :
    (quaternionGroupThreeLinearPPrimeCharacter j).1.values
        (QuaternionGroup.xa i) =
      (ZMod.toCircle
        (j * (1 + 2 * (i.val : ZMod 4))) : ℂ) := by
  change
    (IrreducibleCharacter.linear
        (quaternionGroupThreeLinearHom j)).values
      (QuaternionGroup.xa i) = _
  rw [IrreducibleCharacter.linear_values]
  rfl

/-- A two-dimensional row, packaged directly as a `3'`-degree irreducible
character. -/
def quaternionGroupThreeTwoPPrimeCharacter (k : Fin 2) :
    PPrimeIrreducibleCharacter (QuaternionGroup 3) 3 :=
  ⟨quaternionGroupThreeTwoIrreducibleCharacter k, by
    rw [IrreducibleCharacter.IsPPrimeDegree,
      quaternionGroupThreeTwoIrreducibleCharacter_degree]
    norm_num⟩

@[simp]
theorem quaternionGroupThreeTwoPPrimeCharacter_degree
    (k : Fin 2) :
    (quaternionGroupThreeTwoPPrimeCharacter k).1.degree = 2 :=
  quaternionGroupThreeTwoIrreducibleCharacter_degree k

/-- The two nonlinear rows are distinct. -/
theorem quaternionGroupThreeTwoPPrimeCharacter_injective :
    Function.Injective quaternionGroupThreeTwoPPrimeCharacter := by
  have hne :
      quaternionGroupThreeTwoPPrimeCharacter
          (0 : Fin 2) ≠
        quaternionGroupThreeTwoPPrimeCharacter
          (1 : Fin 2) := by
    intro h
    have hv :=
      congrArg
        (fun χ :
            PPrimeIrreducibleCharacter
              (QuaternionGroup 3) 3 =>
          χ.1.values
            (QuaternionGroup.a (3 : ZMod 6))) h
    simp only [quaternionGroupThreeTwoPPrimeCharacter,
      quaternionGroupThreeTwoIrreducibleCharacter_values_a] at hv
    have hfrequencyZero :
        quaternionGroupThreeTwoFrequency
            (0 : Fin 2) = 1 := by native_decide
    have hfrequencyOne :
        quaternionGroupThreeTwoFrequency
            (1 : Fin 2) = 2 := by native_decide
    have honeMulThree :
        (1 : ZMod 6) * 3 = 3 := by native_decide
    have htwoMulThree :
        (2 : ZMod 6) * 3 = 0 := by native_decide
    have hnegThree :
        -(3 : ZMod 6) = 3 := by native_decide
    have hv' :
        quaternionGroupThreeSixthRootCharacter
              (3 : ZMod 6) +
            quaternionGroupThreeSixthRootCharacter
              (3 : ZMod 6) =
          quaternionGroupThreeSixthRootCharacter
              (0 : ZMod 6) +
            quaternionGroupThreeSixthRootCharacter
              (0 : ZMod 6) := by
      simpa only [hfrequencyZero, hfrequencyOne, honeMulThree,
        htwoMulThree, hnegThree, neg_zero] using hv
    have hroot :
        quaternionGroupThreeSixthRootCharacter
            (3 : ZMod 6) =
          quaternionGroupThreeSixthRootCharacter
            (0 : ZMod 6) := by
      linear_combination (1 / 2 : ℂ) * hv'
    exact
      (by native_decide :
        (3 : ZMod 6) ≠ 0)
        (ZMod.injective_stdAddChar hroot)
  intro k l h
  fin_cases k <;> fin_cases l
  · rfl
  · exact (hne h).elim
  · exact (hne h.symm).elim
  · rfl

/-- The explicit `3'`-row associated with a six-element table index. -/
def quaternionGroupThreePPrimeCharacter :
    QuaternionGroupThreeCharacterRow →
      PPrimeIrreducibleCharacter (QuaternionGroup 3) 3
  | .linear j =>
      quaternionGroupThreeLinearPPrimeCharacter j
  | .twoDimensional k =>
      quaternionGroupThreeTwoPPrimeCharacter k

@[simp]
theorem quaternionGroupThreePPrimeCharacter_degree_linear
    (j : ZMod 4) :
    (quaternionGroupThreePPrimeCharacter
      (.linear j)).1.degree = 1 :=
  quaternionGroupThreeLinearPPrimeCharacter_degree j

@[simp]
theorem quaternionGroupThreePPrimeCharacter_degree_twoDimensional
    (k : Fin 2) :
    (quaternionGroupThreePPrimeCharacter
      (.twoDimensional k)).1.degree = 2 :=
  quaternionGroupThreeTwoPPrimeCharacter_degree k

/-- The six explicit rows are pairwise distinct. -/
theorem quaternionGroupThreePPrimeCharacter_injective :
    Function.Injective quaternionGroupThreePPrimeCharacter := by
  intro r s h
  rcases r with j | k <;> rcases s with l | m
  · congr 1
    apply quaternionGroupThreeLinearHom_injective
    apply IrreducibleCharacter.linear_injective
    exact congrArg Subtype.val h
  · exfalso
    have hdegree :=
      congrArg
        (fun χ :
            PPrimeIrreducibleCharacter
              (QuaternionGroup 3) 3 =>
          χ.1.degree) h
    norm_num at hdegree
  · exfalso
    have hdegree :=
      congrArg
        (fun χ :
            PPrimeIrreducibleCharacter
              (QuaternionGroup 3) 3 =>
          χ.1.degree) h
    norm_num at hdegree
  · congr 1
    exact
      quaternionGroupThreeTwoPPrimeCharacter_injective h

/-- The generalized quaternion group of order twelve has exactly six
conjugacy classes, hence exactly six ordinary irreducible characters. -/
theorem natCard_irreducibleCharacter_quaternionGroupThree :
    Nat.card (IrreducibleCharacter (QuaternionGroup 3)) = 6 := by
  rw [ClassFunction.natCard_irreducibleCharacter_eq_conjClasses]
  rw [Nat.card_eq_fintype_card]
  native_decide

/-- The explicit six rows exhaust all `3'`-degree irreducible characters of
`QuaternionGroup 3`.  In particular, every ordinary irreducible character of
this group has degree prime to three. -/
theorem quaternionGroupThreePPrimeCharacter_bijective :
    Function.Bijective quaternionGroupThreePPrimeCharacter := by
  apply
    quaternionGroupThreePPrimeCharacter_injective.bijective_of_nat_card_le
  have hrows :
      Nat.card QuaternionGroupThreeCharacterRow = 6 := by
    rw [Nat.card_eq_fintype_card]
    native_decide
  have hpPrimeLe :
      Nat.card
          (PPrimeIrreducibleCharacter
            (QuaternionGroup 3) 3) ≤
        Nat.card
          (IrreducibleCharacter
            (QuaternionGroup 3)) :=
    Nat.card_le_card_of_injective
      (fun χ :
          PPrimeIrreducibleCharacter
            (QuaternionGroup 3) 3 => χ.1)
      Subtype.val_injective
  have hirreducible :=
    natCard_irreducibleCharacter_quaternionGroupThree
  omega

/-- The concrete six-row indexing equivalence for the `3'`-characters of
`QuaternionGroup 3`. -/
def quaternionGroupThreePPrimeCharacterEquiv :
    QuaternionGroupThreeCharacterRow ≃
      PPrimeIrreducibleCharacter (QuaternionGroup 3) 3 :=
  Equiv.ofBijective quaternionGroupThreePPrimeCharacter
    quaternionGroupThreePPrimeCharacter_bijective

@[simp]
theorem quaternionGroupThreePPrimeCharacterEquiv_apply
    (r : QuaternionGroupThreeCharacterRow) :
    quaternionGroupThreePPrimeCharacterEquiv r =
      quaternionGroupThreePPrimeCharacter r :=
  rfl

end InductiveMcKay
end McKayConjecture
