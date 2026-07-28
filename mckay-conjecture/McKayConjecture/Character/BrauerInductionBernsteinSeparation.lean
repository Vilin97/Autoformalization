/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerInductionBernsteinIdealMembership
import McKayConjecture.Character.BrauerInductionCyclotomicIdealDescent
import McKayConjecture.Character.IntegerClassFunctionLattice

/-!
# Separating the constant one function from Bernstein congruences

For each prime power `p ^ m`, the Euler power of the Bernstein element is
in the elementary-induction ideal and is pointwise congruent to one modulo
`p ^ m`.  The pointwise integral quotients form an integer class function.
The finite-rank lattice separation theorem therefore produces an actual
element of the ideal whose underlying complex class function is one.

The additive-closure description of the ideal then supplies an explicit
cyclotomic elementary expansion of the constant-one class function.
-/

noncomputable section

namespace McKayConjecture
namespace ClassFunction

variable {p : ℕ}
variable {G : Type} [Group G] [Finite G] [Fact p.Prime]

/-- The integral correction at one element in the pointwise Euler
congruence.  Its sign is chosen so that
`1 = B^(φ(p^m)) + p^m * correction`. -/
def bernsteinEulerCorrectionValue
    (m : ℕ) (g : G) : ℤ :=
  -Classical.choose
    (exists_int_bernsteinElement_pow_eq_one_add_primePower_mul
      (p := p) m g)

/-- The chosen correction value satisfies the exact complex equality
associated to the Euler congruence. -/
theorem bernsteinEulerCorrectionValue_spec
    (m : ℕ) (g : G) :
    (1 : ℂ) =
      bernsteinElement (p := p) (G := G) g ^
          (p ^ m).totient +
        (p ^ m : ℂ) *
          (bernsteinEulerCorrectionValue
            (p := p) m g : ℂ) := by
  let z : ℤ :=
    Classical.choose
      (exists_int_bernsteinElement_pow_eq_one_add_primePower_mul
        (p := p) m g)
  have hz :
      bernsteinElement (p := p) (G := G) g ^
          (p ^ m).totient =
        1 + (p ^ m : ℂ) * (z : ℂ) :=
    Classical.choose_spec
      (exists_int_bernsteinElement_pow_eq_one_add_primePower_mul
        (p := p) m g)
  change
    (1 : ℂ) =
      bernsteinElement (p := p) (G := G) g ^
          (p ^ m).totient +
        (p ^ m : ℂ) * ((-z : ℤ) : ℂ)
  rw [hz]
  push_cast
  ring

/-- The pointwise Euler corrections are invariant under conjugation and
hence form an integer class function. -/
def bernsteinEulerCorrection
    (m : ℕ) :
    IntegerClassFunction G := by
  refine
    ⟨bernsteinEulerCorrectionValue
        (p := p) m,
      ?_⟩
  intro g h
  apply Int.cast_injective (α := ℂ)
  have hfactor :
      (p ^ m : ℂ) ≠ 0 := by
    exact
      (by
        simpa only [Nat.cast_pow] using
          ((Nat.cast_ne_zero (R := ℂ)).mpr
            (pow_ne_zero m
              (Fact.out : p.Prime).ne_zero)))
  apply mul_left_cancel₀ hfactor
  calc
    (p ^ m : ℂ) *
          (bernsteinEulerCorrectionValue
            (p := p) m (h * g * h⁻¹) : ℂ) =
        1 -
          bernsteinElement (p := p) (G := G)
              (h * g * h⁻¹) ^
            (p ^ m).totient := by
      rw [bernsteinEulerCorrectionValue_spec
        (p := p) m (h * g * h⁻¹)]
      ring
    _ =
        1 -
          bernsteinElement (p := p) (G := G) g ^
            (p ^ m).totient := by
      rw [ClassFunction.conj_apply]
    _ =
        (p ^ m : ℂ) *
          (bernsteinEulerCorrectionValue
            (p := p) m g : ℂ) := by
      rw [bernsteinEulerCorrectionValue_spec
        (p := p) m g]
      ring

/-- In the integer class-function lattice, one differs from the Euler
power of the Bernstein element by `p ^ m` times the integral correction. -/
theorem bernsteinEulerPower_integerClassFunction_congruence
    (m : ℕ) :
    IntegerClassFunction.one (G := G) =
      cyclotomicIntegerCharacterToIntegerClassFunction
          (Nat.card G) Nat.card_pos
          (bernsteinElementInCyclotomicIntegerCharacterRing
              (p := p) (G := G) ^
            (p ^ m).totient) +
        p ^ m • bernsteinEulerCorrection
          (p := p) (G := G) m := by
  apply IntegerClassFunction.toComplexAddMonoidHom_injective
  apply ClassFunction.ext
  intro g
  simp only [
    IntegerClassFunction.toComplex_one,
    map_add, map_nsmul,
    toComplex_cyclotomicIntegerCharacterToIntegerClassFunction,
    Subring.coe_pow,
    bernsteinElementInCyclotomicIntegerCharacterRing_coe,
    ClassFunction.one_apply,
    ClassFunction.add_apply,
    ClassFunction.pow_apply,
    nsmul_eq_mul,
    Nat.cast_pow]
  exact
    bernsteinEulerCorrectionValue_spec
      (p := p) m g

variable (G)

/-- Bernstein's prime-power congruences and finite-rank separation produce
an actual member of `J_|G|(G)` equal to the constant-one class function. -/
theorem exists_bernsteinIdeal_member_eq_one :
    ∃ q :
        cyclotomicIntegerCharacterSubring
          (G := G) (Nat.card G) Nat.card_pos,
      q ∈ cyclotomicElementaryInductionIdeal
          (G := G) (n := Nat.card G)
          (hn := Nat.card_pos) ∧
      (q : ClassFunction G) = 1 := by
  apply
    exists_cyclotomicIdeal_member_eq_one_of_congruences
      (G := G) (Nat.card G) Nat.card_pos
  intro p hp m
  letI : Fact p.Prime := ⟨hp⟩
  let q :
      cyclotomicIntegerCharacterSubring
        (G := G) (Nat.card G) Nat.card_pos :=
    bernsteinElementInCyclotomicIntegerCharacterRing
        (p := p) (G := G) ^
      (p ^ m).totient
  refine
    ⟨q,
      bernsteinElement_totientPrimePower_mem_cyclotomicElementaryInductionIdeal
        (p := p) (G := G) m,
      bernsteinEulerCorrection (p := p) (G := G) m,
      ?_⟩
  exact
    bernsteinEulerPower_integerClassFunction_congruence
      (p := p) (G := G) m

/-- The separated ideal element yields a finite cyclotomic elementary
expansion of the constant-one class function. -/
theorem exists_elementaryCyclotomicCoefficients_one :
    ∃ c : ElementaryInductionTerm G →₀
        CyclotomicCoefficientRing (Nat.card G),
      (1 : ClassFunction G) =
        evaluateElementaryInductionCombinationOver
          (Nat.card G) Nat.card_pos c := by
  obtain ⟨q, hq, hqone⟩ :=
    exists_bernsteinIdeal_member_eq_one G
  obtain ⟨c, hc⟩ :=
    exists_elementaryCyclotomicCoefficients_of_mem_ideal
      q hq
  exact ⟨c, hqone.symm.trans hc⟩

end ClassFunction
end McKayConjecture
