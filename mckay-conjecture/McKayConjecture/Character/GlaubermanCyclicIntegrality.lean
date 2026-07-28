/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ClassFunctionPairingIntegrality
import McKayConjecture.Character.FiniteOrderTraceIntegrality
import McKayConjecture.Character.GaloisTraceEquivariance
import McKayConjecture.Character.GlaubermanCyclicCoefficientTrace

/-!
# Arithmetic precursors for cyclic Glauberman Fourier coefficients

The determinant-normalized cyclic trace is the restriction of an
ordinary extension character to the generator coset.  Consequently its
values, and the values of every irreducible character of the fixed-point
group, are algebraic integers.  This proves algebraic integrality of the
unnormalized Fourier coefficient.

More strongly, the normalized coefficient is the trace of a finite-order
endomorphism, so it is itself an algebraic integer.  The final theorem
below packages the remaining rationality input needed to conclude that
the coefficient is an ordinary integer.
-/

noncomputable section

open IntermediateField

namespace McKayConjecture

variable {G : Type} [Group G] [Finite G]
variable (K P : Subgroup G) [K.Normal]
variable [IsCyclic P]
variable {p : ℕ} [Fact p.Prime]

/-- The irreducible Fourier coefficient of the
determinant-normalized cyclic trace. -/
def determinantNormalizedCyclicFourierCoefficient
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (ψ : IrreducibleCharacter
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G))) :
    ℂ :=
  ClassFunction.normalizedPairing
    (determinantNormalizedCyclicTrace
      K P hK hP hgenerate θ)
    ψ.toClassFunction

/-- The group order times a Fourier coefficient of the
determinant-normalized cyclic trace is an algebraic integer. -/
theorem isIntegral_card_mul_normalizedPairing_determinantNormalizedCyclicTrace
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (ψ : IrreducibleCharacter
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G))) :
    IsIntegral ℤ
      ((Nat.card
          (cyclicFixedPoints K
            ((cyclicSubgroupGenerator P : P) : G)) : ℂ) *
        ClassFunction.normalizedPairing
          (determinantNormalizedCyclicTrace
            K P hK hP hgenerate θ)
          ψ.toClassFunction) := by
  apply ClassFunction.isIntegral_card_mul_normalizedPairing
  · intro c
    rw [determinantNormalizedCyclicTrace_eq_extensionCharacter]
    exact
      IrreducibleCharacter.isIntegral_value
        (determinantNormalizedCyclicExtensionCharacter
          K P hK hP hgenerate θ) _
  · intro c
    exact IrreducibleCharacter.isIntegral_value ψ c

/-- Every Fourier coefficient of the determinant-normalized cyclic
trace is an algebraic integer.  The key point is that the coefficient is
the trace of a finite-order endomorphism on a twisted intertwiner
space. -/
theorem isIntegral_normalizedPairing_determinantNormalizedCyclicTrace
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (ψ : IrreducibleCharacter
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G))) :
    IsIntegral ℤ
      (ClassFunction.normalizedPairing
        (determinantNormalizedCyclicTrace
          K P hK hP hgenerate θ)
        ψ.toClassFunction) := by
  rw [
    normalizedPairing_determinantNormalizedCyclicTrace_eq_trace_coefficientEndomorphism]
  apply LinearMap.isIntegral_trace_of_isOfFinOrder
  exact
    determinantNormalizedCyclicCoefficientEndomorphism_isOfFinOrder
      K P hK hP θ ψ

/-- Once a cyclic Fourier coefficient has been shown to be both an
algebraic integer and rational, it is the cast of an ordinary integer.
This is the final purely commutative-algebra step of the integrality
argument. -/
theorem normalizedPairing_determinantNormalizedCyclicTrace_isInteger_of_isIntegral_of_eq_rat
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (ψ : IrreducibleCharacter
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G)))
    (hintegral :
      IsIntegral ℤ
        (ClassFunction.normalizedPairing
          (determinantNormalizedCyclicTrace
            K P hK hP hgenerate θ)
          ψ.toClassFunction))
    (hrat :
      ∃ q : ℚ,
        ClassFunction.normalizedPairing
          (determinantNormalizedCyclicTrace
            K P hK hP hgenerate θ)
          ψ.toClassFunction = (q : ℂ)) :
    ∃ z : ℤ,
      ClassFunction.normalizedPairing
        (determinantNormalizedCyclicTrace
          K P hK hP hgenerate θ)
        ψ.toClassFunction = (z : ℂ) :=
  ClassFunction.exists_int_eq_of_isIntegral_of_eq_rat
    hintegral hrat

/-- Rationality is the only remaining arithmetic input needed to turn
a Fourier coefficient of the determinant-normalized cyclic trace into
an ordinary integer. -/
theorem normalizedPairing_determinantNormalizedCyclicTrace_isInteger_of_eq_rat
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (ψ : IrreducibleCharacter
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G)))
    (hrat :
      ∃ q : ℚ,
        ClassFunction.normalizedPairing
          (determinantNormalizedCyclicTrace
            K P hK hP hgenerate θ)
          ψ.toClassFunction = (q : ℂ)) :
    ∃ z : ℤ,
      ClassFunction.normalizedPairing
        (determinantNormalizedCyclicTrace
          K P hK hP hgenerate θ)
        ψ.toClassFunction = (z : ℂ) :=
  normalizedPairing_determinantNormalizedCyclicTrace_isInteger_of_isIntegral_of_eq_rat
    K P hK hP hgenerate θ ψ
    (isIntegral_normalizedPairing_determinantNormalizedCyclicTrace
      K P hK hP hgenerate θ ψ)
    hrat

/-- To prove that a cyclic Fourier coefficient is an ordinary integer,
it suffices to prove the genuine Galois-invariance statement that every
`ℚ`-embedding of the field generated by the coefficient fixes its
generator.  Algebraic integrality is supplied unconditionally by the
finite-order coefficient endomorphism. -/
theorem normalizedPairing_determinantNormalizedCyclicTrace_isInteger_of_forall_adjoinAlgHom_gen_eq
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (ψ : IrreducibleCharacter
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G)))
    (hfix :
      ∀ σ :
          ((ℚ⟮determinantNormalizedCyclicFourierCoefficient
            K P hK hP hgenerate θ ψ⟯) →ₐ[ℚ] ℂ),
        σ (AdjoinSimple.gen ℚ
          (determinantNormalizedCyclicFourierCoefficient
            K P hK hP hgenerate θ ψ)) =
          determinantNormalizedCyclicFourierCoefficient
            K P hK hP hgenerate θ ψ) :
    ∃ z : ℤ,
      ClassFunction.normalizedPairing
        (determinantNormalizedCyclicTrace
          K P hK hP hgenerate θ)
        ψ.toClassFunction = (z : ℂ) := by
  have hintegral :
      IsIntegral ℤ
        (determinantNormalizedCyclicFourierCoefficient
          K P hK hP hgenerate θ ψ) := by
    exact
      isIntegral_normalizedPairing_determinantNormalizedCyclicTrace
        K P hK hP hgenerate θ ψ
  have hrat :
      ∃ q : ℚ,
        determinantNormalizedCyclicFourierCoefficient
          K P hK hP hgenerate θ ψ = (q : ℂ) :=
    ClassFunction.exists_rat_eq_of_forall_adjoin_algHom_gen_eq
      (ClassFunction.isIntegral_rat_of_isIntegral_int hintegral)
      hfix
  exact
    ClassFunction.exists_int_eq_of_isIntegral_of_eq_rat
      hintegral hrat

end McKayConjecture
