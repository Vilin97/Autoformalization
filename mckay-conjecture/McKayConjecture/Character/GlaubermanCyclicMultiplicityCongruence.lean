/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.FiniteOrderTraceCongruence
import McKayConjecture.Character.GlaubermanCyclicCoefficientTrace
import McKayConjecture.Character.RestrictionMultiplicityPairing

/-!
# Cyclic Glauberman coefficients modulo the acting prime

The Fourier coefficient of the determinant-normalized cyclic trace is the
trace of an operator on the ordinary restriction-multiplicity space.  Since
that operator has `p`-power order, an integral Fourier coefficient is
congruent modulo `p` to the restriction multiplicity.
-/

noncomputable section

namespace McKayConjecture

open CliffordCorrespondence

variable {G : Type} [Group G] [Finite G]
variable (K P : Subgroup G) [K.Normal]
variable [IsCyclic P]
variable {p : ℕ} [Fact p.Prime]

/-- The coefficient space has dimension equal to the ordinary restriction
multiplicity. -/
theorem finrank_cyclicCoefficientSpace_eq_restrictionMultiplicity
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (ψ : IrreducibleCharacter
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G))) :
    Module.finrank ℂ
        ((Representation.linHom
          ψ.realization.ρ
          (cyclicFixedPointRepresentation
            K θ.1.1
            ((cyclicSubgroupGenerator P : P) : G))).invariants) =
      restrictionMultiplicity
        (cyclicFixedPointsInclusion K
          ((cyclicSubgroupGenerator P : P) : G))
        ψ θ.1.1 := by
  rw [restrictionMultiplicity]
  let W :=
    FDRep.res
      (cyclicFixedPointsInclusion K
        ((cyclicSubgroupGenerator P : P) : G))
      θ.1.1.realization
  change
    Module.finrank ℂ
        ((Representation.linHom
          ψ.realization.ρ W.ρ).invariants) =
      Module.finrank ℂ
        (ψ.realization ⟶ W)
  exact
    LinearEquiv.finrank_eq
      (Representation.linHom.invariantsEquivFDRepHom
        ψ.realization W)

/-- An integral cyclic Fourier coefficient is congruent modulo `p` to the
ordinary restriction multiplicity, for every irreducible target character. -/
theorem prime_dvd_restrictionMultiplicity_sub_cyclicCoefficient
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (ψ : IrreducibleCharacter
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G)))
    (a : ℤ)
    (hcoeff :
      ClassFunction.normalizedPairing
          (determinantNormalizedCyclicTrace
            K P hK hP hgenerate θ)
          ψ.toClassFunction =
        (a : ℂ)) :
    (p : ℤ) ∣
      (restrictionMultiplicity
          (cyclicFixedPointsInclusion K
            ((cyclicSubgroupGenerator P : P) : G))
          ψ θ.1.1 : ℤ) - a := by
  obtain ⟨k, hcard : Nat.card P = p ^ k⟩ :=
    IsPGroup.iff_card.mp hP
  let T :=
    determinantNormalizedCyclicCoefficientEndomorphism
      K P hK hP θ ψ
  have hTpow : T ^ (p ^ k) = 1 := by
    rw [← hcard]
    exact
      determinantNormalizedCyclicCoefficientEndomorphism_pow_card_eq_one
        K P hK hP θ ψ
  have hTtrace :
      LinearMap.trace ℂ
          ((Representation.linHom
            ψ.realization.ρ
            (cyclicFixedPointRepresentation
              K θ.1.1
              ((cyclicSubgroupGenerator P : P) : G))).invariants)
          T =
        (a : ℂ) := by
    rw [←
      normalizedPairing_determinantNormalizedCyclicTrace_eq_trace_coefficientEndomorphism
        K P hK hP hgenerate θ ψ]
    exact hcoeff
  have hdiv :=
    LinearMap.prime_dvd_finrank_sub_of_pow_primePower_eq_one
      T hTpow a hTtrace
  rw [
    finrank_cyclicCoefficientSpace_eq_restrictionMultiplicity
      K P θ ψ] at hdiv
  exact hdiv

/-- A zero cyclic Fourier coefficient forces the ordinary restriction
multiplicity to be divisible by `p`. -/
theorem prime_dvd_restrictionMultiplicity_of_cyclicCoefficient_eq_zero
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (ψ : IrreducibleCharacter
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G)))
    (hcoeff :
      ClassFunction.normalizedPairing
          (determinantNormalizedCyclicTrace
            K P hK hP hgenerate θ)
          ψ.toClassFunction =
        0) :
    p ∣
      restrictionMultiplicity
        (cyclicFixedPointsInclusion K
          ((cyclicSubgroupGenerator P : P) : G))
        ψ θ.1.1 := by
  have hdiv :=
    prime_dvd_restrictionMultiplicity_sub_cyclicCoefficient
      K P hK hP hgenerate θ ψ 0
      (by simpa using hcoeff)
  norm_num only [sub_zero] at hdiv
  exact_mod_cast hdiv

/-- A root-of-unity cyclic Fourier coefficient forces the ordinary
restriction multiplicity to be prime to `p`. -/
theorem not_dvd_restrictionMultiplicity_of_cyclicCoefficient_isOfFinOrder
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (ψ : IrreducibleCharacter
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G)))
    (a : ℂ)
    (hcoeff :
      ClassFunction.normalizedPairing
          (determinantNormalizedCyclicTrace
            K P hK hP hgenerate θ)
          ψ.toClassFunction =
        a)
    (ha : IsOfFinOrder a) :
    ¬p ∣
      restrictionMultiplicity
        (cyclicFixedPointsInclusion K
          ((cyclicSubgroupGenerator P : P) : G))
        ψ θ.1.1 := by
  obtain ⟨k, hcard : Nat.card P = p ^ k⟩ :=
    IsPGroup.iff_card.mp hP
  let T :=
    determinantNormalizedCyclicCoefficientEndomorphism
      K P hK hP θ ψ
  have hTpow : T ^ (p ^ k) = 1 := by
    rw [← hcard]
    exact
      determinantNormalizedCyclicCoefficientEndomorphism_pow_card_eq_one
        K P hK hP θ ψ
  have hTtrace :
      LinearMap.trace ℂ
          ((Representation.linHom
            ψ.realization.ρ
            (cyclicFixedPointRepresentation
              K θ.1.1
              ((cyclicSubgroupGenerator P : P) : G))).invariants)
          T =
        a := by
    rw [←
      normalizedPairing_determinantNormalizedCyclicTrace_eq_trace_coefficientEndomorphism
        K P hK hP hgenerate θ ψ]
    exact hcoeff
  have hnot :=
    LinearMap.not_dvd_finrank_of_pow_primePower_eq_one_of_trace_isOfFinOrder
      T hTpow a hTtrace ha
  rw [
    finrank_cyclicCoefficientSpace_eq_restrictionMultiplicity
      K P θ ψ] at hnot
  exact hnot

/-- If the cyclic trace has one root-of-unity coefficient and all other
irreducible coefficients vanish, that coefficient identifies the unique
target irreducible with restriction multiplicity prime to `p`. -/
theorem existsUnique_restrictionMultiplicity_isPPrime_of_unique_rootCoefficient
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (hshape :
      ∃ ψ :
          IrreducibleCharacter
            (cyclicFixedPoints K
              ((cyclicSubgroupGenerator P : P) : G)),
        IsOfFinOrder
          (ClassFunction.normalizedPairing
            (determinantNormalizedCyclicTrace
              K P hK hP hgenerate θ)
            ψ.toClassFunction) ∧
        ∀ φ :
            IrreducibleCharacter
              (cyclicFixedPoints K
                ((cyclicSubgroupGenerator P : P) : G)),
          φ ≠ ψ →
            ClassFunction.normalizedPairing
                (determinantNormalizedCyclicTrace
                  K P hK hP hgenerate θ)
                φ.toClassFunction =
              0) :
    ∃! ψ :
        IrreducibleCharacter
          (cyclicFixedPoints K
            ((cyclicSubgroupGenerator P : P) : G)),
      ¬p ∣
        restrictionMultiplicity
          (cyclicFixedPointsInclusion K
            ((cyclicSubgroupGenerator P : P) : G))
          ψ θ.1.1 := by
  obtain ⟨ψ, hroot, hzero⟩ := hshape
  refine ⟨ψ, ?_, ?_⟩
  · exact
      not_dvd_restrictionMultiplicity_of_cyclicCoefficient_isOfFinOrder
        K P hK hP hgenerate θ ψ
        (ClassFunction.normalizedPairing
          (determinantNormalizedCyclicTrace
            K P hK hP hgenerate θ)
          ψ.toClassFunction)
        rfl hroot
  · intro φ hφ
    by_contra hne
    have hdvd :=
      prime_dvd_restrictionMultiplicity_of_cyclicCoefficient_eq_zero
        K P hK hP hgenerate θ φ (hzero φ hne)
    exact hφ hdvd

end McKayConjecture
