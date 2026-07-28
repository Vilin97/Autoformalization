/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FiniteFactorCompatibleReduction
import McKayConjecture.CharacterTriple.FactorSetCoprimeClassVanishing
import McKayConjecture.CharacterTriple.ProjectiveCrossCharacteristicCoefficientReduction

/-!
# Projective splitting through a compatible coefficient reduction

This is the coefficient-choice-free form of cross-characteristic splitting.
The modular coefficient group may be arbitrary: a complex character of that
group only has to lift the retained prime-to-`q` roots pointwise.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

open Representation

variable {G V K : Type}
variable [Group G]
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable [CommGroup K]

private instance compatibleReductionFinrankNeZero :
    NeZero (Module.finrank ℂ V) :=
  ⟨Module.finrank_pos.ne'⟩

/-- A split retained complex factor which is pointwise the prime-to-`q`
part of the finite factor makes the original projective obstruction
`q`-primary. -/
theorem exists_pow_nsmul_factorSet_h2Class_eq_zero_of_retainedFactor
    (P : ProjectiveRepresentation ℂ G V)
    (q : ℕ) [Fact q.Prime]
    (β : FactorSet G ℂˣ)
    (hretained :
      ∀ g h,
        β g h =
          ((primeToRootsProjection q (Module.finrank ℂ V)
              (P.finiteFactorSet g h) :
            rootsOfUnity (Module.finrank ℂ V) ℂ) : ℂˣ))
    (hreduced :
      letI := trivialMulDistribMulAction G ℂˣ
      β.h2Class = 0) :
    ∃ k : ℕ,
      letI := trivialMulDistribMulAction G ℂˣ
      q ^ k • P.factorSet.h2Class = 0 := by
  obtain ⟨k, hk⟩ :=
    P.finiteFactorSet
      |>.exists_pow_nsmul_map_subtype_h2Class_eq_zero_of_retainedFactor
        q (Module.finrank ℂ V) β hretained hreduced
  refine ⟨k, ?_⟩
  have hclasses :
      letI := trivialMulDistribMulAction G ℂˣ
      P.factorSet.h2Class =
        P.finiteFactorNormalize.factorSet.h2Class :=
    FactorSet.h2Class_eq_of_cohomologous
      P.factorSet_cohomologous_finiteFactorNormalize
  rw [hclasses, ← P.finiteFactorSet_map_subtype]
  exact hk

/-- A split compatible reduction makes the original projective obstruction
`q`-primary. -/
theorem exists_pow_nsmul_factorSet_h2Class_eq_zero_of_compatibleReduction
    (P : ProjectiveRepresentation ℂ G V)
    (q : ℕ) [Fact q.Prime]
    (r :
      rootsOfUnity (Module.finrank ℂ V) ℂ →* K)
    (κ : K →* ℂˣ)
    (hcompat :
      ∀ z : rootsOfUnity (Module.finrank ℂ V) ℂ,
        κ (r z) =
          ((primeToRootsProjection q (Module.finrank ℂ V) z :
            rootsOfUnity (Module.finrank ℂ V) ℂ) : ℂˣ))
    (hreduced :
      letI := trivialMulDistribMulAction G ℂˣ
      ((P.finiteFactorSet.map r).map κ).h2Class = 0) :
    ∃ k : ℕ,
      letI := trivialMulDistribMulAction G ℂˣ
      q ^ k • P.factorSet.h2Class = 0 := by
  apply
    P.exists_pow_nsmul_factorSet_h2Class_eq_zero_of_retainedFactor
      q ((P.finiteFactorSet.map r).map κ)
  · intro g h
    exact hcompat (P.finiteFactorSet g h)
  · exact hreduced

/-- A split retained factor kills the original projective obstruction when
the complex representation dimension is prime to `q`. -/
theorem factorSet_h2Class_eq_zero_of_retainedFactor
    (P : ProjectiveRepresentation ℂ G V)
    (q : ℕ) [Fact q.Prime]
    (hdegree : ¬q ∣ Module.finrank ℂ V)
    (β : FactorSet G ℂˣ)
    (hretained :
      ∀ g h,
        β g h =
          ((primeToRootsProjection q (Module.finrank ℂ V)
              (P.finiteFactorSet g h) :
            rootsOfUnity (Module.finrank ℂ V) ℂ) : ℂˣ))
    (hreduced :
      letI := trivialMulDistribMulAction G ℂˣ
      β.h2Class = 0) :
    letI := trivialMulDistribMulAction G ℂˣ
    P.factorSet.h2Class = 0 := by
  obtain ⟨k, hk⟩ :=
    P.exists_pow_nsmul_factorSet_h2Class_eq_zero_of_retainedFactor
      q β hretained hreduced
  have hdimension :
      letI := trivialMulDistribMulAction G ℂˣ
      Module.finrank ℂ V • P.factorSet.h2Class = 0 :=
    P.finrank_nsmul_factorSet_h2Class_eq_zero
  have hcoprime :
      Nat.Coprime (Module.finrank ℂ V) (q ^ k) :=
    (Fact.out : q.Prime).coprime_pow_of_not_dvd hdegree
  exact
    eq_zero_of_coprime_nsmul_eq_zero
      hcoprime hdimension hk

/-- A split compatible reduction kills the original projective obstruction
when the complex representation dimension is prime to `q`. -/
theorem factorSet_h2Class_eq_zero_of_compatibleReduction
    (P : ProjectiveRepresentation ℂ G V)
    (q : ℕ) [Fact q.Prime]
    (hdegree : ¬q ∣ Module.finrank ℂ V)
    (r :
      rootsOfUnity (Module.finrank ℂ V) ℂ →* K)
    (κ : K →* ℂˣ)
    (hcompat :
      ∀ z : rootsOfUnity (Module.finrank ℂ V) ℂ,
        κ (r z) =
          ((primeToRootsProjection q (Module.finrank ℂ V) z :
            rootsOfUnity (Module.finrank ℂ V) ℂ) : ℂˣ))
    (hreduced :
      letI := trivialMulDistribMulAction G ℂˣ
      ((P.finiteFactorSet.map r).map κ).h2Class = 0) :
    letI := trivialMulDistribMulAction G ℂˣ
    P.factorSet.h2Class = 0 := by
  apply
    P.factorSet_h2Class_eq_zero_of_retainedFactor
      q hdegree ((P.finiteFactorSet.map r).map κ)
  · intro g h
    exact hcompat (P.finiteFactorSet g h)
  · exact hreduced

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
