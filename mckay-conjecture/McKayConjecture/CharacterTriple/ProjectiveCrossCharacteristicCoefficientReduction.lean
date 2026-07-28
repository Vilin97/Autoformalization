/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import McKayConjecture.CharacterTriple.FiniteFactorCrossCharacteristicReduction
import McKayConjecture.CharacterTriple.FiniteFactorNormalization

/-!
# Cross-characteristic coefficient reduction for projective representations

Determinant normalization gives every nonzero finite-dimensional complex
projective representation a factor set valued in roots of unity of order
equal to its dimension.  Applying the cross-characteristic coefficient
reduction then produces a factor set over a concrete finite field.

This file packages that construction and proves the strongest conclusion
available without reducing the operators themselves: if the retained
finite-field factor is split, then the original projective obstruction
class is `q`-primary.  The conclusion is for the original projective
representation, since determinant and identity normalization only change
the factor set by coboundaries.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

open Representation

universe u v

section CoefficientReduction

variable {G : Type u} {V : Type v}
variable [Group G]
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable (q : ℕ) [Fact q.Prime]

private instance projectiveFinrankNeZero :
    NeZero (Module.finrank ℂ V) :=
  ⟨finrank_pos.ne'⟩

/-- The finite-field factor set obtained from the determinant-normalized
factor of a complex projective representation. -/
def finiteFactorCrossCharacteristicReduction
    (P : ProjectiveRepresentation ℂ G V) :
    FactorSet G
      (PrimeToCoefficientField q (Module.finrank ℂ V))ˣ :=
  P.finiteFactorSet.crossCharacteristicReduction
    q (Module.finrank ℂ V)

@[simp]
theorem finiteFactorCrossCharacteristicReduction_apply
    (P : ProjectiveRepresentation ℂ G V)
    (g h : G) :
    P.finiteFactorCrossCharacteristicReduction q g h =
      crossCharacteristicCoefficientReduction
        q (Module.finrank ℂ V)
        (P.finiteFactorSet g h) :=
  rfl

/-- The roots-of-unity factor set becomes exactly the factor set of the
finite-factor-normalized projective representation after coefficient
inclusion. -/
theorem finiteFactorSet_map_subtype
    (P : ProjectiveRepresentation ℂ G V) :
    P.finiteFactorSet.map
        (rootsOfUnity (Module.finrank ℂ V) ℂ).subtype =
      P.finiteFactorNormalize.factorSet := by
  apply FactorSet.ext
  intro g h
  rfl

/-- The original factor set is cohomologous to the finite-factor
normalization. -/
theorem factorSet_cohomologous_finiteFactorNormalize
    (P : ProjectiveRepresentation ℂ G V) :
    P.factorSet.Cohomologous
      P.finiteFactorNormalize.factorSet := by
  exact
    FactorSet.cohomologous_trans
      (P.factorSet_cohomologous_rescale
        P.determinantRescaling)
      P.determinantNormalize.factorSet_cohomologous_normalize

/-- Exact pointwise reconstruction of the determinant-normalized complex
factor from a `q`-primary remainder and a finite-field factor. -/
theorem finiteFactor_primePrimaryRemainder_mul_lifted_reduction
    (P : ProjectiveRepresentation ℂ G V)
    (g h : G) :
    (((P.finiteFactorSet.primePrimaryRemainder
            q (Module.finrank ℂ V) g h :
          (primeToRootsProjection
            q (Module.finrank ℂ V)).ker) :
        rootsOfUnity (Module.finrank ℂ V) ℂ) : ℂˣ) *
      finiteFieldUnitsToComplexUnits
        (PrimeToCoefficientField q (Module.finrank ℂ V))
        (P.finiteFactorCrossCharacteristicReduction q g h) =
      P.finiteFactorNormalize.factor g h := by
  exact
    P.finiteFactorSet
      |>.primePrimaryRemainder_mul_lifted_crossCharacteristicReduction
        q (Module.finrank ℂ V) g h

end CoefficientReduction

variable {G V : Type}
variable [Group G]
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable (q : ℕ) [Fact q.Prime]

/-- If the retained finite-field factor is split after the chosen
complex embedding, then the obstruction class of the original
projective representation is `q`-primary. -/
theorem exists_pow_nsmul_factorSet_h2Class_eq_zero_of_reduction
    (P : ProjectiveRepresentation ℂ G V)
    (hreduced :
      letI := trivialMulDistribMulAction G ℂˣ
      ((P.finiteFactorCrossCharacteristicReduction q).map
        (finiteFieldUnitsToComplexUnits
          (PrimeToCoefficientField
            q (Module.finrank ℂ V)))).h2Class =
        0) :
    ∃ k : ℕ,
      letI := trivialMulDistribMulAction G ℂˣ
      q ^ k • P.factorSet.h2Class = 0 := by
  obtain ⟨k, hk⟩ :=
    P.finiteFactorSet
      |>.exists_pow_nsmul_map_subtype_h2Class_eq_zero_of_reduction
        q (Module.finrank ℂ V) hreduced
  refine ⟨k, ?_⟩
  have hclasses :
      letI := trivialMulDistribMulAction G ℂˣ
      P.factorSet.h2Class =
        P.finiteFactorNormalize.factorSet.h2Class :=
    FactorSet.h2Class_eq_of_cohomologous
      (P.factorSet_cohomologous_finiteFactorNormalize)
  rw [hclasses, ← P.finiteFactorSet_map_subtype]
  exact hk

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
