/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FactorSetCoprimeClassVanishing
import McKayConjecture.CharacterTriple.CrossCharacteristicNormalizerFactor
import McKayConjecture.CharacterTriple.ProjectiveCrossCharacteristicCoefficientReduction
import McKayConjecture.CharacterTriple.ProjectiveCompatibleNormalizerSplitting

/-!
# Splitting a cross-characteristic projective obstruction

The determinant of a projective representation shows that its
dimension annihilates its factor-set class.  Cross-characteristic
coefficient reduction supplies a power-of-`q` annihilator as soon as
the retained finite-field factor splits.  If the dimension is
prime to `q`, these two annihilators are coprime, so the original
complex factor-set class vanishes.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

open Representation

variable {G V : Type}
variable [Group G]
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]

/-- A split cross-characteristic reduction kills the original
projective obstruction when the representation dimension is prime to
the residue characteristic. -/
theorem factorSet_h2Class_eq_zero_of_crossCharacteristicReduction
    (P : ProjectiveRepresentation ℂ G V)
    (q : ℕ) [Fact q.Prime]
    (hdegree : ¬q ∣ Module.finrank ℂ V)
    (hreduced :
      letI := trivialMulDistribMulAction G ℂˣ
      ((P.finiteFactorCrossCharacteristicReduction q).map
        (finiteFieldUnitsToComplexUnits
          (PrimeToCoefficientField
            q (Module.finrank ℂ V)))).h2Class =
        0) :
    letI := trivialMulDistribMulAction G ℂˣ
    P.factorSet.h2Class = 0 := by
  obtain ⟨k, hk⟩ :=
    P.exists_pow_nsmul_factorSet_h2Class_eq_zero_of_reduction
      q hreduced
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

variable {S A : Type}
variable [Group S] [Fintype S]
variable [Ring A]

/-- A Brauer-normalizer realization of the explicit finite-field
factor splits the original complex projective obstruction, provided
the complex representation dimension is prime to `q`. -/
theorem factorSet_h2Class_eq_zero_of_crossCharacteristicNormalizerFactor
    (P : ProjectiveRepresentation ℂ G V)
    (q : ℕ) [Fact q.Prime]
    (hdegree : ¬q ∣ Module.finrank ℂ V)
    [Algebra
      (PrimeToCoefficientField q (Module.finrank ℂ V)) A]
    [MulSemiringAction S A]
    [SMulCommClass S
      (PrimeToCoefficientField q (Module.finrank ℂ V)) A]
    {I : InteriorAction (P := S) (A := A)}
    (T :
      ProjectiveNormalizerLift
        (k :=
          PrimeToCoefficientField q (Module.finrank ℂ V))
        (H := G) I)
    (E :
      BrauerNormalizerExtension
        (k :=
          PrimeToCoefficientField q (Module.finrank ℂ V)) I)
    (Z :
      BrauerScalarIdentification
        (k :=
          PrimeToCoefficientField q (Module.finrank ℂ V))
        (P := S) (A := A))
    (hfactor :
      ∀ g h,
        T.factor g h =
          P.finiteFactorCrossCharacteristicReduction q g h) :
    letI := trivialMulDistribMulAction G ℂˣ
    P.factorSet.h2Class = 0 := by
  let κ :=
    finiteFieldUnitsToComplexUnits
      (PrimeToCoefficientField q (Module.finrank ℂ V))
  apply
    P.factorSet_h2Class_eq_zero_of_retainedNormalizerFactor
      q hdegree T E Z κ
  intro g h
  rw [hfactor g h]
  exact
    finiteFieldUnitsToComplexUnits_crossCharacteristicCoefficientReduction
      q (Module.finrank ℂ V)
      (P.finiteFactorSet g h)

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
