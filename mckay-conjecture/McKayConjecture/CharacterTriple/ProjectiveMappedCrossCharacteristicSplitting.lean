/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeAlgebraBrauerDimensionCriterion
import McKayConjecture.CharacterTriple.ProjectiveCompatibleNormalizerSplitting

/-!
# Cross-characteristic splitting through a coefficient map

A Brauer-normalizer lift need not live over the project's chosen explicit
Galois field.  It is enough to map its scalar units into that field and prove
that the mapped factor is the explicit cross-characteristic factor.  This
form is tailored to a projective representation obtained by reducing an
integral lattice at an arbitrary residue field above the defining prime.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

open Representation

variable {G V k S A : Type}
variable [Group G]
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable [Field k]
variable [Group S] [Fintype S]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction S A] [SMulCommClass S k A]

/-- A Brauer-normalizer factor over any coefficient field splits the original
complex obstruction when its image is the explicit cross-characteristic
factor and the complex representation dimension is prime to `q`. -/
theorem factorSet_h2Class_eq_zero_of_mappedCrossCharacteristicNormalizerFactor
    (P : ProjectiveRepresentation ℂ G V)
    (q : ℕ) [Fact q.Prime]
    (hdegree : ¬q ∣ Module.finrank ℂ V)
    {I : InteriorAction (P := S) (A := A)}
    (T : ProjectiveNormalizerLift (k := k) (H := G) I)
    (E : BrauerNormalizerExtension (k := k) I)
    (Z : BrauerScalarIdentification (k := k) (P := S) (A := A))
    (ι :
      kˣ →*
        (PrimeToCoefficientField q (Module.finrank ℂ V))ˣ)
    (hfactor :
      ∀ g h,
        ι (T.factor g h) =
          P.finiteFactorCrossCharacteristicReduction q g h) :
    letI := trivialMulDistribMulAction G ℂˣ
    P.factorSet.h2Class = 0 := by
  let j :=
    finiteFieldUnitsToComplexUnits
      (PrimeToCoefficientField q (Module.finrank ℂ V))
  let scalarMap : kˣ →* ℂˣ :=
    j.comp ι
  apply
    P.factorSet_h2Class_eq_zero_of_retainedNormalizerFactor
      q hdegree T E Z scalarMap
  intro g h
  change
    j (ι (T.factor g h)) =
      ((primeToRootsProjection q (Module.finrank ℂ V)
          (P.finiteFactorSet g h) :
        rootsOfUnity (Module.finrank ℂ V) ℂ) : ℂˣ)
  rw [hfactor g h]
  exact
    finiteFieldUnitsToComplexUnits_crossCharacteristicCoefficientReduction
      q (Module.finrank ℂ V)
      (P.finiteFactorSet g h)

variable (q : ℕ) [Fact q.Prime] [CharP k q]

/-- Brauer primitivity supplies the scalar identification in the mapped
coefficient version of cross-characteristic splitting. -/
theorem factorSet_h2Class_eq_zero_of_mappedCrossCharacteristicDadeFactor
    (P : ProjectiveRepresentation ℂ G V)
    (hdegree : ¬q ∣ Module.finrank ℂ V)
    (D : DadeAlgebra q k S A)
    (hprimitive : D.IsBrauerPrimitive)
    (I : InteriorAction (P := S) (A := A))
    (T : ProjectiveNormalizerLift (k := k) (H := G) I)
    (E : BrauerNormalizerExtension (k := k) I)
    (ι :
      kˣ →*
        (PrimeToCoefficientField q (Module.finrank ℂ V))ˣ)
    (hfactor :
      ∀ g h,
        ι (T.factor g h) =
          P.finiteFactorCrossCharacteristicReduction q g h) :
    letI := trivialMulDistribMulAction G ℂˣ
    P.factorSet.h2Class = 0 :=
  P.factorSet_h2Class_eq_zero_of_mappedCrossCharacteristicNormalizerFactor
    q hdegree T E
    (brauerScalarIdentificationOfFinrankOne
      ((D.finrank_brauerQuotientAlgebra_eq_one_iff_isBrauerPrimitive).2
        hprimitive))
    ι hfactor

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
