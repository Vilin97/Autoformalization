/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ProjectiveNormalizerCorrection
import McKayConjecture.CharacterTriple.FiniteFactorCrossCharacteristicReduction

/-!
# Cross-characteristic factors split by a Brauer normalizer

The canonical coefficient reduction of a finite complex factor set has
values in a concrete finite field.  If that reduced factor is realized as
the factor of a projective interior-normalizer lift, a Brauer-normalizer
extension supplies an explicit splitting cochain.  Mapping the cochain back
to complex units shows that the retained factor has zero class.  The exact
CRT decomposition then shows that the original factor class is `q`-primary.

This is the complete coefficient-level bridge between the finite-root
normalization and the modular normalizer theorem.  Its remaining input is
the factor equality supplied by an operator-level integral reduction.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace FactorSet

open Representation

variable {G B : Type} [Group G] [CommGroup B]

/-- An explicit scalar splitting makes a factor set cohomologically
trivial. -/
theorem h2Class_eq_zero_of_scalar_split
    (α : FactorSet G B)
    (b : G → B)
    (hb :
      ∀ g h,
        b g * b h = α g h * b (g * h)) :
    letI := trivialMulDistribMulAction G B
    α.h2Class = 0 := by
  have hfactor :
      α = (FactorSet.one : FactorSet G B).gauge b := by
    apply FactorSet.ext
    intro g h
    rw [gauge_apply, one_apply, mul_one, hb]
    simp
  rw [hfactor, h2Class_gauge, h2Class_one]

variable {P A : Type}
variable [Group P] [Fintype P]
variable [Ring A]
variable (q n : ℕ) [Fact q.Prime] [NeZero n]
variable [Algebra (PrimeToCoefficientField q n) A]
variable [MulSemiringAction P A]
variable [SMulCommClass P (PrimeToCoefficientField q n) A]

/-- A Brauer-normalizer splitting of the concretely reduced factor
makes the original finite complex factor class `q`-primary. -/
theorem
    exists_pow_nsmul_map_subtype_h2Class_eq_zero_of_normalizerFactor
    (α : FactorSet G (rootsOfUnity n ℂ))
    {I :
      InteriorAction
        (P := P) (A := A)}
    (T :
      ProjectiveNormalizerLift
        (k := PrimeToCoefficientField q n)
        (H := G) I)
    (E :
      BrauerNormalizerExtension
        (k := PrimeToCoefficientField q n) I)
    (Z :
      BrauerScalarIdentification
        (k := PrimeToCoefficientField q n)
        (P := P) (A := A))
    (hfactor :
      ∀ g h,
        T.factor g h =
          α.crossCharacteristicReduction q n g h) :
    ∃ k : ℕ,
      letI := trivialMulDistribMulAction G ℂˣ
      q ^ k •
          (α.map (rootsOfUnity n ℂ).subtype).h2Class =
        0 := by
  apply
    α.exists_pow_nsmul_map_subtype_h2Class_eq_zero_of_reduction
      q n
  let ι :=
    finiteFieldUnitsToComplexUnits
      (PrimeToCoefficientField q n)
  let b : G → ℂˣ :=
    fun g ↦ ι (T.brauerScalar E Z g)
  apply h2Class_eq_zero_of_scalar_split _ b
  intro g h
  have hmul :=
    congrArg ι (T.brauerScalar_mul E Z g h)
  simpa only [b, map_mul, map_apply, hfactor] using hmul

end FactorSet
end CharacterTriple
end McKayConjecture
