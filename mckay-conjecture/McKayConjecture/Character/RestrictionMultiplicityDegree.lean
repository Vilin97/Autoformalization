/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.IrreducibleCharacterBasis
import McKayConjecture.Character.RestrictionMultiplicityPairing

/-!
# Degree decomposition under restriction

Evaluating the irreducible Fourier expansion of a restricted character at
the identity expresses its degree as the sum of constituent degrees weighted
by restriction multiplicity.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace CliffordCorrespondence

variable {G H : Type} [Group G] [Group H]
variable [Finite G] [Finite H]

noncomputable local instance restrictionMultiplicityDegreeFintypeIrr :
    Fintype (IrreducibleCharacter H) :=
  Fintype.ofFinite _

/-- The degree of a restricted irreducible character is the weighted sum of
the degrees of all irreducible constituents. -/
theorem degree_eq_sum_restrictionMultiplicity_mul_degree
    (φ : H →* G)
    (χ : IrreducibleCharacter G) :
    (χ.degree : ℂ) =
      ∑ η : IrreducibleCharacter H,
        (restrictionMultiplicity φ η χ : ℂ) *
          (η.degree : ℂ) := by
  let f : ClassFunction H :=
    FDRep.characterClassFunction
      (FDRep.res φ χ.realization)
  have hexpansion :=
    ClassFunction.irreducibleCharacter_fourierExpansion f
  have h :=
    congrArg (fun k : ClassFunction H ↦ k (1 : H))
      hexpansion
  have hleft :
      f (1 : H) = (χ.degree : ℂ) := by
    change
      (FDRep.res φ χ.realization).character 1 =
        (χ.degree : ℂ)
    rw [FDRep.char_one]
    exact_mod_cast χ.realization_finrank
  rw [hleft] at h
  simpa [f, map_sum, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, IrreducibleCharacter.toClassFunction_apply,
    IrreducibleCharacter.value_one,
    normalizedPairing_restrictedCharacter_eq_restrictionMultiplicity]
    using h

/-- Natural-number form of the degree decomposition under restriction. -/
theorem degree_eq_sum_restrictionMultiplicity_mul_degree_nat
    (φ : H →* G)
    (χ : IrreducibleCharacter G) :
    χ.degree =
      ∑ η : IrreducibleCharacter H,
        restrictionMultiplicity φ η χ * η.degree := by
  exact_mod_cast
    degree_eq_sum_restrictionMultiplicity_mul_degree φ χ

end CliffordCorrespondence
end McKayConjecture
