/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordCorrespondence
import McKayConjecture.Character.InductionCharacter
import McKayConjecture.Character.IrreducibleCharacterBasis
import McKayConjecture.Character.Multiplicity

/-!
# Multiplicity and degree formulas for induced characters

Frobenius reciprocity identifies the irreducible Fourier coefficients of
an induced character with restriction multiplicities.  Evaluating the
resulting expansion at the identity gives the corresponding degree sum.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

namespace McKayConjecture
namespace CliffordCorrespondence

variable {G : Type} [Group G] [Finite G]

noncomputable local instance inductionMultiplicityDegreeFintypeG :
    Fintype G :=
  Fintype.ofFinite _

noncomputable local instance inductionMultiplicityDegreeFintypeIrr :
    Fintype (IrreducibleCharacter G) :=
  Fintype.ofFinite _

/-- The Fourier coefficient of an induced irreducible character is its
restriction multiplicity. -/
theorem normalizedPairing_inducedCharacter_eq_restrictionMultiplicity
    (S : Subgroup G)
    (η : IrreducibleCharacter S)
    (χ : IrreducibleCharacter G) :
    ClassFunction.normalizedPairing
        (FDRep.characterClassFunction
          (FDRep.ind S.subtype η.realization))
        χ.toClassFunction =
      (restrictionMultiplicity S.subtype η χ : ℂ) := by
  rw [ClassFunction.normalizedPairing_comm]
  change
    ClassFunction.characterPairing
        χ.toClassFunction
        (FDRep.characterClassFunction
          (FDRep.ind S.subtype η.realization)) =
      (restrictionMultiplicity S.subtype η χ : ℂ)
  rw [← inductionMultiplicity_eq_restrictionMultiplicity]
  simpa [inductionMultiplicity,
    FDRep.multiplicity,
    IrreducibleCharacter.realization_character] using
    FDRep.characterPairing_eq_multiplicity
      (FDRep.ind S.subtype η.realization)
      χ.realization

/-- Exact irreducible-character expansion of an induced irreducible
character. -/
theorem inducedCharacter_eq_restrictionMultiplicity_sum
    (S : Subgroup G)
    (η : IrreducibleCharacter S) :
    FDRep.characterClassFunction
        (FDRep.ind S.subtype η.realization) =
      ∑ χ : IrreducibleCharacter G,
        (restrictionMultiplicity S.subtype η χ : ℂ) •
          χ.toClassFunction := by
  rw [ClassFunction.irreducibleCharacter_fourierExpansion
    (FDRep.characterClassFunction
      (FDRep.ind S.subtype η.realization))]
  apply Finset.sum_congr rfl
  intro χ _hχ
  rw [
    normalizedPairing_inducedCharacter_eq_restrictionMultiplicity]

/-- The subgroup index times the inducing degree is the sum of constituent
degrees weighted by restriction multiplicity. -/
theorem index_mul_degree_eq_sum_restrictionMultiplicity_mul_degree
    (S : Subgroup G)
    (η : IrreducibleCharacter S) :
    (S.index : ℂ) * (η.degree : ℂ) =
      ∑ χ : IrreducibleCharacter G,
        (restrictionMultiplicity S.subtype η χ : ℂ) *
          (χ.degree : ℂ) := by
  have h :=
    congrArg
      (fun f : ClassFunction G ↦ f (1 : G))
      (inducedCharacter_eq_restrictionMultiplicity_sum S η)
  rw [InductionCharacter.ind_characterClassFunction_eq_induce,
    ClassFunction.induce_apply_one] at h
  simpa [FDRep.characterClassFunction_apply,
    FDRep.char_one,
    IrreducibleCharacter.toClassFunction_apply,
    IrreducibleCharacter.realization_character,
    IrreducibleCharacter.value_one,
    IrreducibleCharacter.realization_finrank,
    Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] using h

/-- Natural-number form of the induced-character degree formula. -/
theorem index_mul_degree_eq_sum_restrictionMultiplicity_mul_degree_nat
    (S : Subgroup G)
    (η : IrreducibleCharacter S) :
    S.index * η.degree =
      ∑ χ : IrreducibleCharacter G,
        restrictionMultiplicity S.subtype η χ *
          χ.degree := by
  exact_mod_cast
    index_mul_degree_eq_sum_restrictionMultiplicity_mul_degree
      S η

end CliffordCorrespondence
end McKayConjecture
