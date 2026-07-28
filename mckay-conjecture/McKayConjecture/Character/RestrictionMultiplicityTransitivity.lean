/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ClassFunctionRestriction
import McKayConjecture.Character.RestrictionMultiplicityPairing

/-!
# Transitivity of restriction multiplicities

Restriction through an intermediate finite group decomposes through all
irreducible characters of that intermediate group.  This is the ordinary
character-theoretic transitivity formula

`[ξ, Res (Res χ)] = ∑ η, [ξ, Res η] [η, Res χ]`.

It is a basic numerical input for composing successive coprime-action
correspondences.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace CliffordCorrespondence

variable {G H L : Type}
variable [Group G] [Group H] [Group L]
variable [Finite G] [Finite H] [Finite L]

noncomputable local instance :
    Fintype (IrreducibleCharacter H) :=
  Fintype.ofFinite _

/-- Restriction multiplicity through a composite homomorphism is the sum of
the products of the two successive restriction multiplicities. -/
theorem restrictionMultiplicity_comp
    (φ : H →* G) (ψ : L →* H)
    (ξ : IrreducibleCharacter L)
    (χ : IrreducibleCharacter G) :
    restrictionMultiplicity (φ.comp ψ) ξ χ =
      ∑ η : IrreducibleCharacter H,
        restrictionMultiplicity ψ ξ η *
          restrictionMultiplicity φ η χ := by
  have hexpansion :=
    restrictedCharacter_eq_integerCharacterCombination φ χ
  have hpair :=
    congrArg
      (fun f : ClassFunction H =>
        ClassFunction.normalizedPairing
          (ClassFunction.comapLinearMap ψ f)
          ξ.toClassFunction)
      hexpansion
  have hleft :
      ClassFunction.comapLinearMap ψ
          (FDRep.characterClassFunction
            (FDRep.res φ χ.realization)) =
        FDRep.characterClassFunction
          (FDRep.res (φ.comp ψ) χ.realization) := by
    rw [← ClassFunction.characterClassFunction_res,
      FDRep.res_comp]
  have hterm :
      ∀ η : IrreducibleCharacter H,
        ClassFunction.comapLinearMap ψ η.toClassFunction =
          FDRep.characterClassFunction
            (FDRep.res ψ η.realization) := by
    intro η
    rw [ClassFunction.characterClassFunction_res]
    apply congrArg (ClassFunction.comapLinearMap ψ)
    apply ClassFunction.ext
    intro h
    exact
      (congrFun η.realization_character h).symm
  have hcomplex :
      (restrictionMultiplicity (φ.comp ψ) ξ χ : ℂ) =
        ∑ η : IrreducibleCharacter H,
          (restrictionMultiplicity ψ ξ η : ℂ) *
            (restrictionMultiplicity φ η χ : ℂ) := by
    rw [
      IrreducibleCharacter.integerCharacterCombination] at hpair
    simp only [map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul] at hpair
    rw [hleft,
      normalizedPairing_restrictedCharacter_eq_restrictionMultiplicity
    ] at hpair
    simp_rw [hterm,
      normalizedPairing_restrictedCharacter_eq_restrictionMultiplicity]
      at hpair
    simpa only [
      Int.cast_natCast, mul_comm] using hpair
  exact_mod_cast hcomplex

end CliffordCorrespondence
end McKayConjecture
