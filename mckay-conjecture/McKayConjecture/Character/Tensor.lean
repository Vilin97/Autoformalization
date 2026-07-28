/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Extension

/-!
# Tensor products with inflated quotient representations

This file provides the representation-theoretic tensor construction used in
Gallagher's theorem.  If `H ⫳ K`, a representation of `K/H` inflates along
the quotient map and can then be tensored with a representation of `K`.
The character and degree formulas are recorded explicitly.

For an irreducible character `χ` of `H` with extension `ψ` to `K`, the
restriction of this tensor product is a direct character multiple of `χ`.
The irreducibility and classification statements are proved separately in
`Character.GallagherCorrespondence`.
-/

noncomputable section

open CategoryTheory
open scoped MonoidalCategory

universe u

namespace McKayConjecture
namespace IrreducibleCharacter

variable {K : Type u} [Group K]
variable (H : Subgroup K) [hH : H.Normal]

/-! ### Inflation and tensor products -/

/-- Inflation of a finite-dimensional representation of `K/H` to `K`. -/
abbrev inflateFDRep (V : FDRep ℂ (K ⧸ H)) : FDRep ℂ K :=
  FDRep.res (QuotientGroup.mk' H) V

@[simp]
theorem inflateFDRep_character
    (V : FDRep ℂ (K ⧸ H)) (g : K) :
    (inflateFDRep H V).character g =
      V.character (QuotientGroup.mk' H g) :=
  FDRep.res_character_apply (QuotientGroup.mk' H) V g

/-- Tensor a `K`-representation with an inflated `K/H`-representation. -/
abbrev tensorInflationFDRep
    (V : FDRep ℂ K) (W : FDRep ℂ (K ⧸ H)) :
    FDRep ℂ K :=
  V ⊗ inflateFDRep H W

@[simp]
theorem tensorInflationFDRep_character
    (V : FDRep ℂ K) (W : FDRep ℂ (K ⧸ H)) (g : K) :
    (tensorInflationFDRep H V W).character g =
      V.character g *
        W.character (QuotientGroup.mk' H g) := by
  have hchar :=
    congrFun (FDRep.char_tensor V (inflateFDRep H W)) g
  simpa only [Pi.mul_apply, inflateFDRep_character] using hchar

@[simp]
theorem tensorInflationFDRep_finrank
    (V : FDRep ℂ K) (W : FDRep ℂ (K ⧸ H)) :
    Module.finrank ℂ (tensorInflationFDRep H V W) =
      Module.finrank ℂ V * Module.finrank ℂ W := by
  exact Module.finrank_tensorProduct

/-- The tensor product attached to a fixed irreducible extension and a
quotient representation. -/
abbrev extensionTensorFDRep
    (ψ : IrreducibleCharacter K)
    (W : FDRep ℂ (K ⧸ H)) :
    FDRep ℂ K :=
  tensorInflationFDRep H ψ.realization W

@[simp]
theorem extensionTensorFDRep_character
    (ψ : IrreducibleCharacter K)
    (W : FDRep ℂ (K ⧸ H)) (g : K) :
    (extensionTensorFDRep H ψ W).character g =
      ψ.values g *
        W.character (QuotientGroup.mk' H g) := by
  rw [tensorInflationFDRep_character,
    ψ.realization_character]

@[simp]
theorem extensionTensorFDRep_finrank
    (ψ : IrreducibleCharacter K)
    (W : FDRep ℂ (K ⧸ H)) :
    Module.finrank ℂ (extensionTensorFDRep H ψ W) =
      ψ.degree * Module.finrank ℂ W := by
  rw [tensorInflationFDRep_finrank,
    ψ.realization_finrank]

/-! ### Consequences of extending an irreducible normal character -/

variable {H}
variable {χ : IrreducibleCharacter H}
variable {ψ : IrreducibleCharacter K}

/-- An irreducible normal-subgroup character admitting an ambient extension
is invariant under the ambient group. -/
theorem IsExtensionAlong.conjBy_eq
    (hψ : IsExtensionAlong H.subtype χ ψ) (g : K) :
    conjBy H g χ = χ := by
  apply IrreducibleCharacter.ext
  funext h
  rw [conjBy_values]
  let x : H := (MulAut.conjNormal g).symm h
  calc
    χ.values x = ψ.values (x : K) :=
      (hψ x).symm
    _ = ψ.values (h : K) := by
      have hclass :=
        ClassFunction.conj_apply ψ.toClassFunction
          (h : K) g⁻¹
      simpa [x] using hclass
    _ = χ.values h := hψ h

/-- On the normal subgroup, tensoring an extension by an inflated quotient
character multiplies the original character by the quotient degree. -/
theorem extensionTensorFDRep_restrict_character
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (beta : IrreducibleCharacter (K ⧸ H)) (h : H) :
    (FDRep.res H.subtype
      (extensionTensorFDRep H ψ beta.realization)).character h =
        (beta.degree : ℂ) * χ.values h := by
  rw [FDRep.res_character_apply,
    extensionTensorFDRep_character, hψ h]
  have hquot :
      QuotientGroup.mk' H (H.subtype h) = 1 :=
    (QuotientGroup.eq_one_iff (H.subtype h)).2 h.property
  rw [hquot, beta.realization_character,
    beta.value_one]
  exact mul_comm _ _

end IrreducibleCharacter
end McKayConjecture
