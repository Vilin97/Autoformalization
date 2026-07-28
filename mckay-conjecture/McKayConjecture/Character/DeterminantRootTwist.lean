/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Determination
import McKayConjecture.Character.DirectProductLinearExtension
import McKayConjecture.Character.PPrimeDeterminantRoot
import McKayConjecture.Character.Twist

/-!
# Determinant roots and linear twists

Twisting a representation by a linear character multiplies its determinant by
the degree-th power of that linear character.  If the degree is coprime to the
order of a finite source group, the determinant-root normalization removes
that degree-th power and therefore commutes with twisting.

We also record the corresponding elementary compatibility for the standard
linear extensions from the first factor of a direct product.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace IrreducibleCharacter

universe u v

variable {G : Type u} [Group G] [Finite G]

/-- The determinant of a linear twist is the original determinant multiplied
by the degree-th power of the twisting character. -/
theorem determinantParameter_twist
    (lam : G →* ℂˣ) (χ : IrreducibleCharacter G) :
    determinantParameter (twist lam χ) =
      (lam ^ χ.degree) * determinantParameter χ := by
  apply MonoidHom.ext
  intro g
  let V : FDRep ℂ G := twistFDRep lam χ.realization
  have hcharacter :
      (twist lam χ).realization.character = V.character := by
    rw [(twist lam χ).realization_character]
    funext x
    simp [V]
  letI : Simple V := by
    dsimp [V]
    exact twistFDRep_simple lam χ.realization
  obtain ⟨i : (twist lam χ).realization ≅ V⟩ :=
    FDRep.nonempty_iso_of_character_eq
      (twist lam χ).realization V hcharacter
  have hdet :
      LinearMap.det
          ((twist lam χ).realization.ρ g :
            (twist lam χ).realization →ₗ[ℂ]
              (twist lam χ).realization) =
        LinearMap.det (V.ρ g : V →ₗ[ℂ] V) := by
    rw [FDRep.Iso.conj_ρ i g, LinearEquiv.conj_apply,
      LinearMap.comp_assoc, LinearMap.det_conj]
  apply Units.ext
  rw [determinantParameter_eq_det]
  simp only [MonoidHom.mul_apply, MonoidHom.pow_apply,
    Units.val_mul, Units.val_pow_eq_pow_val]
  rw [determinantParameter_eq_det]
  rw [hdet]
  change
    LinearMap.det ((lam g : ℂ) •
        (χ.realization.ρ g :
          χ.realization →ₗ[ℂ] χ.realization)) =
      (lam g : ℂ) ^ χ.degree *
        LinearMap.det
          (χ.realization.ρ g :
            χ.realization →ₗ[ℂ] χ.realization)
  rw [LinearMap.det_smul, χ.realization_finrank]

variable {H : Type v} [Group H]

/-- Determinant-root normalization commutes with twisting by a linear
character. -/
theorem determinantRootParameter_twist
    (lam : G →* ℂˣ) (χ : IrreducibleCharacter G)
    (f : H →* G)
    (hcoprime : (Nat.card H).Coprime χ.degree) :
    determinantRootParameter (twist lam χ) f
        (by simpa using hcoprime) =
      (lam.comp f) *
        determinantRootParameter χ f hcoprime := by
  apply MonoidHom.ext
  intro h
  let mu : ℂˣ := lam (f h)
  have hmuOrder : mu ^ Nat.card H = 1 := by
    change lam (f h) ^ Nat.card H = 1
    calc
      lam (f h) ^ Nat.card H =
          lam ((f h) ^ Nat.card H) := by
        exact (map_pow lam (f h) (Nat.card H)).symm
      _ = lam (f (h ^ Nat.card H)) := by
        exact congrArg lam
          (map_pow f h (Nat.card H)).symm
      _ = 1 := by
        rw [pow_card_eq_one']
        simp
  have hroot :
      mu =
        (mu ^ χ.degree) ^
          (Nat.card H).gcdB χ.degree :=
    eq_pow_gcdB_of_pow_eq_one
      mu (Nat.card H) χ.degree hcoprime hmuOrder
  change
    (determinantParameter (twist lam χ) (f h)) ^
        (Nat.card H).gcdB (twist lam χ).degree =
      lam (f h) *
        (determinantParameter χ (f h)) ^
          (Nat.card H).gcdB χ.degree
  rw [twist_degree, determinantParameter_twist,
    MonoidHom.mul_apply, MonoidHom.pow_apply]
  exact
    calc
      (lam (f h) ^ χ.degree *
            determinantParameter χ (f h)) ^
          (Nat.card H).gcdB χ.degree =
        (lam (f h) ^ χ.degree) ^
              (Nat.card H).gcdB χ.degree *
            (determinantParameter χ (f h)) ^
              (Nat.card H).gcdB χ.degree :=
          mul_zpow _ _ _
      _ = lam (f h) *
            (determinantParameter χ (f h)) ^
              (Nat.card H).gcdB χ.degree := by
        simpa [mu] using congrArg
          (fun z : ℂˣ ↦
            z *
              (determinantParameter χ (f h)) ^
                (Nat.card H).gcdB χ.degree)
          hroot.symm

section DirectProduct

variable {A B : Type} [Group A] [Group B]

/-- Multiplying the chosen second-factor parameter of a direct-product
extension is the same as twisting the extension by that parameter. -/
theorem directProductFirstFactorLinearExtension_mul
    (χ :
      IrreducibleCharacter
        (directProductFirstFactor (G := A) (H := B)))
    (lam mu : B →* ℂˣ) :
    directProductFirstFactorLinearExtension χ (lam * mu) =
      twist (mu.comp (MonoidHom.snd A B))
        (directProductFirstFactorLinearExtension χ lam) := by
  apply IrreducibleCharacter.ext
  funext x
  rw [directProductFirstFactorLinearExtension,
    directProductFirstFactorLinearExtension,
    externalTensor_values, linear_values,
    twist_values, externalTensor_values, linear_values]
  simp [mul_left_comm, mul_comm]

end DirectProduct

end IrreducibleCharacter
end McKayConjecture
