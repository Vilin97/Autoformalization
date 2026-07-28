/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CyclicExtensionConstruction
import McKayConjecture.Character.Extension
import McKayConjecture.Character.Linear

/-!
# Twisting irreducible characters by linear characters

Tensoring with a one-dimensional representation preserves simplicity.  For
finite groups this is proved directly from mathlib's character-norm
criterion.  The resulting operation multiplies character values, preserves
degree, and is compatible with extension along homomorphisms.
-/

noncomputable section

open CategoryTheory

universe u v

namespace McKayConjecture
namespace IrreducibleCharacter

variable {G : Type u} [Group G]

/-- Scale the operators of `V` by the linear character `lam`. -/
def twistRepresentation (lam : G →* ℂˣ) (V : FDRep ℂ G) :
    Representation ℂ G V where
  toFun g := (lam g : ℂ) • V.ρ g
  map_one' := by
    rw [map_one, Units.val_one, one_smul, map_one]
  map_mul' g h := by
    rw [map_mul, Units.val_mul, map_mul]
    ext v
    simp [Module.End.mul_apply, smul_smul, mul_comm]

/-- The finite-dimensional representation obtained by twisting `V`. -/
abbrev twistFDRep (lam : G →* ℂˣ) (V : FDRep ℂ G) :
    FDRep ℂ G :=
  FDRep.of (twistRepresentation lam V)

@[simp]
theorem twistFDRep_character (lam : G →* ℂˣ) (V : FDRep ℂ G)
    (g : G) :
    (twistFDRep lam V).character g =
      (lam g : ℂ) * V.character g := by
  change
    LinearMap.trace ℂ V ((lam g : ℂ) • V.ρ g) =
      (lam g : ℂ) * LinearMap.trace ℂ V (V.ρ g)
  rw [map_smul]
  rfl

@[simp]
theorem twistFDRep_finrank (lam : G →* ℂˣ) (V : FDRep ℂ G) :
    Module.finrank ℂ (twistFDRep lam V) =
      Module.finrank ℂ V := by
  rfl

/-- Tensoring a simple representation by a linear character remains simple. -/
theorem twistFDRep_simple
    (lam : G →* ℂˣ) (V : FDRep ℂ G) [Simple V] :
    Simple (twistFDRep lam V) := by
  letI : Representation.IsIrreducible V.ρ :=
    CliffordRestriction.isIrreducible_of_simple V
  letI : Nontrivial V :=
    CliffordRestriction.nontrivial_of_simple V
  let ρ := twistRepresentation lam V
  letI : Nontrivial (Subrepresentation ρ) :=
    ⟨⟨⊥, ⊤, fun h =>
      bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩⟩
  letI : Representation.IsIrreducible ρ := by
    refine ⟨fun W => ?_⟩
    let W' : Subrepresentation V.ρ :=
      { toSubmodule := W.toSubmodule
        apply_mem_toSubmodule := fun g v hv => by
          have hw := W.apply_mem_toSubmodule g hv
          have hscaled :=
            W.toSubmodule.smul_mem ((lam g : ℂ)⁻¹) hw
          simpa [ρ, twistRepresentation, smul_smul] using hscaled }
    rcases eq_bot_or_eq_top W' with hW | hW
    · left
      apply Subrepresentation.ext
      change W.toSubmodule =
        (⊥ : Subrepresentation V.ρ).toSubmodule
      simpa [W'] using congrArg
        (fun Z : Subrepresentation V.ρ ↦ Z.toSubmodule) hW
    · right
      apply Subrepresentation.ext
      change W.toSubmodule =
        (⊤ : Subrepresentation V.ρ).toSubmodule
      simpa [W'] using congrArg
        (fun Z : Subrepresentation V.ρ ↦ Z.toSubmodule) hW
  exact RepresentationTheory.simple_fdRep_of_isIrreducible ρ

/-- Twist an irreducible character by a multiplicative linear character. -/
def twist (lam : G →* ℂˣ) (χ : IrreducibleCharacter G) :
    IrreducibleCharacter G := by
  letI : Simple (twistFDRep lam χ.realization) :=
    twistFDRep_simple lam χ.realization
  exact ofSimple (twistFDRep lam χ.realization)

@[simp]
theorem twist_values (lam : G →* ℂˣ)
    (χ : IrreducibleCharacter G) (g : G) :
    (twist lam χ).values g = (lam g : ℂ) * χ.values g := by
  change
    (twistFDRep lam χ.realization).character g =
      (lam g : ℂ) * χ.values g
  rw [twistFDRep_character, χ.realization_character]

@[simp]
theorem twist_degree (lam : G →* ℂˣ)
    (χ : IrreducibleCharacter G) :
    (twist lam χ).degree = χ.degree := by
  change
    Module.finrank ℂ (twistFDRep lam χ.realization) =
      χ.degree
  rw [twistFDRep_finrank, χ.realization_finrank]

@[simp]
theorem twist_one (χ : IrreducibleCharacter G) :
    twist (1 : G →* ℂˣ) χ = χ := by
  apply IrreducibleCharacter.ext
  funext g
  simp

@[simp]
theorem twist_mul (lam mu : G →* ℂˣ)
    (χ : IrreducibleCharacter G) :
    twist (lam * mu) χ = twist lam (twist mu χ) := by
  apply IrreducibleCharacter.ext
  funext g
  simp [mul_assoc]

@[simp]
theorem twist_isPPrimeDegree_iff (p : ℕ)
    (lam : G →* ℂˣ) (χ : IrreducibleCharacter G) :
    (twist lam χ).IsPPrimeDegree p ↔ χ.IsPPrimeDegree p := by
  simp only [IsPPrimeDegree, twist_degree]

section Extension

variable {H : Type v} [Group H]
variable {f : H →* G}
variable {χ : IrreducibleCharacter H}
  {ψ : IrreducibleCharacter G}

/-- Twisting commutes with restriction along a homomorphism. -/
theorem IsExtensionAlong.twist
    (hψ : IsExtensionAlong f χ ψ) (lam : G →* ℂˣ) :
    IsExtensionAlong f
      (IrreducibleCharacter.twist (lam.comp f) χ)
      (IrreducibleCharacter.twist lam ψ) := by
  intro h
  simp only [twist_values, MonoidHom.coe_comp, Function.comp_apply]
  rw [hψ h]

/-- If the linear character is trivial on the source, twisting an extension
gives another extension of the same character. -/
theorem IsExtensionAlong.twist_of_eq_one
    (hψ : IsExtensionAlong f χ ψ) (lam : G →* ℂˣ)
    (hlam : ∀ h : H, lam (f h) = 1) :
    IsExtensionAlong f χ (IrreducibleCharacter.twist lam ψ) := by
  intro h
  rw [twist_values, hψ h, hlam h, Units.val_one, one_mul]

end Extension

end IrreducibleCharacter
end McKayConjecture
