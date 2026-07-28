/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Gallagher
import McKayConjecture.Character.PGroupQuotientGallagher

/-!
# Changing the base extension in Gallagher coordinates

Gallagher coordinates on the irreducible characters above a normal-subgroup
character are introduced by choosing one extension of that character.  The
choice is harmless: replacing the base extension by its twist through a
quotient-linear character translates every quotient parameter by that same
linear character.

The results in this file state this at both the unrestricted character level
and in the prime-to-`p` fibre over a finite `p`-group quotient.  This is the
choice-independence input needed when proving normalizer covariance of
orbitwise Gallagher constructions.
-/

noncomputable section

namespace McKayConjecture
namespace IrreducibleCharacter

variable {K : Type} [Group K] [Finite K]
variable {H : Subgroup K} [H.Normal]
variable {χ : IrreducibleCharacter H}
variable {ψ₁ ψ₂ : IrreducibleCharacter K}

/-- The multiplicative-linear presentation of the prime-to-`p` Gallagher
correspondence has the expected underlying tensor character. -/
@[simp]
theorem gallagherLinearCorrespondenceOfPGroupQuotient_coe
    {p : ℕ} [Fact p.Prime]
    (hquotient : IsPGroup p (K ⧸ H))
    (hψ : IsExtensionAlong H.subtype χ ψ₁)
    (hχp : χ.IsPPrimeDegree p)
    (lam : (K ⧸ H) →* ℂˣ) :
    (gallagherLinearCorrespondenceOfPGroupQuotient
        H hquotient hψ hχp lam).1.1 =
      gallagherTensorCharacter hψ (linear lam) :=
  rfl

/-- If the second base extension is the quotient-linear twist of the first,
then its Gallagher parameter `mu` represents the same ambient character as
the parameter `lam * mu` relative to the first base extension. -/
theorem gallagherTensorCharacter_linear_baseChange
    (hψ₁ : IsExtensionAlong H.subtype χ ψ₁)
    (hψ₂ : IsExtensionAlong H.subtype χ ψ₂)
    (lam mu : (K ⧸ H) →* ℂˣ)
    (hbase :
      ψ₂ =
        twist (inflateLinearCharacter H lam) ψ₁) :
    gallagherTensorCharacter hψ₂ (linear mu) =
      gallagherTensorCharacter hψ₁ (linear (lam * mu)) := by
  apply IrreducibleCharacter.ext
  funext g
  rw [gallagherTensorCharacter_values,
    gallagherTensorCharacter_values, hbase,
    twist_values, linear_values, linear_values]
  change
    ((lam (QuotientGroup.mk' H g) : ℂ) * ψ₁.values g) *
        (mu (QuotientGroup.mk' H g) : ℂ) =
      ψ₁.values g *
        (((lam * mu) (QuotientGroup.mk' H g) : ℂ))
  simp only [MonoidHom.mul_apply, Units.val_mul]
  ring

/-- Base change for the prime-to-`p` Gallagher fibre over a `p`-group
quotient. -/
theorem gallagherLinearCorrespondenceOfPGroupQuotient_baseChange
    {p : ℕ} [Fact p.Prime]
    (hquotient : IsPGroup p (K ⧸ H))
    (hψ₁ : IsExtensionAlong H.subtype χ ψ₁)
    (hψ₂ : IsExtensionAlong H.subtype χ ψ₂)
    (hχp : χ.IsPPrimeDegree p)
    (lam mu : (K ⧸ H) →* ℂˣ)
    (hbase :
      ψ₂ =
        twist (inflateLinearCharacter H lam) ψ₁) :
    gallagherLinearCorrespondenceOfPGroupQuotient
        H hquotient hψ₂ hχp mu =
      gallagherLinearCorrespondenceOfPGroupQuotient
        H hquotient hψ₁ hχp (lam * mu) := by
  apply Subtype.ext
  apply Subtype.ext
  simpa using
    gallagherTensorCharacter_linear_baseChange
      hψ₁ hψ₂ lam mu hbase

/-- Any two base extensions differ by a quotient-linear parameter, and that
single parameter translates their entire prime-to-`p` Gallagher fibres. -/
theorem exists_gallagherLinearCorrespondence_baseChangeParameter
    {p : ℕ} [Fact p.Prime]
    (hquotient : IsPGroup p (K ⧸ H))
    (hψ₁ : IsExtensionAlong H.subtype χ ψ₁)
    (hψ₂ : IsExtensionAlong H.subtype χ ψ₂)
    (hχp : χ.IsPPrimeDegree p) :
    ∃ lam : (K ⧸ H) →* ℂˣ,
      ∀ mu : (K ⧸ H) →* ℂˣ,
        gallagherLinearCorrespondenceOfPGroupQuotient
            H hquotient hψ₂ hχp mu =
          gallagherLinearCorrespondenceOfPGroupQuotient
            H hquotient hψ₁ hχp (lam * mu) := by
  let ψ₂Extension : Extensions H χ :=
    ⟨ψ₂, hψ₂⟩
  obtain ⟨lam, hlam⟩ :=
    (quotientTwistExtension_surjective hψ₁) ψ₂Extension
  refine ⟨lam, fun mu ↦ ?_⟩
  apply
    gallagherLinearCorrespondenceOfPGroupQuotient_baseChange
      hquotient hψ₁ hψ₂ hχp lam mu
  exact congrArg Subtype.val hlam.symm

/-- The unique quotient-linear character carrying one chosen extension to
another. -/
def gallagherBaseChangeParameter
    (hψ₁ : IsExtensionAlong H.subtype χ ψ₁)
    (hψ₂ : IsExtensionAlong H.subtype χ ψ₂) :
    (K ⧸ H) →* ℂˣ :=
  Classical.choose
    (existsUnique_quotientLinearCharacter_twist
      hψ₁ (⟨ψ₂, hψ₂⟩ : Extensions H χ))

/-- The canonical base-change parameter really twists the first extension
to the second. -/
theorem gallagherBaseChangeParameter_spec
    (hψ₁ : IsExtensionAlong H.subtype χ ψ₁)
    (hψ₂ : IsExtensionAlong H.subtype χ ψ₂) :
    ψ₂ =
      twist
        (inflateLinearCharacter H
          (gallagherBaseChangeParameter hψ₁ hψ₂))
        ψ₁ :=
  (Classical.choose_spec
    (existsUnique_quotientLinearCharacter_twist
      hψ₁ (⟨ψ₂, hψ₂⟩ : Extensions H χ))).1

/-- Characterization of the canonical base-change parameter. -/
theorem eq_gallagherBaseChangeParameter
    (hψ₁ : IsExtensionAlong H.subtype χ ψ₁)
    (hψ₂ : IsExtensionAlong H.subtype χ ψ₂)
    (lam : (K ⧸ H) →* ℂˣ)
    (hlam :
      ψ₂ =
        twist (inflateLinearCharacter H lam) ψ₁) :
    lam = gallagherBaseChangeParameter hψ₁ hψ₂ :=
  (Classical.choose_spec
    (existsUnique_quotientLinearCharacter_twist
      hψ₁ (⟨ψ₂, hψ₂⟩ : Extensions H χ))).2 lam hlam

/-- The base-change parameter from an extension to itself is trivial. -/
@[simp]
theorem gallagherBaseChangeParameter_self
    (hψ : IsExtensionAlong H.subtype χ ψ₁) :
    gallagherBaseChangeParameter hψ hψ = 1 := by
  symm
  apply eq_gallagherBaseChangeParameter hψ hψ
  apply IrreducibleCharacter.ext
  funext g
  simp [inflateLinearCharacter]

/-- Base-change parameters compose.  The order reflects the convention
`twist (lam * mu) ψ = twist lam (twist mu ψ)`. -/
theorem gallagherBaseChangeParameter_trans
    {ψ₃ : IrreducibleCharacter K}
    (hψ₁ : IsExtensionAlong H.subtype χ ψ₁)
    (hψ₂ : IsExtensionAlong H.subtype χ ψ₂)
    (hψ₃ : IsExtensionAlong H.subtype χ ψ₃) :
    gallagherBaseChangeParameter hψ₁ hψ₃ =
      gallagherBaseChangeParameter hψ₂ hψ₃ *
        gallagherBaseChangeParameter hψ₁ hψ₂ := by
  symm
  apply eq_gallagherBaseChangeParameter hψ₁ hψ₃
  rw [inflateLinearCharacter, MonoidHom.mul_comp,
    twist_mul]
  change
    ψ₃ =
      twist
        (inflateLinearCharacter H
          (gallagherBaseChangeParameter hψ₂ hψ₃))
        (twist
          (inflateLinearCharacter H
            (gallagherBaseChangeParameter hψ₁ hψ₂))
          ψ₁)
  rw [← gallagherBaseChangeParameter_spec hψ₁ hψ₂,
    ← gallagherBaseChangeParameter_spec hψ₂ hψ₃]

/-- The inverse base change is represented by the inverse quotient-linear
character. -/
theorem gallagherBaseChangeParameter_symm
    (hψ₁ : IsExtensionAlong H.subtype χ ψ₁)
    (hψ₂ : IsExtensionAlong H.subtype χ ψ₂) :
    gallagherBaseChangeParameter hψ₂ hψ₁ =
      (gallagherBaseChangeParameter hψ₁ hψ₂)⁻¹ := by
  have htrans :=
    gallagherBaseChangeParameter_trans
      hψ₁ hψ₂ hψ₁
  rw [gallagherBaseChangeParameter_self] at htrans
  have hmul :
      gallagherBaseChangeParameter hψ₂ hψ₁ *
          gallagherBaseChangeParameter hψ₁ hψ₂ =
        1 :=
    htrans.symm
  exact
    eq_inv_of_mul_eq_one_left
      (G := (K ⧸ H) →* ℂˣ) hmul

/-- The entire prime-to-`p` Gallagher equivalence changes by left
translation through the canonical base-change parameter. -/
theorem gallagherLinearCorrespondence_baseChange
    {p : ℕ} [Fact p.Prime]
    (hquotient : IsPGroup p (K ⧸ H))
    (hψ₁ : IsExtensionAlong H.subtype χ ψ₁)
    (hψ₂ : IsExtensionAlong H.subtype χ ψ₂)
    (hχp : χ.IsPPrimeDegree p) :
    (Equiv.mulLeft
        (gallagherBaseChangeParameter hψ₁ hψ₂)).trans
      (gallagherLinearCorrespondenceOfPGroupQuotient
        H hquotient hψ₁ hχp) =
      gallagherLinearCorrespondenceOfPGroupQuotient
        H hquotient hψ₂ hχp := by
  ext mu
  exact
    (gallagherLinearCorrespondenceOfPGroupQuotient_baseChange
      hquotient hψ₁ hψ₂ hχp
      (gallagherBaseChangeParameter hψ₁ hψ₂) mu
      (gallagherBaseChangeParameter_spec hψ₁ hψ₂)).symm

end IrreducibleCharacter
end McKayConjecture
