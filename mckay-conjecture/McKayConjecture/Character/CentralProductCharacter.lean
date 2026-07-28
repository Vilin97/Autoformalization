/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CyclicExtensionIntertwiner
import McKayConjecture.Character.InternalCentralProduct
import McKayConjecture.CharacterTriple.Product

/-!
# Irreducible characters of internal central products

Compatible irreducible characters of two commuting central factors have an
external tensor representation which is trivial on the central kernel of the
multiplication map.  It therefore descends to the quotient and transports to
the internal central-product subgroup.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace McKayConjecture

open CharacterTriple

namespace FDRep

variable {G : Type u} [Group G]
variable (V : FDRep ℂ G) (N : Subgroup G) [N.Normal]

/-- A representation on which `N` acts trivially, descended to `G ⧸ N`. -/
def quotient
    (htriv : ∀ n : N, V.ρ (n : G) = LinearMap.id) :
    FDRep ℂ (G ⧸ N) := by
  letI : Representation.IsTrivial (V.ρ.comp N.subtype) :=
    ⟨htriv⟩
  exact FDRep.of (Representation.ofQuotient V.ρ N)

@[simp]
theorem quotient_ρ_mk
    (htriv : ∀ n : N, V.ρ (n : G) = LinearMap.id)
    (g : G) :
    (FDRep.quotient V N htriv).ρ (QuotientGroup.mk' N g) = V.ρ g := by
  rfl

@[simp]
theorem quotient_character_mk
    (htriv : ∀ n : N, V.ρ (n : G) = LinearMap.id)
    (g : G) :
    (FDRep.quotient V N htriv).character (QuotientGroup.mk' N g) =
      V.character g := by
  rfl

/-- Descent through a quotient preserves simplicity. -/
theorem quotient_simple
    [Simple V]
    (htriv : ∀ n : N, V.ρ (n : G) = LinearMap.id) :
    Simple (FDRep.quotient V N htriv) := by
  letI : Representation.IsTrivial (V.ρ.comp N.subtype) :=
    ⟨htriv⟩
  let σ : Representation ℂ (G ⧸ N) V :=
    Representation.ofQuotient V.ρ N
  have hcomp :
      σ.comp (QuotientGroup.mk' N) = V.ρ := by
    ext g v
    exact Representation.ofQuotient_coe_apply V.ρ N g v
  letI : Representation.IsIrreducible V.ρ :=
    CliffordRestriction.isIrreducible_of_simple V
  letI : Representation.IsIrreducible σ :=
    RepresentationTheory.Representation.isIrreducible_of_isIrreducible_comp σ
      (hcomp ▸ (inferInstance :
        Representation.IsIrreducible V.ρ))
  exact FDRep.simple_of_representation_isIrreducible σ

end FDRep

namespace InternalCentralProduct

variable {G : Type u} [Group G]
variable (P : InternalCentralProduct G)

/-- The external tensor realization is trivial on the multiplication kernel. -/
def KernelCompatible
    (χ : IrreducibleCharacter P.left)
    (ψ : IrreducibleCharacter P.right) : Prop :=
  ∀ n : P.kernel,
    (FDRep.externalTensor χ.realization ψ.realization).ρ (n : P.left × P.right) =
      LinearMap.id

/-- Compatibility of the central characters on the overlap: every overlap
element acts on the two simple realizations by the same nonzero scalar. -/
def CompatibleCentralCharacters
    (χ : IrreducibleCharacter P.left)
    (ψ : IrreducibleCharacter P.right) : Prop :=
  ∀ z : (P.left ⊓ P.right : Subgroup G),
    ∃ c : ℂˣ,
      χ.realization.ρ
          ⟨(z : G), z.property.1⟩ =
          (scalarLinearEquiv ℂ χ.realization c : χ.realization →ₗ[ℂ] χ.realization) ∧
        ψ.realization.ρ
          ⟨(z : G), z.property.2⟩ =
          (scalarLinearEquiv ℂ ψ.realization c : ψ.realization →ₗ[ℂ] ψ.realization)

/-- Equal scalar actions on the overlap make the external tensor trivial on
the anti-diagonal multiplication kernel. -/
theorem kernelCompatible_of_compatibleCentralCharacters
    (χ : IrreducibleCharacter P.left)
    (ψ : IrreducibleCharacter P.right)
    (hcompat : P.CompatibleCentralCharacters χ ψ) :
    P.KernelCompatible χ ψ := by
  intro n
  have hn :
      (n.1.1 : G) * (n.1.2 : G) = 1 :=
    (P.mem_kernel_iff n.1).mp n.2
  have hn₂ : (n.1.2 : G) = (n.1.1 : G)⁻¹ :=
    eq_inv_of_mul_eq_one_right hn
  have hnright : (n.1.1 : G) ∈ P.right := by
    rw [← inv_inv (n.1.1 : G), ← hn₂]
    exact P.right.inv_mem n.1.2.property
  let z : (P.left ⊓ P.right : Subgroup G) :=
    ⟨(n.1.1 : G), ⟨n.1.1.property, hnright⟩⟩
  obtain ⟨c, hcχ, hcψ⟩ := hcompat z
  have hn₂sub :
      n.1.2 =
        (⟨(z : G), z.property.2⟩ : P.right)⁻¹ := by
    apply Subtype.ext
    exact hn₂
  have hcψinv :
      ψ.realization.ρ n.1.2 =
        (scalarLinearEquiv ℂ ψ.realization c⁻¹ :
          ψ.realization →ₗ[ℂ] ψ.realization) := by
    rw [hn₂sub]
    apply LinearMap.ext
    intro v
    have h :=
      Representation.inv_self_apply ψ.realization.ρ
        (⟨(z : G), z.property.2⟩ : P.right) v
    rw [hcψ] at h
    change
      ψ.realization.ρ
          (⟨(z : G), z.property.2⟩ : P.right)⁻¹
          ((c : ℂ) • v) = v at h
    rw [map_smul] at h
    calc
      ψ.realization.ρ
          (⟨(z : G), z.property.2⟩ : P.right)⁻¹ v =
          (c⁻¹ : ℂ) •
            ((c : ℂ) •
              ψ.realization.ρ
                (⟨(z : G), z.property.2⟩ : P.right)⁻¹ v) := by
            simp [smul_smul]
      _ = (c⁻¹ : ℂ) • v := by
            rw [h]
      _ = scalarLinearEquiv ℂ ψ.realization c⁻¹ v := by
        simpa only [Units.val_inv_eq_inv_val] using
          (scalarLinearEquiv_apply ℂ ψ.realization c⁻¹ v).symm
      _ =
          (scalarLinearEquiv ℂ ψ.realization c⁻¹ :
            ψ.realization →ₗ[ℂ] ψ.realization) v := by
            rfl
  rw [FDRep.externalTensor_ρ_apply]
  change
    TensorProduct.map
        (χ.realization.ρ n.1.1)
        (ψ.realization.ρ n.1.2) =
      LinearMap.id
  have hn₁sub :
      n.1.1 = ⟨(z : G), z.property.1⟩ := by
    apply Subtype.ext
    rfl
  rw [hn₁sub, hcχ, hcψinv]
  have hscalar :=
    congrArg LinearEquiv.toLinearMap
      (CharacterTriple.TensorProduct.congr_scalarLinearEquiv
        (V := χ.realization) (W := ψ.realization) c c⁻¹)
  simpa using hscalar

/-- The descended external tensor character on the quotient by the central
kernel. -/
def quotientCharacter
    (χ : IrreducibleCharacter P.left)
    (ψ : IrreducibleCharacter P.right)
    (hker : P.KernelCompatible χ ψ) :
    IrreducibleCharacter ((P.left × P.right) ⧸ P.kernel) := by
  let V := FDRep.externalTensor χ.realization ψ.realization
  letI : Simple V :=
    FDRep.externalTensor_simple χ.realization ψ.realization
  letI : Simple (FDRep.quotient V P.kernel hker) :=
    FDRep.quotient_simple V P.kernel hker
  exact IrreducibleCharacter.ofSimple
    (FDRep.quotient V P.kernel hker)

@[simp]
theorem quotientCharacter_values_mk
    (χ : IrreducibleCharacter P.left)
    (ψ : IrreducibleCharacter P.right)
    (hker : P.KernelCompatible χ ψ)
    (z : P.left × P.right) :
    (P.quotientCharacter χ ψ hker).values
        (QuotientGroup.mk' P.kernel z) =
      χ.values z.1 * ψ.values z.2 := by
  unfold quotientCharacter
  dsimp only
  change
    (FDRep.externalTensor χ.realization ψ.realization).character z =
      χ.values z.1 * ψ.values z.2
  rw [FDRep.externalTensor_character,
    χ.realization_character, ψ.realization_character]

/-- The irreducible character of the internal central-product subgroup. -/
def character
    (χ : IrreducibleCharacter P.left)
    (ψ : IrreducibleCharacter P.right)
    (hker : P.KernelCompatible χ ψ) :
    IrreducibleCharacter P.subgroup :=
  (P.quotientCharacter χ ψ hker).comap P.quotientEquiv.symm

@[simp]
theorem character_values_multiplication
    (χ : IrreducibleCharacter P.left)
    (ψ : IrreducibleCharacter P.right)
    (hker : P.KernelCompatible χ ψ)
    (z : P.left × P.right) :
    (P.character χ ψ hker).values
        ⟨P.multiplication z, ⟨z, rfl⟩⟩ =
      χ.values z.1 * ψ.values z.2 := by
  rw [character, IrreducibleCharacter.comap_values]
  have hq :
      P.quotientEquiv.symm
          ⟨P.multiplication z, ⟨z, rfl⟩⟩ =
        QuotientGroup.mk' P.kernel z := by
    apply P.quotientEquiv.injective
    rw [P.quotientEquiv.apply_symm_apply, P.quotientEquiv_mk]
  rw [hq, P.quotientCharacter_values_mk]

@[simp]
theorem character_degree
    (χ : IrreducibleCharacter P.left)
    (ψ : IrreducibleCharacter P.right)
    (hker : P.KernelCompatible χ ψ) :
    (P.character χ ψ hker).degree = χ.degree * ψ.degree := by
  rw [character, IrreducibleCharacter.comap_degree]
  unfold quotientCharacter
  dsimp only
  change
    Module.finrank ℂ
      (FDRep.externalTensor χ.realization ψ.realization) =
      χ.degree * ψ.degree
  rw [FDRep.externalTensor_finrank,
    χ.realization_finrank, ψ.realization_finrank]

/-- Prime-to-`p` degree is coordinatewise for a central-product character. -/
theorem character_isPPrimeDegree_iff
    (p : ℕ) (hp : p.Prime)
    (χ : IrreducibleCharacter P.left)
    (ψ : IrreducibleCharacter P.right)
    (hker : P.KernelCompatible χ ψ) :
    (P.character χ ψ hker).IsPPrimeDegree p ↔
      χ.IsPPrimeDegree p ∧ ψ.IsPPrimeDegree p := by
  rw [IrreducibleCharacter.IsPPrimeDegree,
    P.character_degree χ ψ hker,
    IrreducibleCharacter.IsPPrimeDegree,
    IrreducibleCharacter.IsPPrimeDegree]
  constructor
  · intro h
    exact
      ⟨fun hχ => h (hp.dvd_mul.mpr (Or.inl hχ)),
        fun hψ => h (hp.dvd_mul.mpr (Or.inr hψ))⟩
  · rintro ⟨hχ, hψ⟩ hpdiv
    rcases hp.dvd_mul.mp hpdiv with hpχ | hpψ
    · exact hχ hpχ
    · exact hψ hpψ

/-- The multiplication pullback formula uniquely determines the internal
central-product character. -/
theorem character_unique
    (χ : IrreducibleCharacter P.left)
    (ψ : IrreducibleCharacter P.right)
    (hker : P.KernelCompatible χ ψ)
    (θ : IrreducibleCharacter P.subgroup)
    (hθ : ∀ z : P.left × P.right,
      θ.values ⟨P.multiplication z, ⟨z, rfl⟩⟩ =
        χ.values z.1 * ψ.values z.2) :
    θ = P.character χ ψ hker := by
  apply IrreducibleCharacter.ext
  funext g
  obtain ⟨z, hz⟩ := g.property
  have hg :
      g = ⟨P.multiplication z, ⟨z, rfl⟩⟩ := by
    apply Subtype.ext
    exact hz.symm
  subst g
  rw [hθ, P.character_values_multiplication]

/-- Construction directly from compatible central characters. -/
def characterOfCompatible
    (χ : IrreducibleCharacter P.left)
    (ψ : IrreducibleCharacter P.right)
    (hcompat : P.CompatibleCentralCharacters χ ψ) :
    IrreducibleCharacter P.subgroup :=
  P.character χ ψ
    (P.kernelCompatible_of_compatibleCentralCharacters χ ψ hcompat)

@[simp]
theorem characterOfCompatible_values_multiplication
    (χ : IrreducibleCharacter P.left)
    (ψ : IrreducibleCharacter P.right)
    (hcompat : P.CompatibleCentralCharacters χ ψ)
    (z : P.left × P.right) :
    (P.characterOfCompatible χ ψ hcompat).values
        ⟨P.multiplication z, ⟨z, rfl⟩⟩ =
      χ.values z.1 * ψ.values z.2 :=
  P.character_values_multiplication χ ψ _ z

@[simp]
theorem characterOfCompatible_degree
    (χ : IrreducibleCharacter P.left)
    (ψ : IrreducibleCharacter P.right)
    (hcompat : P.CompatibleCentralCharacters χ ψ) :
    (P.characterOfCompatible χ ψ hcompat).degree =
      χ.degree * ψ.degree :=
  P.character_degree χ ψ _

/-- Compatible factor characters determine a unique irreducible character on
the internal central product with the prescribed multiplication formula. -/
theorem characterOfCompatible_unique
    (χ : IrreducibleCharacter P.left)
    (ψ : IrreducibleCharacter P.right)
    (hcompat : P.CompatibleCentralCharacters χ ψ)
    (θ : IrreducibleCharacter P.subgroup)
    (hθ : ∀ z : P.left × P.right,
      θ.values ⟨P.multiplication z, ⟨z, rfl⟩⟩ =
        χ.values z.1 * ψ.values z.2) :
    θ = P.characterOfCompatible χ ψ hcompat :=
  P.character_unique χ ψ _ θ hθ

/-- Prime-to-`p` degree for the construction from compatible central
characters. -/
theorem characterOfCompatible_isPPrimeDegree_iff
    (p : ℕ) (hp : p.Prime)
    (χ : IrreducibleCharacter P.left)
    (ψ : IrreducibleCharacter P.right)
    (hcompat : P.CompatibleCentralCharacters χ ψ) :
    (P.characterOfCompatible χ ψ hcompat).IsPPrimeDegree p ↔
      χ.IsPPrimeDegree p ∧ ψ.IsPPrimeDegree p :=
  P.character_isPPrimeDegree_iff p hp χ ψ _

end InternalCentralProduct
end McKayConjecture
