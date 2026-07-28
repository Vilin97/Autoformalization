/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.FaithfulInvariantCenter
import McKayConjecture.Character.QuotientDescent

/-!
# Kernels and faithful quotients of irreducible characters

The kernel of an irreducible character is defined as the kernel of the
honest general-linear-group action afforded by its chosen realization.
This file proves that it is the largest subgroup on which the character is
`TrivialOn`, and that descent through this kernel produces a faithful
irreducible character of the quotient.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace IrreducibleCharacter

universe u

variable {G : Type u} [Group G]

/-- The chosen realization regarded as an honest homomorphism to the
general linear group. -/
def realizationLinearEquivHom
    (χ : IrreducibleCharacter G) :
    G →* (χ.realization ≃ₗ[ℂ] χ.realization) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv
      ℂ χ.realization).toMonoidHom.comp
    χ.realization.ρ.toHomUnits

@[simp]
theorem realizationLinearEquivHom_toLinearMap
    (χ : IrreducibleCharacter G) (g : G) :
    (χ.realizationLinearEquivHom g).toLinearMap =
      χ.realization.ρ g :=
  rfl

/-- The kernel of an irreducible character, computed in its chosen
realization. -/
def kernel (χ : IrreducibleCharacter G) : Subgroup G :=
  χ.realizationLinearEquivHom.ker

instance kernelNormal (χ : IrreducibleCharacter G) :
    χ.kernel.Normal :=
  MonoidHom.normal_ker χ.realizationLinearEquivHom

@[simp]
theorem mem_kernel_iff
    (χ : IrreducibleCharacter G) (g : G) :
    g ∈ χ.kernel ↔
      χ.realization.ρ g =
        (LinearMap.id :
          Module.End ℂ χ.realization) := by
  rw [kernel, MonoidHom.mem_ker]
  constructor
  · intro h
    exact congrArg LinearEquiv.toLinearMap h
  · intro h
    apply LinearEquiv.toLinearMap_injective
    exact h

/-- A character is trivial on its kernel. -/
theorem trivialOn_kernel
    (χ : IrreducibleCharacter G) :
    χ.TrivialOn χ.kernel := by
  intro g
  exact (χ.mem_kernel_iff g).mp g.2

/-- The character kernel is the largest subgroup on which the character is
trivial. -/
theorem trivialOn_iff_le_kernel
    (χ : IrreducibleCharacter G) (N : Subgroup G) :
    χ.TrivialOn N ↔ N ≤ χ.kernel := by
  constructor
  · intro hN g hg
    exact (χ.mem_kernel_iff g).mpr (hN ⟨g, hg⟩)
  · intro hN g
    exact (χ.mem_kernel_iff g).mp (hN g.2)

/-- Faithfulness is equivalent to having trivial character kernel. -/
theorem isFaithful_iff_kernel_eq_bot
    (χ : IrreducibleCharacter G) :
    χ.IsFaithful ↔ χ.kernel = ⊥ := by
  change
    Function.Injective χ.realization.ρ ↔
      χ.realizationLinearEquivHom.ker = ⊥
  rw [MonoidHom.ker_eq_bot_iff]
  constructor
  · intro h g k hgk
    exact h (congrArg LinearEquiv.toLinearMap hgk)
  · intro h g k hgk
    exact h (LinearEquiv.toLinearMap_injective hgk)

section Finite

variable [Finite G]

/-- The explicit quotient representation obtained by descending the chosen
realization through its kernel. -/
def kernelQuotientRepresentation
    (χ : IrreducibleCharacter G) :
    FDRep ℂ (G ⧸ χ.kernel) :=
  FDRep.quotient χ.realization χ.kernel
    (trivialOn_action χ.trivialOn_kernel)

instance kernelQuotientRepresentationSimple
    (χ : IrreducibleCharacter G) :
    Simple χ.kernelQuotientRepresentation := by
  exact FDRep.quotient_simple χ.realization χ.kernel
    (trivialOn_action χ.trivialOn_kernel)

@[simp]
theorem kernelQuotientRepresentation_ρ_mk
    (χ : IrreducibleCharacter G) (g : G) :
    χ.kernelQuotientRepresentation.ρ
        (QuotientGroup.mk' χ.kernel g) =
      χ.realization.ρ g :=
  rfl

/-- The quotient representation agrees with the injective kernel lift of
the general-linear-group realization. -/
theorem kerLift_toLinearMap_eq_kernelQuotientRepresentation
    (χ : IrreducibleCharacter G)
    (q : G ⧸ χ.kernel) :
    (QuotientGroup.kerLift
        χ.realizationLinearEquivHom q).toLinearMap =
      χ.kernelQuotientRepresentation.ρ q := by
  refine Quotient.inductionOn' q ?_
  intro g
  rfl

/-- Descent through the exact realization kernel is faithful at the
representation level. -/
theorem kernelQuotientRepresentation_injective
    (χ : IrreducibleCharacter G) :
    Function.Injective χ.kernelQuotientRepresentation.ρ := by
  intro q r hqr
  apply QuotientGroup.kerLift_injective
    χ.realizationLinearEquivHom
  apply LinearEquiv.toLinearMap_injective
  rw [χ.kerLift_toLinearMap_eq_kernelQuotientRepresentation,
    χ.kerLift_toLinearMap_eq_kernelQuotientRepresentation,
    hqr]

/-- The irreducible quotient character produced by ordinary quotient
descent through the exact character kernel. -/
def faithfulQuotientCharacter
    (χ : IrreducibleCharacter G) :
    IrreducibleCharacter (G ⧸ χ.kernel) :=
  descend χ.kernel ⟨χ, χ.trivialOn_kernel⟩

@[simp]
theorem faithfulQuotientCharacter_values_mk
    (χ : IrreducibleCharacter G) (g : G) :
    χ.faithfulQuotientCharacter.values
        (QuotientGroup.mk' χ.kernel g) =
      χ.values g :=
  descend_values_mk χ.kernel
    ⟨χ, χ.trivialOn_kernel⟩ g

@[simp]
theorem faithfulQuotientCharacter_degree
    (χ : IrreducibleCharacter G) :
    χ.faithfulQuotientCharacter.degree = χ.degree :=
  descend_degree χ.kernel
    ⟨χ, χ.trivialOn_kernel⟩

/-- The character obtained by descending through the exact kernel is
faithful, even though its chosen realization need not be definitionally the
explicit quotient representation above. -/
theorem faithfulQuotientCharacter_isFaithful
    (χ : IrreducibleCharacter G) :
    χ.faithfulQuotientCharacter.IsFaithful := by
  let V := χ.kernelQuotientRepresentation
  have hchar :
      χ.faithfulQuotientCharacter.realization.character =
        V.character := by
    funext q
    obtain ⟨g, rfl⟩ :=
      QuotientGroup.mk'_surjective χ.kernel q
    rw [χ.faithfulQuotientCharacter.realization_character,
      faithfulQuotientCharacter_values_mk]
    change χ.values g = χ.realization.character g
    exact (congrFun χ.realization_character g).symm
  obtain ⟨i⟩ :=
    FDRep.nonempty_iso_of_character_eq
      χ.faithfulQuotientCharacter.realization V hchar
  intro q r hqr
  apply χ.kernelQuotientRepresentation_injective
  rw [FDRep.Iso.conj_ρ i q, FDRep.Iso.conj_ρ i r,
    hqr]

end Finite

end IrreducibleCharacter
end McKayConjecture
