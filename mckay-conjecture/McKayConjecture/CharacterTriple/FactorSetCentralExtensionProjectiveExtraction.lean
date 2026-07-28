/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GallagherCorrespondence
import McKayConjecture.Character.CentralScalar
import McKayConjecture.CharacterTriple.FactorSetCentralExtensionCharacter

/-!
# Extracting projective representations from factor-extension characters

Let `alpha : FactorSet G C` be normalized and let `iota : C →* ℂˣ`.
An irreducible character of the corresponding factor-set central extension
whose coefficient subgroup acts through `iota` determines a projective
representation of `G`.  Its chosen operator at `g` is the operator of the
extension character at the canonical base lift `(g, 1)`, and its factor is
literally `iota (alpha g h)`.

This is the positive-coefficient counterpart of the inverse-coefficient
extraction used for multiplicity characters.  The construction records
literal factor equality, not merely equality of cohomology classes.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace FactorSet
namespace CentralExtensionGroup

variable {G C : Type}
variable [Group G] [Finite G] [CommGroup C] [Finite C]
variable (alpha : FactorSet G C) (halpha : alpha.IsNormalized)

/-- The canonical lift `(g, 1)` of a base-group element. -/
def baseLift (g : G) :
    CentralExtensionGroup alpha halpha :=
  mk alpha halpha g 1

@[simp]
theorem baseLift_base (g : G) :
    base alpha halpha (baseLift alpha halpha g) = g :=
  rfl

@[simp]
theorem baseLift_coefficient (g : G) :
    coefficient alpha halpha (baseLift alpha halpha g) = 1 :=
  rfl

/-- Multiplication of base lifts exposes the factor as a coefficient
element. -/
theorem baseLift_mul (g h : G) :
    baseLift alpha halpha g * baseLift alpha halpha h =
      coefficientEmbedding alpha halpha (alpha g h) *
        baseLift alpha halpha (g * h) := by
  apply ext alpha halpha
  · simp [baseLift]
  · simp [baseLift, halpha.1]

/-- Every element is its coefficient coordinate times its base lift. -/
theorem coefficientEmbedding_mul_baseLift
    (x : CentralExtensionGroup alpha halpha) :
    coefficientEmbedding alpha halpha
          (coefficient alpha halpha x) *
        baseLift alpha halpha (base alpha halpha x) =
      x := by
  apply ext alpha halpha
  · simp [baseLift]
  · simp [baseLift, halpha.1]

/-- Character-value form of the requirement that the coefficient subgroup
act through `iota`. -/
def HasCoefficientCharacter
    (iota : C →* ℂˣ)
    (psi : IrreducibleCharacter
      (CentralExtensionGroup alpha halpha)) : Prop :=
  ∀ c : C,
    psi.values (coefficientEmbedding alpha halpha c) =
      (iota c : ℂ) * (psi.degree : ℂ)

/-- The coefficient character determines the exact scalar operator on the
chosen realization of an irreducible extension character. -/
theorem realization_coefficientEmbedding
    (iota : C →* ℂˣ)
    (psi : IrreducibleCharacter
      (CentralExtensionGroup alpha halpha))
    (hpsi : HasCoefficientCharacter alpha halpha iota psi)
    (c : C) :
    IrreducibleCharacter.extensionRealizationAction (ψ := psi)
        (coefficientEmbedding alpha halpha c) =
      scalarLinearEquiv ℂ psi.realization (iota c) := by
  let z := coefficientEmbedding alpha halpha c
  have hz :
      z ∈ Subgroup.center
        (CentralExtensionGroup alpha halpha) := by
    exact
      coefficientEmbedding_range_le_center alpha halpha
        ⟨c, rfl⟩
  obtain ⟨d, hd⟩ :=
    psi.exists_realization_scalar_of_mem_center z hz
  have hdegree :
      d * (psi.degree : ℂ) =
        (iota c : ℂ) * (psi.degree : ℂ) := by
    rw [← psi.values_eq_scalar_mul_degree z d hd]
    exact hpsi c
  have hdValue : d = (iota c : ℂ) :=
    mul_right_cancel₀
      (Nat.cast_ne_zero.mpr psi.degree_ne_zero) hdegree
  apply LinearEquiv.toLinearMap_injective
  rw [IrreducibleCharacter.extensionRealizationAction_toLinearMap, hd]
  ext v
  change d • v = (iota c : ℂ) • v
  rw [hdValue]

/-- The projective representation extracted from an extension character
with prescribed coefficient action. -/
def projectiveOfCoefficientCharacter
    (iota : C →* ℂˣ)
    (psi : IrreducibleCharacter
      (CentralExtensionGroup alpha halpha))
    (hpsi : HasCoefficientCharacter alpha halpha iota psi) :
    ProjectiveRepresentation ℂ G psi.realization where
  operator g :=
    IrreducibleCharacter.extensionRealizationAction (ψ := psi)
      (baseLift alpha halpha g)
  factor g h := iota (alpha g h)
  map_mul g h := by
    rw [← map_mul
      (IrreducibleCharacter.extensionRealizationAction (ψ := psi))]
    rw [baseLift_mul alpha halpha g h, map_mul,
      realization_coefficientEmbedding alpha halpha iota psi hpsi]

@[simp]
theorem projectiveOfCoefficientCharacter_operator
    (iota : C →* ℂˣ)
    (psi : IrreducibleCharacter
      (CentralExtensionGroup alpha halpha))
    (hpsi : HasCoefficientCharacter alpha halpha iota psi)
    (g : G) :
    (projectiveOfCoefficientCharacter alpha halpha iota psi hpsi
      ).operator g =
      IrreducibleCharacter.extensionRealizationAction (ψ := psi)
        (baseLift alpha halpha g) :=
  rfl

@[simp]
theorem projectiveOfCoefficientCharacter_factor
    (iota : C →* ℂˣ)
    (psi : IrreducibleCharacter
      (CentralExtensionGroup alpha halpha))
    (hpsi : HasCoefficientCharacter alpha halpha iota psi)
    (g h : G) :
    (projectiveOfCoefficientCharacter alpha halpha iota psi hpsi
      ).factor g h =
      iota (alpha g h) :=
  rfl

/-- A base-lift value of the extension character is the trace of the
corresponding extracted projective operator. -/
@[simp]
theorem values_baseLift_eq_projective_trace
    (iota : C →* ℂˣ)
    (psi : IrreducibleCharacter
      (CentralExtensionGroup alpha halpha))
    (hpsi : HasCoefficientCharacter alpha halpha iota psi)
    (g : G) :
    psi.values (baseLift alpha halpha g) =
      LinearMap.trace ℂ psi.realization
        ((projectiveOfCoefficientCharacter
          alpha halpha iota psi hpsi).operator g :
          psi.realization →ₗ[ℂ] psi.realization) := by
  rw [← congrFun psi.realization_character
    (baseLift alpha halpha g)]
  rfl

/-- Linearizing the extracted projective representation recovers the chosen
realization of the extension character exactly. -/
theorem projectiveOfCoefficientCharacter_centralExtensionRepresentation
    (iota : C →* ℂˣ)
    (psi : IrreducibleCharacter
      (CentralExtensionGroup alpha halpha))
    (hpsi : HasCoefficientCharacter alpha halpha iota psi) :
    (projectiveOfCoefficientCharacter alpha halpha iota psi hpsi
      ).centralExtensionRepresentation
        alpha halpha iota
        (fun _ _ ↦ rfl) =
      psi.realization.ρ := by
  apply MonoidHom.ext
  intro x
  apply LinearMap.ext
  intro v
  let c := coefficient alpha halpha x
  let g := base alpha halpha x
  have hx :
      coefficientEmbedding alpha halpha c *
          baseLift alpha halpha g =
        x :=
    coefficientEmbedding_mul_baseLift alpha halpha x
  change
    (iota c : ℂ) •
        IrreducibleCharacter.extensionRealizationAction (ψ := psi)
          (baseLift alpha halpha g) v =
      psi.realization.ρ x v
  rw [← hx, map_mul,
    ← IrreducibleCharacter.extensionRealizationAction_toLinearMap,
    realization_coefficientEmbedding alpha halpha iota psi hpsi]
  rfl

/-- The extracted projective representation is irreducible. -/
theorem projectiveOfCoefficientCharacter_isIrreducible
    (iota : C →* ℂˣ)
    (psi : IrreducibleCharacter
      (CentralExtensionGroup alpha halpha))
    (hpsi : HasCoefficientCharacter alpha halpha iota psi) :
    (projectiveOfCoefficientCharacter alpha halpha iota psi hpsi
      ).IsIrreducible := by
  letI : Nontrivial psi.realization :=
    CliffordRestriction.nontrivial_of_simple psi.realization
  let Q :=
    projectiveOfCoefficientCharacter alpha halpha iota psi hpsi
  let rho :=
    Q.centralExtensionRepresentation
      alpha halpha iota (fun _ _ ↦ rfl)
  have hrho : rho.IsIrreducible := by
    rw [show rho = psi.realization.ρ by
      exact
        projectiveOfCoefficientCharacter_centralExtensionRepresentation
          alpha halpha iota psi hpsi]
    exact
      CliffordRestriction.isIrreducible_of_simple
        psi.realization
  refine ⟨inferInstance, ?_⟩
  intro U hU
  have hInvariant :
      ∀ (x : CentralExtensionGroup alpha halpha)
          ⦃v : psi.realization⦄,
        v ∈ U → rho x v ∈ U :=
    (Q.centralExtensionRepresentation_invariant_iff_isStable
      alpha halpha iota (fun _ _ ↦ rfl) U).mpr hU
  let W : Subrepresentation rho :=
    { toSubmodule := U
      apply_mem_toSubmodule := hInvariant }
  letI : rho.IsIrreducible := hrho
  obtain hW | hW := IsSimpleOrder.eq_bot_or_eq_top W
  · left
    exact congrArg Subrepresentation.toSubmodule hW
  · right
    exact congrArg Subrepresentation.toSubmodule hW

end CentralExtensionGroup
end FactorSet
end CharacterTriple
end McKayConjecture
