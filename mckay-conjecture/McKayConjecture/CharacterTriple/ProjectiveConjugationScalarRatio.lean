/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.ProjectiveScalarSummandIntertwining

/-!
# Scalar ratios in projective Hom actions

Suppose two chosen operators are respectively scalar multiples of honest
operators on the target and source of a linear Hom-space.  Conjugation on
the Hom-space then differs from the honest `Representation.linHom` action
by the target scalar times the inverse source scalar.

This file records that orientation once and for all.  In the
Dade--Glauberman--Nagao comparison, the two scalar cochains come from
comparing the canonical kernel intertwiners with the normalized source and
local Gallagher extensions.  Their ratio is the scalar `mu` selecting the
correct Sylow summand, and its inverse is the rescaling required before
quotient descent.
-/

noncomputable section

open CategoryTheory

universe u v w x

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

variable {K : Type u} [Field K]
variable {G : Type v} [Group G]
variable {H : Type w} [Group H]
variable {V W : Type x}
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

/-- The scalar carried by conjugation on a Hom-space: target scalar divided
by source scalar. -/
def conjugationScalarRatio
    (targetScalar sourceScalar : H → Kˣ) :
    H → Kˣ :=
  fun h ↦ targetScalar h * (sourceScalar h)⁻¹

@[simp]
theorem conjugationScalarRatio_apply
    (targetScalar sourceScalar : H → Kˣ)
    (h : H) :
    conjugationScalarRatio targetScalar sourceScalar h =
      targetScalar h * (sourceScalar h)⁻¹ :=
  rfl

/-- The inverse scalar used to normalize the selected Hom summand before
quotient descent. -/
def inverseConjugationScalarRatio
    (targetScalar sourceScalar : H → Kˣ) :
    H → Kˣ :=
  fun h ↦
    (conjugationScalarRatio targetScalar sourceScalar h)⁻¹

@[simp]
theorem inverseConjugationScalarRatio_apply
    (targetScalar sourceScalar : H → Kˣ)
    (h : H) :
    inverseConjugationScalarRatio targetScalar sourceScalar h =
      sourceScalar h * (targetScalar h)⁻¹ := by
  simp [inverseConjugationScalarRatio,
    conjugationScalarRatio]

/-- Pointwise scalar-ratio calculation for conjugation on a linear
Hom-space. -/
theorem conjugation_apply_eq_scalarRatio_smul_linHom
    (rho : Representation K H V)
    (sigma : Representation K H W)
    (sourceOperator : H → V ≃ₗ[K] V)
    (targetOperator : H → W ≃ₗ[K] W)
    (sourceScalar targetScalar : H → Kˣ)
    (hsource :
      ∀ (h : H) (v : V),
        sourceOperator h v =
          (sourceScalar h : K) • rho h v)
    (htarget :
      ∀ (h : H) (w : W),
        targetOperator h w =
          (targetScalar h : K) • sigma h w)
    (h : H) (f : V →ₗ[K] W) (v : V) :
    targetOperator h
        (f ((sourceOperator h).symm v)) =
      (conjugationScalarRatio
          targetScalar sourceScalar h : K) •
        Representation.linHom rho sigma h f v := by
  have hsourceInv :
      (sourceOperator h).symm v =
        ((sourceScalar h : K)⁻¹) •
          rho h⁻¹ v := by
    apply (sourceOperator h).injective
    rw [LinearEquiv.apply_symm_apply, hsource]
    simp only [map_smul, smul_smul]
    simp [← map_mul]
  rw [hsourceInv]
  simp only [map_smul]
  rw [htarget]
  simp only [Representation.linHom_apply,
    LinearMap.comp_apply, conjugationScalarRatio_apply,
    Units.val_mul, Units.val_inv_eq_inv_val, smul_smul]
  module

/-- Operator form of
`conjugation_apply_eq_scalarRatio_smul_linHom`. -/
theorem projective_operator_eq_scalarRatio_smul_linHom
    (P : ProjectiveRepresentation K G (V →ₗ[K] W))
    (j : H →* G)
    (rho : Representation K H V)
    (sigma : Representation K H W)
    (sourceOperator : H → V ≃ₗ[K] V)
    (targetOperator : H → W ≃ₗ[K] W)
    (sourceScalar targetScalar : H → Kˣ)
    (hoperator :
      ∀ (h : H) (f : V →ₗ[K] W) (v : V),
        P.operator (j h) f v =
          targetOperator h
            (f ((sourceOperator h).symm v)))
    (hsource :
      ∀ (h : H) (v : V),
        sourceOperator h v =
          (sourceScalar h : K) • rho h v)
    (htarget :
      ∀ (h : H) (w : W),
        targetOperator h w =
          (targetScalar h : K) • sigma h w)
    (h : H) (f : V →ₗ[K] W) :
    P.operator (j h) f =
      (conjugationScalarRatio
          targetScalar sourceScalar h : K) •
        Representation.linHom rho sigma h f := by
  ext v
  rw [hoperator]
  exact
    conjugation_apply_eq_scalarRatio_smul_linHom
      rho sigma sourceOperator targetOperator
      sourceScalar targetScalar hsource htarget h f v

/-- Once the source and target comparison cochains are known separately,
their ratio gives the selected projective summand, and that summand is
canonically the space of morphisms between the honest finite-dimensional
representations. -/
def scalarRestrictionSubmoduleEquivFDRepHomOfConjugationComparisons
    (X Y : FDRep K H)
    (P :
      ProjectiveRepresentation K G
        (X.V →ₗ[K] Y.V))
    (j : H →* G)
    (sourceOperator : H → X.V ≃ₗ[K] X.V)
    (targetOperator : H → Y.V ≃ₗ[K] Y.V)
    (sourceScalar targetScalar : H → Kˣ)
    (hoperator :
      ∀ (h : H) (f : X.V →ₗ[K] Y.V) (v : X.V),
        P.operator (j h) f v =
          targetOperator h
            (f ((sourceOperator h).symm v)))
    (hsource :
      ∀ (h : H) (v : X.V),
        sourceOperator h v =
          (sourceScalar h : K) • X.ρ h v)
    (htarget :
      ∀ (h : H) (w : Y.V),
        targetOperator h w =
          (targetScalar h : K) • Y.ρ h w) :
    scalarRestrictionSubmodule P j
        (conjugationScalarRatio
          targetScalar sourceScalar) ≃ₗ[K]
      (X ⟶ Y) :=
  scalarRestrictionSubmoduleEquivFDRepHom
    X Y P j
    (conjugationScalarRatio
      targetScalar sourceScalar)
    (projective_operator_eq_scalarRatio_smul_linHom
      P j X.ρ Y.ρ sourceOperator targetOperator
      sourceScalar targetScalar hoperator hsource htarget)

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
