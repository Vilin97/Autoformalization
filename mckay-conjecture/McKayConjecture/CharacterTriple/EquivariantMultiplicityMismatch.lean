/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FactorSetCoprimeClassVanishing
import McKayConjecture.CharacterTriple.AssociatedExistence
import McKayConjecture.CharacterTriple.FactorSetCentralExtensionNormalizer
import McKayConjecture.CharacterTriple.MultiplicityProjective
import McKayConjecture.CharacterTriple.ProjectiveFactorDeterminantCoboundary

/-!
# Projective mismatch for two equivariant normal characters

Let `Γ` act on finite groups `K` and `L`, let `i : L → K` be equivariant,
and let `θ ∈ Irr(K)` and `η ∈ Irr(L)` be invariant under the two actions.
The restriction multiplicity space

`Hom_L(η, θ ∘ i)`

carries the projective action

`f ↦ T_θ(γ) ∘ f ∘ T_η(γ)⁻¹`,

where the `T`'s are the normalized intertwiners used in the canonical
semidirect-product associated projective representations.  Its factor set
is the quotient of the two intertwiner factor sets.

Taking determinants shows that the ordinary restriction multiplicity
annihilates this mismatch class in `H²(Γ, ℂˣ)`.  This is the external-action
form needed for the classical Glauberman multiplicity space.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace CharacterTriple
namespace EquivariantMultiplicityMismatch

variable {K L Γ : Type}
variable [Group K] [Finite K] [Group L] [Finite L]
variable [Group Γ]
variable (α : Γ →* MulAut K) (β : Γ →* MulAut L)
variable (i : L →* K)
variable (hcompat : ∀ (γ : Γ) (x : L), i (β γ x) = α γ (i x))
variable (θ : IrreducibleCharacter K) (η : IrreducibleCharacter L)
variable (hθ : IsInvariant α θ) (hη : IsInvariant β η)

/-- The ordinary restriction-multiplicity space, using the canonical
realizations of the two irreducible characters. -/
abbrev Space :=
  Representation.IntertwiningMap η.realization.ρ
    (θ.realization.ρ.comp i)

/-- Translate the categorical character Hom-space to the unbundled
intertwining-map model carrying the mismatch action. -/
def fdRepHomEquivSpace :
    (η.realization ⟶ FDRep.res i θ.realization) ≃ₗ[ℂ]
      Space i θ η :=
  (FDRep.forget₂HomLinearEquiv
      η.realization (FDRep.res i θ.realization)).symm |>.trans
    (Rep.homLinearEquiv _ _)

omit [Finite K] [Finite L] in
/-- The dimension of the external-action mismatch space is the ordinary
restriction multiplicity. -/
theorem finrank_space_eq_restrictionMultiplicity :
    Module.finrank ℂ (Space i θ η) =
      CliffordCorrespondence.restrictionMultiplicity i η θ := by
  rw [CliffordCorrespondence.restrictionMultiplicity]
  exact (fdRepHomEquivSpace i θ η).finrank_eq.symm

/-- Move a right realization operator past the inverse chosen
intertwiner. -/
theorem right_action_mul_intertwiner_symm
    (γ : Γ) (x : L) :
    AssociatedExistence.realizationAction η ((β γ).symm x) *
        (AssociatedExistence.intertwiner β η hη γ).symm =
      (AssociatedExistence.intertwiner β η hη γ).symm *
        AssociatedExistence.realizationAction η x := by
  have h :=
    AssociatedExistence.intertwiner_mul_rho
      β η hη γ ((β γ).symm x)
  have h' :
      AssociatedExistence.intertwiner β η hη γ *
          AssociatedExistence.realizationAction η ((β γ).symm x) =
        AssociatedExistence.realizationAction η x *
          AssociatedExistence.intertwiner β η hη γ := by
    simpa only [MulEquiv.apply_symm_apply] using h
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro v
  change
    AssociatedExistence.realizationAction η ((β γ).symm x)
        ((AssociatedExistence.intertwiner β η hη γ).symm v) =
      (AssociatedExistence.intertwiner β η hη γ).symm
        (AssociatedExistence.realizationAction η x v)
  apply (AssociatedExistence.intertwiner β η hη γ).injective
  have hv :=
    DFunLike.congr_fun h'
      ((AssociatedExistence.intertwiner β η hη γ).symm v)
  simpa only [LinearEquiv.mul_apply,
    LinearEquiv.apply_symm_apply] using hv

omit [Finite L] in
include hcompat in
/-- The left chosen intertwiner carries the restricted operator at `x` to
the restricted operator at `β γ x`. -/
theorem left_intertwiner_mul_action
    (γ : Γ) (x : L) :
    AssociatedExistence.intertwiner α θ hθ γ *
        AssociatedExistence.realizationAction θ (i x) =
      AssociatedExistence.realizationAction θ (i (β γ x)) *
        AssociatedExistence.intertwiner α θ hθ γ := by
  rw [hcompat γ x]
  exact
    AssociatedExistence.intertwiner_mul_rho
      α θ hθ γ (i x)

include α β hcompat hθ hη in
/-- The value of the external projective mismatch action at `γ`. -/
def actValue
    (γ : Γ) (f : Space i θ η) :
    Space i θ η where
  toLinearMap :=
    (AssociatedExistence.intertwiner α θ hθ γ).toLinearMap ∘ₗ
      f.toLinearMap ∘ₗ
        (AssociatedExistence.intertwiner β η hη γ).symm.toLinearMap
  isIntertwining' x := by
    apply LinearMap.ext
    intro w
    let y : L := (β γ).symm x
    have hright :=
      DFunLike.congr_fun
        (right_action_mul_intertwiner_symm β η hη γ x) w
    have hright' :
        AssociatedExistence.realizationAction η y
            ((AssociatedExistence.intertwiner β η hη γ).symm w) =
          (AssociatedExistence.intertwiner β η hη γ).symm
            (AssociatedExistence.realizationAction η x w) := by
      simpa only [LinearEquiv.mul_apply] using hright
    change
      AssociatedExistence.intertwiner α θ hθ γ
          (f ((AssociatedExistence.intertwiner β η hη γ).symm
            (AssociatedExistence.realizationAction η x w))) =
        AssociatedExistence.realizationAction θ (i x)
          (AssociatedExistence.intertwiner α θ hθ γ
            (f ((AssociatedExistence.intertwiner β η hη γ).symm w)))
    rw [← hright']
    have hf :=
      LinearMap.ext_iff.mp (f.isIntertwining' y)
        ((AssociatedExistence.intertwiner β η hη γ).symm w)
    change
      f (AssociatedExistence.realizationAction η y
          ((AssociatedExistence.intertwiner β η hη γ).symm w)) =
        AssociatedExistence.realizationAction θ (i y)
          (f ((AssociatedExistence.intertwiner β η hη γ).symm w)) at hf
    rw [hf]
    have hleft :=
      DFunLike.congr_fun
        (left_intertwiner_mul_action
          α β i hcompat θ hθ γ y)
        (f ((AssociatedExistence.intertwiner β η hη γ).symm w))
    have hy : β γ y = x :=
      MulEquiv.apply_symm_apply (β γ) x
    simpa only [LinearEquiv.mul_apply, hy] using hleft

@[simp]
theorem actValue_apply
    (γ : Γ) (f : Space i θ η) (w : η.realization) :
    actValue α β i hcompat θ η hθ hη γ f w =
      AssociatedExistence.intertwiner α θ hθ γ
        (f ((AssociatedExistence.intertwiner β η hη γ).symm w)) :=
  rfl

include α β hcompat hθ hη in
/-- The explicit inverse of the mismatch action at `γ`. -/
def actValueInv
    (γ : Γ) (f : Space i θ η) :
    Space i θ η where
  toLinearMap :=
    (AssociatedExistence.intertwiner α θ hθ γ).symm.toLinearMap ∘ₗ
      f.toLinearMap ∘ₗ
        (AssociatedExistence.intertwiner β η hη γ).toLinearMap
  isIntertwining' x := by
    apply LinearMap.ext
    intro w
    let z : L := β γ x
    have hright :=
      DFunLike.congr_fun
        (AssociatedExistence.intertwiner_mul_rho β η hη γ x) w
    have hright' :
        AssociatedExistence.intertwiner β η hη γ
            (AssociatedExistence.realizationAction η x w) =
          AssociatedExistence.realizationAction η z
            (AssociatedExistence.intertwiner β η hη γ w) := by
      simpa only [LinearEquiv.mul_apply] using hright
    change
      (AssociatedExistence.intertwiner α θ hθ γ).symm
          (f (AssociatedExistence.intertwiner β η hη γ
            (AssociatedExistence.realizationAction η x w))) =
        AssociatedExistence.realizationAction θ (i x)
          ((AssociatedExistence.intertwiner α θ hθ γ).symm
            (f (AssociatedExistence.intertwiner β η hη γ w)))
    rw [hright']
    have hf :=
      LinearMap.ext_iff.mp (f.isIntertwining' z)
        (AssociatedExistence.intertwiner β η hη γ w)
    change
      f (AssociatedExistence.realizationAction η z
          (AssociatedExistence.intertwiner β η hη γ w)) =
        AssociatedExistence.realizationAction θ (i z)
          (f (AssociatedExistence.intertwiner β η hη γ w)) at hf
    rw [hf]
    apply (AssociatedExistence.intertwiner α θ hθ γ).injective
    have hleft :=
      DFunLike.congr_fun
        (left_intertwiner_mul_action
          α β i hcompat θ hθ γ x)
        ((AssociatedExistence.intertwiner α θ hθ γ).symm
          (f (AssociatedExistence.intertwiner β η hη γ w)))
    simpa only [LinearEquiv.mul_apply,
      LinearEquiv.apply_symm_apply] using hleft.symm

@[simp]
theorem actValueInv_apply
    (γ : Γ) (f : Space i θ η) (w : η.realization) :
    actValueInv α β i hcompat θ η hθ hη γ f w =
      (AssociatedExistence.intertwiner α θ hθ γ).symm
        (f (AssociatedExistence.intertwiner β η hη γ w)) :=
  rfl

include α β hcompat hθ hη in
/-- Each acting-group element acts invertibly on the mismatch space. -/
def operator
    (γ : Γ) :
    Space i θ η ≃ₗ[ℂ] Space i θ η where
  toFun := actValue α β i hcompat θ η hθ hη γ
  invFun := actValueInv α β i hcompat θ η hθ hη γ
  left_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro w
    change
      (AssociatedExistence.intertwiner α θ hθ γ).symm
          (AssociatedExistence.intertwiner α θ hθ γ
            (f ((AssociatedExistence.intertwiner β η hη γ).symm
              (AssociatedExistence.intertwiner β η hη γ w)))) =
        f w
    simp
  right_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro w
    change
      AssociatedExistence.intertwiner α θ hθ γ
          ((AssociatedExistence.intertwiner α θ hθ γ).symm
            (f (AssociatedExistence.intertwiner β η hη γ
              ((AssociatedExistence.intertwiner β η hη γ).symm w)))) =
        f w
    simp
  map_add' f f' := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro w
    change
      AssociatedExistence.intertwiner α θ hθ γ
          ((f + f') ((AssociatedExistence.intertwiner β η hη γ).symm w)) =
        AssociatedExistence.intertwiner α θ hθ γ
            (f ((AssociatedExistence.intertwiner β η hη γ).symm w)) +
          AssociatedExistence.intertwiner α θ hθ γ
            (f' ((AssociatedExistence.intertwiner β η hη γ).symm w))
    simp
  map_smul' c f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro w
    change
      AssociatedExistence.intertwiner α θ hθ γ
          ((c • f) ((AssociatedExistence.intertwiner β η hη γ).symm w)) =
        c • AssociatedExistence.intertwiner α θ hθ γ
          (f ((AssociatedExistence.intertwiner β η hη γ).symm w))
    simp

@[simp]
theorem operator_apply
    (γ : Γ) (f : Space i θ η) (w : η.realization) :
    operator α β i hcompat θ η hθ hη γ f w =
      AssociatedExistence.intertwiner α θ hθ γ
        (f ((AssociatedExistence.intertwiner β η hη γ).symm w)) :=
  rfl

include α β hcompat hθ hη in
/-- The external multiplicity action is projective, with factor equal to
the quotient of the two canonical intertwiner factors. -/
def projective :
    ProjectiveRepresentation ℂ Γ (Space i θ η) where
  operator := operator α β i hcompat θ η hθ hη
  factor γ δ :=
    AssociatedExistence.intertwinerFactor α θ hθ γ δ *
      (AssociatedExistence.intertwinerFactor β η hη γ δ)⁻¹
  map_mul γ δ := by
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext
    intro f
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro w
    change
      actValue α β i hcompat θ η hθ hη γ
          (actValue α β i hcompat θ η hθ hη δ f) w =
        (scalarLinearEquiv ℂ (Space i θ η)
          (AssociatedExistence.intertwinerFactor α θ hθ γ δ *
            (AssociatedExistence.intertwinerFactor β η hη γ δ)⁻¹)
          (actValue α β i hcompat θ η hθ hη (γ * δ) f)).toLinearMap w
    rw [actValue_apply, actValue_apply, scalarLinearEquiv_apply]
    change
      AssociatedExistence.intertwiner α θ hθ γ
          (AssociatedExistence.intertwiner α θ hθ δ
            (f ((AssociatedExistence.intertwiner β η hη δ).symm
              ((AssociatedExistence.intertwiner β η hη γ).symm w)))) =
        (↑(AssociatedExistence.intertwinerFactor α θ hθ γ δ *
            (AssociatedExistence.intertwinerFactor β η hη γ δ)⁻¹) : ℂ) •
          actValue α β i hcompat θ η hθ hη (γ * δ) f w
    rw [actValue_apply]
    have hηmul :=
      congrArg (fun z : η.realization ≃ₗ[ℂ] η.realization ↦ z⁻¹)
        (AssociatedExistence.intertwiner_mul β η hη γ δ)
    have hηapp := DFunLike.congr_fun hηmul w
    simp only [mul_inv_rev, LinearEquiv.mul_apply] at hηapp
    have hηapp' :
        (AssociatedExistence.intertwiner β η hη δ).symm
            ((AssociatedExistence.intertwiner β η hη γ).symm w) =
          (AssociatedExistence.intertwiner β η hη (γ * δ)).symm
            ((scalarLinearEquiv ℂ η.realization
              (AssociatedExistence.intertwinerFactor β η hη γ δ))⁻¹ w) :=
      hηapp
    rw [hηapp']
    have hηscalar :
        (scalarLinearEquiv ℂ η.realization
          (AssociatedExistence.intertwinerFactor β η hη γ δ))⁻¹ w =
          ((AssociatedExistence.intertwinerFactor β η hη γ δ : ℂ)⁻¹ • w) := by
      rw [← map_inv]
      rw [scalarLinearEquiv_apply, Units.val_inv_eq_inv_val]
    rw [hηscalar]
    simp only [map_smul]
    have hθapp :=
      DFunLike.congr_fun
        (AssociatedExistence.intertwiner_mul α θ hθ γ δ)
        (f ((AssociatedExistence.intertwiner β η hη (γ * δ)).symm w))
    have hθapp' :
        AssociatedExistence.intertwiner α θ hθ γ
            (AssociatedExistence.intertwiner α θ hθ δ
              (f ((AssociatedExistence.intertwiner β η hη (γ * δ)).symm w))) =
          (AssociatedExistence.intertwinerFactor α θ hθ γ δ : ℂ) •
            AssociatedExistence.intertwiner α θ hθ (γ * δ)
              (f ((AssociatedExistence.intertwiner β η hη (γ * δ)).symm w)) := by
      simpa only [LinearEquiv.mul_apply,
        scalarLinearEquiv_apply] using hθapp
    rw [hθapp']
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    module

@[simp]
theorem projective_factor
    (γ δ : Γ) :
    (projective α β i hcompat θ η hθ hη).factor γ δ =
      AssociatedExistence.intertwinerFactor α θ hθ γ δ *
        (AssociatedExistence.intertwinerFactor β η hη γ δ)⁻¹ :=
  rfl

/-- The factor set of the canonical semidirect projective lift, restricted
to the acting-group coordinate. -/
def intertwinerFactorSet
    {J Δ : Type} [Group J] [Finite J] [Group Δ]
    (φ : Δ →* MulAut J)
    (χ : IrreducibleCharacter J)
    (hχ : IsInvariant φ χ) :
    FactorSet Δ ℂˣ :=
  (AssociatedExistence.projectiveRepresentation φ χ hχ).factorSet.comap
    (SemidirectProduct.inr : Δ →* J ⋊[φ] Δ)

@[simp]
theorem intertwinerFactorSet_apply
    {J Δ : Type} [Group J] [Finite J] [Group Δ]
    (φ : Δ →* MulAut J)
    (χ : IrreducibleCharacter J)
    (hχ : IsInvariant φ χ)
    (γ δ : Δ) :
    intertwinerFactorSet φ χ hχ γ δ =
      AssociatedExistence.intertwinerFactor φ χ hχ γ δ :=
  rfl

include α β hθ hη in
/-- The canonical external mismatch factor set.  Unlike the projective
action on the multiplicity space, this definition remains meaningful when
the multiplicity space is zero. -/
def factorSet : FactorSet Γ ℂˣ :=
  intertwinerFactorSet α θ hθ *
    (intertwinerFactorSet β η hη)⁻¹

@[simp]
theorem factorSet_apply
    (γ δ : Γ) :
    factorSet α β θ η hθ hη γ δ =
      AssociatedExistence.intertwinerFactor α θ hθ γ δ *
        (AssociatedExistence.intertwinerFactor β η hη γ δ)⁻¹ := by
  rw [factorSet, FactorSet.mul_apply, FactorSet.inv_apply]
  rfl

/-- When the multiplicity space is nonzero, its projective action has the
canonical external mismatch factor set. -/
theorem projective_factorSet
    [Nontrivial (Space i θ η)] :
    (projective α β i hcompat θ η hθ hη).factorSet =
      factorSet α β θ η hθ hη := by
  apply FactorSet.ext
  intro γ δ
  rw [ProjectiveRepresentation.factorSet_apply,
    projective_factor, factorSet_apply]

include hcompat in
/-- The restriction multiplicity annihilates the external projective
mismatch class. -/
theorem finrank_nsmul_factorSet_h2Class_eq_zero
    [Nontrivial (Space i θ η)] :
    letI := trivialMulDistribMulAction Γ ℂˣ
    Module.finrank ℂ (Space i θ η) •
        (factorSet α β θ η hθ hη).h2Class =
      0 :=
  by
    rw [← projective_factorSet α β i hcompat θ η hθ hη]
    exact
      (projective α β i hcompat θ η hθ hη
        ).finrank_nsmul_factorSet_h2Class_eq_zero

include α β hθ hη in
/-- The external mismatch is `q`-primary when a power of `q` annihilates
its cohomology class. -/
def IsQPrimary (q : ℕ) : Prop :=
  ∃ k : ℕ,
    letI := trivialMulDistribMulAction Γ ℂˣ
    q ^ k •
        (factorSet α β θ η hθ hη).h2Class =
      0

include hcompat in
/-- A prime-to-`q` restriction multiplicity kills a `q`-primary external
projective mismatch. -/
theorem factorSet_h2Class_eq_zero_of_multiplicity_prime_to_of_qPrimary
    (q : ℕ) [Fact q.Prime]
    (hmultiplicity :
      ¬q ∣ Module.finrank ℂ (Space i θ η))
    (hprimary :
      IsQPrimary α β θ η hθ hη q) :
    letI := trivialMulDistribMulAction Γ ℂˣ
    (factorSet α β θ η hθ hη).h2Class =
      0 := by
  have hpositive :
      0 < Module.finrank ℂ (Space i θ η) := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hmultiplicity (hzero ▸ dvd_zero q)
  letI : Nontrivial (Space i θ η) :=
    Module.nontrivial_of_finrank_pos hpositive
  obtain ⟨k, hk⟩ := hprimary
  have hdimension :=
    finrank_nsmul_factorSet_h2Class_eq_zero
      α β i hcompat θ η hθ hη
  have hcoprime :
      Nat.Coprime (Module.finrank ℂ (Space i θ η)) (q ^ k) :=
    (Fact.out : q.Prime).coprime_pow_of_not_dvd hmultiplicity
  exact
    eq_zero_of_coprime_nsmul_eq_zero
      hcoprime hdimension hk

end EquivariantMultiplicityMismatch
end CharacterTriple
end McKayConjecture
