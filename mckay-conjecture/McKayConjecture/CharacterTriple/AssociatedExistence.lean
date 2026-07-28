/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Determination
import McKayConjecture.CharacterTriple.Semidirect

/-!
# Associated projective representations for invariant characters

An invariant irreducible character admits a projective extension to the
corresponding semidirect product.  This file constructs the intertwining
operators from character equality and Schur orthogonality, normalizing the
operator at the identity.
-/

noncomputable section

open CategoryTheory

universe u v

namespace McKayConjecture.CharacterTriple

variable {X : Type u} {Γ : Type v} [Group X] [Finite X] [Group Γ]
  (φ : Γ →* MulAut X)
  (χ : IrreducibleCharacter X)

namespace AssociatedExistence

/-- The chosen realization as an honest action by linear automorphisms. -/
def realizationAction :
    X →* (χ.realization ≃ₗ[ℂ] χ.realization) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv ℂ χ.realization).toMonoidHom.comp
    χ.realization.ρ.toHomUnits

instance realizationNontrivial : Nontrivial χ.realization :=
  Module.nontrivial_of_finrank_pos (by
    rw [χ.realization_finrank]
    exact χ.degree_pos)

omit [Finite X] in
@[simp]
theorem realizationAction_toLinearMap (x : X) :
    (realizationAction χ x).toLinearMap = χ.realization.ρ x :=
  rfl

omit [Finite X] in
@[simp]
theorem realizationAction_apply (x : X) (z : χ.realization) :
    realizationAction χ x z = χ.realization.ρ x z :=
  rfl

/-- The chosen realization pulled back by one automorphism in the action.
This is an abbreviation so its carrier remains definitionally the carrier of
`χ.realization`. -/
abbrev twist (γ : Γ) : FDRep ℂ X :=
  FDRep.of (χ.realization.ρ.comp (φ γ).toMonoidHom)

instance twistSimple (γ : Γ) : Simple (twist φ χ γ) :=
  let E := Action.resEquiv (FGModuleCat ℂ) (φ γ)
  show Simple (E.functor.obj χ.realization) from
    CategoryTheory.simple_obj E.functor χ.realization

omit [Finite X] in
@[simp]
theorem twist_rho (γ : Γ) (x : X) :
    (twist φ χ γ).ρ x = χ.realization.ρ (φ γ x) :=
  rfl

omit [Finite X] in
@[simp]
theorem twist_character (hχ : IsInvariant φ χ) (γ : Γ) :
    (twist φ χ γ).character = χ.realization.character := by
  funext x
  change χ.realization.character (φ γ x) =
    χ.realization.character x
  simpa only [χ.realization_character] using hχ γ x

/-- There is an intertwining isomorphism from a realization to each
automorphic twist. -/
theorem nonempty_iso_twist (hχ : IsInvariant φ χ) (γ : Γ) :
    Nonempty (χ.realization ≅ twist φ χ γ) :=
  FDRep.nonempty_iso_of_character_eq
    χ.realization (twist φ χ γ) (twist_character φ χ hχ γ).symm

/-- A chosen intertwining operator.  At the identity we choose the identity
operator explicitly; this normalization is what makes the eventual
projective lift restrict literally to the original representation on `X`. -/
def intertwiner (hχ : IsInvariant φ χ) (γ : Γ) :
    χ.realization ≃ₗ[ℂ] χ.realization := by
  classical
  exact if hγ : γ = 1 then
      LinearEquiv.refl ℂ χ.realization
    else by
      let i := Classical.choice (nonempty_iso_twist φ χ hχ γ)
      change χ.realization ≅
        FDRep.of (χ.realization.ρ.comp (φ γ).toMonoidHom) at i
      let e := FDRep.isoToLinearEquiv i
      change χ.realization ≃ₗ[ℂ] χ.realization at e
      exact e

@[simp]
theorem intertwiner_one (hχ : IsInvariant φ χ) :
    intertwiner φ χ hχ 1 = 1 := by
  simp only [intertwiner]
  rfl

/-- The chosen operator intertwines the original representation with its
automorphic twist. -/
theorem intertwiner_mul_rho (hχ : IsInvariant φ χ) (γ : Γ) (x : X) :
    intertwiner φ χ hχ γ * realizationAction χ x =
      realizationAction χ (φ γ x) * intertwiner φ χ hχ γ := by
  by_cases hγ : γ = 1
  · subst γ
    simp
  · let i : χ.realization ≅ twist φ χ γ :=
      Classical.choice (nonempty_iso_twist φ χ hχ γ)
    change χ.realization ≅
      FDRep.of (χ.realization.ρ.comp (φ γ).toMonoidHom) at i
    let ei := FDRep.isoToLinearEquiv i
    change χ.realization ≃ₗ[ℂ] χ.realization at ei
    have hconj := FDRep.Iso.conj_ρ i x
    rw [twist_rho] at hconj
    have hconj' :
        ei *
            realizationAction χ x =
          realizationAction χ (φ γ x) *
            ei := by
      ext z
      have hz := LinearMap.congr_fun hconj (ei z)
      simpa [ei, LinearEquiv.conj_apply] using hz.symm
    simpa [intertwiner, hγ, i, ei] using hconj'

/-- A product of two chosen intertwiners has the covariance law for the
product automorphism. -/
theorem intertwiner_mul_intertwiner_mul_rho
    (hχ : IsInvariant φ χ) (γ δ : Γ) (x : X) :
    (intertwiner φ χ hχ γ * intertwiner φ χ hχ δ) *
        realizationAction χ x =
      realizationAction χ (φ (γ * δ) x) *
        (intertwiner φ χ hχ γ * intertwiner φ χ hχ δ) := by
  calc
    (intertwiner φ χ hχ γ * intertwiner φ χ hχ δ) *
          realizationAction χ x =
      intertwiner φ χ hχ γ *
        (intertwiner φ χ hχ δ * realizationAction χ x) := by
          rw [mul_assoc]
    _ = intertwiner φ χ hχ γ *
        (realizationAction χ (φ δ x) * intertwiner φ χ hχ δ) := by
          rw [intertwiner_mul_rho]
    _ = (intertwiner φ χ hχ γ *
          realizationAction χ (φ δ x)) *
        intertwiner φ χ hχ δ := by rw [mul_assoc]
    _ = (realizationAction χ (φ γ (φ δ x)) *
          intertwiner φ χ hχ γ) *
        intertwiner φ χ hχ δ := by
          rw [intertwiner_mul_rho]
    _ = realizationAction χ (φ (γ * δ) x) *
        (intertwiner φ χ hχ γ * intertwiner φ χ hχ δ) := by
          simp only [map_mul, MulAut.mul_apply, mul_assoc]

/-- The quotient of the product intertwiner by the chosen product
intertwiner.  It is an endomorphism of the original irreducible
representation. -/
def comparison (hχ : IsInvariant φ χ) (γ δ : Γ) :
    χ.realization ≃ₗ[ℂ] χ.realization :=
  (intertwiner φ χ hχ (γ * δ))⁻¹ *
    (intertwiner φ χ hχ γ * intertwiner φ χ hχ δ)

/-- The comparison operator commutes with the original `X`-action. -/
theorem comparison_mul_rho (hχ : IsInvariant φ χ) (γ δ : Γ) (x : X) :
    comparison φ χ hχ γ δ * realizationAction χ x =
      realizationAction χ x * comparison φ χ hχ γ δ := by
  let A := intertwiner φ χ hχ γ * intertwiner φ χ hχ δ
  let B := intertwiner φ χ hχ (γ * δ)
  have hA : A * realizationAction χ x =
      realizationAction χ (φ (γ * δ) x) * A :=
    intertwiner_mul_intertwiner_mul_rho φ χ hχ γ δ x
  have hB : B * realizationAction χ x =
      realizationAction χ (φ (γ * δ) x) * B :=
    intertwiner_mul_rho φ χ hχ (γ * δ) x
  have hBinv :
      B⁻¹ * realizationAction χ (φ (γ * δ) x) =
        realizationAction χ x * B⁻¹ := by
    apply mul_left_cancel (a := B)
    calc
      B * (B⁻¹ * realizationAction χ (φ (γ * δ) x)) =
          realizationAction χ (φ (γ * δ) x) := by simp
      _ = (B * realizationAction χ x) * B⁻¹ := by
            rw [hB]
            simp
      _ = B * (realizationAction χ x * B⁻¹) := by rw [mul_assoc]
  change (B⁻¹ * A) * realizationAction χ x =
    realizationAction χ x * (B⁻¹ * A)
  calc
    (B⁻¹ * A) * realizationAction χ x =
        B⁻¹ * (A * realizationAction χ x) := by rw [mul_assoc]
    _ = B⁻¹ *
        (realizationAction χ (φ (γ * δ) x) * A) := by rw [hA]
    _ = (B⁻¹ * realizationAction χ (φ (γ * δ) x)) * A := by
          rw [mul_assoc]
    _ = (realizationAction χ x * B⁻¹) * A := by rw [hBinv]
    _ = realizationAction χ x * (B⁻¹ * A) := by rw [mul_assoc]

/-- The comparison as an endomorphism of the realization. -/
def comparisonEndomorphism (hχ : IsInvariant φ χ) (γ δ : Γ) :
    χ.realization ⟶ χ.realization :=
  ⟨InducedCategory.homMk
      (ModuleCat.ofHom (comparison φ χ hχ γ δ).toLinearMap),
    fun x ↦ by
      ext z
      exact DFunLike.congr_fun (comparison_mul_rho φ χ hχ γ δ x) z⟩

@[simp]
theorem comparisonEndomorphism_apply
    (hχ : IsInvariant φ χ) (γ δ : Γ) (z : χ.realization) :
    comparisonEndomorphism φ χ hχ γ δ z =
      comparison φ χ hχ γ δ z :=
  rfl

/-- Schur's lemma makes the comparison a unique nonzero scalar. -/
theorem comparison_isScalar (hχ : IsInvariant φ χ) (γ δ : Γ) :
    ∃ c : ℂˣ,
      comparison φ χ hχ γ δ =
        scalarLinearEquiv ℂ χ.realization c := by
  let f := comparisonEndomorphism φ χ hχ γ δ
  obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id ℂ f
  have hpoint : ∀ z : χ.realization,
      c • z = comparison φ χ hχ γ δ z := by
    intro z
    have hz := ConcreteCategory.congr_hom hc z
    change c • z = comparison φ χ hχ γ δ z at hz
    exact hz
  have hc0 : c ≠ 0 := by
    intro hc0
    obtain ⟨z : χ.realization, hz⟩ := exists_ne (0 : χ.realization)
    have hcomparison_zero : comparison φ χ hχ γ δ z = 0 := by
      rw [← hpoint z, hc0, zero_smul]
    exact hz ((comparison φ χ hχ γ δ).injective
      (by simpa using hcomparison_zero))
  refine ⟨Units.mk0 c hc0, ?_⟩
  ext z
  exact (hpoint z).symm

/-- The scalar factor attached to a pair of chosen intertwiners. -/
def intertwinerFactor (hχ : IsInvariant φ χ) (γ δ : Γ) : ℂˣ :=
  Classical.choose (comparison_isScalar φ χ hχ γ δ)

theorem comparison_eq_scalar (hχ : IsInvariant φ χ) (γ δ : Γ) :
    comparison φ χ hχ γ δ =
      scalarLinearEquiv ℂ χ.realization
        (intertwinerFactor φ χ hχ γ δ) :=
  Classical.choose_spec (comparison_isScalar φ χ hχ γ δ)

/-- Multiplication of the chosen intertwiners is projective with factor
`intertwinerFactor`. -/
theorem intertwiner_mul (hχ : IsInvariant φ χ) (γ δ : Γ) :
    intertwiner φ χ hχ γ * intertwiner φ χ hχ δ =
      scalarLinearEquiv ℂ χ.realization
          (intertwinerFactor φ χ hχ γ δ) *
        intertwiner φ χ hχ (γ * δ) := by
  let B := intertwiner φ χ hχ (γ * δ)
  let A := intertwiner φ χ hχ γ * intertwiner φ χ hχ δ
  have hcomparison := comparison_eq_scalar φ χ hχ γ δ
  change B⁻¹ * A =
    scalarLinearEquiv ℂ χ.realization
      (intertwinerFactor φ χ hχ γ δ) at hcomparison
  calc
    A = B * (B⁻¹ * A) := by simp
    _ = B * scalarLinearEquiv ℂ χ.realization
        (intertwinerFactor φ χ hχ γ δ) := by rw [hcomparison]
    _ = scalarLinearEquiv ℂ χ.realization
          (intertwinerFactor φ χ hχ γ δ) * B :=
      (scalarLinearEquiv_comm ℂ χ.realization
        (intertwinerFactor φ χ hχ γ δ) B).symm

/-- The chosen lift on the semidirect product:
`P(x,γ) = ρ(x) T(γ)`. -/
def projectiveOperator (hχ : IsInvariant φ χ)
    (g : X ⋊[φ] Γ) :
    χ.realization ≃ₗ[ℂ] χ.realization :=
  realizationAction χ g.left * intertwiner φ χ hχ g.right

@[simp]
theorem projectiveOperator_inl (hχ : IsInvariant φ χ) (x : X) :
    projectiveOperator φ χ hχ (SemidirectProduct.inl x) =
      realizationAction χ x := by
  simp [projectiveOperator]

@[simp]
theorem projectiveOperator_one (hχ : IsInvariant φ χ) :
    projectiveOperator φ χ hχ 1 = 1 := by
  simp [projectiveOperator]

/-- The projective representation of the semidirect product associated with
the invariant character. -/
def projectiveRepresentation (hχ : IsInvariant φ χ) :
    ProjectiveRepresentation ℂ (X ⋊[φ] Γ) χ.realization where
  operator := projectiveOperator φ χ hχ
  factor g h := intertwinerFactor φ χ hχ g.right h.right
  map_mul g h := by
    change
      (realizationAction χ g.left * intertwiner φ χ hχ g.right) *
          (realizationAction χ h.left * intertwiner φ χ hχ h.right) =
        scalarLinearEquiv ℂ χ.realization
            (intertwinerFactor φ χ hχ g.right h.right) *
          (realizationAction χ (g * h).left *
            intertwiner φ χ hχ (g * h).right)
    calc
      (realizationAction χ g.left * intertwiner φ χ hχ g.right) *
            (realizationAction χ h.left * intertwiner φ χ hχ h.right) =
        (realizationAction χ g.left *
            (intertwiner φ χ hχ g.right *
              realizationAction χ h.left)) *
          intertwiner φ χ hχ h.right := by simp only [mul_assoc]
      _ = (realizationAction χ g.left *
            (realizationAction χ (φ g.right h.left) *
              intertwiner φ χ hχ g.right)) *
          intertwiner φ χ hχ h.right := by
            rw [intertwiner_mul_rho]
      _ = (realizationAction χ g.left *
            realizationAction χ (φ g.right h.left)) *
          (intertwiner φ χ hχ g.right *
            intertwiner φ χ hχ h.right) := by
              simp only [mul_assoc]
      _ = realizationAction χ (g.left * φ g.right h.left) *
          (intertwiner φ χ hχ g.right *
            intertwiner φ χ hχ h.right) := by rw [map_mul]
      _ = realizationAction χ (g.left * φ g.right h.left) *
          (scalarLinearEquiv ℂ χ.realization
              (intertwinerFactor φ χ hχ g.right h.right) *
            intertwiner φ χ hχ (g.right * h.right)) := by
              rw [intertwiner_mul]
      _ = scalarLinearEquiv ℂ χ.realization
            (intertwinerFactor φ χ hχ g.right h.right) *
          (realizationAction χ (g.left * φ g.right h.left) *
            intertwiner φ χ hχ (g.right * h.right)) := by
              rw [← mul_assoc, ← scalarLinearEquiv_comm, mul_assoc]
      _ = scalarLinearEquiv ℂ χ.realization
            (intertwinerFactor φ χ hχ g.right h.right) *
          (realizationAction χ (g * h).left *
            intertwiner φ χ hχ (g * h).right) := by
              rw [SemidirectProduct.mul_left, SemidirectProduct.mul_right]

@[simp]
theorem projectiveRepresentation_operator
    (hχ : IsInvariant φ χ) (g : X ⋊[φ] Γ) :
    (projectiveRepresentation φ χ hχ).operator g =
      projectiveOperator φ χ hχ g :=
  rfl

@[simp]
theorem projectiveRepresentation_factor
    (hχ : IsInvariant φ χ) (g h : X ⋊[φ] Γ) :
    (projectiveRepresentation φ χ hχ).factor g h =
      intertwinerFactor φ χ hχ g.right h.right :=
  rfl

/-- The constructed projective representation is normalized. -/
theorem projectiveRepresentation_isNormalized
    (hχ : IsInvariant φ χ) :
    (projectiveRepresentation φ χ hχ).IsNormalized :=
  projectiveOperator_one φ χ hχ

/-- The literal restriction of the projective lift to the canonical copy of
`X`. -/
def semidirectRestriction :
    semidirectNormalSubgroup φ →*
      (χ.realization ≃ₗ[ℂ] χ.realization) :=
  (realizationAction χ).comp (semidirectNormalEquiv φ).toMonoidHom

omit [Finite X] in
@[simp]
theorem semidirectRestriction_apply
    (x : semidirectNormalSubgroup φ) :
    semidirectRestriction φ χ x =
      realizationAction χ (semidirectNormalEquiv φ x) :=
  rfl

omit [Finite X] in
/-- Every element of the canonical normal subgroup is literally `inl` of
its image under `semidirectNormalEquiv`. -/
theorem coe_eq_inl_normalEquiv
    (x : semidirectNormalSubgroup φ) :
    (x : X ⋊[φ] Γ) =
      SemidirectProduct.inl (semidirectNormalEquiv φ x) := by
  have hx := congrArg Subtype.val
    ((semidirectNormalEquiv φ).symm_apply_apply x)
  exact hx.symm

/-- The normal subgroup stored in `ofSemidirect`, transported through its
definitional identification with the canonical range of `inl`. -/
def tripleNormalEquiv [Finite Γ] (hχ : IsInvariant φ χ) :
    (ofSemidirect φ χ hχ).normalSubgroup ≃* X :=
  (MulEquiv.subgroupCongr
      (ofSemidirect_normalSubgroup φ χ hχ)).trans
    (semidirectNormalEquiv φ)

/-- The restriction action, with domain exactly the subgroup field of the
semidirect character triple. -/
def tripleRestriction [Finite Γ] (hχ : IsInvariant φ χ) :
    (ofSemidirect φ χ hχ).normalSubgroup →*
      (χ.realization ≃ₗ[ℂ] χ.realization) :=
  (realizationAction χ).comp (tripleNormalEquiv φ χ hχ).toMonoidHom

/-- An element of the normal subgroup stored in `ofSemidirect` is `inl` of
its image under `tripleNormalEquiv`. -/
theorem coe_eq_inl_tripleNormalEquiv [Finite Γ]
    (hχ : IsInvariant φ χ)
    (x : (ofSemidirect φ χ hχ).normalSubgroup) :
    (x : X ⋊[φ] Γ) =
      SemidirectProduct.inl (tripleNormalEquiv φ χ hχ x) := by
  apply SemidirectProduct.ext
  · change x.1.left = x.1.left
    rfl
  · have hxmem : (x : X ⋊[φ] Γ) ∈ semidirectNormalSubgroup φ := by
      rw [← ofSemidirect_normalSubgroup φ χ hχ]
      exact x.property
    have hxker :
        SemidirectProduct.rightHom (x : X ⋊[φ] Γ) = 1 := by
      rw [← MonoidHom.mem_ker]
      rw [← SemidirectProduct.range_inl_eq_ker_rightHom]
      exact hxmem
    change x.1.right = 1
    simpa only [SemidirectProduct.rightHom_eq_right] using hxker

/-- The constructed projective representation is associated with the
semidirect-product character triple. -/
def associated [Finite Γ] (hχ : IsInvariant φ χ) :
    AssociatedProjectiveRepresentation
      (ofSemidirect φ χ hχ) χ.realization
      (projectiveRepresentation φ χ hχ) where
  restriction := tripleRestriction φ χ hχ
  restriction_apply := by
    intro x
    rw [coe_eq_inl_tripleNormalEquiv]
    exact (projectiveOperator_inl φ χ hχ
      (tripleNormalEquiv φ χ hχ x)).symm
  restriction_simple := by
    let E : FDRep ℂ X ≌
        FDRep ℂ (ofSemidirect φ χ hχ).normalSubgroup :=
      Action.resEquiv (FGModuleCat ℂ) (tripleNormalEquiv φ χ hχ)
    change Simple (E.functor.obj χ.realization)
    exact CategoryTheory.simple_obj E.functor χ.realization
  restriction_character := by
    funext x
    change χ.realization.character (tripleNormalEquiv φ χ hχ x) =
      χ.values (tripleNormalEquiv φ χ hχ x)
    exact congrFun χ.realization_character (tripleNormalEquiv φ χ hχ x)
  normal_mul := by
    intro x a
    rw [coe_eq_inl_tripleNormalEquiv]
    change projectiveOperator φ χ hχ
        (SemidirectProduct.inl (tripleNormalEquiv φ χ hχ x) * a) =
      projectiveOperator φ χ hχ
          (SemidirectProduct.inl (tripleNormalEquiv φ χ hχ x)) *
        projectiveOperator φ χ hχ a
    simp only [projectiveOperator_inl]
    simp [projectiveOperator, mul_assoc]
  mul_normal := by
    intro a x
    rw [coe_eq_inl_tripleNormalEquiv]
    let y := tripleNormalEquiv φ χ hχ x
    change projectiveOperator φ χ hχ
        (a * SemidirectProduct.inl y) =
      projectiveOperator φ χ hχ a *
        projectiveOperator φ χ hχ (SemidirectProduct.inl y)
    rw [projectiveOperator_inl]
    unfold projectiveOperator
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      mul_one]
    calc
      realizationAction χ (a.left * φ a.right y) *
          intertwiner φ χ hχ a.right =
        (realizationAction χ a.left *
          realizationAction χ (φ a.right y)) *
            intertwiner φ χ hχ a.right := by rw [map_mul]
      _ = realizationAction χ a.left *
          (realizationAction χ (φ a.right y) *
            intertwiner φ χ hχ a.right) := by rw [mul_assoc]
      _ = realizationAction χ a.left *
          (intertwiner φ χ hχ a.right *
            realizationAction χ y) := by
              rw [intertwiner_mul_rho]
      _ = (realizationAction χ a.left *
            intertwiner φ χ hχ a.right) *
          realizationAction χ y := by rw [mul_assoc]

/-- Existence form: every invariant irreducible character has a normalized
associated projective representation on its chosen realization. -/
theorem exists_normalized_associated [Finite Γ]
    (hχ : IsInvariant φ χ) :
    ∃ P : ProjectiveRepresentation ℂ (X ⋊[φ] Γ) χ.realization,
      P.IsNormalized ∧
        Nonempty (AssociatedProjectiveRepresentation
          (ofSemidirect φ χ hχ) χ.realization P) :=
  ⟨projectiveRepresentation φ χ hχ,
    projectiveRepresentation_isNormalized φ χ hχ,
    ⟨associated φ χ hχ⟩⟩

end AssociatedExistence
end McKayConjecture.CharacterTriple
