/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordCorrespondence
import McKayConjecture.Character.Determination
import McKayConjecture.CharacterTriple.CentralIsomorphism
import McKayConjecture.CharacterTriple.ProjectiveTensor

/-!
# The projective action on a multiplicity space

Let `T = (A, N, θ)` be a character triple, let `P` be a projective
representation of `A` associated with `θ`, and let `D` be an ordinary
representation of `A`.  The multiplicity space

`Hom_N(P|_N, D|_N)`

has a natural projective action

`f ↦ D(g) ∘ f ∘ P(g)⁻¹`.

This file constructs that action directly on mathlib's intertwining-map
space.  Its factor is proved to be the pointwise inverse of the factor of
`P`, so `ProjectiveRepresentation.tensorLinearAction` produces an honest
linear action on the tensor product without any additional coherence
assumption.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace McKayConjecture
namespace CharacterTriple
namespace MultiplicityProjective

variable {A : Type u} [Finite A] [Group A]
variable {V W : Type}
variable [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W]
variable {T : CharacterTriple A}
variable {P : ProjectiveRepresentation ℂ A V}

/-- The space recording the multiplicity of the normal character afforded by
`R` inside the restriction of an ambient representation `D`. -/
abbrev Space (R : AssociatedProjectiveRepresentation T V P)
    (D : Representation ℂ A W) :=
  Representation.IntertwiningMap R.fdRestriction.ρ
    (D.comp T.normalSubgroup.subtype)

/-- Conjugation by `P(g)` carries the restricted operator at `x` to the
restricted operator at `g x g⁻¹`.  The equality is exact because an
associated projective representation has trivial factor whenever either
argument lies in the normal subgroup. -/
theorem operator_mul_restriction
    (R : AssociatedProjectiveRepresentation T V P)
    (g : A) (x : T.normalSubgroup) :
    P.operator g * R.restriction x =
      R.restriction (MulAut.conjNormal g x) * P.operator g := by
  rw [R.restriction_apply, R.restriction_apply,
    ← R.mul_normal g x,
    ← R.normal_mul (MulAut.conjNormal g x) g]
  congr 1
  simp only [MulAut.conjNormal_apply]
  group

/-- Move a restricted operator past `P(g)⁻¹`. -/
theorem restriction_mul_operator_symm
    (R : AssociatedProjectiveRepresentation T V P)
    (g : A) (x : T.normalSubgroup) :
    R.restriction ((MulAut.conjNormal g).symm x) *
        (P.operator g).symm =
      (P.operator g).symm * R.restriction x := by
  have h :=
    operator_mul_restriction R g
      ((MulAut.conjNormal g).symm x)
  have h' :
      P.operator g *
          R.restriction ((MulAut.conjNormal g).symm x) =
        R.restriction x * P.operator g := by
    simpa only [MulEquiv.apply_symm_apply] using h
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro v
  change
    R.restriction ((MulAut.conjNormal g).symm x)
        ((P.operator g).symm v) =
      (P.operator g).symm (R.restriction x v)
  apply (P.operator g).injective
  have hv :=
    DFunLike.congr_fun h' ((P.operator g).symm v)
  simpa only [LinearEquiv.mul_apply,
    LinearEquiv.apply_symm_apply] using hv

/-- The value of the multiplicity-space action at `g`. -/
def actValue
    (R : AssociatedProjectiveRepresentation T V P)
    (D : Representation ℂ A W) (g : A) (f : Space R D) :
    Space R D where
  toLinearMap :=
    D g ∘ₗ f.toLinearMap ∘ₗ (P.operator g).symm.toLinearMap
  isIntertwining' x := by
    apply LinearMap.ext
    intro v
    let y : T.normalSubgroup := (MulAut.conjNormal g).symm x
    have hmove :=
      DFunLike.congr_fun
        (restriction_mul_operator_symm R g x) v
    have hmove' :
        R.restriction y ((P.operator g).symm v) =
          (P.operator g).symm (R.restriction x v) := by
      simpa only [LinearEquiv.mul_apply] using hmove
    change
      D g (f ((P.operator g).symm (R.restriction x v))) =
        D (x : A) (D g (f ((P.operator g).symm v)))
    rw [← hmove']
    have hf :=
      LinearMap.ext_iff.mp (f.isIntertwining' y)
        ((P.operator g).symm v)
    change
      f (R.restriction y ((P.operator g).symm v)) =
        D (y : A) (f ((P.operator g).symm v)) at hf
    rw [hf]
    rw [← Module.End.mul_apply, ← map_mul,
      ← Module.End.mul_apply, ← map_mul]
    congr 2
    dsimp [y]
    simp only [MulAut.conjNormal_symm_apply]
    group

@[simp]
theorem actValue_apply
    (R : AssociatedProjectiveRepresentation T V P)
    (D : Representation ℂ A W) (g : A) (f : Space R D) (v : V) :
    actValue R D g f v =
      D g (f ((P.operator g).symm v)) :=
  rfl

/-- The explicit inverse value to `actValue`. -/
def actValueInv
    (R : AssociatedProjectiveRepresentation T V P)
    (D : Representation ℂ A W) (g : A) (f : Space R D) :
    Space R D where
  toLinearMap :=
    D g⁻¹ ∘ₗ f.toLinearMap ∘ₗ
      (P.operator g).toLinearMap
  isIntertwining' x := by
    apply LinearMap.ext
    intro v
    let z : T.normalSubgroup := MulAut.conjNormal g x
    have hmove :=
      DFunLike.congr_fun (operator_mul_restriction R g x) v
    have hmove' :
        P.operator g (R.restriction x v) =
          R.restriction z (P.operator g v) := by
      simpa only [LinearEquiv.mul_apply] using hmove
    change
      D g⁻¹
          (f (P.operator g (R.restriction x v))) =
        D (x : A)
          (D g⁻¹
            (f (P.operator g v)))
    rw [hmove']
    have hf :=
      LinearMap.ext_iff.mp (f.isIntertwining' z)
        (P.operator g v)
    change
      f (R.restriction z (P.operator g v)) =
        D (z : A) (f (P.operator g v)) at hf
    rw [hf]
    apply (D.apply_bijective g).1
    simp only [Representation.self_inv_apply]
    rw [← Module.End.mul_apply, ← map_mul,
      ← Module.End.mul_apply, ← map_mul]
    congr 2

@[simp]
theorem actValueInv_apply
    (R : AssociatedProjectiveRepresentation T V P)
    (D : Representation ℂ A W) (g : A) (f : Space R D) (v : V) :
    actValueInv R D g f v =
      D g⁻¹ (f (P.operator g v)) :=
  rfl

/-- Each element of the ambient group acts by an invertible linear map on
the multiplicity space. -/
def operator
    (R : AssociatedProjectiveRepresentation T V P)
    (D : Representation ℂ A W) (g : A) :
    Space R D ≃ₗ[ℂ] Space R D where
  toFun := actValue R D g
  invFun := actValueInv R D g
  left_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    change
      D g⁻¹ (D g
        (f ((P.operator g).symm (P.operator g v)))) = f v
    simp
  right_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    change
      D g
        (D g⁻¹
          (f (P.operator g ((P.operator g).symm v)))) = f v
    simp
  map_add' f f' := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    change
      D g
          ((f + f') ((P.operator g).symm v)) =
        D g (f ((P.operator g).symm v)) +
          D g (f' ((P.operator g).symm v))
    simp
    rfl
  map_smul' c f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    change
      D g ((c • f) ((P.operator g).symm v)) =
        c • D g (f ((P.operator g).symm v))
    simp
    rfl

@[simp]
theorem operator_apply
    (R : AssociatedProjectiveRepresentation T V P)
    (D : Representation ℂ A W) (g : A) (f : Space R D) (v : V) :
    operator R D g f v =
      D g (f ((P.operator g).symm v)) :=
  rfl

/-- The multiplicity-space lift is literally the identity on the normal
subgroup.  This exact, rather than merely scalar, triviality is what allows
the projective action to descend to the quotient. -/
theorem operator_normal
    (R : AssociatedProjectiveRepresentation T V P)
    (D : Representation ℂ A W)
    (x : T.normalSubgroup) :
    operator R D (x : A) = 1 := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext
  intro f
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  change
    D (x : A)
        (f ((P.operator (x : A)).symm v)) =
      f v
  have hf :=
    LinearMap.ext_iff.mp (f.isIntertwining' x)
      ((P.operator (x : A)).symm v)
  change
    f (R.restriction x
        ((P.operator (x : A)).symm v)) =
      D (x : A)
        (f ((P.operator (x : A)).symm v)) at hf
  rw [← hf, R.restriction_apply,
    LinearEquiv.apply_symm_apply]

/-- The natural multiplicity-space action is projective, with factor set the
pointwise inverse of the factor set of the associated projective
representation. -/
def projective
    (R : AssociatedProjectiveRepresentation T V P)
    (D : Representation ℂ A W) :
    ProjectiveRepresentation ℂ A (Space R D) where
  operator := operator R D
  factor g h := (P.factor g h)⁻¹
  map_mul g h := by
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext
    intro f
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    change
      (actValue R D g (actValue R D h f)).toLinearMap v =
        ((scalarLinearEquiv ℂ (Space R D) (P.factor g h)⁻¹)
          (actValue R D (g * h) f)).toLinearMap v
    change
      actValue R D g (actValue R D h f) v =
        (scalarLinearEquiv ℂ (Space R D) (P.factor g h)⁻¹)
          (actValue R D (g * h) f) v
    rw [actValue_apply, actValue_apply,
      scalarLinearEquiv_apply]
    rw [Representation.IntertwiningMap.smul_apply]
    rw [actValue_apply]
    have hmul := congrArg
      (fun e : V ≃ₗ[ℂ] V ↦ e⁻¹) (P.map_mul g h)
    have happ := DFunLike.congr_fun hmul v
    simp only [mul_inv_rev, LinearEquiv.mul_apply] at happ
    have happ' :
        (P.operator h).symm ((P.operator g).symm v) =
          (P.operator (g * h)).symm
            ((scalarLinearEquiv ℂ V (P.factor g h))⁻¹ v) :=
      happ
    rw [happ']
    have hscalar :
        (scalarLinearEquiv ℂ V (P.factor g h))⁻¹ v =
          ((P.factor g h : ℂ)⁻¹ • v) := by
      rw [← map_inv]
      rw [scalarLinearEquiv_apply, Units.val_inv_eq_inv_val]
    rw [hscalar, map_smul, map_smul, map_smul, map_smul]
    rw [← Module.End.mul_apply, ← map_mul]
    rw [Units.val_inv_eq_inv_val]

@[simp]
theorem projective_operator
    (R : AssociatedProjectiveRepresentation T V P)
    (D : Representation ℂ A W) (g : A) :
    (projective R D).operator g = operator R D g :=
  rfl

@[simp]
theorem projective_operator_normal
    (R : AssociatedProjectiveRepresentation T V P)
    (D : Representation ℂ A W)
    (x : T.normalSubgroup) :
    (projective R D).operator (x : A) = 1 :=
  operator_normal R D x

@[simp]
theorem projective_factor
    (R : AssociatedProjectiveRepresentation T V P)
    (D : Representation ℂ A W) (g h : A) :
    (projective R D).factor g h = (P.factor g h)⁻¹ :=
  rfl

/-- The two projective factors cancel pointwise. -/
theorem factor_cancellation
    (R : AssociatedProjectiveRepresentation T V P)
    (D : Representation ℂ A W) (g h : A) :
    P.factor g h * (projective R D).factor g h = 1 := by
  simp

/-- The multiplicity-space action has the inverse factor set to `P`, in the
bundled form consumed by `ProjectiveRepresentation.cancelTensorLinearAction`. -/
theorem hasInverseFactorSet
    (R : AssociatedProjectiveRepresentation T V P)
    (D : Representation ℂ A W) :
    P.HasInverseFactorSet (projective R D) := by
  intro g h
  rfl

/-- The honest tensor action obtained by cancelling the factor of `P`
against the inverse factor on the multiplicity space. -/
def cancelTensorLinearAction
    (R : AssociatedProjectiveRepresentation T V P)
    (D : Representation ℂ A W) :
    A →* ((V ⊗[ℂ] Space R D) ≃ₗ[ℂ]
      (V ⊗[ℂ] Space R D)) :=
  P.cancelTensorLinearAction (projective R D)
    (hasInverseFactorSet R D)

@[simp]
theorem cancelTensorLinearAction_apply
    (R : AssociatedProjectiveRepresentation T V P)
    (D : Representation ℂ A W) (g : A) :
    cancelTensorLinearAction R D g =
      TensorProduct.congr (P.operator g)
        (operator R D g) :=
  rfl

/-- The bilinear evaluation pairing between the associated space and its
multiplicity space. -/
def evaluationBilinear
    (R : AssociatedProjectiveRepresentation T V P)
    (D : Representation ℂ A W) :
    V →ₗ[ℂ] Space R D →ₗ[ℂ] W where
  toFun v :=
    { toFun := fun f ↦ f v
      map_add' := fun f f' ↦ by rfl
      map_smul' := fun c f ↦ by rfl }
  map_add' v v' := by
    apply LinearMap.ext
    intro f
    exact f.map_add v v'
  map_smul' c v := by
    apply LinearMap.ext
    intro f
    exact f.map_smul c v

/-- Evaluation `v ⊗ f ↦ f(v)` as a linear map. -/
def evaluation
    (R : AssociatedProjectiveRepresentation T V P)
    (D : Representation ℂ A W) :
    V ⊗[ℂ] Space R D →ₗ[ℂ] W :=
  TensorProduct.lift (evaluationBilinear R D)

@[simp]
theorem evaluation_tmul
    (R : AssociatedProjectiveRepresentation T V P)
    (D : Representation ℂ A W) (v : V) (f : Space R D) :
    evaluation R D (v ⊗ₜ[ℂ] f) = f v :=
  rfl

/-- The representation underlying the factor-cancelled tensor action. -/
abbrev tensorRepresentation
    (R : AssociatedProjectiveRepresentation T V P)
    (D : Representation ℂ A W) :
    Representation ℂ A (V ⊗[ℂ] Space R D) :=
  linearRepresentationOfAction
    (cancelTensorLinearAction R D)

/-- Evaluation is equivariant for the factor-cancelled tensor action and the
original ambient action. -/
def evaluationIntertwiningMap
    (R : AssociatedProjectiveRepresentation T V P)
    (D : Representation ℂ A W) :
    Representation.IntertwiningMap
      (tensorRepresentation R D) D where
  toLinearMap := evaluation R D
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro v f
      change
        evaluation R D
            (TensorProduct.congr (P.operator g)
              (operator R D g) (v ⊗ₜ[ℂ] f)) =
          D g (evaluation R D (v ⊗ₜ[ℂ] f))
      rw [TensorProduct.congr_tmul,
        evaluation_tmul, evaluation_tmul,
        operator_apply, LinearEquiv.symm_apply_apply]
    · intro x y hx hy
      simpa only [map_add] using congrArg₂ (· + ·) hx hy

@[simp]
theorem evaluationIntertwiningMap_tmul
    (R : AssociatedProjectiveRepresentation T V P)
    (D : Representation ℂ A W) (v : V) (f : Space R D) :
    evaluationIntertwiningMap R D (v ⊗ₜ[ℂ] f) = f v :=
  rfl

/-- Evaluation is nonzero whenever the multiplicity space is nonzero. -/
theorem evaluationIntertwiningMap_ne_zero
    (R : AssociatedProjectiveRepresentation T V P)
    (D : Representation ℂ A W)
    [Nontrivial (Space R D)] :
    evaluationIntertwiningMap R D ≠ 0 := by
  obtain ⟨f : Space R D, hf⟩ :=
    exists_ne (0 : Space R D)
  have hfv : ∃ v : V, f v ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    change f v = (0 : W)
    exact h v
  obtain ⟨v, hv⟩ := hfv
  intro heval
  have happ :=
    congrArg (fun e : Representation.IntertwiningMap
      (tensorRepresentation R D) D ↦ e (v ⊗ₜ[ℂ] f)) heval
  apply hv
  simpa using happ

/-- For an irreducible ambient representation, nonzero multiplicity forces
the evaluation intertwiner to be surjective. -/
theorem evaluationIntertwiningMap_surjective
    (R : AssociatedProjectiveRepresentation T V P)
    (D : Representation ℂ A W)
    [D.IsIrreducible] [Nontrivial (Space R D)] :
    Function.Surjective (evaluationIntertwiningMap R D) := by
  let e := evaluationIntertwiningMap R D
  rcases
      (show IsSimpleOrder (Subrepresentation D) from
        inferInstance).eq_bot_or_eq_top e.range with hbot | htop
  · exfalso
    apply evaluationIntertwiningMap_ne_zero R D
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    have hx : e x ∈ e.range := by
      exact ⟨x, rfl⟩
    rw [hbot] at hx
    change e x = 0 at hx
    exact hx
  · intro w
    have hw : w ∈ e.range := by
      rw [htop]
      exact Submodule.mem_top
    exact hw

/-- Evaluation is a linear equivalence once the standard multiplicity
dimension identity has been established. -/
def evaluationLinearEquivOfFinrankEq
    (R : AssociatedProjectiveRepresentation T V P)
    (D : Representation ℂ A W)
    [Module.Finite ℂ W] [D.IsIrreducible]
    [Nontrivial (Space R D)]
    (hfin :
      Module.finrank ℂ (V ⊗[ℂ] Space R D) =
        Module.finrank ℂ W) :
    V ⊗[ℂ] Space R D ≃ₗ[ℂ] W := by
  let hsurj := evaluationIntertwiningMap_surjective R D
  exact LinearEquiv.ofBijective (evaluation R D)
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        hfin).mpr hsurj,
      hsurj⟩

/-- Equivariant form of `evaluationLinearEquivOfFinrankEq`. -/
def evaluationRepresentationEquivOfFinrankEq
    (R : AssociatedProjectiveRepresentation T V P)
    (D : Representation ℂ A W)
    [Module.Finite ℂ W] [D.IsIrreducible]
    [Nontrivial (Space R D)]
    (hfin :
      Module.finrank ℂ (V ⊗[ℂ] Space R D) =
        Module.finrank ℂ W) :
    Representation.Equiv (tensorRepresentation R D) D :=
  Representation.Equiv.mk
    (evaluationLinearEquivOfFinrankEq R D hfin)
    (evaluationIntertwiningMap R D).isIntertwining'

/-- The associated restriction is isomorphic to the chosen realization of
the normal character. -/
def restrictionIsoRealization
    (R : AssociatedProjectiveRepresentation T V P) :
    R.fdRestriction ≅ T.character.realization := by
  apply Classical.choice
  apply FDRep.nonempty_iso_of_character_eq
  rw [R.fdRestriction_character,
    T.character.realization_character]

/-- Translate between the categorical `FDRep` Hom-space and the unbundled
intertwining-map model used for the projective multiplicity action. -/
def fdRepHomEquivSpace
    (R : AssociatedProjectiveRepresentation T V P)
    (E : FDRep ℂ A) :
    (R.fdRestriction ⟶
        FDRep.res T.normalSubgroup.subtype E) ≃ₗ[ℂ]
      Space R E.ρ :=
  (FDRep.forget₂HomLinearEquiv
      R.fdRestriction
      (FDRep.res T.normalSubgroup.subtype E)).symm |>.trans
    (Rep.homLinearEquiv _ _)

/-- Precomposition by an isomorphism as a linear equivalence of `FDRep`
Hom-spaces. -/
def precomposeFDRepHomEquiv
    {L : Type u} [Group L]
    {X Y Z : FDRep ℂ L} (i : X ≅ Y) :
    (Y ⟶ Z) ≃ₗ[ℂ] (X ⟶ Z) where
  toFun f := i.hom ≫ f
  invFun f := i.inv ≫ f
  left_inv f := by simp
  right_inv f := by simp
  map_add' f g := by simp
  map_smul' c f := by simp

/-- Identify the multiplicity space with the Hom-space from the triple's
chosen normal-character realization. -/
def characterHomEquivSpace
    (R : AssociatedProjectiveRepresentation T V P)
    (E : FDRep ℂ A) :
    (T.character.realization ⟶
        FDRep.res T.normalSubgroup.subtype E) ≃ₗ[ℂ]
      Space R E.ρ :=
  (precomposeFDRepHomEquiv
      (restrictionIsoRealization R)).trans
    (fdRepHomEquivSpace R E)

/-- A nonzero map from the normal-character realization into an ambient
restriction makes the associated multiplicity space nonzero. -/
theorem space_nontrivial_of_exists_character_hom
    (R : AssociatedProjectiveRepresentation T V P)
    (E : FDRep ℂ A)
    (hE : ∃ f : T.character.realization ⟶
      FDRep.res T.normalSubgroup.subtype E, f ≠ 0) :
    Nontrivial (Space R E.ρ) := by
  obtain ⟨f, hf⟩ := hE
  let i : R.fdRestriction ≅ T.character.realization :=
    restrictionIsoRealization R
  let q : R.fdRestriction ⟶
      FDRep.res T.normalSubgroup.subtype E :=
    i.hom ≫ f
  have hq : q ≠ 0 := by
    intro hq
    apply hf
    have hzero :=
      congrArg (fun z ↦ i.inv ≫ z) hq
    simpa [q, Category.assoc] using hzero
  let e :=
    fdRepHomEquivSpace R E
  let s : Space R E.ρ := e q
  have hs : s ≠ 0 := by
    intro hs
    apply hq
    apply e.injective
    simpa [s] using hs
  exact ⟨⟨s, 0, hs⟩⟩

section LiesOver

variable {A₀ V₀ : Type} [Finite A₀] [Group A₀]
variable [AddCommGroup V₀] [Module ℂ V₀]
  [Module.Finite ℂ V₀] [Nontrivial V₀]
variable {T₀ : CharacterTriple A₀}
variable {P₀ : ProjectiveRepresentation ℂ A₀ V₀}

/-- If an irreducible ambient character lies over the normal character, its
multiplicity space is nonzero. -/
theorem space_nontrivial_of_liesOver
    (R : AssociatedProjectiveRepresentation T₀ V₀ P₀)
    (χ : IrreducibleCharacter A₀)
    (hχ : CliffordCorrespondence.LiesOverAlong
      T₀.normalSubgroup.subtype T₀.character χ) :
    Nontrivial (Space R χ.realization.ρ) := by
  apply space_nontrivial_of_exists_character_hom R χ.realization
  exact
    (CliffordCorrespondence.liesOverAlong_iff_exists_nonzero
      T₀.normalSubgroup.subtype T₀.character χ).mp hχ

end LiesOver

end MultiplicityProjective
end CharacterTriple
end McKayConjecture
