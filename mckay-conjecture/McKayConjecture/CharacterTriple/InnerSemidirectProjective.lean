/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedExistence

/-!
# Projective representations for semidirect products acting innerly

Suppose an action `Γ → Aut(X)` is supplied with a normalized set-theoretic
lift `s : Γ → X` which realizes every automorphism by conjugation.  For an
irreducible representation `ρ` of `X`, the operators

`(x, γ) ↦ ρ(x s(γ))`

form an associated projective representation of `X ⋊ Γ`.  Its factor is
the scalar action of the central defect between the two words
`x s(γ) y s(δ)` and the word chosen for their semidirect product.

The construction deliberately accepts the scalar action as data.  This
makes it possible to use the same factor function for two character rows
whose central characters agree.
-/

noncomputable section

open CategoryTheory

universe u v

namespace McKayConjecture
namespace CharacterTriple
namespace InnerSemidirectProjective

variable {X : Type u} {Γ : Type v}
  [Group X] [Finite X] [Group Γ] [Finite Γ]
variable (φ : Γ →* MulAut X)
variable (χ : IrreducibleCharacter X)
variable (hχ : IsInvariant φ χ)
variable (lift : Γ → X)
variable (lift_one : lift 1 = 1)
variable (lift_spec : ∀ a : Γ, φ a = MulAut.conj (lift a))

/-- The group word used to lift an element of the semidirect product. -/
def word (z : X ⋊[φ] Γ) : X :=
  z.left * lift z.right

/-- The discrepancy between multiplication of lifted words and the word
chosen for the product. -/
def defect (z w : X ⋊[φ] Γ) : X :=
  word φ lift z * word φ lift w *
    (word φ lift (z * w))⁻¹

include lift_spec

theorem conj_word (z : X ⋊[φ] Γ) :
    MulAut.conj (word φ lift z) =
      MulAut.conj z.left * φ z.right := by
  rw [word, map_mul, lift_spec]

theorem conj_word_mul (z w : X ⋊[φ] Γ) :
    MulAut.conj (word φ lift z * word φ lift w) =
      MulAut.conj (word φ lift (z * w)) := by
  rw [map_mul, conj_word φ lift lift_spec,
    conj_word φ lift lift_spec,
    conj_word φ lift lift_spec]
  apply DFunLike.ext _ _
  intro x
  simp only [MulAut.mul_apply, MulAut.conj_apply,
    map_mul, SemidirectProduct.mul_left,
    SemidirectProduct.mul_right, map_inv]

/-- The word discrepancy is central because the two words induce the same
inner automorphism. -/
theorem defect_mem_center (z w : X ⋊[φ] Γ) :
    defect φ lift z w ∈ Subgroup.center X := by
  have hconj :
      MulAut.conj (defect φ lift z w) = 1 := by
    rw [defect, map_mul, map_inv,
      conj_word_mul φ lift lift_spec]
    simp
  rw [Subgroup.mem_center_iff]
  intro x
  have hx := DFunLike.congr_fun hconj x
  simp only [MulAut.conj_apply, MulAut.one_apply] at hx
  have hcomm :
      defect φ lift z w * x =
        (defect φ lift z w * x *
            (defect φ lift z w)⁻¹) *
          defect φ lift z w := by group
  calc
    x * defect φ lift z w =
        (defect φ lift z w * x *
            (defect φ lift z w)⁻¹) *
          defect φ lift z w := by rw [hx]
    _ = defect φ lift z w * x := hcomm.symm

variable (centralUnit : X → ℂˣ)
variable
  (central_action :
    ∀ z : X, z ∈ Subgroup.center X →
      AssociatedExistence.realizationAction χ z =
        scalarLinearEquiv ℂ χ.realization (centralUnit z))

include central_action

/-- The projective representation obtained from an inner-action lift. -/
def projectiveRepresentation :
    ProjectiveRepresentation ℂ (X ⋊[φ] Γ) χ.realization where
  operator z :=
    AssociatedExistence.realizationAction χ
      (word φ lift z)
  factor z w :=
    centralUnit (defect φ lift z w)
  map_mul z w := by
    change
      AssociatedExistence.realizationAction χ
            (word φ lift z) *
          AssociatedExistence.realizationAction χ
            (word φ lift w) =
        scalarLinearEquiv ℂ χ.realization
            (centralUnit (defect φ lift z w)) *
          AssociatedExistence.realizationAction χ
            (word φ lift (z * w))
    rw [← map_mul,
      ← central_action
        (defect φ lift z w)
        (defect_mem_center φ lift lift_spec z w),
      ← map_mul]
    apply congrArg
      (AssociatedExistence.realizationAction χ)
    unfold defect
    group

@[simp]
theorem projectiveRepresentation_operator
    (z : X ⋊[φ] Γ) :
    (projectiveRepresentation φ χ lift lift_spec
      centralUnit central_action).operator z =
      AssociatedExistence.realizationAction χ
        (word φ lift z) :=
  rfl

@[simp]
theorem projectiveRepresentation_factor
    (z w : X ⋊[φ] Γ) :
    (projectiveRepresentation φ χ lift lift_spec
      centralUnit central_action).factor z w =
      centralUnit (defect φ lift z w) :=
  rfl

/-- The inner-lift projective representation is associated with the
canonical semidirect-product character triple. -/
def associated :
    AssociatedProjectiveRepresentation
      (ofSemidirect φ χ hχ)
      χ.realization
      (projectiveRepresentation
        φ χ lift lift_spec centralUnit central_action) where
  restriction :=
    (AssociatedExistence.realizationAction χ).comp
      (AssociatedExistence.tripleNormalEquiv
        φ χ hχ).toMonoidHom
  restriction_apply := by
    intro x
    rw [AssociatedExistence.coe_eq_inl_tripleNormalEquiv]
    change
      AssociatedExistence.realizationAction χ
          (AssociatedExistence.tripleNormalEquiv φ χ hχ x) =
        AssociatedExistence.realizationAction χ
          (word φ lift
            (SemidirectProduct.inl
              (AssociatedExistence.tripleNormalEquiv
                φ χ hχ x)))
    simp [word, lift_one]
  restriction_simple := by
    let E : FDRep ℂ X ≌
        FDRep ℂ (ofSemidirect φ χ hχ).normalSubgroup :=
      Action.resEquiv
        (FGModuleCat ℂ)
        (AssociatedExistence.tripleNormalEquiv φ χ hχ)
    change Simple (E.functor.obj χ.realization)
    exact CategoryTheory.simple_obj E.functor χ.realization
  restriction_character := by
    funext x
    change
      χ.realization.character
          (AssociatedExistence.tripleNormalEquiv
            φ χ hχ x) =
        χ.values
          (AssociatedExistence.tripleNormalEquiv
            φ χ hχ x)
    exact
      congrFun χ.realization_character
        (AssociatedExistence.tripleNormalEquiv
          φ χ hχ x)
  normal_mul := by
    intro x a
    rw [AssociatedExistence.coe_eq_inl_tripleNormalEquiv]
    simp only [projectiveRepresentation_operator]
    change
      AssociatedExistence.realizationAction χ
          (word φ lift
            (SemidirectProduct.inl
                (AssociatedExistence.tripleNormalEquiv
                  φ χ hχ x) * a)) =
        AssociatedExistence.realizationAction χ
            (word φ lift
              (SemidirectProduct.inl
                (AssociatedExistence.tripleNormalEquiv
                  φ χ hχ x))) *
          AssociatedExistence.realizationAction χ
            (word φ lift a)
    rw [← map_mul]
    apply congrArg
      (AssociatedExistence.realizationAction χ)
    simp [word, lift_one, mul_assoc]
  mul_normal := by
    intro a x
    rw [AssociatedExistence.coe_eq_inl_tripleNormalEquiv]
    simp only [projectiveRepresentation_operator]
    let y :=
      AssociatedExistence.tripleNormalEquiv φ χ hχ x
    change
      AssociatedExistence.realizationAction χ
          (word φ lift
            (a * SemidirectProduct.inl y)) =
        AssociatedExistence.realizationAction χ
            (word φ lift a) *
          AssociatedExistence.realizationAction χ
            (word φ lift (SemidirectProduct.inl y))
    rw [← map_mul]
    apply congrArg
      (AssociatedExistence.realizationAction χ)
    have ha :
        φ a.right y =
          lift a.right * y * (lift a.right)⁻¹ := by
      rw [lift_spec]
      rfl
    simp only [word, SemidirectProduct.mul_left,
      SemidirectProduct.mul_right,
      SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, lift_one, mul_one]
    rw [ha]
    group

end InnerSemidirectProjective
end CharacterTriple
end McKayConjecture
