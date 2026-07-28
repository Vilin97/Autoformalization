/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.SemidirectProduct
import McKayConjecture.Character.ClassFunction
import McKayConjecture.Character.Transport
import McKayConjecture.CharacterTriple.CentralIsomorphism

/-!
# Character triples attached to semidirect products

The inductive McKay condition uses triples of the form
`(X ⋊ Γ_χ, X, χ)`.  This file constructs that triple without identifying
`X` definitionally with its image in the semidirect product.  The normal
subgroup is the range of `SemidirectProduct.inl`, and the character is
transported across its canonical isomorphism with `X`.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace CharacterTriple

variable {X : Type u} {Γ : Type v} [Group X] [Group Γ]
  (φ : Γ →* MulAut X)

/-- Finiteness of both factors gives finiteness of the semidirect product. -/
instance semidirectFinite [Finite X] [Finite Γ] :
    Finite (X ⋊[φ] Γ) :=
  Finite.of_equiv (X × Γ) SemidirectProduct.equivProd.symm

/-- The canonical copy of `X` inside `X ⋊ Γ`. -/
abbrev semidirectNormalSubgroup : Subgroup (X ⋊[φ] Γ) :=
  MonoidHom.range (SemidirectProduct.inl : X →* X ⋊[φ] Γ)

/-- The canonical copy of `X` is normal in its semidirect product. -/
instance semidirectNormalSubgroupNormal :
    (semidirectNormalSubgroup φ).Normal := by
  rw [semidirectNormalSubgroup, SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

/-- The canonical copy of `X` in the semidirect product is isomorphic to
`X` itself. -/
def semidirectNormalEquiv :
    semidirectNormalSubgroup φ ≃* X where
  toFun x := x.1.left
  invFun x :=
    ⟨SemidirectProduct.inl x, ⟨x, rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · have hx :
        SemidirectProduct.rightHom (x : X ⋊[φ] Γ) = 1 := by
          rw [← MonoidHom.mem_ker]
          rw [← SemidirectProduct.range_inl_eq_ker_rightHom]
          exact x.property
      exact hx.symm
  right_inv x := rfl
  map_mul' x y := by
    have hx :
        SemidirectProduct.rightHom (x : X ⋊[φ] Γ) = 1 := by
      rw [← MonoidHom.mem_ker]
      rw [← SemidirectProduct.range_inl_eq_ker_rightHom]
      exact x.property
    change (x.1 * y.1).left = x.1.left * y.1.left
    rw [SemidirectProduct.mul_left]
    have hx' : x.1.right = 1 := by
      simpa only [SemidirectProduct.rightHom_eq_right] using hx
    simp only [hx', map_one, MulAut.one_apply]

@[simp]
theorem semidirectNormalEquiv_apply
    (x : semidirectNormalSubgroup φ) :
    semidirectNormalEquiv φ x = x.1.left :=
  rfl

@[simp]
theorem semidirectNormalEquiv_symm_apply_coe (x : X) :
    ((semidirectNormalEquiv φ).symm x :
      semidirectNormalSubgroup φ) =
        ⟨SemidirectProduct.inl x, ⟨x, rfl⟩⟩ :=
  rfl

/-- An irreducible character of `X` is invariant under the acting group
when its values are fixed by every automorphism in the action. -/
def IsInvariant
    (χ : IrreducibleCharacter X) : Prop :=
  ∀ (γ : Γ) (x : X), χ.values (φ γ x) = χ.values x

namespace IsInvariant

variable {φ}

@[simp]
theorem inv_apply
    {χ : IrreducibleCharacter X} (hχ : IsInvariant φ χ)
    (γ : Γ) (x : X) :
    χ.values ((φ γ)⁻¹ x) = χ.values x := by
  simpa using hχ γ⁻¹ x

end IsInvariant

/-- Conjugating an element of the canonical normal subgroup has the expected
left coordinate. -/
theorem conjugate_semidirectNormal_left
    (a : X ⋊[φ] Γ) (x : semidirectNormalSubgroup φ) :
    (a * x.1 * a⁻¹).left =
      a.left * φ a.right x.1.left * a.left⁻¹ := by
  have hx :
      SemidirectProduct.rightHom (x : X ⋊[φ] Γ) = 1 := by
    rw [← MonoidHom.mem_ker]
    rw [← SemidirectProduct.range_inl_eq_ker_rightHom]
    exact x.property
  have hx' : x.1.right = 1 := by
    simpa only [SemidirectProduct.rightHom_eq_right] using hx
  simp [SemidirectProduct.mul_left, hx', mul_assoc]

/-- The character triple `(X ⋊ Γ, X, χ)` attached to an invariant
irreducible character `χ`.

The subgroup component is the canonical range of `inl`; the character
component is `χ` transported across `semidirectNormalEquiv`.
-/
def ofSemidirect [Finite X] [Finite Γ]
    (χ : IrreducibleCharacter X) (hχ : IsInvariant φ χ) :
    CharacterTriple (X ⋊[φ] Γ) where
  normalSubgroup := semidirectNormalSubgroup φ
  isNormal := inferInstance
  character := χ.comap (semidirectNormalEquiv φ)
  isInvariant := by
    intro a x
    change
      χ.values (a * x.1 * a⁻¹).left =
        χ.values x.1.left
    rw [conjugate_semidirectNormal_left φ]
    calc
      χ.values (a.left * φ a.right x.1.left * a.left⁻¹) =
          χ.values (φ a.right x.1.left) :=
        ClassFunction.conj_apply χ.toClassFunction
          (φ a.right x.1.left) a.left
      _ = χ.values x.1.left := hχ a.right x.1.left

@[simp]
theorem ofSemidirect_normalSubgroup [Finite X] [Finite Γ]
    (χ : IrreducibleCharacter X) (hχ : IsInvariant φ χ) :
    (ofSemidirect φ χ hχ).normalSubgroup =
      semidirectNormalSubgroup φ :=
  rfl

@[simp]
theorem ofSemidirect_character_values [Finite X] [Finite Γ]
    (χ : IrreducibleCharacter X) (hχ : IsInvariant φ χ)
    (x : semidirectNormalSubgroup φ) :
    (ofSemidirect φ χ hχ).character.values x =
      χ.values x.1.left :=
  rfl

end CharacterTriple
end McKayConjecture
