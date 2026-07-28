/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.CategoryTheory.Action.Basic
import McKayConjecture.IrreducibleCharacter

/-!
# Transport of irreducible characters

An isomorphism of groups transports finite-dimensional representations, and
hence irreducible characters, by restriction along the isomorphism.  This file
packages that construction at the level of `IrreducibleCharacter`.
-/

noncomputable section

open CategoryTheory

universe u v w

namespace McKayConjecture
namespace IrreducibleCharacter

variable {G : Type u} {H : Type v} {K : Type w}
variable [Group G] [Group H] [Group K]

/-- Pull an irreducible character of `G` back along a group isomorphism
`e : H ≃* G`. -/
def comap (e : H ≃* G) (χ : IrreducibleCharacter G) :
    IrreducibleCharacter H where
  values h := χ.values (e h)
  degree := χ.degree
  isIrreducible := by
    obtain ⟨V, hV, hvalues, hdegree⟩ := χ.isIrreducible
    let E : FDRep ℂ G ≌ FDRep ℂ H :=
      Action.resEquiv (FGModuleCat ℂ) e
    let W : FDRep ℂ H := E.functor.obj V
    haveI : Simple V := hV
    haveI : Simple W := CategoryTheory.simple_obj E.functor V
    refine ⟨W, inferInstance, ?_, ?_⟩
    · funext h
      change LinearMap.trace ℂ W (W.ρ h) = χ.values (e h)
      change LinearMap.trace ℂ V (V.ρ (e h)) = χ.values (e h)
      exact congrFun hvalues (e h)
    · exact hdegree

@[simp]
theorem comap_values (e : H ≃* G) (χ : IrreducibleCharacter G) (h : H) :
    (χ.comap e).values h = χ.values (e h) :=
  rfl

@[simp]
theorem comap_degree (e : H ≃* G) (χ : IrreducibleCharacter G) :
    (χ.comap e).degree = χ.degree :=
  rfl

@[simp]
theorem comap_refl (χ : IrreducibleCharacter G) :
    χ.comap (MulEquiv.refl G) = χ := by
  ext
  rfl

@[simp]
theorem comap_trans (e : H ≃* G) (f : K ≃* H)
    (χ : IrreducibleCharacter G) :
    (χ.comap e).comap f = χ.comap (f.trans e) := by
  ext
  rfl

/-- A group isomorphism induces a bijection on irreducible characters. -/
def comapEquiv (e : H ≃* G) :
    IrreducibleCharacter G ≃ IrreducibleCharacter H where
  toFun := comap e
  invFun := comap e.symm
  left_inv χ := by
    ext
    simp
  right_inv χ := by
    ext
    simp

@[simp]
theorem comapEquiv_apply (e : H ≃* G) (χ : IrreducibleCharacter G) :
    comapEquiv e χ = χ.comap e :=
  rfl

/-- Transport along a group isomorphism preserves the `p'`-degree condition. -/
def pPrimeComapEquiv (p : ℕ) (e : H ≃* G) :
    PPrimeIrreducibleCharacter G p ≃ PPrimeIrreducibleCharacter H p where
  toFun χ := ⟨χ.1.comap e, χ.2⟩
  invFun χ := ⟨χ.1.comap e.symm, χ.2⟩
  left_inv χ := by
    apply Subtype.ext
    simp
  right_inv χ := by
    apply Subtype.ext
    simp

@[simp]
theorem pPrimeComapEquiv_degree (p : ℕ) (e : H ≃* G)
    (χ : PPrimeIrreducibleCharacter G p) :
    (pPrimeComapEquiv p e χ).1.degree = χ.1.degree :=
  rfl

/-- Isomorphic groups have equally many irreducible characters of `p'`-degree.

The common universe hypothesis matches the cardinal equality used by
`McKayConjecture.Statement`; no finiteness assumption is needed here.
-/
theorem cardinal_pPrime_eq_of_mulEquiv
    {G H : Type u} [Group G] [Group H] (p : ℕ) (e : H ≃* G) :
    Cardinal.mk (PPrimeIrreducibleCharacter G p) =
      Cardinal.mk (PPrimeIrreducibleCharacter H p) :=
  Cardinal.mk_congr (pPrimeComapEquiv p e)

end IrreducibleCharacter
end McKayConjecture
