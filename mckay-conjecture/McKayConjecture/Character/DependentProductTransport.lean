/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.FiniteProductAutomorphism
import McKayConjecture.GroupTheory.LayerSylowNormalizerAction

/-!
# Transport between dependently indexed products

An equivalence `e : α ≃ β` of index types and coordinate
isomorphisms `c a : G a ≃* H (e a)` induce an isomorphism between the
dependent products of `G` and `H`.  This file proves that finite
external tensor products and the corresponding finite-product
character equivalences are natural for this simultaneous reindexing
and coordinate transport, both for ordinary and `p'`-characters.

For the family of components of a finite group, this construction is
exactly the external component-product conjugation map.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace IrreducibleCharacter

universe u v w

/-- The multiplicative equivalence of dependent products induced by an
index equivalence and isomorphisms between the matched coordinates. -/
def dependentProductMulEquiv
    {α β : Type u}
    {G : α → Type v} {H : β → Type w}
    [∀ a, Group (G a)] [∀ b, Group (H b)]
    (e : α ≃ β)
    (c : ∀ a, G a ≃* H (e a)) :
    (∀ a, G a) ≃* ∀ b, H b :=
  (coordinatewiseMulEquiv c).trans
    (piCongrLeftMulEquiv H e)

/-- At a matched target coordinate, dependent-product transport is the
specified coordinate isomorphism. -/
@[simp]
theorem dependentProductMulEquiv_apply_apply
    {α β : Type u}
    {G : α → Type v} {H : β → Type w}
    [∀ a, Group (G a)] [∀ b, Group (H b)]
    (e : α ≃ β)
    (c : ∀ a, G a ≃* H (e a))
    (x : ∀ a, G a) (a : α) :
    dependentProductMulEquiv e c x (e a) =
      c a (x a) := by
  simp [dependentProductMulEquiv]

/-- The inverse dependent-product transport evaluates by applying the
inverse coordinate isomorphism after reindexing along `e`. -/
@[simp]
theorem dependentProductMulEquiv_symm_apply
    {α β : Type u}
    {G : α → Type v} {H : β → Type w}
    [∀ a, Group (G a)] [∀ b, Group (H b)]
    (e : α ≃ β)
    (c : ∀ a, G a ≃* H (e a))
    (y : ∀ b, H b) (a : α) :
    (dependentProductMulEquiv e c).symm y a =
      (c a).symm (y (e a)) := by
  rfl

/-- Pull back a family of irreducible characters by simultaneously
reindexing it and applying the matched coordinate isomorphisms. -/
def dependentProductIrreducibleEquiv
    {α β : Type u}
    {G : α → Type v} {H : β → Type w}
    [∀ a, Group (G a)] [∀ b, Group (H b)]
    (e : α ≃ β)
    (c : ∀ a, G a ≃* H (e a)) :
    (∀ b, IrreducibleCharacter (H b)) ≃
      ∀ a, IrreducibleCharacter (G a) :=
  (reindexIrreducibleEquiv H e).trans
    (coordinatewiseIrreducibleEquiv c)

@[simp]
theorem dependentProductIrreducibleEquiv_apply
    {α β : Type u}
    {G : α → Type v} {H : β → Type w}
    [∀ a, Group (G a)] [∀ b, Group (H b)]
    (e : α ≃ β)
    (c : ∀ a, G a ≃* H (e a))
    (χ : ∀ b, IrreducibleCharacter (H b))
    (a : α) :
    dependentProductIrreducibleEquiv e c χ a =
      (χ (e a)).comap (c a) :=
  rfl

/-- Finite external tensor product is natural for simultaneous index
and coordinate transport. -/
@[simp]
theorem finiteExternalTensor_comap_dependentProduct
    {α β : Type u} [Fintype α] [Fintype β]
    {G : α → Type v} {H : β → Type w}
    [∀ a, Group (G a)] [∀ b, Group (H b)]
    (e : α ≃ β)
    (c : ∀ a, G a ≃* H (e a))
    (χ : ∀ b, IrreducibleCharacter (H b)) :
    (finiteExternalTensor χ).comap
        (dependentProductMulEquiv e c) =
      finiteExternalTensor
        (dependentProductIrreducibleEquiv e c χ) := by
  change
    (finiteExternalTensor χ).comap
        ((coordinatewiseMulEquiv c).trans
          (piCongrLeftMulEquiv H e)) =
      finiteExternalTensor
        (coordinatewiseIrreducibleEquiv c
          (reindexIrreducibleEquiv H e χ))
  rw [← comap_trans,
    finiteExternalTensor_comap_reindex,
    finiteExternalTensor_comap_coordinatewise]
  rfl

/-- The finite-product character equivalence is natural for simultaneous
index and coordinate transport. -/
@[simp]
theorem finiteProductEquiv_comap_dependentProduct
    {α β : Type} [Fintype α] [Fintype β]
    {G : α → Type} {H : β → Type}
    [∀ a, Finite (G a)] [∀ b, Finite (H b)]
    [∀ a, Group (G a)] [∀ b, Group (H b)]
    (e : α ≃ β)
    (c : ∀ a, G a ≃* H (e a))
    (χ : ∀ b, IrreducibleCharacter (H b)) :
    (finiteProductEquiv H χ).comap
        (dependentProductMulEquiv e c) =
      finiteProductEquiv G
        (dependentProductIrreducibleEquiv e c χ) := by
  rw [finiteProductEquiv_apply,
    finiteProductEquiv_apply,
    finiteExternalTensor_comap_dependentProduct]

/-- Commuting-square form of dependent finite-product naturality. -/
theorem finiteProductEquiv_dependentProduct_comm
    {α β : Type} [Fintype α] [Fintype β]
    {G : α → Type} {H : β → Type}
    [∀ a, Finite (G a)] [∀ b, Finite (H b)]
    [∀ a, Group (G a)] [∀ b, Group (H b)]
    (e : α ≃ β)
    (c : ∀ a, G a ≃* H (e a)) :
    (finiteProductEquiv H).trans
        (comapEquiv (dependentProductMulEquiv e c)) =
      (dependentProductIrreducibleEquiv e c).trans
        (finiteProductEquiv G) := by
  apply Equiv.ext
  intro χ
  exact finiteProductEquiv_comap_dependentProduct
    e c χ

/-! ### Prime-to-`p` characters -/

/-- Pull back a family of `p'`-degree irreducible characters by
simultaneously reindexing it and applying the matched coordinate
isomorphisms. -/
def dependentProductPPrimeEquiv
    {α β : Type u}
    {G : α → Type v} {H : β → Type w}
    [∀ a, Group (G a)] [∀ b, Group (H b)]
    (p : ℕ) (e : α ≃ β)
    (c : ∀ a, G a ≃* H (e a)) :
    (∀ b, PPrimeIrreducibleCharacter (H b) p) ≃
      ∀ a, PPrimeIrreducibleCharacter (G a) p :=
  (reindexPPrimeEquiv H p e).trans
    (coordinatewisePPrimeEquiv p c)

@[simp]
theorem dependentProductPPrimeEquiv_apply
    {α β : Type u}
    {G : α → Type v} {H : β → Type w}
    [∀ a, Group (G a)] [∀ b, Group (H b)]
    (p : ℕ) (e : α ≃ β)
    (c : ∀ a, G a ≃* H (e a))
    (χ : ∀ b, PPrimeIrreducibleCharacter (H b) p)
    (a : α) :
    dependentProductPPrimeEquiv p e c χ a =
      pPrimeComapEquiv p (c a) (χ (e a)) :=
  rfl

/-- Finite external tensor product on `p'`-characters is natural for
simultaneous index and coordinate transport. -/
@[simp]
theorem finiteExternalTensorPPrime_comap_dependentProduct
    {α β : Type u} [Fintype α] [Fintype β]
    {G : α → Type v} {H : β → Type w}
    [∀ a, Group (G a)] [∀ b, Group (H b)]
    (p : ℕ) [Fact p.Prime]
    (e : α ≃ β)
    (c : ∀ a, G a ≃* H (e a))
    (χ : ∀ b, PPrimeIrreducibleCharacter (H b) p) :
    pPrimeComapEquiv p (dependentProductMulEquiv e c)
        (finiteExternalTensorPPrime p χ) =
      finiteExternalTensorPPrime p
        (dependentProductPPrimeEquiv p e c χ) := by
  apply Subtype.ext
  exact
    finiteExternalTensor_comap_dependentProduct
      e c (fun b ↦ (χ b).1)

/-- The finite-product `p'`-character equivalence is natural for
simultaneous index and coordinate transport. -/
@[simp]
theorem finiteProductPPrimeEquiv_comap_dependentProduct
    {α β : Type} [Fintype α] [Fintype β]
    {G : α → Type} {H : β → Type}
    [∀ a, Finite (G a)] [∀ b, Finite (H b)]
    [∀ a, Group (G a)] [∀ b, Group (H b)]
    (p : ℕ) [Fact p.Prime]
    (e : α ≃ β)
    (c : ∀ a, G a ≃* H (e a))
    (χ : ∀ b, PPrimeIrreducibleCharacter (H b) p) :
    pPrimeComapEquiv p (dependentProductMulEquiv e c)
        (finiteProductPPrimeEquiv H p χ) =
      finiteProductPPrimeEquiv G p
        (dependentProductPPrimeEquiv p e c χ) := by
  rw [finiteProductPPrimeEquiv_apply,
    finiteProductPPrimeEquiv_apply,
    finiteExternalTensorPPrime_comap_dependentProduct]

/-- Commuting-square form of dependent finite-product naturality for
`p'`-characters. -/
theorem finiteProductPPrimeEquiv_dependentProduct_comm
    {α β : Type} [Fintype α] [Fintype β]
    {G : α → Type} {H : β → Type}
    [∀ a, Finite (G a)] [∀ b, Finite (H b)]
    [∀ a, Group (G a)] [∀ b, Group (H b)]
    (p : ℕ) [Fact p.Prime]
    (e : α ≃ β)
    (c : ∀ a, G a ≃* H (e a)) :
    (finiteProductPPrimeEquiv H p).trans
        (pPrimeComapEquiv p
          (dependentProductMulEquiv e c)) =
      (dependentProductPPrimeEquiv p e c).trans
        (finiteProductPPrimeEquiv G p) := by
  apply Equiv.ext
  intro χ
  exact finiteProductPPrimeEquiv_comap_dependentProduct
    p e c χ

/-! ### Component-product conjugation -/

open GroupTheory

/-- Dependent-product transport for the conjugation permutation of
components and the canonical carrier isomorphisms is exactly the
component-product conjugation automorphism. -/
theorem dependentProductMulEquiv_componentConjugation
    (A : Type) [Group A] [Finite A]
    (g : A) :
    dependentProductMulEquiv
        (G := fun K : ComponentIndex A ↦ K.1)
        (H := fun K : ComponentIndex A ↦ K.1)
        (componentConjugationPermutation A g)
        (fun K ↦
          show K.1 ≃*
              ((componentConjugationPermutation A g) K).1
            from componentConjugationEquiv A g K) =
      layerComponentProductConjugation A g := by
  apply MulEquiv.ext
  intro x
  funext L
  obtain ⟨K, rfl⟩ :=
    (componentConjugationPermutation A g).surjective L
  apply Subtype.ext
  rw [dependentProductMulEquiv_apply_apply]
  change
    ((componentConjugationEquiv A g K (x K) :
        (g • K).1) : A) =
      ((layerComponentProductConjugation A g x (g • K) :
          (g • K).1) : A)
  rw [componentConjugationEquiv_apply_coe,
    layerComponentProductConjugation_apply_coe]
  have hindex : g⁻¹ • (g • K) = K :=
    inv_smul_smul g K
  have hcoe :
      ((x (g⁻¹ • (g • K)) :
          (g⁻¹ • (g • K)).1) : A) =
        (x K : A) := by
    rw [hindex]
  rw [hcoe]

end IrreducibleCharacter
end McKayConjecture
