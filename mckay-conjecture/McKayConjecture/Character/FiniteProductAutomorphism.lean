/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Automorphism
import McKayConjecture.Character.FiniteProductCorrespondence

/-!
# Naturality of finite external tensor products

Finite external tensor products commute with coordinatewise group
isomorphisms and with equivalences of finite index types.  This file
packages those two naturality statements both pointwise and as commuting
squares of character equivalences.

The external-tensor statements are universe-polymorphic and do not require
finite groups.  Statements involving `finiteProductEquiv` retain its
universe-zero exhaustivity boundary.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

namespace McKayConjecture
namespace IrreducibleCharacter

universe u v w x

/-! ### Coordinatewise group isomorphisms -/

/-- The isomorphism of dependent products induced coordinatewise by a
family of group isomorphisms. -/
def coordinatewiseMulEquiv
    {ι : Type u} {G : ι → Type v} {H : ι → Type w}
    [∀ i, Group (G i)] [∀ i, Group (H i)]
    (e : ∀ i, G i ≃* H i) :
    (∀ i, G i) ≃* ∀ i, H i :=
  MulEquiv.piCongrRight e

@[simp]
theorem coordinatewiseMulEquiv_apply
    {ι : Type u} {G : ι → Type v} {H : ι → Type w}
    [∀ i, Group (G i)] [∀ i, Group (H i)]
    (e : ∀ i, G i ≃* H i) (g : ∀ i, G i) (i : ι) :
    coordinatewiseMulEquiv e g i = e i (g i) :=
  rfl

@[simp]
theorem coordinatewiseMulEquiv_symm_apply
    {ι : Type u} {G : ι → Type v} {H : ι → Type w}
    [∀ i, Group (G i)] [∀ i, Group (H i)]
    (e : ∀ i, G i ≃* H i) (h : ∀ i, H i) (i : ι) :
    (coordinatewiseMulEquiv e).symm h i =
      (e i).symm (h i) :=
  rfl

@[simp]
theorem coordinatewiseMulEquiv_symm
    {ι : Type u} {G : ι → Type v} {H : ι → Type w}
    [∀ i, Group (G i)] [∀ i, Group (H i)]
    (e : ∀ i, G i ≃* H i) :
    (coordinatewiseMulEquiv e).symm =
      coordinatewiseMulEquiv (fun i ↦ (e i).symm) :=
  rfl

@[simp]
theorem coordinatewiseMulEquiv_refl
    {ι : Type u} {G : ι → Type v}
    [∀ i, Group (G i)] :
    coordinatewiseMulEquiv
        (fun i ↦ MulEquiv.refl (G i)) =
      MulEquiv.refl (∀ i, G i) :=
  rfl

@[simp]
theorem coordinatewiseMulEquiv_trans
    {ι : Type u}
    {G : ι → Type v} {H : ι → Type w}
    {K : ι → Type x}
    [∀ i, Group (G i)] [∀ i, Group (H i)]
    [∀ i, Group (K i)]
    (e : ∀ i, G i ≃* H i)
    (f : ∀ i, H i ≃* K i) :
    (coordinatewiseMulEquiv e).trans
        (coordinatewiseMulEquiv f) =
      coordinatewiseMulEquiv
        (fun i ↦ (e i).trans (f i)) :=
  rfl

/-- Pullback along a coordinatewise group isomorphism commutes with finite
external tensor product. -/
@[simp]
theorem finiteExternalTensor_comap_coordinatewise
    {ι : Type u} [Fintype ι]
    {G : ι → Type v} {H : ι → Type w}
    [∀ i, Group (G i)] [∀ i, Group (H i)]
    (e : ∀ i, G i ≃* H i)
    (χ : ∀ i, IrreducibleCharacter (H i)) :
    (finiteExternalTensor χ).comap
        (coordinatewiseMulEquiv e) =
      finiteExternalTensor
        (fun i ↦ (χ i).comap (e i)) := by
  apply IrreducibleCharacter.ext
  funext g
  simp [coordinatewiseMulEquiv]

@[simp]
theorem finiteExternalTensor_comap_coordinatewise_values
    {ι : Type u} [Fintype ι]
    {G : ι → Type v} {H : ι → Type w}
    [∀ i, Group (G i)] [∀ i, Group (H i)]
    (e : ∀ i, G i ≃* H i)
    (χ : ∀ i, IrreducibleCharacter (H i))
    (g : ∀ i, G i) :
    ((finiteExternalTensor χ).comap
        (coordinatewiseMulEquiv e)).values g =
      ∏ i, (χ i).values (e i (g i)) := by
  simp

/-- Coordinatewise pullback on families of irreducible characters. -/
def coordinatewiseIrreducibleEquiv
    {ι : Type u} {G : ι → Type v} {H : ι → Type w}
    [∀ i, Group (G i)] [∀ i, Group (H i)]
    (e : ∀ i, G i ≃* H i) :
    (∀ i, IrreducibleCharacter (H i)) ≃
      ∀ i, IrreducibleCharacter (G i) :=
  Equiv.piCongrRight
    (fun i ↦ comapEquiv (e i))

@[simp]
theorem coordinatewiseIrreducibleEquiv_apply
    {ι : Type u} {G : ι → Type v} {H : ι → Type w}
    [∀ i, Group (G i)] [∀ i, Group (H i)]
    (e : ∀ i, G i ≃* H i)
    (χ : ∀ i, IrreducibleCharacter (H i)) (i : ι) :
    coordinatewiseIrreducibleEquiv e χ i =
      (χ i).comap (e i) :=
  rfl

/-- The finite-product character equivalence commutes with coordinatewise
group isomorphisms. -/
@[simp]
theorem finiteProductEquiv_comap_coordinatewise
    {ι : Type} [Fintype ι]
    {G H : ι → Type}
    [∀ i, Finite (G i)] [∀ i, Finite (H i)]
    [∀ i, Group (G i)] [∀ i, Group (H i)]
    (e : ∀ i, G i ≃* H i)
    (χ : ∀ i, IrreducibleCharacter (H i)) :
    (finiteProductEquiv H χ).comap
        (coordinatewiseMulEquiv e) =
      finiteProductEquiv G
        (coordinatewiseIrreducibleEquiv e χ) := by
  rw [finiteProductEquiv_apply,
    finiteProductEquiv_apply,
    finiteExternalTensor_comap_coordinatewise]
  rfl

/-- Commuting-square form of coordinatewise naturality. -/
theorem finiteProductEquiv_coordinatewise_comm
    {ι : Type} [Fintype ι]
    {G H : ι → Type}
    [∀ i, Finite (G i)] [∀ i, Finite (H i)]
    [∀ i, Group (G i)] [∀ i, Group (H i)]
    (e : ∀ i, G i ≃* H i) :
    (finiteProductEquiv H).trans
        (comapEquiv (coordinatewiseMulEquiv e)) =
      (coordinatewiseIrreducibleEquiv e).trans
        (finiteProductEquiv G) := by
  apply Equiv.ext
  intro χ
  exact finiteProductEquiv_comap_coordinatewise e χ

/-! ### Coordinatewise transport of `p'`-characters -/

/-- Coordinatewise pullback on families of `p'`-degree irreducible
characters. -/
def coordinatewisePPrimeEquiv
    {ι : Type u} {G : ι → Type v} {H : ι → Type w}
    [∀ i, Group (G i)] [∀ i, Group (H i)]
    (p : ℕ) (e : ∀ i, G i ≃* H i) :
    (∀ i, PPrimeIrreducibleCharacter (H i) p) ≃
      ∀ i, PPrimeIrreducibleCharacter (G i) p :=
  Equiv.piCongrRight
    (fun i ↦ pPrimeComapEquiv p (e i))

@[simp]
theorem coordinatewisePPrimeEquiv_apply
    {ι : Type u} {G : ι → Type v} {H : ι → Type w}
    [∀ i, Group (G i)] [∀ i, Group (H i)]
    (p : ℕ) (e : ∀ i, G i ≃* H i)
    (χ : ∀ i, PPrimeIrreducibleCharacter (H i) p)
    (i : ι) :
    coordinatewisePPrimeEquiv p e χ i =
      pPrimeComapEquiv p (e i) (χ i) :=
  rfl

/-- Coordinatewise pullback commutes with finite external tensor product
on `p'`-characters. -/
@[simp]
theorem finiteExternalTensorPPrime_comap_coordinatewise
    {ι : Type u} [Fintype ι]
    {G : ι → Type v} {H : ι → Type w}
    [∀ i, Group (G i)] [∀ i, Group (H i)]
    (p : ℕ) [Fact p.Prime]
    (e : ∀ i, G i ≃* H i)
    (χ : ∀ i, PPrimeIrreducibleCharacter (H i) p) :
    pPrimeComapEquiv p (coordinatewiseMulEquiv e)
        (finiteExternalTensorPPrime p χ) =
      finiteExternalTensorPPrime p
        (coordinatewisePPrimeEquiv p e χ) := by
  apply Subtype.ext
  exact finiteExternalTensor_comap_coordinatewise
    e (fun i ↦ (χ i).1)

/-- The finite-product `p'`-character equivalence commutes with
coordinatewise group isomorphisms. -/
@[simp]
theorem finiteProductPPrimeEquiv_comap_coordinatewise
    {ι : Type} [Fintype ι]
    {G H : ι → Type}
    [∀ i, Finite (G i)] [∀ i, Finite (H i)]
    [∀ i, Group (G i)] [∀ i, Group (H i)]
    (p : ℕ) [Fact p.Prime]
    (e : ∀ i, G i ≃* H i)
    (χ : ∀ i, PPrimeIrreducibleCharacter (H i) p) :
    pPrimeComapEquiv p (coordinatewiseMulEquiv e)
        (finiteProductPPrimeEquiv H p χ) =
      finiteProductPPrimeEquiv G p
        (coordinatewisePPrimeEquiv p e χ) := by
  rw [finiteProductPPrimeEquiv_apply,
    finiteProductPPrimeEquiv_apply,
    finiteExternalTensorPPrime_comap_coordinatewise]

/-- Commuting-square form of coordinatewise naturality for
`p'`-characters. -/
theorem finiteProductPPrimeEquiv_coordinatewise_comm
    {ι : Type} [Fintype ι]
    {G H : ι → Type}
    [∀ i, Finite (G i)] [∀ i, Finite (H i)]
    [∀ i, Group (G i)] [∀ i, Group (H i)]
    (p : ℕ) [Fact p.Prime]
    (e : ∀ i, G i ≃* H i) :
    (finiteProductPPrimeEquiv H p).trans
        (pPrimeComapEquiv p
          (coordinatewiseMulEquiv e)) =
      (coordinatewisePPrimeEquiv p e).trans
        (finiteProductPPrimeEquiv G p) := by
  apply Equiv.ext
  intro χ
  exact
    finiteProductPPrimeEquiv_comap_coordinatewise
      p e χ

/-! ### Reindexing finite products -/

@[simp]
theorem piCongrLeftMulEquiv_apply_apply
    {α β : Type u} (G : β → Type v)
    [∀ b, Group (G b)] (e : α ≃ β)
    (g : ∀ a, G (e a)) (a : α) :
    piCongrLeftMulEquiv G e g (e a) = g a :=
  Equiv.piCongrLeft_apply_apply
    (fun b ↦ G b) e g a

@[simp]
theorem piCongrLeftMulEquiv_symm_apply
    {α β : Type u} (G : β → Type v)
    [∀ b, Group (G b)] (e : α ≃ β)
    (g : ∀ b, G b) (a : α) :
    (piCongrLeftMulEquiv G e).symm g a =
      g (e a) :=
  Equiv.piCongrLeft_symm_apply
    (fun b ↦ G b) e g a

/-- Reindex a family of irreducible characters along an equivalence of
index types. -/
def reindexIrreducibleEquiv
    {α β : Type u} (G : β → Type v)
    [∀ b, Group (G b)] (e : α ≃ β) :
    (∀ b, IrreducibleCharacter (G b)) ≃
      ∀ a, IrreducibleCharacter (G (e a)) :=
  (Equiv.piCongrLeft
    (fun b ↦ IrreducibleCharacter (G b)) e).symm

@[simp]
theorem reindexIrreducibleEquiv_apply
    {α β : Type u} (G : β → Type v)
    [∀ b, Group (G b)] (e : α ≃ β)
    (χ : ∀ b, IrreducibleCharacter (G b)) (a : α) :
    reindexIrreducibleEquiv G e χ a = χ (e a) := by
  simp [reindexIrreducibleEquiv]

/-- Pullback along index reindexing commutes with finite external tensor
product. -/
@[simp]
theorem finiteExternalTensor_comap_reindex
    {α β : Type u} [Fintype α] [Fintype β]
    (G : β → Type v) [∀ b, Group (G b)]
    (e : α ≃ β)
    (χ : ∀ b, IrreducibleCharacter (G b)) :
    (finiteExternalTensor χ).comap
        (piCongrLeftMulEquiv G e) =
      finiteExternalTensor
        (reindexIrreducibleEquiv G e χ) := by
  apply IrreducibleCharacter.ext
  funext g
  rw [comap_values, finiteExternalTensor_values,
    finiteExternalTensor_values]
  simpa [piCongrLeftMulEquiv] using
    (e.prod_comp
      (fun b ↦
        (χ b).values
          (piCongrLeftMulEquiv G e g b))).symm

@[simp]
theorem finiteExternalTensor_comap_reindex_values
    {α β : Type u} [Fintype α] [Fintype β]
    (G : β → Type v) [∀ b, Group (G b)]
    (e : α ≃ β)
    (χ : ∀ b, IrreducibleCharacter (G b))
    (g : ∀ a, G (e a)) :
    ((finiteExternalTensor χ).comap
        (piCongrLeftMulEquiv G e)).values g =
      ∏ a, (χ (e a)).values (g a) := by
  rw [finiteExternalTensor_comap_reindex,
    finiteExternalTensor_values]
  simp

/-- The finite-product character equivalence commutes with an equivalence
of finite index types. -/
@[simp]
theorem finiteProductEquiv_comap_reindex
    {α β : Type} [Fintype α] [Fintype β]
    (G : β → Type) [∀ b, Finite (G b)]
    [∀ b, Group (G b)]
    (e : α ≃ β)
    (χ : ∀ b, IrreducibleCharacter (G b)) :
    (finiteProductEquiv G χ).comap
        (piCongrLeftMulEquiv G e) =
      finiteProductEquiv (fun a ↦ G (e a))
        (reindexIrreducibleEquiv G e χ) := by
  rw [finiteProductEquiv_apply,
    finiteProductEquiv_apply,
    finiteExternalTensor_comap_reindex]

/-- Commuting-square form of finite-index reindexing naturality. -/
theorem finiteProductEquiv_reindex_comm
    {α β : Type} [Fintype α] [Fintype β]
    (G : β → Type) [∀ b, Finite (G b)]
    [∀ b, Group (G b)]
    (e : α ≃ β) :
    (finiteProductEquiv G).trans
        (comapEquiv (piCongrLeftMulEquiv G e)) =
      (reindexIrreducibleEquiv G e).trans
        (finiteProductEquiv (fun a ↦ G (e a))) := by
  apply Equiv.ext
  intro χ
  exact finiteProductEquiv_comap_reindex G e χ

/-! ### Reindexing `p'`-characters -/

/-- Reindex a family of `p'`-degree irreducible characters along an
equivalence of index types. -/
def reindexPPrimeEquiv
    {α β : Type u} (G : β → Type v)
    [∀ b, Group (G b)] (p : ℕ) (e : α ≃ β) :
    (∀ b, PPrimeIrreducibleCharacter (G b) p) ≃
      ∀ a, PPrimeIrreducibleCharacter (G (e a)) p :=
  (Equiv.piCongrLeft
    (fun b ↦ PPrimeIrreducibleCharacter (G b) p) e).symm

@[simp]
theorem reindexPPrimeEquiv_apply
    {α β : Type u} (G : β → Type v)
    [∀ b, Group (G b)] (p : ℕ) (e : α ≃ β)
    (χ : ∀ b, PPrimeIrreducibleCharacter (G b) p)
    (a : α) :
    reindexPPrimeEquiv G p e χ a = χ (e a) := by
  simp [reindexPPrimeEquiv]

/-- Pullback along index reindexing commutes with finite external tensor
product on `p'`-characters. -/
@[simp]
theorem finiteExternalTensorPPrime_comap_reindex
    {α β : Type u} [Fintype α] [Fintype β]
    (G : β → Type v) [∀ b, Group (G b)]
    (p : ℕ) [Fact p.Prime] (e : α ≃ β)
    (χ : ∀ b, PPrimeIrreducibleCharacter (G b) p) :
    pPrimeComapEquiv p (piCongrLeftMulEquiv G e)
        (finiteExternalTensorPPrime p χ) =
      finiteExternalTensorPPrime p
        (reindexPPrimeEquiv G p e χ) := by
  apply Subtype.ext
  exact finiteExternalTensor_comap_reindex
    G e (fun b ↦ (χ b).1)

/-- The finite-product `p'`-character equivalence commutes with an
equivalence of finite index types. -/
@[simp]
theorem finiteProductPPrimeEquiv_comap_reindex
    {α β : Type} [Fintype α] [Fintype β]
    (G : β → Type) [∀ b, Finite (G b)]
    [∀ b, Group (G b)]
    (p : ℕ) [Fact p.Prime] (e : α ≃ β)
    (χ : ∀ b, PPrimeIrreducibleCharacter (G b) p) :
    pPrimeComapEquiv p (piCongrLeftMulEquiv G e)
        (finiteProductPPrimeEquiv G p χ) =
      finiteProductPPrimeEquiv (fun a ↦ G (e a)) p
        (reindexPPrimeEquiv G p e χ) := by
  rw [finiteProductPPrimeEquiv_apply,
    finiteProductPPrimeEquiv_apply,
    finiteExternalTensorPPrime_comap_reindex]

/-- Commuting-square form of finite-index reindexing naturality for
`p'`-characters. -/
theorem finiteProductPPrimeEquiv_reindex_comm
    {α β : Type} [Fintype α] [Fintype β]
    (G : β → Type) [∀ b, Finite (G b)]
    [∀ b, Group (G b)]
    (p : ℕ) [Fact p.Prime] (e : α ≃ β) :
    (finiteProductPPrimeEquiv G p).trans
        (pPrimeComapEquiv p
          (piCongrLeftMulEquiv G e)) =
      (reindexPPrimeEquiv G p e).trans
        (finiteProductPPrimeEquiv
          (fun a ↦ G (e a)) p) := by
  apply Equiv.ext
  intro χ
  exact finiteProductPPrimeEquiv_comap_reindex
    G p e χ

/-! ### Coordinatewise automorphisms -/

/-- The automorphism of a dependent product induced by automorphisms of
its coordinates. -/
def coordinatewiseMulAut
    {ι : Type u} {G : ι → Type v}
    [∀ i, Group (G i)] (a : ∀ i, MulAut (G i)) :
    MulAut (∀ i, G i) :=
  coordinatewiseMulEquiv a

@[simp]
theorem coordinatewiseMulAut_apply
    {ι : Type u} {G : ι → Type v}
    [∀ i, Group (G i)] (a : ∀ i, MulAut (G i))
    (g : ∀ i, G i) (i : ι) :
    coordinatewiseMulAut a g i = a i (g i) :=
  rfl

@[simp]
theorem coordinatewiseMulAut_symm_apply
    {ι : Type u} {G : ι → Type v}
    [∀ i, Group (G i)] (a : ∀ i, MulAut (G i))
    (g : ∀ i, G i) (i : ι) :
    (coordinatewiseMulAut a).symm g i =
      (a i).symm (g i) :=
  rfl

/-- Finite external tensor product is equivariant for coordinatewise
automorphisms. -/
@[simp]
theorem coordinatewiseMulAut_smul_finiteExternalTensor
    {ι : Type u} [Fintype ι]
    {G : ι → Type v} [∀ i, Group (G i)]
    (a : ∀ i, MulAut (G i))
    (χ : ∀ i, IrreducibleCharacter (G i)) :
    coordinatewiseMulAut a • finiteExternalTensor χ =
      finiteExternalTensor (fun i ↦ a i • χ i) := by
  change
    (finiteExternalTensor χ).comap
        (coordinatewiseMulAut a).symm =
      finiteExternalTensor
        (fun i ↦ (χ i).comap (a i).symm)
  simpa [coordinatewiseMulAut,
    coordinatewiseMulEquiv] using
    (finiteExternalTensor_comap_coordinatewise
      (fun i ↦ (a i).symm) χ)

@[simp]
theorem coordinatewiseMulAut_smul_finiteExternalTensor_values
    {ι : Type u} [Fintype ι]
    {G : ι → Type v} [∀ i, Group (G i)]
    (a : ∀ i, MulAut (G i))
    (χ : ∀ i, IrreducibleCharacter (G i))
    (g : ∀ i, G i) :
    (coordinatewiseMulAut a •
        finiteExternalTensor χ).values g =
      ∏ i, (χ i).values ((a i).symm (g i)) := by
  rw [coordinatewiseMulAut_smul_finiteExternalTensor,
    finiteExternalTensor_values]
  simp

/-- The finite-product character equivalence is equivariant for
coordinatewise automorphisms. -/
@[simp]
theorem coordinatewiseMulAut_smul_finiteProductEquiv
    {ι : Type} [Fintype ι]
    {G : ι → Type} [∀ i, Finite (G i)]
    [∀ i, Group (G i)]
    (a : ∀ i, MulAut (G i))
    (χ : ∀ i, IrreducibleCharacter (G i)) :
    coordinatewiseMulAut a • finiteProductEquiv G χ =
      finiteProductEquiv G (fun i ↦ a i • χ i) := by
  rw [finiteProductEquiv_apply,
    finiteProductEquiv_apply,
    coordinatewiseMulAut_smul_finiteExternalTensor]

/-- Finite external tensor product on `p'`-characters is equivariant for
coordinatewise automorphisms. -/
@[simp]
theorem coordinatewiseMulAut_smul_finiteExternalTensorPPrime
    {ι : Type u} [Fintype ι]
    {G : ι → Type v} [∀ i, Group (G i)]
    (p : ℕ) [Fact p.Prime]
    (a : ∀ i, MulAut (G i))
    (χ : ∀ i, PPrimeIrreducibleCharacter (G i) p) :
    coordinatewiseMulAut a •
        finiteExternalTensorPPrime p χ =
      finiteExternalTensorPPrime p
        (fun i ↦ a i • χ i) := by
  apply Subtype.ext
  exact coordinatewiseMulAut_smul_finiteExternalTensor
    a (fun i ↦ (χ i).1)

/-- The finite-product `p'`-character equivalence is equivariant for
coordinatewise automorphisms. -/
@[simp]
theorem coordinatewiseMulAut_smul_finiteProductPPrimeEquiv
    {ι : Type} [Fintype ι]
    {G : ι → Type} [∀ i, Finite (G i)]
    [∀ i, Group (G i)]
    (p : ℕ) [Fact p.Prime]
    (a : ∀ i, MulAut (G i))
    (χ : ∀ i, PPrimeIrreducibleCharacter (G i) p) :
    coordinatewiseMulAut a •
        finiteProductPPrimeEquiv G p χ =
      finiteProductPPrimeEquiv G p
        (fun i ↦ a i • χ i) := by
  rw [finiteProductPPrimeEquiv_apply,
    finiteProductPPrimeEquiv_apply,
    coordinatewiseMulAut_smul_finiteExternalTensorPPrime]

/-! ### Permutations of equal factors -/

/-- An index permutation acts on a power of a group by permuting
coordinates.  Thus
`indexPermutationMulAut G σ g i = g (σ⁻¹ i)`. -/
def indexPermutationMulAut
    {ι : Type u} (G : Type v) [Group G]
    (σ : Equiv.Perm ι) :
    MulAut (ι → G) :=
  piCongrLeftMulEquiv (fun _ : ι ↦ G) σ

@[simp]
theorem indexPermutationMulAut_apply
    {ι : Type u} (G : Type v) [Group G]
    (σ : Equiv.Perm ι) (g : ι → G) (i : ι) :
    indexPermutationMulAut G σ g i =
      g (σ.symm i) := by
  change
    (Equiv.piCongrLeft (fun _ : ι ↦ G) σ) g i =
      g (σ.symm i)
  simp [Equiv.piCongrLeft_apply]

@[simp]
theorem indexPermutationMulAut_symm_apply
    {ι : Type u} (G : Type v) [Group G]
    (σ : Equiv.Perm ι) (g : ι → G) (i : ι) :
    (indexPermutationMulAut G σ).symm g i =
      g (σ i) := by
  change
    (Equiv.piCongrLeft
      (fun _ : ι ↦ G) σ).symm g i =
      g (σ i)
  simp

@[simp]
theorem indexPermutationMulAut_symm
    {ι : Type u} (G : Type v) [Group G]
    (σ : Equiv.Perm ι) :
    (indexPermutationMulAut G σ).symm =
      indexPermutationMulAut G σ.symm := by
  apply MulEquiv.ext
  intro g
  funext i
  simp

@[simp]
theorem indexPermutationMulAut_refl
    {ι : Type u} (G : Type v) [Group G] :
    indexPermutationMulAut G (Equiv.refl ι) =
      MulEquiv.refl (ι → G) := by
  apply MulEquiv.ext
  intro g
  funext i
  simp

/-- The permutation action on a family of irreducible characters, with
the inverse convention dictated by the left automorphism action. -/
def permutationIrreducibleEquiv
    {ι : Type u} (G : Type v) [Group G]
    (σ : Equiv.Perm ι) :
    (ι → IrreducibleCharacter G) ≃
      (ι → IrreducibleCharacter G) :=
  reindexIrreducibleEquiv
    (fun _ : ι ↦ G) σ.symm

@[simp]
theorem permutationIrreducibleEquiv_apply
    {ι : Type u} (G : Type v) [Group G]
    (σ : Equiv.Perm ι)
    (χ : ι → IrreducibleCharacter G) (i : ι) :
    permutationIrreducibleEquiv G σ χ i =
      χ (σ.symm i) := by
  simp [permutationIrreducibleEquiv]

/-- Finite external tensor product is equivariant for permutations of
equal factors. -/
@[simp]
theorem indexPermutationMulAut_smul_finiteExternalTensor
    {ι : Type u} [Fintype ι]
    (G : Type v) [Group G]
    (σ : Equiv.Perm ι)
    (χ : ι → IrreducibleCharacter G) :
    indexPermutationMulAut G σ •
        finiteExternalTensor χ =
      finiteExternalTensor
        (permutationIrreducibleEquiv G σ χ) := by
  change
    (finiteExternalTensor χ).comap
        (indexPermutationMulAut G σ).symm =
      finiteExternalTensor
        (permutationIrreducibleEquiv G σ χ)
  rw [indexPermutationMulAut_symm]
  exact finiteExternalTensor_comap_reindex
    (fun _ : ι ↦ G) σ.symm χ

@[simp]
theorem indexPermutationMulAut_smul_finiteExternalTensor_values
    {ι : Type u} [Fintype ι]
    (G : Type v) [Group G]
    (σ : Equiv.Perm ι)
    (χ : ι → IrreducibleCharacter G)
    (g : ι → G) :
    (indexPermutationMulAut G σ •
        finiteExternalTensor χ).values g =
      ∏ i, (χ (σ.symm i)).values (g i) := by
  rw [indexPermutationMulAut_smul_finiteExternalTensor,
    finiteExternalTensor_values]
  simp

/-- The finite-product character equivalence is equivariant for
permutations of equal finite factors. -/
@[simp]
theorem indexPermutationMulAut_smul_finiteProductEquiv
    {ι : Type} [Fintype ι]
    (G : Type) [Finite G] [Group G]
    (σ : Equiv.Perm ι)
    (χ : ι → IrreducibleCharacter G) :
    indexPermutationMulAut G σ •
        finiteProductEquiv (fun _ : ι ↦ G) χ =
      finiteProductEquiv (fun _ : ι ↦ G)
        (permutationIrreducibleEquiv G σ χ) := by
  rw [finiteProductEquiv_apply,
    finiteProductEquiv_apply,
    indexPermutationMulAut_smul_finiteExternalTensor]

/-- Commuting-square form of permutation equivariance. -/
theorem finiteProductEquiv_permutation_comm
    {ι : Type} [Fintype ι]
    (G : Type) [Finite G] [Group G]
    (σ : Equiv.Perm ι) :
    (finiteProductEquiv (fun _ : ι ↦ G)).trans
        (comapEquiv
          (indexPermutationMulAut G σ).symm) =
      (permutationIrreducibleEquiv G σ).trans
        (finiteProductEquiv (fun _ : ι ↦ G)) := by
  apply Equiv.ext
  intro χ
  exact
    indexPermutationMulAut_smul_finiteProductEquiv
      G σ χ

/-! ### Permutations of equal factors for `p'`-characters -/

/-- The permutation action on a family of `p'`-degree irreducible
characters. -/
def permutationPPrimeEquiv
    {ι : Type u} (G : Type v) [Group G]
    (p : ℕ) (σ : Equiv.Perm ι) :
    (ι → PPrimeIrreducibleCharacter G p) ≃
      (ι → PPrimeIrreducibleCharacter G p) :=
  reindexPPrimeEquiv
    (fun _ : ι ↦ G) p σ.symm

@[simp]
theorem permutationPPrimeEquiv_apply
    {ι : Type u} (G : Type v) [Group G]
    (p : ℕ) (σ : Equiv.Perm ι)
    (χ : ι → PPrimeIrreducibleCharacter G p)
    (i : ι) :
    permutationPPrimeEquiv G p σ χ i =
      χ (σ.symm i) := by
  simp [permutationPPrimeEquiv]

/-- Finite external tensor product on `p'`-characters is equivariant for
permutations of equal factors. -/
@[simp]
theorem indexPermutationMulAut_smul_finiteExternalTensorPPrime
    {ι : Type u} [Fintype ι]
    (G : Type v) [Group G]
    (p : ℕ) [Fact p.Prime]
    (σ : Equiv.Perm ι)
    (χ : ι → PPrimeIrreducibleCharacter G p) :
    indexPermutationMulAut G σ •
        finiteExternalTensorPPrime p χ =
      finiteExternalTensorPPrime p
        (permutationPPrimeEquiv G p σ χ) := by
  apply Subtype.ext
  exact indexPermutationMulAut_smul_finiteExternalTensor
    G σ (fun i ↦ (χ i).1)

/-- The finite-product `p'`-character equivalence is equivariant for
permutations of equal finite factors. -/
@[simp]
theorem indexPermutationMulAut_smul_finiteProductPPrimeEquiv
    {ι : Type} [Fintype ι]
    (G : Type) [Finite G] [Group G]
    (p : ℕ) [Fact p.Prime]
    (σ : Equiv.Perm ι)
    (χ : ι → PPrimeIrreducibleCharacter G p) :
    indexPermutationMulAut G σ •
        finiteProductPPrimeEquiv
          (fun _ : ι ↦ G) p χ =
      finiteProductPPrimeEquiv
        (fun _ : ι ↦ G) p
        (permutationPPrimeEquiv G p σ χ) := by
  rw [finiteProductPPrimeEquiv_apply,
    finiteProductPPrimeEquiv_apply,
    indexPermutationMulAut_smul_finiteExternalTensorPPrime]

/-- Commuting-square form of permutation equivariance for
`p'`-characters. -/
theorem finiteProductPPrimeEquiv_permutation_comm
    {ι : Type} [Fintype ι]
    (G : Type) [Finite G] [Group G]
    (p : ℕ) [Fact p.Prime]
    (σ : Equiv.Perm ι) :
    (finiteProductPPrimeEquiv
        (fun _ : ι ↦ G) p).trans
        (pPrimeComapEquiv p
          (indexPermutationMulAut G σ).symm) =
      (permutationPPrimeEquiv G p σ).trans
        (finiteProductPPrimeEquiv
          (fun _ : ι ↦ G) p) := by
  apply Equiv.ext
  intro χ
  exact
    indexPermutationMulAut_smul_finiteProductPPrimeEquiv
      G p σ χ

end IrreducibleCharacter
end McKayConjecture
