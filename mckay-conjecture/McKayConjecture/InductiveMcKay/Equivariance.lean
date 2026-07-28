/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.GroupAction.Hom
import McKayConjecture.Character.Automorphism
import McKayConjecture.Proof.Correspondence

/-!
# Equivariant `p'`-character correspondences

The inductive McKay condition asks for more than a bijection of character
sets: the bijection must commute with an appropriate automorphism action.
This file packages that elementary equivariance datum independently of the
deeper character-triple compatibility conditions.
-/

noncomputable section

universe u v

namespace McKayConjecture.InductiveMcKay

/-- A bijection between `p'`-degree irreducible characters which commutes with
the action of a common group `A`. -/
structure EquivariantPPrimeCorrespondence
    (A : Type v) [Group A] (p : ℕ) (G H : Type u)
    [Group G] [Group H]
    [MulAction A (PPrimeIrreducibleCharacter G p)]
    [MulAction A (PPrimeIrreducibleCharacter H p)] where
  /-- The underlying bijection of `p'`-degree characters. -/
  toCorrespondence : PPrimeCorrespondence p G H
  /-- The correspondence commutes with the `A`-actions. -/
  map_smul' : ∀ (a : A) (χ : PPrimeIrreducibleCharacter G p),
    toCorrespondence (a • χ) = a • toCorrespondence χ

namespace EquivariantPPrimeCorrespondence

variable {A : Type v} [Group A]
variable {G H K : Type u} [Group G] [Group H] [Group K]
variable {p : ℕ}
variable [MulAction A (PPrimeIrreducibleCharacter G p)]
variable [MulAction A (PPrimeIrreducibleCharacter H p)]
variable [MulAction A (PPrimeIrreducibleCharacter K p)]

instance : CoeFun (EquivariantPPrimeCorrespondence A p G H)
    (fun _ ↦ PPrimeIrreducibleCharacter G p →
      PPrimeIrreducibleCharacter H p) where
  coe f := f.toCorrespondence

@[simp]
theorem map_smul (f : EquivariantPPrimeCorrespondence A p G H)
    (a : A) (χ : PPrimeIrreducibleCharacter G p) :
    f (a • χ) = a • f χ :=
  f.map_smul' a χ

/-- Regard an equivariant character correspondence as a bundled equivariant
function. -/
def toMulActionHom (f : EquivariantPPrimeCorrespondence A p G H) :
    PPrimeIrreducibleCharacter G p →[A]
      PPrimeIrreducibleCharacter H p where
  toFun := f
  map_smul' := f.map_smul'

@[simp]
theorem toMulActionHom_apply
    (f : EquivariantPPrimeCorrespondence A p G H)
    (χ : PPrimeIrreducibleCharacter G p) :
    f.toMulActionHom χ = f χ :=
  rfl

/-- Two equivariant correspondences are equal when their underlying functions
are equal. -/
@[ext]
theorem ext {f g : EquivariantPPrimeCorrespondence A p G H}
    (h : ∀ χ, f χ = g χ) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have hfg : f = g := Equiv.ext h
      subst g
      rfl

/-- The identity equivariant `p'`-character correspondence. -/
def refl (A : Type v) [Group A] (p : ℕ) (G : Type u) [Group G]
    [MulAction A (PPrimeIrreducibleCharacter G p)] :
    EquivariantPPrimeCorrespondence A p G G where
  toCorrespondence := PPrimeCorrespondence.refl p G
  map_smul' _ _ := rfl

@[simp]
theorem refl_apply (χ : PPrimeIrreducibleCharacter G p) :
    refl A p G χ = χ :=
  rfl

/-- Reverse an equivariant `p'`-character correspondence. -/
def symm (f : EquivariantPPrimeCorrespondence A p G H) :
    EquivariantPPrimeCorrespondence A p H G where
  toCorrespondence := f.toCorrespondence.symm
  map_smul' a ψ := by
    apply f.toCorrespondence.injective
    calc
      f.toCorrespondence (f.toCorrespondence.symm (a • ψ)) = a • ψ :=
        f.toCorrespondence.apply_symm_apply _
      _ = a • f.toCorrespondence (f.toCorrespondence.symm ψ) :=
        congrArg (a • ·) (f.toCorrespondence.apply_symm_apply ψ).symm
      _ = f.toCorrespondence (a • f.toCorrespondence.symm ψ) :=
        (f.map_smul' _ _).symm

@[simp]
theorem symm_apply_apply (f : EquivariantPPrimeCorrespondence A p G H)
    (χ : PPrimeIrreducibleCharacter G p) :
    f.symm (f χ) = χ :=
  f.toCorrespondence.symm_apply_apply χ

@[simp]
theorem apply_symm_apply (f : EquivariantPPrimeCorrespondence A p G H)
    (ψ : PPrimeIrreducibleCharacter H p) :
    f (f.symm ψ) = ψ :=
  f.toCorrespondence.apply_symm_apply ψ

/-- Compose two equivariant `p'`-character correspondences. -/
def trans (f : EquivariantPPrimeCorrespondence A p G H)
    (g : EquivariantPPrimeCorrespondence A p H K) :
    EquivariantPPrimeCorrespondence A p G K where
  toCorrespondence := f.toCorrespondence.trans g.toCorrespondence
  map_smul' a χ := by
    change g.toCorrespondence (f.toCorrespondence (a • χ)) =
      a • g.toCorrespondence (f.toCorrespondence χ)
    rw [f.map_smul', g.map_smul']

@[simp]
theorem trans_apply (f : EquivariantPPrimeCorrespondence A p G H)
    (g : EquivariantPPrimeCorrespondence A p H K)
    (χ : PPrimeIrreducibleCharacter G p) :
    f.trans g χ = g (f χ) :=
  rfl

/-- Restrict equivariance from `A` to a subgroup of `A`.  The underlying
character correspondence is unchanged. -/
def restrict (f : EquivariantPPrimeCorrespondence A p G H)
    (B : Subgroup A) :
    EquivariantPPrimeCorrespondence B p G H where
  toCorrespondence := f.toCorrespondence
  map_smul' b χ := f.map_smul' b.1 χ

@[simp]
theorem restrict_apply (f : EquivariantPPrimeCorrespondence A p G H)
    (B : Subgroup A) (χ : PPrimeIrreducibleCharacter G p) :
    f.restrict B χ = f χ :=
  rfl

/-- An equivariant correspondence gives the underlying cardinal equality. -/
theorem cardinal_eq (f : EquivariantPPrimeCorrespondence A p G H) :
    Cardinal.mk (PPrimeIrreducibleCharacter G p) =
      Cardinal.mk (PPrimeIrreducibleCharacter H p) :=
  PPrimeCorrespondence.cardinal_eq f.toCorrespondence

end EquivariantPPrimeCorrespondence

/-- An equivariant strengthening of a McKay correspondence for a fixed Sylow
subgroup. -/
abbrev EquivariantMcKayCorrespondence
    (A : Type v) [Group A] (G : Type u) [Group G] (p : ℕ)
    (P : Sylow p G)
    [MulAction A (PPrimeIrreducibleCharacter G p)]
    [MulAction A (PPrimeIrreducibleCharacter (SylowNormalizer P) p)] :=
  EquivariantPPrimeCorrespondence A p G (SylowNormalizer P)

namespace EquivariantMcKayCorrespondence

variable {A : Type v} [Group A]
variable {G : Type u} [Finite G] [Group G]
variable {p : ℕ} [Fact p.Prime] {P : Sylow p G}
variable [MulAction A (PPrimeIrreducibleCharacter G p)]
variable [MulAction A (PPrimeIrreducibleCharacter (SylowNormalizer P) p)]

/-- Forgetting equivariance from an equivariant McKay correspondence proves
the McKay cardinality statement. -/
theorem statement (f : EquivariantMcKayCorrespondence A G p P) :
    McKayConjecture.Statement G p P :=
  McKayConjecture.Statement.of_correspondence f.toCorrespondence

end EquivariantMcKayCorrespondence

end McKayConjecture.InductiveMcKay
