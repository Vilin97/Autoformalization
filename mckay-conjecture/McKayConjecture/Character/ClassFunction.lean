/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Group.ConjFinite
import McKayConjecture.Character.Finiteness

/-!
# Complex class functions

This file bundles the complex-valued functions on a group which are constant
on conjugacy classes.  It identifies their vector space with the function
space on `ConjClasses G`, then places ordinary irreducible characters in that
smaller space.

For finite groups, Schur orthogonality therefore bounds the number of
irreducible characters by the number of conjugacy classes.
-/

noncomputable section

universe u

namespace McKayConjecture

variable (G : Type u) [Group G]

/-- The complex vector space of functions on `G` which are invariant under
conjugation. -/
def ClassFunction : Submodule ℂ (G → ℂ) where
  carrier := {f | ∀ g h : G, f (h * g * h⁻¹) = f g}
  zero_mem' := by
    intro g h
    rfl
  add_mem' := fun {f k} hf hk g h ↦ by
    change f (h * g * h⁻¹) + k (h * g * h⁻¹) = f g + k g
    rw [hf, hk]
  smul_mem' := fun c {f} hf g h ↦ by
    change c * f (h * g * h⁻¹) = c * f g
    rw [hf]

namespace ClassFunction

variable {G}

instance : CoeFun (ClassFunction G) (fun _ ↦ G → ℂ) :=
  ⟨fun f ↦ f.1⟩

@[ext]
theorem ext {f k : ClassFunction G} (h : ∀ g : G, f g = k g) : f = k :=
  Subtype.ext (funext h)

/-- A class function is invariant under conjugation. -/
@[simp]
theorem conj_apply (f : ClassFunction G) (g h : G) :
    f (h * g * h⁻¹) = f g :=
  f.property g h

/-- Forget that a class function is conjugation-invariant. -/
def coeLinearMap : ClassFunction G →ₗ[ℂ] (G → ℂ) :=
  (ClassFunction G).subtype

@[simp]
theorem coeLinearMap_apply (f : ClassFunction G) :
    coeLinearMap f = (f : G → ℂ) :=
  rfl

theorem coeLinearMap_injective : Function.Injective (coeLinearMap (G := G)) :=
  (ClassFunction G).subtype_injective

/-- Regard a class function as a function on conjugacy classes. -/
def toConjClassesLinearMap :
    ClassFunction G →ₗ[ℂ] (ConjClasses G → ℂ) where
  toFun f :=
    Quotient.lift (fun g : G ↦ f g) fun a b hab ↦ by
      obtain ⟨h, hh⟩ := isConj_iff.mp hab
      rw [← hh]
      exact (conj_apply f a h).symm
  map_add' f k := by
    funext c
    refine Quotient.inductionOn c ?_
    intro g
    rfl
  map_smul' c f := by
    funext q
    refine Quotient.inductionOn q ?_
    intro g
    rfl

@[simp]
theorem toConjClassesLinearMap_mk (f : ClassFunction G) (g : G) :
    toConjClassesLinearMap f (ConjClasses.mk g) = f g :=
  rfl

/-- Pull a complex-valued function on conjugacy classes back to `G`. -/
def ofConjClassesLinearMap :
    (ConjClasses G → ℂ) →ₗ[ℂ] ClassFunction G where
  toFun f :=
    ⟨fun g ↦ f (ConjClasses.mk g), by
      intro g h
      apply congrArg f
      rw [ConjClasses.mk_eq_mk_iff_isConj]
      exact IsConj.symm (isConj_iff.mpr ⟨h, rfl⟩)⟩
  map_add' f k := by
    ext g
    rfl
  map_smul' c f := by
    ext g
    rfl

@[simp]
theorem ofConjClassesLinearMap_apply (f : ConjClasses G → ℂ) (g : G) :
    ofConjClassesLinearMap f g = f (ConjClasses.mk g) :=
  rfl

/-- Complex class functions on `G` are linearly equivalent to arbitrary
complex-valued functions on its conjugacy classes. -/
def linearEquivConjClasses :
    ClassFunction G ≃ₗ[ℂ] (ConjClasses G → ℂ) where
  __ := toConjClassesLinearMap
  invFun := ofConjClassesLinearMap
  left_inv f := by
    ext g
    exact toConjClassesLinearMap_mk f g
  right_inv f := by
    funext c
    refine Quotient.inductionOn c ?_
    intro g
    change
      toConjClassesLinearMap (ofConjClassesLinearMap f) (ConjClasses.mk g) =
        f (ConjClasses.mk g)
    rw [toConjClassesLinearMap_mk, ofConjClassesLinearMap_apply]

@[simp]
theorem linearEquivConjClasses_apply_mk (f : ClassFunction G) (g : G) :
    linearEquivConjClasses f (ConjClasses.mk g) = f g :=
  rfl

@[simp]
theorem linearEquivConjClasses_symm_apply (f : ConjClasses G → ℂ) (g : G) :
    (linearEquivConjClasses (G := G)).symm f g = f (ConjClasses.mk g) :=
  rfl

/-- The class-function space of a finite group is finite-dimensional. -/
instance instFiniteDimensional [Finite G] :
    FiniteDimensional ℂ (ClassFunction G) := by
  letI : Fintype (ConjClasses G) := Fintype.ofFinite _
  exact (linearEquivConjClasses (G := G)).symm.finiteDimensional

/-- The dimension of the class-function space is the number of conjugacy
classes. -/
theorem finrank_eq_natCard_conjClasses [Finite G] :
    Module.finrank ℂ (ClassFunction G) = Nat.card (ConjClasses G) := by
  letI : Fintype (ConjClasses G) := Fintype.ofFinite _
  calc
    Module.finrank ℂ (ClassFunction G) =
        Module.finrank ℂ (ConjClasses G → ℂ) :=
      LinearEquiv.finrank_eq (linearEquivConjClasses (G := G))
    _ = Fintype.card (ConjClasses G) :=
      Module.finrank_fintype_fun_eq_card ℂ
    _ = Nat.card (ConjClasses G) :=
      Nat.card_eq_fintype_card.symm

end ClassFunction

namespace IrreducibleCharacter

variable {G}

/-- An ordinary irreducible character, regarded as a complex class function. -/
def toClassFunction (χ : IrreducibleCharacter G) : ClassFunction G :=
  ⟨χ.values, fun g h ↦ by
    simpa only [χ.realization_character] using
      FDRep.char_conj χ.realization g h⟩

@[simp]
theorem toClassFunction_apply (χ : IrreducibleCharacter G) (g : G) :
    χ.toClassFunction g = χ.values g :=
  rfl

/-- Passing from an irreducible character to its class function loses no
information. -/
theorem toClassFunction_injective :
    Function.Injective
      (toClassFunction : IrreducibleCharacter G → ClassFunction G) := by
  intro χ ψ h
  apply IrreducibleCharacter.ext
  exact congrArg Subtype.val h

/-- The class functions afforded by the irreducible characters of a finite
group are linearly independent. -/
theorem linearIndependent_toClassFunction [Finite G] :
    LinearIndependent ℂ
      (toClassFunction : IrreducibleCharacter G → ClassFunction G) := by
  apply LinearIndependent.of_comp (ClassFunction.coeLinearMap (G := G))
  have h :
      (ClassFunction.coeLinearMap (G := G) ∘
          (toClassFunction : IrreducibleCharacter G → ClassFunction G)) =
        (fun χ : IrreducibleCharacter G ↦ χ.values) := by
    funext χ
    rfl
  rw [h]
  exact linearIndependent_values (G := G)

/-- The number of irreducible complex characters of a finite group is at most
the number of its conjugacy classes. -/
theorem natCard_le_conjClasses [Finite G] :
    Nat.card (IrreducibleCharacter G) ≤ Nat.card (ConjClasses G) := by
  letI : Fintype (IrreducibleCharacter G) := Fintype.ofFinite _
  calc
    Nat.card (IrreducibleCharacter G) =
        Fintype.card (IrreducibleCharacter G) :=
      Nat.card_eq_fintype_card
    _ ≤ Module.finrank ℂ (ClassFunction G) :=
      (linearIndependent_toClassFunction (G := G)).fintype_card_le_finrank
    _ = Nat.card (ConjClasses G) :=
      ClassFunction.finrank_eq_natCard_conjClasses

end IrreducibleCharacter

/-- The number of irreducible characters of `p'`-degree is at most the number
of conjugacy classes. -/
theorem natCard_pPrimeIrreducibleCharacter_le_conjClasses [Finite G] (p : ℕ) :
    Nat.card (PPrimeIrreducibleCharacter G p) ≤ Nat.card (ConjClasses G) :=
  (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
    IrreducibleCharacter.natCard_le_conjClasses

end McKayConjecture
