/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.LinearAlgebra.Basis.Basic
import McKayConjecture.Character.ClassFunctionCompleteness

/-!
# Irreducible characters as a basis of class functions

Completeness and row orthogonality give the usual Fourier expansion of a
class function.  In particular, irreducible complex characters form a basis
and their number equals the number of conjugacy classes.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace ClassFunction

variable {G : Type} [Group G] [Finite G]

noncomputable local instance irreducibleCharacterBasisFintype :
    Fintype (IrreducibleCharacter G) :=
  Fintype.ofFinite _

/-- Fourier expansion in the irreducible-character basis. -/
theorem irreducibleCharacter_fourierExpansion
    (f : ClassFunction G) :
    f =
      ∑ χ : IrreducibleCharacter G,
        normalizedPairing f χ.toClassFunction •
          χ.toClassFunction := by
  classical
  apply sub_eq_zero.mp
  apply eq_zero_of_normalizedPairing_irreducible_eq_zero
  intro ψ
  rw [map_sub, LinearMap.sub_apply]
  simp only [map_sum, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply]
  rw [Finset.sum_eq_single ψ]
  · simp
  · intro χ _ hχ
    rw [normalizedPairing_irreducible_eq_zero_of_ne
      χ ψ hχ]
    simp
  · simp

/-- The class functions afforded by irreducible characters span all class
functions. -/
theorem span_irreducibleCharacter_toClassFunction_eq_top :
    Submodule.span ℂ
        (Set.range
          (IrreducibleCharacter.toClassFunction :
            IrreducibleCharacter G → ClassFunction G)) =
      ⊤ := by
  classical
  apply top_unique
  intro f _hf
  rw [irreducibleCharacter_fourierExpansion f]
  apply Submodule.sum_mem
  intro χ _hχ
  apply Submodule.smul_mem
  exact
    Submodule.subset_span
      (Set.mem_range_self χ)

/-- The canonical basis of class functions indexed by irreducible complex
characters. -/
def irreducibleCharacterBasis :
    Module.Basis (IrreducibleCharacter G) ℂ (ClassFunction G) :=
  Module.Basis.mk
    IrreducibleCharacter.linearIndependent_toClassFunction
    (span_irreducibleCharacter_toClassFunction_eq_top
      (G := G)).ge

@[simp]
theorem irreducibleCharacterBasis_apply
    (χ : IrreducibleCharacter G) :
    irreducibleCharacterBasis (G := G) χ =
      χ.toClassFunction :=
  Module.Basis.mk_apply _ _ _

/-- A finite group has as many irreducible complex characters as
conjugacy classes. -/
theorem natCard_irreducibleCharacter_eq_conjClasses :
    Nat.card (IrreducibleCharacter G) =
      Nat.card (ConjClasses G) := by
  calc
    Nat.card (IrreducibleCharacter G) =
        Fintype.card (IrreducibleCharacter G) :=
      Nat.card_eq_fintype_card
    _ = Module.finrank ℂ (ClassFunction G) :=
      (Module.finrank_eq_card_basis
        (irreducibleCharacterBasis (G := G))).symm
    _ = Nat.card (ConjClasses G) :=
      finrank_eq_natCard_conjClasses

end ClassFunction
end McKayConjecture
