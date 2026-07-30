/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GallagherInducedNormal
import McKayConjecture.Character.GoodElementCommutatorFiber

/-!
# Gallagher's commutator identity reindexed by quotient centralizers

The filtered commutator sum for an invariant normal-subgroup character
can be reindexed, one left variable at a time, by the inverse image of
the corresponding quotient centralizer.  Combining that reindexing
with the division-free filtered Gallagher identity gives the exact
centralizer-sum formula in this file.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace CliffordCorrespondence

variable {A : Type} [Group A] [Finite A]

noncomputable local instance (priority := 100)
    gallagherCentralizerCommutatorGroupFintype
    (G : Type) [Group G] [Finite G] : Fintype G :=
  Fintype.ofFinite G

attribute [local instance]
  goodElementCommutatorFiberPropDecidable

/-- Division-free Gallagher commutator identity, with each filtered
right-variable sum reindexed by the inverse image of the appropriate
quotient centralizer. -/
theorem degree_mul_sum_goodElementCentralizer_commutator
    (N : Subgroup A) [N.Normal]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ a : A, a • θ = θ) :
    (θ.degree : ℂ) *
        ∑ x : A,
          ∑ y :
              IrreducibleCharacter.goodElementCentralizer N
                (QuotientGroup.mk' N x),
            θ.values
              ⟨x⁻¹ * (y : A)⁻¹ * x * (y : A),
                (IrreducibleCharacter.gallagherCommutator_mem_iff_mem_goodElementCentralizer
                  N x (y : A)).mpr y.property⟩ =
      (Nat.card A : ℂ) * (Nat.card N : ℂ) *
        (Nat.card
          (IrreducibleCharactersOverAlong N.subtype θ) : ℂ) := by
  classical
  let f : A → A → ℂ :=
    fun x y =>
      if hcomm : x⁻¹ * y⁻¹ * x * y ∈ N then
        θ.values ⟨x⁻¹ * y⁻¹ * x * y, hcomm⟩
      else 0
  have hreindex :
      (∑ x : A, ∑ y : A,
          if hcomm : x⁻¹ * y⁻¹ * x * y ∈ N then
            θ.values
              ⟨x⁻¹ * y⁻¹ * x * y, hcomm⟩
          else 0) =
        ∑ x : A,
          ∑ y :
              IrreducibleCharacter.goodElementCentralizer N
                (QuotientGroup.mk' N x),
            θ.values
              ⟨x⁻¹ * (y : A)⁻¹ * x * (y : A),
                (IrreducibleCharacter.gallagherCommutator_mem_iff_mem_goodElementCentralizer
                  N x (y : A)).mpr y.property⟩ := by
    calc
      (∑ x : A, ∑ y : A,
          if hcomm : x⁻¹ * y⁻¹ * x * y ∈ N then
            θ.values
              ⟨x⁻¹ * y⁻¹ * x * y, hcomm⟩
          else 0) =
          ∑ x : A, ∑ y : A,
            if x⁻¹ * y⁻¹ * x * y ∈ N then
              f x y
            else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        by_cases hcomm :
            x⁻¹ * y⁻¹ * x * y ∈ N <;>
          simp [f, hcomm]
      _ =
          ∑ x : A,
            ∑ y :
                IrreducibleCharacter.goodElementCentralizer N
                  (QuotientGroup.mk' N x),
              f x y :=
        IrreducibleCharacter.sum_sum_ite_gallagherCommutator_mem_eq_sum_goodElementCentralizer
          N f
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        have hcomm :
            x⁻¹ * (y : A)⁻¹ * x * (y : A) ∈ N :=
          (IrreducibleCharacter.gallagherCommutator_mem_iff_mem_goodElementCentralizer
            N x (y : A)).mpr y.property
        simp [f, hcomm]
  rw [← hreindex]
  exact degree_mul_filteredCommutatorSum
    N θ hinvariant

end CliffordCorrespondence
end McKayConjecture
