/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Azumaya algebras over fields are simple

Mathlib defines an Azumaya algebra through the bijectivity of the
left-right multiplication map

`A ⊗[k] Aᵐᵒᵖ → Endₖ(A)`.

Over a field this immediately forces ring simplicity.  Given a nonzero
element `x` of a two-sided ideal, choose a linear endomorphism sending
`x` to `1`.  Surjectivity of the left-right multiplication map writes
that endomorphism as a sum of operators `y ↦ a * y * b`, each of which
preserves the ideal.  Hence the ideal contains `1`.

This elementary argument is the ideal-theoretic last step in
Thévenaz, *G-Algebras and Modular Representation Theory*,
Theorem 28.6(a).
-/

noncomputable section

open scoped TensorProduct

namespace Representation

universe u v

variable {k : Type u} {A : Type v}
variable [Field k] [Ring A] [Algebra k A]

/-- An Azumaya algebra over a field has no nontrivial two-sided ideals. -/
theorem isSimpleRing_of_isAzumaya
    [IsAzumaya k A] :
    IsSimpleRing A := by
  letI : Nontrivial A :=
    Function.Injective.nontrivial
      (FaithfulSMul.algebraMap_injective k A)
  apply IsSimpleRing.of_eq_bot_or_eq_top
  intro I
  by_cases hI : I = ⊥
  · exact Or.inl hI
  · right
    rw [← I.one_mem_iff]
    obtain ⟨x, hxI, hx0⟩ :=
      SetLike.exists_of_lt
        (bot_lt_iff_ne_bot.mpr hI : (⊥ : TwoSidedIdeal A) < I)
    obtain ⟨f, hfx⟩ :=
      Module.Projective.exists_dual_eq_one k hx0
    let e : Module.End k A :=
      f.smulRight (1 : A)
    obtain ⟨t, ht⟩ :=
      (IsAzumaya.AlgHom.mulLeftRight_bij k A).surjective e
    have hpreserves :
        ∀ z : A ⊗[k] Aᵐᵒᵖ,
          AlgHom.mulLeftRight k A z x ∈ I := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero =>
          simp
      | tmul a b =>
          rw [AlgHom.mulLeftRight_apply]
          exact
            I.mul_mem_right _ _
              (I.mul_mem_left _ _ hxI)
      | add z w hz hw =>
          rw [map_add, LinearMap.add_apply]
          exact I.add_mem hz hw
    have heI : e x ∈ I := by
      rw [← ht]
      exact hpreserves t
    simpa [e, LinearMap.smulRight_apply, hfx] using heI

end Representation
