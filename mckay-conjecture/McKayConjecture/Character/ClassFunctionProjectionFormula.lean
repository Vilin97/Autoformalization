/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ClassFunctionPointwiseRing
import McKayConjecture.Character.ClassFunctionRestriction

/-!
# Projection formula for induced class functions

Pointwise multiplication of an induced class function by an ambient class
function can be moved inside induction after restricting the ambient
factor:

`Ind_S^G(θ) * f = Ind_S^G(θ * Res_S^G(f))`.

This is the elementary calculation that makes the span of elementary
inductions an ideal in the class-function character ring.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace ClassFunction

variable {G : Type} [Group G]

/-- The projection formula holds term by term in the defining induction
sum. -/
theorem inductionTerm_mul_comap
    (S : Subgroup G)
    (θ : ClassFunction S)
    (f : ClassFunction G)
    (x g : G) :
    inductionTerm S
        (θ * comapLinearMap S.subtype f) x g =
      inductionTerm S θ x g * f g := by
  classical
  by_cases hx : x⁻¹ * g * x ∈ S
  · rw [inductionTerm_of_mem S
      (θ * comapLinearMap S.subtype f) hx,
      inductionTerm_of_mem S θ hx,
      mul_apply, comapLinearMap_apply]
    change
      θ ⟨x⁻¹ * g * x, hx⟩ *
          f (x⁻¹ * g * x) =
        θ ⟨x⁻¹ * g * x, hx⟩ * f g
    have hf :=
      ClassFunction.conj_apply f g x⁻¹
    simpa only [inv_inv] using
      congrArg (fun z : ℂ => θ ⟨x⁻¹ * g * x, hx⟩ * z) hf
  · rw [inductionTerm_of_not_mem S
      (θ * comapLinearMap S.subtype f) hx,
      inductionTerm_of_not_mem S θ hx,
      zero_mul]

/-- Projection formula for induction and pointwise multiplication. -/
theorem induce_mul_comap
    [Fintype G]
    (S : Subgroup G)
    (θ : ClassFunction S)
    (f : ClassFunction G) :
    induce S
        (θ * comapLinearMap S.subtype f) =
      induce S θ * f := by
  apply ClassFunction.ext
  intro g
  rw [mul_apply, induce_apply, induce_apply]
  simp_rw [inductionTerm_mul_comap]
  rw [← Finset.sum_mul]
  simp only [mul_assoc]

/-- Symmetric form of the projection formula. -/
theorem induce_comap_mul
    [Fintype G]
    (S : Subgroup G)
    (θ : ClassFunction S)
    (f : ClassFunction G) :
    induce S
        (comapLinearMap S.subtype f * θ) =
      f * induce S θ := by
  rw [mul_comm
      (comapLinearMap S.subtype f) θ,
    induce_mul_comap, mul_comm]

end ClassFunction
end McKayConjecture
