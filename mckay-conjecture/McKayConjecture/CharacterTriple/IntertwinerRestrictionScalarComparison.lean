/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.RepresentationEquivScalarComparison

/-!
# Scalar comparison under restriction of an acting group

The canonical intertwiner chosen after restricting an action need not be
definitionally the canonical intertwiner chosen before restriction.  Both
implement the same automorphism, so Schur uniqueness compares them by a
nonzero scalar.  This distinction matters when a projective Hom action has
already been constructed before restricting its acting group.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace AssociatedExistence

variable {N Γ H : Type}
variable [Group N] [Finite N] [Group Γ] [Group H]

/-- An intertwiner chosen for an action and the intertwiner independently
chosen after restricting that action differ by a nonzero scalar. -/
theorem exists_scalar_between_intertwiner_and_restriction
    (alpha : Γ →* MulAut N)
    (chi : IrreducibleCharacter N)
    (hchi : IsInvariant alpha chi)
    (j : H →* Γ)
    (hrestricted : IsInvariant (alpha.comp j) chi)
    (h : H) :
    ∃ c : ℂˣ, ∀ v : chi.realization,
      intertwiner alpha chi hchi (j h) v =
        (c : ℂ) •
          intertwiner (alpha.comp j) chi hrestricted h v := by
  apply
    exists_scalar_of_covariance
      chi (alpha (j h))
      (intertwiner (alpha.comp j) chi hrestricted h)
      (intertwiner alpha chi hchi (j h))
  · intro n
    simpa only [MonoidHom.coe_comp, Function.comp_apply] using
      intertwiner_mul_rho
        (alpha.comp j) chi hrestricted h n
  · intro n
    exact intertwiner_mul_rho alpha chi hchi (j h) n

/-- Combining a scalar comparison between two source operators with an
operator comparison after a linear equivalence multiplies the scalars. -/
theorem operator_comparison_of_source_scalar
    {V W : Type}
    [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (E : V ≃ₗ[ℂ] W)
    (T T' : V ≃ₗ[ℂ] V)
    (P : W ≃ₗ[ℂ] W)
    (a c : ℂˣ)
    (hTT' : ∀ v : V, T v = (a : ℂ) • T' v)
    (hT' : ∀ v : V, E (T' v) = (c : ℂ) • P (E v))
    (v : V) :
    E (T v) = ((a * c : ℂˣ) : ℂ) • P (E v) := by
  rw [hTT', map_smul, hT']
  simp only [Units.val_mul, smul_smul]

end AssociatedExistence
end CharacterTriple
end McKayConjecture
