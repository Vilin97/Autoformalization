/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.InvariantExtensionIntertwinerComparison

/-!
# Scalar comparison of irreducible representation equivalences

Two equivalences from the canonical realization of an irreducible character
to the same representation differ by one nonzero scalar.  Naming this
elementary Schur-lemma consequence separately keeps concrete applications
from repeatedly normalizing large representation terms.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace AssociatedExistence

variable {N W : Type}
variable [Group N] [Finite N]
variable [AddCommGroup W] [Module ℂ W]

/-- Two equivalences from an irreducible-character realization to the same
representation differ pointwise by a single nonzero scalar. -/
theorem exists_scalar_between_representation_equiv
    (chi : IrreducibleCharacter N)
    (sigma : Representation ℂ N W)
    (E F : Representation.Equiv chi.realization.ρ sigma) :
    ∃ c : ℂˣ, ∀ v : chi.realization,
      E v = (c : ℂ) • F v := by
  let comparison : chi.realization ≃ₗ[ℂ] chi.realization :=
    E.toLinearEquiv.trans F.toLinearEquiv.symm
  have hComparisonApply (v : chi.realization) :
      F (comparison v) = E v := by
    dsimp only [comparison]
    exact F.toLinearEquiv.apply_symm_apply (E v)
  have hcovariance :
      ∀ n : N,
        comparison * realizationAction chi n =
          realizationAction chi n * comparison := by
    intro n
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext
    intro v
    apply F.toLinearEquiv.injective
    change
      F (comparison (chi.realization.ρ n v)) =
        F (chi.realization.ρ n (comparison v))
    have hEpoint :
        E (chi.realization.ρ n v) =
          sigma n (E v) :=
      LinearMap.congr_fun (E.isIntertwining' n) v
    have hFpoint :
        F (chi.realization.ρ n (comparison v)) =
          sigma n (F (comparison v)) :=
      LinearMap.congr_fun
        (F.isIntertwining' n) (comparison v)
    rw [hComparisonApply]
    rw [hEpoint, hFpoint]
    rw [hComparisonApply]
  obtain ⟨c, hc⟩ :=
    exists_scalar_of_covariance
      chi (1 : MulAut N) 1 comparison
      (fun _ ↦ rfl) hcovariance
  refine ⟨c, fun v ↦ ?_⟩
  have hv :=
    congrArg (fun w : chi.realization ↦ F w) (hc v)
  rw [hComparisonApply, map_smul] at hv
  exact hv

/-- Replacing an operator equivalence by a constant nonzero scalar multiple
does not change its elementwise operator-comparison scalar. -/
theorem operator_comparison_of_constant_equiv
    {V W : Type}
    [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (E F : V ≃ₗ[ℂ] W)
    (T : V ≃ₗ[ℂ] V)
    (Q : W ≃ₗ[ℂ] W)
    (c t : ℂˣ)
    (hEF : ∀ v : V, E v = (c : ℂ) • F v)
    (hF : ∀ v : V, F (T v) = (t : ℂ) • Q (F v))
    (v : V) :
    E (T v) = (t : ℂ) • Q (E v) := by
  rw [hEF, hF, hEF, map_smul]
  simp only [smul_smul]
  ring

end AssociatedExistence
end CharacterTriple
end McKayConjecture
