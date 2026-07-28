/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.EndomorphismInteriorAction
import McKayConjecture.CharacterTriple.ProjectiveNormalizerLift
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Covariant projective operators normalize an interior action

Suppose a projective action of `G` on `V` transports a linear `P`-action
according to an action of `G` on `P`.  Conjugating an implementing
`P`-unit by any projective operator is then another implementing unit.
Since `P` is finite, this inclusion proves that every projective operator
normalizes the whole interior image.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

open Representation

variable {K P G V : Type}
variable [Field K] [Group P] [Finite P] [Group G]
variable [AddCommGroup V] [Module K V]

/-- Covariance of a projective action with a linear action of a second
group. -/
def IsCovariantWith
    (Q : ProjectiveRepresentation K G V)
    (ρ : P →* (V ≃ₗ[K] V))
    (φ : G →* MulAut P) : Prop :=
  ∀ g p,
    Q.operator g * ρ p * (Q.operator g)⁻¹ =
      ρ (φ g p)

/-- Every covariant projective operator normalizes the unit image of the
linear action. -/
theorem operatorUnit_mem_linearActionUnit_normalizer
    (Q : ProjectiveRepresentation K G V)
    (ρ : P →* (V ≃ₗ[K] V))
    (φ : G →* MulAut P)
    (hcov : Q.IsCovariantWith ρ φ)
    (g : G) :
    operatorUnit (Q.operator g) ∈
      Subgroup.normalizer
        ((linearActionUnit ρ).range :
          Set (Module.End K V)ˣ) := by
  letI :
      Finite
        ((linearActionUnit ρ).range :
          Set (Module.End K V)ˣ) :=
    Set.finite_range (linearActionUnit ρ)
  apply Subgroup.mem_normalizer_fintype
  intro u hu
  rcases hu with ⟨p, rfl⟩
  refine ⟨φ g p, ?_⟩
  apply
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).injective
  simpa only [_root_.map_mul, _root_.map_inv,
    generalLinearEquiv_operatorUnit,
    generalLinearEquiv_linearActionUnit] using (hcov g p).symm

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
