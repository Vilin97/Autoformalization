/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.EquivariantMultiplicityMismatch
import McKayConjecture.CharacterTriple.FactorSetPGroupPullback

/-!
# `p`-primary equivariant multiplicity mismatches

Finite-order projective operators alone annihilate a mismatch class by the
order of the acting group.  They give a `p`-power annihilator precisely
when the mismatch factor set is pulled back from a finite `p`-group.  This
file packages that constructive criterion for the external multiplicity
mismatch.

The criterion is deliberately pointwise: it asks for an actual group
homomorphism and an actual factor set whose pullback is the canonical
mismatch.  Thus a Dade--Glauberman argument can discharge it by constructing
operators, without first developing functoriality of abstract `H²`.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace EquivariantMultiplicityMismatch

variable {K L Γ Δ : Type}
variable [Group K] [Finite K] [Group L] [Finite L]
variable [Group Γ] [Group Δ] [Finite Δ]
variable (α : Γ →* MulAut K) (β : Γ →* MulAut L)
variable (θ : IrreducibleCharacter K) (η : IrreducibleCharacter L)
variable (hθ : IsInvariant α θ) (hη : IsInvariant β η)

/-- An explicit factorization of the canonical mismatch through a finite
`p`-group makes the mismatch `p`-primary. -/
theorem isQPrimary_of_pGroup_factorization
    (p : ℕ) [Fact p.Prime]
    (hΔ : IsPGroup p Δ)
    (ρ : Γ →* Δ)
    (c : FactorSet Δ ℂˣ)
    (hfactor :
      factorSet α β θ η hθ hη =
        c.comap ρ) :
    IsQPrimary α β θ η hθ hη p := by
  obtain ⟨k, hk⟩ :=
    c.exists_pow_nsmul_comap_h2Class_eq_zero_of_isPGroup
      p hΔ ρ
  refine ⟨k, ?_⟩
  rw [hfactor]
  exact hk

/-- In the special case where the acting group itself is a finite
`p`-group, every external projective mismatch is `p`-primary. -/
theorem isQPrimary_of_isPGroup
    (p : ℕ) [Fact p.Prime]
    [Finite Γ]
    (hΓ : IsPGroup p Γ) :
    IsQPrimary α β θ η hθ hη p :=
  (factorSet α β θ η hθ hη
    ).exists_pow_nsmul_h2Class_eq_zero_of_isPGroup p hΓ

end EquivariantMultiplicityMismatch
end CharacterTriple
end McKayConjecture
