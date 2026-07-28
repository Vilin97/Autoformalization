/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.EquivariantMultiplicityMismatch
import McKayConjecture.CharacterTriple.FactorSetPPrimaryValues

/-!
# Equivariant multiplicity mismatches with `p`-primary scalar values

If the canonical multiplicity mismatch is obtained from a factor set
valued in a finite commutative `p`-group, its scalar `H²` class is
`p`-primary.  Unlike a factorization of the acting group, this criterion
records the projective scalar values themselves and is therefore suited
to finite-order intertwiner calculations.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace EquivariantMultiplicityMismatch

variable {K L Γ A : Type}
variable [Group K] [Finite K] [Group L] [Finite L]
variable [Group Γ] [CommGroup A] [Finite A]
variable (α : Γ →* MulAut K) (β : Γ →* MulAut L)
variable (θ : IrreducibleCharacter K) (η : IrreducibleCharacter L)
variable (hθ : IsInvariant α θ) (hη : IsInvariant β η)

/-- A realization of the mismatch factor set in a finite commutative
`p`-group of scalars makes the mismatch `p`-primary. -/
theorem isQPrimary_of_pGroup_coefficients
    (p : ℕ)
    (hA : IsPGroup p A)
    (c : FactorSet Γ A)
    (ι : A →* ℂˣ)
    (hfactor :
      factorSet α β θ η hθ hη =
        c.map ι) :
    IsQPrimary α β θ η hθ hη p := by
  obtain ⟨k, hk⟩ :=
    c.exists_pow_nsmul_map_h2Class_eq_zero_of_isPGroup
      p hA ι
  refine ⟨k, ?_⟩
  rw [hfactor]
  exact hk

end EquivariantMultiplicityMismatch
end CharacterTriple
end McKayConjecture
