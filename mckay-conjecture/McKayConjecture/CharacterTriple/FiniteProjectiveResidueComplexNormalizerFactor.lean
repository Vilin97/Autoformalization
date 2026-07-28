/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FiniteProjectiveResidueComplexFactor
import McKayConjecture.CharacterTriple.FiniteProjectiveResidueNormalizerLift

/-!
# Complex lift of a projective residue normalizer factor

The unconditional character of residue-field units sends the factor of the
residue normalizer lift directly to the prime-to-`q` part of the original
determinant-normalized complex factor.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

open Representation

variable {G V ι S : Type}
variable [Group G] [Finite G]
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable [Finite ι]
variable [Group S] [Fintype S]

private instance residueComplexNormalizerFinrankNeZero :
    NeZero (Module.finrank ℂ V) :=
  ⟨Module.finrank_pos.ne'⟩

variable
  (P : ProjectiveRepresentation ℂ G V)
  (b : Module.Basis ι ℂ V)
  (q : ℕ) [Fact q.Prime]

/-- The complex lift of the residue normalizer factor is exactly the
prime-to-`q` projection of the finite complex factor. -/
@[simp]
theorem residueUnitsComplexCharacter_residueFieldProjectiveNormalizerLift_factor
    (ρ :
      S →*
        (P.residueFieldLattice b q ≃ₗ[FiniteRootCoefficientRing.ResidueFieldAbovePrime
            q (Module.finrank ℂ V)]
          P.residueFieldLattice b q))
    (hnorm :
      PointwiseNormalizesLinearAction
        (P.residueFieldProjectiveRepresentation b q) ρ)
    (g h : G) :
    letI :
        MulAction
          (FiniteRootCoefficientRing.ResidueFieldAbovePrime
            q (Module.finrank ℂ V))
          (P.residueFieldLattice b q) :=
      (inferInstance :
        Module
          (FiniteRootCoefficientRing.ResidueFieldAbovePrime
            q (Module.finrank ℂ V))
          (P.residueFieldLattice b q)).toDistribMulAction.toMulAction
    letI :=
      endomorphismConjugationMulSemiringAction ρ
    letI :=
      endomorphismConjugation_smulCommClass ρ
    FiniteRootCoefficientRing.residueUnitsComplexCharacter
        q (Module.finrank ℂ V)
        ((P.residueFieldProjectiveNormalizerLift b q ρ hnorm).factor g h) =
      (primeToRootsProjection q (Module.finrank ℂ V)
        (P.finiteFactorSet g h) : ℂˣ) := by
  rw [P.residueFieldProjectiveNormalizerLift_factor b q ρ hnorm]
  exact
    P.residueUnitsComplexCharacter_finiteFactorResidueReduction
      q g h

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
