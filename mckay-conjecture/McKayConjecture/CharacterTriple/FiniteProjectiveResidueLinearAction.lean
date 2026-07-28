/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FiniteFieldProjectiveLinearActionNormalizer
import McKayConjecture.CharacterTriple.FiniteProjectiveResidueFieldRepresentation

/-!
# Honest actions on a projective residue lattice

The chosen cyclotomic residue field is finite of characteristic `q`.
Consequently, when the group indexing the reduced projective operators is a
finite `q`-group, those operators can be scalar-rescaled to an honest action.
The original reduced projective operators pointwise normalize that action,
so it is immediately suitable for the residue interior-normalizer package.

For a `q`-group mapping into a larger ambient group, restriction still
produces an honest action.  The only remaining ambient-normalization
obligation is the explicit scalar-correction equivariance condition
`ScalarCorrectionIsConjugationStable`.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

open Representation

variable {G V ι R : Type}
variable [Group G] [Finite G]
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable [Finite ι]
variable [Group R] [Finite R]

private instance residueLinearActionFinrankNeZero :
    NeZero (Module.finrank ℂ V) :=
  ⟨Module.finrank_pos.ne'⟩

variable
  (P : ProjectiveRepresentation ℂ G V)
  (b : Module.Basis ι ℂ V)
  (q : ℕ) [Fact q.Prime]

/-- If the indexing group itself is a `q`-group, the residue-field
projective representation admits an honest scalar-rescaling normalized by
all of its original operators.  This includes the possibly zero residue
module. -/
theorem exists_residueFieldLinearAction_pointwiseNormalizer
    (hG : IsPGroup q G) :
    ∃ d :
        G →
          (FiniteRootCoefficientRing.ResidueFieldAbovePrime
            q (Module.finrank ℂ V))ˣ,
      ∃ rho :
          G →*
            (P.residueFieldLattice b q ≃ₗ[
              FiniteRootCoefficientRing.ResidueFieldAbovePrime
                q (Module.finrank ℂ V)]
              P.residueFieldLattice b q),
        (∀ g : G,
          rho g =
            scalarLinearEquiv
                (FiniteRootCoefficientRing.ResidueFieldAbovePrime
                  q (Module.finrank ℂ V))
                (P.residueFieldLattice b q)
                (d g) *
              (P.residueFieldProjectiveRepresentation b q).operator g) ∧
          (P.residueFieldProjectiveRepresentation b q
            ).PointwiseNormalizesLinearAction rho :=
  (P.residueFieldProjectiveRepresentation b q
    ).exists_linearAction_rescaling_pointwiseNormalizer hG

/-- Restricting the residue-field projective representation along a finite
`q`-group homomorphism always constructs an honest action of that `q`-group.
Ambient normalization is then reduced precisely to
`ScalarCorrectionIsConjugationStable`. -/
theorem exists_residueFieldComapLinearAction_rescaling
    (i : R →* G)
    (hR : IsPGroup q R) :
    ∃ d :
        R →
          (FiniteRootCoefficientRing.ResidueFieldAbovePrime
            q (Module.finrank ℂ V))ˣ,
      ∃ rho :
          R →*
            (P.residueFieldLattice b q ≃ₗ[
              FiniteRootCoefficientRing.ResidueFieldAbovePrime
                q (Module.finrank ℂ V)]
              P.residueFieldLattice b q),
        ∀ r : R,
          rho r =
            scalarLinearEquiv
                (FiniteRootCoefficientRing.ResidueFieldAbovePrime
                  q (Module.finrank ℂ V))
                (P.residueFieldLattice b q)
                (d r) *
              (P.residueFieldProjectiveRepresentation b q).operator (i r) :=
  (P.residueFieldProjectiveRepresentation b q
    ).exists_comap_linearAction_rescaling i hR

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
