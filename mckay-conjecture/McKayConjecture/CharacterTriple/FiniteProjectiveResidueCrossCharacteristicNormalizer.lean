/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FiniteProjectiveResidueCrossCharacteristicEmbedding
import McKayConjecture.CharacterTriple.FiniteProjectiveResidueNormalizerLift

/-!
# Optional finite-field comparison for residue normalizer factors

This file specializes the optional prescribed finite-field embedding to the
factor of the residue normalizer lift.  The core normalizer and residue-Dade
interfaces do not depend on this comparison.
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

private instance residueNormalizerComparisonFinrankNeZero :
    NeZero (Module.finrank ℂ V) :=
  ⟨Module.finrank_pos.ne'⟩

variable
  (P : ProjectiveRepresentation ℂ G V)
  (b : Module.Basis ι ℂ V)
  (q : ℕ) [Fact q.Prime]

/-- Mapping the residue normalizer factor through a compatible coefficient
embedding gives the explicit cross-characteristic factor pointwise. -/
theorem unitsHom_residueFieldProjectiveNormalizerLift_factor
    (ρ :
      S →*
        (P.residueFieldLattice b q ≃ₗ[FiniteRootCoefficientRing.ResidueFieldAbovePrime
              q (Module.finrank ℂ V)]
          P.residueFieldLattice b q))
    (hnorm :
      PointwiseNormalizesLinearAction
        (P.residueFieldProjectiveRepresentation b q) ρ)
    (E :
      FiniteRootCoefficientRing.CrossCharacteristicResidueEmbedding
        q (Module.finrank ℂ V))
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
    FiniteRootCoefficientRing.CrossCharacteristicResidueEmbedding.unitsHom
        q (Module.finrank ℂ V) E
        ((P.residueFieldProjectiveNormalizerLift b q ρ hnorm).factor g h) =
      P.finiteFactorCrossCharacteristicReduction q g h := by
  rw [P.residueFieldProjectiveNormalizerLift_factor b q ρ hnorm]
  exact
    congrArg
      (fun α :
          FactorSet G
            (PrimeToCoefficientField
              q (Module.finrank ℂ V))ˣ ↦
        α.toFun g h)
      (P.finiteFactorResidueReduction_map_eq_crossCharacteristic
        q E)

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
