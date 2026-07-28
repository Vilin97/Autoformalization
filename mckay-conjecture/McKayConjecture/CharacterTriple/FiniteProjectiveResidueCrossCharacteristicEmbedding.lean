/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FiniteProjectiveResidueFieldRepresentation
import McKayConjecture.CharacterTriple.FiniteRootCrossCharacteristicResidueEmbedding
import McKayConjecture.CharacterTriple.ProjectiveCrossCharacteristicCoefficientReduction

/-!
# Optional finite-field comparison for projective residue factors

The residue field need not be definitionally the concrete Galois field used by
`crossCharacteristicCoefficientReduction`.  When a prescribed compatible
field embedding is available, this file records the induced equality of
factor sets.  The unconditional proof path uses a complex character instead.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

open Representation

variable {G : Type u} {V : Type v}
variable [Group G]
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]

private instance comparisonFinrankNeZero :
    NeZero (Module.finrank ℂ V) :=
  ⟨Module.finrank_pos.ne'⟩

variable
  (P : ProjectiveRepresentation ℂ G V)
  (q : ℕ) [Fact q.Prime]

/-- Mapping the residue factor along a compatible finite-field embedding
gives exactly the explicit cross-characteristic factor set. -/
theorem finiteFactorResidueReduction_map_eq_crossCharacteristic
    (E :
      FiniteRootCoefficientRing.CrossCharacteristicResidueEmbedding
        q (Module.finrank ℂ V)) :
    (P.finiteFactorResidueReduction
        (FiniteRootCoefficientRing.maximalIdealAbovePrime
          q (Module.finrank ℂ V))).map
        (FiniteRootCoefficientRing.CrossCharacteristicResidueEmbedding.unitsHom
          q (Module.finrank ℂ V) E) =
      P.finiteFactorCrossCharacteristicReduction q := by
  apply FactorSet.ext
  intro g h
  exact
    FiniteRootCoefficientRing.CrossCharacteristicResidueEmbedding.unitsHom_rootToResidueField
      q (Module.finrank ℂ V) E
      (P.finiteFactorSet g h)

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
