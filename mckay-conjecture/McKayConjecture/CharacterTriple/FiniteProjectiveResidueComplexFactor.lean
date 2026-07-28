/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FiniteProjectiveResidueReduction
import McKayConjecture.CharacterTriple.FiniteRootResidueComplexCharacter

/-!
# Comparing residue factors directly in the complex units

The multiplicative character constructed from the exact residue kernel
maps the reduced finite factor set directly to the complex prime-to-`q`
part of the determinant-normalized factor set.  This comparison does
not use a ring homomorphism out of the residue field.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

open Representation

universe u v

variable {G : Type u} {V : Type v}
variable [Group G]
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]

private instance residueComplexFactorFinrankNeZero :
    NeZero (Module.finrank ℂ V) :=
  ⟨Module.finrank_pos.ne'⟩

variable
  (P : ProjectiveRepresentation ℂ G V)
  (q : ℕ) [Fact q.Prime]

/-- Mapping the residue factor set through the compatible complex
character recovers its complex prime-to-`q` factor set. -/
theorem finiteFactorResidueReduction_map_residueUnitsComplexCharacter :
    (P.finiteFactorResidueReduction
        (FiniteRootCoefficientRing.maximalIdealAbovePrime
          q (Module.finrank ℂ V))).map
        (FiniteRootCoefficientRing.residueUnitsComplexCharacter
          q (Module.finrank ℂ V)) =
      P.finiteFactorSet.map
        (FiniteRootCoefficientRing.complexPrimeToRootsProjection
          q (Module.finrank ℂ V)) := by
  apply FactorSet.ext
  intro g h
  exact
    FiniteRootCoefficientRing.residueUnitsComplexCharacter_rootToResidueField
      q (Module.finrank ℂ V)
      (P.finiteFactorSet g h)

@[simp]
theorem residueUnitsComplexCharacter_finiteFactorResidueReduction
    (g h : G) :
    FiniteRootCoefficientRing.residueUnitsComplexCharacter
        q (Module.finrank ℂ V)
        (P.finiteFactorResidueReduction
          (FiniteRootCoefficientRing.maximalIdealAbovePrime
            q (Module.finrank ℂ V)) g h) =
      (primeToRootsProjection
        q (Module.finrank ℂ V)
        (P.finiteFactorSet g h) : ℂˣ) :=
  FiniteRootCoefficientRing.residueUnitsComplexCharacter_rootToResidueField
    q (Module.finrank ℂ V)
    (P.finiteFactorSet g h)

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
