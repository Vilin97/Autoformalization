/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyClasses
import McKayConjecture.GroupTheory.AlternatingSixSchurOuterAutomorphismChecks
import McKayConjecture.InductiveMcKay.AutomorphismStabilizer

/-!
# A Sylow-two-stabilizing representative of the first audited `6.A₆` automorphism

The first audited automorphism is constructed on the computable Schur-cover
coordinates.  This file transports it to the canonical free-presentation
universal cover.  The fixed Sylow subgroup of that cover is an arbitrary
`default` choice, so the transported automorphism need not preserve it
literally.  Sylow conjugacy supplies an inner correction, producing a
genuine element of `SylowAutStabilizer`.

This is only a group-theoretic bridge.  It makes no claim about the action
of this representative on the project's character rows or on CTblLib row
indices.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixTwoAlphaOneStabilizerFactPrime :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The first audited Schur-coordinate automorphism transported to the
canonical universal cover. -/
def alternatingSixUniversalCoverAlphaOneAutomorphism :
    MulAut AlternatingSixUniversalCover :=
  MulAut.congr alternatingSixSchurCoordinatesEquivUniversalCover
    alternatingSixSchurAlphaOneAutomorphism

@[simp]
theorem alternatingSixUniversalCoverAlphaOneAutomorphism_apply
    (x : AlternatingSixUniversalCover) :
    alternatingSixUniversalCoverAlphaOneAutomorphism x =
      alternatingSixSchurCoordinatesEquivUniversalCover
        (alternatingSixSchurAlphaOneAutomorphism
          (alternatingSixSchurCoordinatesEquivUniversalCover.symm x)) :=
  rfl

/-- A conjugating element which moves the image of the fixed Sylow
`2`-subgroup back to that fixed Sylow subgroup. -/
def alternatingSixUniversalCoverAlphaOneSylowTwoConjugator :
    AlternatingSixUniversalCover :=
  Classical.choose
    (MulAction.exists_smul_eq
      AlternatingSixUniversalCover
      (alternatingSixUniversalCoverAlphaOneAutomorphism •
        alternatingSixUniversalCoverSylow 2)
      (alternatingSixUniversalCoverSylow 2))

/-- The chosen inner correction sends the transported Sylow subgroup back
to the fixed one. -/
theorem alternatingSixUniversalCoverAlphaOneSylowTwoConjugator_smul :
    alternatingSixUniversalCoverAlphaOneSylowTwoConjugator •
        (alternatingSixUniversalCoverAlphaOneAutomorphism •
          alternatingSixUniversalCoverSylow 2) =
      alternatingSixUniversalCoverSylow 2 :=
  Classical.choose_spec
    (MulAction.exists_smul_eq
      AlternatingSixUniversalCover
      (alternatingSixUniversalCoverAlphaOneAutomorphism •
        alternatingSixUniversalCoverSylow 2)
      (alternatingSixUniversalCoverSylow 2))

/-- The transported first audited automorphism, corrected by an inner
automorphism so that it preserves the fixed Sylow `2`-subgroup. -/
def alternatingSixUniversalCoverAlphaOneSylowTwoAutomorphism :
    MulAut AlternatingSixUniversalCover :=
  MulAut.conj
      alternatingSixUniversalCoverAlphaOneSylowTwoConjugator *
    alternatingSixUniversalCoverAlphaOneAutomorphism

/-- The inner-corrected automorphism genuinely stabilizes the fixed Sylow
`2`-subgroup. -/
theorem alternatingSixUniversalCoverAlphaOneSylowTwoAutomorphism_smul :
    alternatingSixUniversalCoverAlphaOneSylowTwoAutomorphism •
        alternatingSixUniversalCoverSylow 2 =
      alternatingSixUniversalCoverSylow 2 := by
  rw [alternatingSixUniversalCoverAlphaOneSylowTwoAutomorphism, mul_smul]
  exact
    alternatingSixUniversalCoverAlphaOneSylowTwoConjugator_smul

/-- The first audited automorphism, with its Sylow-conjugacy correction,
as an element of the exact stabilizer used by equivariant McKay data. -/
def alternatingSixUniversalCoverAlphaOneSylowTwoStabilizer :
    SylowAutStabilizer (alternatingSixUniversalCoverSylow 2) :=
  ⟨alternatingSixUniversalCoverAlphaOneSylowTwoAutomorphism,
    alternatingSixUniversalCoverAlphaOneSylowTwoAutomorphism_smul⟩

@[simp]
theorem alternatingSixUniversalCoverAlphaOneSylowTwoStabilizer_coe :
    (alternatingSixUniversalCoverAlphaOneSylowTwoStabilizer :
      MulAut AlternatingSixUniversalCover) =
        MulAut.conj
            alternatingSixUniversalCoverAlphaOneSylowTwoConjugator *
          alternatingSixUniversalCoverAlphaOneAutomorphism :=
  rfl

end InductiveMcKay
end McKayConjecture
