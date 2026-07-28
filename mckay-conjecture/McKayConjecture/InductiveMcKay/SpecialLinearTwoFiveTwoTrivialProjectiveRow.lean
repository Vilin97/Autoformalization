/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Trivial
import McKayConjecture.InductiveMcKay.HonestExtensionProjectiveCompatibility
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveTwoEquivariance

/-!
# The trivial projective row at `p = 2` for `SL(2, 𝔽₅)`

The first row of the exact McKay matching pairs the two trivial characters.
Both extend to the corresponding canonical semidirect products as the trivial
character, so their projective factors and central scalars are identically
one.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance factPrimeTwoForTrivialProjectiveRow :
    Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The trivial row in the four-row ambient `2'` table. -/
def specialLinearTwoFiveTwoTrivialPPrimeRow :
    SpecialLinearTwoFivePPrimeCharacterRow 2 :=
  ⟨.trivial, by
    simp [specialLinearTwoFiveCharacterRowDegree]⟩

/-- The displayed ambient trivial row is the intrinsic trivial irreducible
character. -/
theorem specialLinearTwoFiveTwoAmbientTrivialCharacter_eq :
    (specialLinearTwoFiveTwoPPrimeCharacterEquiv
        specialLinearTwoFiveTwoTrivialPPrimeRow).1 =
      IrreducibleCharacter.trivial SpecialLinearTwoFive := by
  apply IrreducibleCharacter.ext
  funext g
  change
    (specialLinearTwoFiveCharacterFDRep .trivial).character g = 1
  change
    LinearMap.trace ℂ ℂ
        (LinearMap.id : Module.End ℂ ℂ) =
      1
  simp

/-- The frequency-zero linear row of the binary tetrahedral normalizer is
the intrinsic trivial irreducible character. -/
theorem specialLinearTwoFiveTwoNormalizerLinearZeroCharacter_eq :
    specialLinearTwoFiveTwoNormalizerLinearCharacter 0 =
      IrreducibleCharacter.trivial
        SpecialLinearTwoFiveSylowTwoNormalizer := by
  apply IrreducibleCharacter.ext
  funext g
  simp [specialLinearTwoFiveTwoNormalizerLinearHom,
    zmodThreeComplexUnitCharacter]

/-- The ordinary McKay equivalence sends the ambient trivial row to the
normalizer trivial row. -/
theorem specialLinearTwoFiveTwoMcKay_trivialCharacter_eq :
    (specialLinearTwoFiveTwoCharacterTableCompletion
        |>.toEquivariantMcKayEquiv
        (specialLinearTwoFiveTwoPPrimeCharacterEquiv
          specialLinearTwoFiveTwoTrivialPPrimeRow)).1 =
      IrreducibleCharacter.trivial
        SpecialLinearTwoFiveSylowTwoNormalizer := by
  rw [
    SpecialLinearTwoFiveTwoCharacterTableCompletion.toEquivariantMcKayEquiv_apply_enumerated]
  change
    specialLinearTwoFiveTwoNormalizerLinearCharacter 0 =
      IrreducibleCharacter.trivial
        SpecialLinearTwoFiveSylowTwoNormalizer
  exact specialLinearTwoFiveTwoNormalizerLinearZeroCharacter_eq

/-- Honest trivial extensions prove the complete projective condition for
the first `p = 2` row. -/
theorem specialLinearTwoFiveTwoTrivialRow_tripleCompatible :
    let e :=
      specialLinearTwoFiveTwoCharacterTableCompletion
        |>.toEquivariantMcKayEquiv
    e.toExactNormalizerLocalCorrespondence.TripleCompatible
      (specialLinearTwoFiveTwoPPrimeCharacterEquiv
        specialLinearTwoFiveTwoTrivialPPrimeRow) := by
  let e :=
    specialLinearTwoFiveTwoCharacterTableCompletion
      |>.toEquivariantMcKayEquiv
  let d := e.toExactNormalizerLocalCorrespondence
  let χ :=
    specialLinearTwoFiveTwoPPrimeCharacterEquiv
      specialLinearTwoFiveTwoTrivialPPrimeRow
  let ψ :=
    IrreducibleCharacter.trivial
      (SpecialLinearTwoFive ⋊[
        PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer specialLinearTwoFiveSylowTwo χ)
  let ξ :=
    IrreducibleCharacter.trivial
      (d.intermediate ⋊[d.stabilizerIntermediateAction χ]
        PPrimeCharacterStabilizer specialLinearTwoFiveSylowTwo χ)
  apply d.tripleCompatible_of_honestExtensions χ ψ ξ
  · intro x
    change
      (1 : ℂ) =
        (specialLinearTwoFiveTwoPPrimeCharacterEquiv
          specialLinearTwoFiveTwoTrivialPPrimeRow).1.values x.1.left
    rw [specialLinearTwoFiveTwoAmbientTrivialCharacter_eq]
    rfl
  · intro x
    change
      (1 : ℂ) =
        (e
          (specialLinearTwoFiveTwoPPrimeCharacterEquiv
            specialLinearTwoFiveTwoTrivialPPrimeRow)).1.values x.1.left
    rw [specialLinearTwoFiveTwoMcKay_trivialCharacter_eq]
    rfl
  · intro h _
    rfl

/-- The concrete exact-normalizer projective certificate for the trivial
row. -/
def specialLinearTwoFiveTwoTrivialProjectiveRowData :
    let e :=
      specialLinearTwoFiveTwoCharacterTableCompletion
        |>.toEquivariantMcKayEquiv
    ExactNormalizerProjectiveRowData e
      (specialLinearTwoFiveTwoPPrimeCharacterEquiv
        specialLinearTwoFiveTwoTrivialPPrimeRow) := by
  let e :=
    specialLinearTwoFiveTwoCharacterTableCompletion
      |>.toEquivariantMcKayEquiv
  exact
    ExactNormalizerProjectiveRowData.ofTripleCompatible e
      (specialLinearTwoFiveTwoPPrimeCharacterEquiv
        specialLinearTwoFiveTwoTrivialPPrimeRow)
      specialLinearTwoFiveTwoTrivialRow_tripleCompatible

end InductiveMcKay
end McKayConjecture
