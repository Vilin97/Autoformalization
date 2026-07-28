/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Trivial
import McKayConjecture.InductiveMcKay.HonestExtensionProjectiveCompatibility
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveFiveEquivariantTable

/-!
# The trivial projective row at `p = 5` for `SL(2, 𝔽₅)`

The displayed McKay matching pairs the two trivial characters.  Their
canonical semidirect extensions are again trivial, so both projective
factor sets and all central scalars are identically one.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance factPrimeFiveForTrivialProjectiveRow :
    Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The trivial row in the ambient `5'` table. -/
def specialLinearTwoFiveFiveTrivialPPrimeRow :
    SpecialLinearTwoFivePPrimeCharacterRow 5 :=
  ⟨.trivial, by
    simp [specialLinearTwoFiveCharacterRowDegree]⟩

/-- The displayed ambient trivial row is the intrinsic trivial
irreducible character. -/
theorem specialLinearTwoFiveFiveAmbientTrivialCharacter_eq :
    (specialLinearTwoFivePPrimeCharacterEquiv 5
        specialLinearTwoFiveFiveTrivialPPrimeRow).1 =
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

/-- Frequency zero in the linear dicyclic family is the intrinsic
trivial character. -/
theorem quaternionGroupFiveLinearZeroCharacter_eq :
    QuaternionGroupFive.linearCharacter 0 =
      IrreducibleCharacter.trivial (QuaternionGroup 5) := by
  apply IrreducibleCharacter.ext
  funext g
  rcases g with i | i
  · simp [QuaternionGroupFive.linearCharacter,
      QuaternionGroupFive.linearHom,
      QuaternionGroupFive.linearHomOfFourthRoot,
      QuaternionGroupFive.fourthRootParameter]
    rw [← ZMod.natCast_zmod_val i,
      QuaternionGroup.zmodPower_natCast]
    simp
  · simp [QuaternionGroupFive.linearCharacter,
      QuaternionGroupFive.linearHom,
      QuaternionGroupFive.linearHomOfFourthRoot,
      QuaternionGroupFive.fourthRootParameter]
    rw [← ZMod.natCast_zmod_val i,
      QuaternionGroup.zmodPower_natCast]
    simp

/-- The transported frequency-zero row is the trivial character of the
exact Sylow-five normalizer. -/
theorem specialLinearTwoFiveFiveNormalizerLinearZeroCharacter_eq :
    (specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv
        (.linear 0)).1 =
      IrreducibleCharacter.trivial
        (SylowNormalizer specialLinearTwoFiveSylowFive) := by
  apply IrreducibleCharacter.ext
  funext x
  obtain ⟨q, rfl⟩ :=
    quaternionFiveEquivSylowFiveNormalizer.surjective x
  rw [specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv_values]
  change
    (QuaternionGroupFive.linearCharacter 0).values q = 1
  rw [quaternionGroupFiveLinearZeroCharacter_eq]
  rfl

/-- The ordinary McKay equivalence sends the ambient trivial character
to the normalizer trivial character. -/
theorem specialLinearTwoFiveFiveMcKay_trivialCharacter_eq :
    (specialLinearTwoFiveFiveEquivariantMcKayEquiv
      (specialLinearTwoFivePPrimeCharacterEquiv 5
        specialLinearTwoFiveFiveTrivialPPrimeRow)).1 =
      IrreducibleCharacter.trivial
        (SylowNormalizer specialLinearTwoFiveSylowFive) := by
  rw [specialLinearTwoFiveFiveEquivariantMcKayEquiv_apply]
  change
    (specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv
      (.linear 0)).1 =
      IrreducibleCharacter.trivial
        (SylowNormalizer specialLinearTwoFiveSylowFive)
  exact specialLinearTwoFiveFiveNormalizerLinearZeroCharacter_eq

/-- Honest trivial extensions prove the complete projective condition for
the trivial `p = 5` row. -/
theorem specialLinearTwoFiveFiveTrivialRow_tripleCompatible :
    specialLinearTwoFiveFiveEquivariantMcKayEquiv
      |>.toExactNormalizerLocalCorrespondence.TripleCompatible
        (specialLinearTwoFivePPrimeCharacterEquiv 5
          specialLinearTwoFiveFiveTrivialPPrimeRow) := by
  let e := specialLinearTwoFiveFiveEquivariantMcKayEquiv
  let d := e.toExactNormalizerLocalCorrespondence
  let χ :=
    specialLinearTwoFivePPrimeCharacterEquiv 5
      specialLinearTwoFiveFiveTrivialPPrimeRow
  let ψ :=
    IrreducibleCharacter.trivial
      (SpecialLinearTwoFive ⋊[
        PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer specialLinearTwoFiveSylowFive χ)
  let ξ :=
    IrreducibleCharacter.trivial
      (d.intermediate ⋊[d.stabilizerIntermediateAction χ]
        PPrimeCharacterStabilizer specialLinearTwoFiveSylowFive χ)
  apply d.tripleCompatible_of_honestExtensions χ ψ ξ
  · intro x
    change
      (1 : ℂ) =
        (specialLinearTwoFivePPrimeCharacterEquiv 5
          specialLinearTwoFiveFiveTrivialPPrimeRow).1.values x.1.left
    rw [specialLinearTwoFiveFiveAmbientTrivialCharacter_eq]
    rfl
  · intro x
    change
      (1 : ℂ) =
        (e
          (specialLinearTwoFivePPrimeCharacterEquiv 5
            specialLinearTwoFiveFiveTrivialPPrimeRow)).1.values x.1.left
    rw [specialLinearTwoFiveFiveMcKay_trivialCharacter_eq]
    rfl
  · intro h _
    rfl

/-- The concrete exact-normalizer projective certificate for the trivial
row. -/
def specialLinearTwoFiveFiveTrivialProjectiveRowData :
    ExactNormalizerProjectiveRowData
      specialLinearTwoFiveFiveEquivariantMcKayEquiv
      (specialLinearTwoFivePPrimeCharacterEquiv 5
        specialLinearTwoFiveFiveTrivialPPrimeRow) :=
  ExactNormalizerProjectiveRowData.ofTripleCompatible
    specialLinearTwoFiveFiveEquivariantMcKayEquiv
    (specialLinearTwoFivePPrimeCharacterEquiv 5
      specialLinearTwoFiveFiveTrivialPPrimeRow)
    specialLinearTwoFiveFiveTrivialRow_tripleCompatible

end InductiveMcKay
end McKayConjecture
