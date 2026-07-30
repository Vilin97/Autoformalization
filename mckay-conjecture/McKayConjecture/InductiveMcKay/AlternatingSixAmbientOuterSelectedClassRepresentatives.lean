/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurOuterClassActionAutomorphisms
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOuterABSquaredEvaluation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOuterSecondSeparator

/-!
# Selected class representatives for the ambient outer-row proof

Only five noncentral test elements are needed to resolve all repeated
degree/scalar signatures: `B`, `AB`, `AB²`, and the two long separators.
This file identifies their checked conjugacy-class indices, and records
literal representative equalities when the chosen positive word is itself
the advertised representative.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private theorem alternatingSixAmbientCanonicalGeneratorA_eq_coordinateA :
    alternatingSixAmbientCanonicalGeneratorA =
      alternatingSixSchurCoordinatesEquivUniversalCover
        alternatingSixSchurCoordinateA := by
  change
    (alternatingSixSchurUniversalCentralExtension.sourceEquiv
      alternatingSixUniversalCentralExtension)
        alternatingSixSchurPresentedA =
      (alternatingSixSchurUniversalCentralExtension.sourceEquiv
        alternatingSixUniversalCentralExtension)
          (AlternatingSixSchurCoordinates.mulEquivPresentedGroup
            alternatingSixSchurCoordinateA)
  apply congrArg
    (alternatingSixSchurUniversalCentralExtension.sourceEquiv
      alternatingSixUniversalCentralExtension)
  simpa using
    congrArg AlternatingSixSchurCoordinates.mulEquivPresentedGroup
      alternatingSixSchurCoordinateA_preimage

private theorem alternatingSixAmbientCanonicalGeneratorB_eq_coordinateB :
    alternatingSixAmbientCanonicalGeneratorB =
      alternatingSixSchurCoordinatesEquivUniversalCover
        alternatingSixSchurCoordinateB := by
  change
    (alternatingSixSchurUniversalCentralExtension.sourceEquiv
      alternatingSixUniversalCentralExtension)
        alternatingSixSchurPresentedB =
      (alternatingSixSchurUniversalCentralExtension.sourceEquiv
        alternatingSixUniversalCentralExtension)
          (AlternatingSixSchurCoordinates.mulEquivPresentedGroup
            alternatingSixSchurCoordinateB)
  apply congrArg
    (alternatingSixSchurUniversalCentralExtension.sourceEquiv
      alternatingSixUniversalCentralExtension)
  simpa using
    congrArg AlternatingSixSchurCoordinates.mulEquivPresentedGroup
      alternatingSixSchurCoordinateB_preimage

/-- The canonical `A` test element is checked class representative `6`. -/
theorem alternatingSixAmbientCanonicalGeneratorA_eq_classRepresentative :
    alternatingSixAmbientCanonicalGeneratorA =
      alternatingSixUniversalCoverClassRepresentative 6 := by
  rw [alternatingSixAmbientCanonicalGeneratorA_eq_coordinateA]
  rfl

/-- The canonical `B` test element is checked class representative `9`. -/
theorem alternatingSixAmbientCanonicalGeneratorB_eq_classRepresentative :
    alternatingSixAmbientCanonicalGeneratorB =
      alternatingSixUniversalCoverClassRepresentative 9 := by
  rw [alternatingSixAmbientCanonicalGeneratorB_eq_coordinateB]
  rfl

/-- The distinguished central generator is checked class representative
`1`. -/
theorem alternatingSixAmbientCanonicalCentralGenerator_eq_classRepresentative :
    alternatingSixAmbientCanonicalCentralGenerator =
      alternatingSixUniversalCoverClassRepresentative 1 := by
  rw [alternatingSixAmbientCanonicalCentralGenerator,
    alternatingSixAmbientCanonicalGeneratorA_eq_coordinateA]
  simpa only [alternatingSixUniversalCoverClassRepresentative, map_pow] using
    congrArg
      alternatingSixSchurCoordinatesEquivUniversalCover
      (show
        alternatingSixSchurCoordinateA ^ 2 =
          alternatingSixSchurClassRepresentative 1 by
        decide)

/-- The canonical `AB` test element is checked class representative `15`. -/
theorem alternatingSixAmbientCanonicalGeneratorAB_eq_classRepresentative :
    alternatingSixAmbientCanonicalGeneratorAB =
      alternatingSixUniversalCoverClassRepresentative 15 := by
  rw [alternatingSixAmbientCanonicalGeneratorAB,
    alternatingSixAmbientCanonicalGeneratorA_eq_coordinateA,
    alternatingSixAmbientCanonicalGeneratorB_eq_coordinateB]
  simpa only [alternatingSixUniversalCoverClassRepresentative, map_mul] using
    congrArg
    alternatingSixSchurCoordinatesEquivUniversalCover
    (show
      alternatingSixSchurCoordinateA *
          alternatingSixSchurCoordinateB =
        alternatingSixSchurClassRepresentative 15 by
      decide)

/-- The canonical `AB²` test element is checked class representative `21`. -/
theorem
    alternatingSixAmbientCanonicalGeneratorABSquared_eq_classRepresentative :
    alternatingSixAmbientCanonicalGeneratorABSquared =
      alternatingSixUniversalCoverClassRepresentative 21 := by
  rw [alternatingSixAmbientCanonicalGeneratorABSquared,
    alternatingSixAmbientCanonicalGeneratorA_eq_coordinateA,
    alternatingSixAmbientCanonicalGeneratorB_eq_coordinateB]
  simpa only [alternatingSixUniversalCoverClassRepresentative, map_mul] using
    congrArg
    alternatingSixSchurCoordinatesEquivUniversalCover
    (show
      alternatingSixSchurCoordinateA *
            alternatingSixSchurCoordinateB *
          alternatingSixSchurCoordinateB =
        alternatingSixSchurClassRepresentative 21 by
      decide)

/-- The positive state-77 separator belongs to checked class `28`.

Its coordinate is `⟨77, 3⟩`, whereas the advertised representative is
`⟨77, 1⟩`, so these elements are conjugate but not literally equal. -/
theorem alternatingSixAmbientCanonicalSeparator_classIndex :
    alternatingSixUniversalCoverClassIndex
        alternatingSixAmbientCanonicalSeparator = 28 := by
  rw [alternatingSixAmbientCanonicalSeparator,
    alternatingSixAmbientCanonicalGeneratorA_eq_coordinateA,
    alternatingSixAmbientCanonicalGeneratorB_eq_coordinateB]
  simp only [alternatingSixUniversalCoverClassIndex, map_mul,
    MulEquiv.symm_apply_apply]
  decide

/-- The positive state-79 separator belongs to checked class `30`.

Its coordinate is `⟨79, 3⟩`, whereas the advertised representative is
`⟨79, 1⟩`, so these elements are conjugate but not literally equal. -/
theorem
    alternatingSixAmbientCanonicalSecondSeparator_classIndex :
    alternatingSixUniversalCoverClassIndex
        alternatingSixAmbientCanonicalSecondSeparator = 30 := by
  rw [alternatingSixAmbientCanonicalSecondSeparator,
    alternatingSixAmbientCanonicalGeneratorA_eq_coordinateA,
    alternatingSixAmbientCanonicalGeneratorB_eq_coordinateB]
  simp only [alternatingSixUniversalCoverClassIndex, map_mul,
    MulEquiv.symm_apply_apply]
  decide

end InductiveMcKay
end McKayConjecture
