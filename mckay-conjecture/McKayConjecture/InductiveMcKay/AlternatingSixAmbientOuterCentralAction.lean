/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOuterSelectedClassRepresentatives

/-!
# Central action of the two ambient outer automorphisms

Both audited outer automorphisms negate all six central coordinates.
Transporting that calculation to the canonical cover shows that their
inverses invert the distinguished central generator, as required by the
ordinary-row signature reduction.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

private theorem symm_apply_eq_inv_of_apply_eq_inv
    {G : Type*} [Group G] (a : MulAut G) (z : G)
    (happly : a z = z⁻¹) :
    a.symm z = z⁻¹ := by
  apply a.injective
  rw [a.apply_symm_apply, map_inv, happly, inv_inv]

/-- The first audited automorphism inverts the distinguished central
generator. -/
theorem alternatingSixUniversalCoverAlphaOneAutomorphism_centralGenerator :
    alternatingSixUniversalCoverAlphaOneAutomorphism
        alternatingSixAmbientCanonicalCentralGenerator =
      alternatingSixAmbientCanonicalCentralGenerator⁻¹ := by
  rw [alternatingSixAmbientCanonicalCentralGenerator_eq_classRepresentative,
    alternatingSixUniversalCoverClassRepresentative,
    alternatingSixUniversalCoverAlphaOneAutomorphism_apply_coordinate,
    ← map_inv]
  apply congrArg alternatingSixSchurCoordinatesEquivUniversalCover
  change
    alternatingSixSchurAlphaOneEndomorphism
        (alternatingSixSchurAuditedCoordinate 0 1) =
      (alternatingSixSchurAuditedCoordinate 0 1)⁻¹
  rw [show
    (alternatingSixSchurAuditedCoordinate 0 1)⁻¹ =
      alternatingSixSchurAuditedCoordinate 0 5 by
    decide]
  simpa [alternatingSixSchurAuditedPresentationGeneratorCoordinates,
    alternatingSixSchurAlphaOneGeneratorCoordinates,
    alternatingSixSchurAuditedCoordinate] using
    alternatingSixSchurAlphaOneEndomorphism_generator 2

/-- The inverse of the first audited automorphism also inverts the
distinguished central generator. -/
theorem
    alternatingSixUniversalCoverAlphaOneAutomorphism_symm_centralGenerator :
    alternatingSixUniversalCoverAlphaOneAutomorphism.symm
        alternatingSixAmbientCanonicalCentralGenerator =
      alternatingSixAmbientCanonicalCentralGenerator⁻¹ :=
  symm_apply_eq_inv_of_apply_eq_inv
    alternatingSixUniversalCoverAlphaOneAutomorphism
    alternatingSixAmbientCanonicalCentralGenerator
    alternatingSixUniversalCoverAlphaOneAutomorphism_centralGenerator

/-- The second audited automorphism inverts the distinguished central
generator. -/
theorem alternatingSixUniversalCoverAlphaTwoAutomorphism_centralGenerator :
    alternatingSixUniversalCoverAlphaTwoAutomorphism
        alternatingSixAmbientCanonicalCentralGenerator =
      alternatingSixAmbientCanonicalCentralGenerator⁻¹ := by
  rw [alternatingSixAmbientCanonicalCentralGenerator_eq_classRepresentative,
    alternatingSixUniversalCoverClassRepresentative,
    alternatingSixUniversalCoverAlphaTwoAutomorphism_apply_coordinate,
    ← map_inv]
  apply congrArg alternatingSixSchurCoordinatesEquivUniversalCover
  change
    alternatingSixSchurAlphaTwoEndomorphism
        (alternatingSixSchurAuditedCoordinate 0 1) =
      (alternatingSixSchurAuditedCoordinate 0 1)⁻¹
  rw [show
    (alternatingSixSchurAuditedCoordinate 0 1)⁻¹ =
      alternatingSixSchurAuditedCoordinate 0 5 by
    decide]
  simpa [alternatingSixSchurAuditedPresentationGeneratorCoordinates,
    alternatingSixSchurAlphaTwoGeneratorCoordinates,
    alternatingSixSchurAuditedCoordinate] using
    alternatingSixSchurAlphaTwoEndomorphism_generator 2

/-- The inverse of the second audited automorphism also inverts the
distinguished central generator. -/
theorem
    alternatingSixUniversalCoverAlphaTwoAutomorphism_symm_centralGenerator :
    alternatingSixUniversalCoverAlphaTwoAutomorphism.symm
        alternatingSixAmbientCanonicalCentralGenerator =
      alternatingSixAmbientCanonicalCentralGenerator⁻¹ :=
  symm_apply_eq_inv_of_apply_eq_inv
    alternatingSixUniversalCoverAlphaTwoAutomorphism
    alternatingSixAmbientCanonicalCentralGenerator
    alternatingSixUniversalCoverAlphaTwoAutomorphism_centralGenerator

end InductiveMcKay
end McKayConjecture
