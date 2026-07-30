/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOrdinaryRowAutomorphismTransport
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientOuterRowActionData

/-!
# Degree and central-scalar signatures under outer transport

An automorphism that inverts the distinguished central generator preserves
ordinary-row dimension and applies the explicit scalar-pattern involution.
These two signatures reduce every `A₆` outer-row calculation to at most two
candidate rows.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- Transport by an automorphism whose inverse inverts the distinguished
central generator applies the finite scalar-pattern involution. -/
theorem alternatingSixAmbientOrdinaryRowAutomorphismAction_scalarPattern
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (a : MulAut AlternatingSixUniversalCover)
    (hcentral :
      a.symm alternatingSixAmbientCanonicalCentralGenerator =
        alternatingSixAmbientCanonicalCentralGenerator⁻¹)
    (row : AlternatingSixAmbientOrdinaryRow) :
    (alternatingSixAmbientOrdinaryRowAutomorphismAction T a row).scalarPattern =
      alternatingSixAmbientOuterScalarPattern row.scalarPattern := by
  let target :=
    alternatingSixAmbientOrdinaryRowAutomorphismAction T a row
  have hvalue :=
    congrArg
      (fun χ : IrreducibleCharacter AlternatingSixUniversalCover ↦
        χ.values alternatingSixAmbientCanonicalCentralGenerator)
      (alternatingSixAmbientOrdinaryRowAutomorphismAction_character
        T a row)
  rw [
    T.character_values_centralGenerator,
    IrreducibleCharacter.smul_values,
    hcentral,
    alternatingSixAmbientOrdinaryCharacter_values_centralGenerator_inv
  ] at hvalue
  have hdimension :
      target.dimension = row.dimension :=
    alternatingSixAmbientOrdinaryRowAutomorphismAction_dimension
      T a row
  rw [hdimension] at hvalue
  have hscalar :
      alternatingSixComplexCyclotomicRoot ^
          target.scalarPattern.exponent 0 =
        (alternatingSixComplexCyclotomicRoot ^
          row.scalarPattern.exponent 0)⁻¹ :=
    mul_left_cancel₀
      (Nat.cast_ne_zero.mpr row.dimension_pos.ne')
      hvalue
  apply AlternatingSixAmbientScalarPattern.firstScalar_injective
  exact hscalar.trans
    (alternatingSixAmbientOuterScalarPattern_firstScalar
      row.scalarPattern).symm

end InductiveMcKay
end McKayConjecture
