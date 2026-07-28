/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.LinearCombination
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasDegreeTwelveTraceSeparation
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientAtlasTwelvePowerTwoClassMatrixCertificate

/-!
# Short matrix-word traces for the ATLAS degree-twelve power-2 row

These exact calculations cover the two generators and the words `ab` and
`ab²` among the seven class-representative base words.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

local notation "ζ" => alternatingSixComplexCyclotomicRoot

macro "close_atlas_twelve_power_two_short_trace" q:term : tactic =>
  `(tactic|
    first
    | linear_combination
        ($q) * alternatingSixComplexCyclotomicRoot_relation
    | linear_combination
        (-($q)) * alternatingSixComplexCyclotomicRoot_relation)

/-- Trace of the ATLAS power-2 first generator. -/
theorem alternatingSixAmbientAtlasTwelvePowerTwo_matrixA_trace :
    alternatingSixFiveAmbient_atlas12Power2_matrixA.trace = 0 := by
  change
    (∑ i : Fin 12,
      alternatingSixFiveAmbient_atlas12Power2_matrixA i i) = 0
  simp [alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  ring

/-- Trace of the ATLAS power-2 second generator. -/
theorem alternatingSixAmbientAtlasTwelvePowerTwo_matrixB_trace :
    alternatingSixFiveAmbient_atlas12Power2_matrixB.trace = 0 := by
  change
    (∑ i : Fin 12,
      alternatingSixFiveAmbient_atlas12Power2_matrixB i i) = 0
  simp [alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]

/-- Trace of the ATLAS power-2 word `ab`. -/
theorem alternatingSixAmbientAtlasTwelvePowerTwo_matrixAB_trace :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA *
          alternatingSixFiveAmbient_atlas12Power2_matrixB).trace =
      alternatingSixCyclotomicValue
        [(-1, 0), (-1, 4), (1, 16), (1, 20)] :=
  alternatingSixAmbientAtlas12Power2_matrixAB_trace

/-- Trace of the ATLAS power-2 word `ab²`. -/
theorem alternatingSixAmbientAtlasTwelvePowerTwo_matrixABSquared_trace :
    (alternatingSixFiveAmbient_atlas12Power2_matrixA *
          alternatingSixFiveAmbient_atlas12Power2_matrixB ^ 2).trace =
      alternatingSixCyclotomicValue
        [(-1, 0), (-1, 4), (1, 8), (1, 12),
          (1, 16), (-1, 28)] := by
  change
    (∑ i : Fin 12,
      (alternatingSixFiveAmbient_atlas12Power2_matrixA *
        alternatingSixFiveAmbient_atlas12Power2_matrixB ^ 2) i i) = _
  simp only [pow_two]
  simp_rw [Matrix.mul_apply]
  simp [alternatingSixFiveAmbient_atlas12Power2_matrixA,
    alternatingSixFiveAmbient_atlas12Power2_matrixB,
    alternatingSixCyclotomicValue, Fin.sum_univ_succ]
  close_atlas_twelve_power_two_short_trace
    ((2 : ℂ) - ζ ^ 4 + 2 * ζ ^ 8 + ζ ^ 12 -
      ζ ^ 16 - ζ ^ 20 - ζ ^ 32 + ζ ^ 36)

end InductiveMcKay
end McKayConjecture
