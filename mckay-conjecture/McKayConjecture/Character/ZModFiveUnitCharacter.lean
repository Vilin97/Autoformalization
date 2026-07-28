/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic

/-!
# A faithful complex character of `(ZMod 5)ˣ`

The unit `2` generates `(ZMod 5)ˣ`.  We record its discrete logarithm in
`ZMod 4` and compose with the standard circle character.  In particular,
the unit `4 = 2²` is sent to `-1`; this is the scalar correction needed
for the `GL(2,5)` central cover.
-/

noncomputable section

namespace McKayConjecture

/-- The units `2` and `4` in `ZMod 5`, with computational inverses. -/
def zmodFiveUnitTwo : (ZMod 5)ˣ :=
  ⟨2, 3, by native_decide, by native_decide⟩

def zmodFiveUnitFour : (ZMod 5)ˣ :=
  ⟨4, 4, by native_decide, by native_decide⟩

/-- Discrete logarithm to the base `2`, written multiplicatively. -/
def zmodFiveUnitLog :
    (ZMod 5)ˣ →* Multiplicative (ZMod 4) where
  toFun u :=
    Multiplicative.ofAdd
      (match u.1.val with
      | 1 => 0
      | 2 => 1
      | 3 => 3
      | 4 => 2
      | _ => 0)
  map_one' := by native_decide
  map_mul' := by native_decide

/-- The chosen unit `2` generates all four units of `ZMod 5`. -/
theorem zmodFiveUnit_eq_two_pow
    (u : (ZMod 5)ˣ) :
    ∃ n : Fin 4, zmodFiveUnitTwo ^ n.val = u := by
  revert u
  native_decide

/-- The standard frequency-one complex unit character of `ZMod 4`. -/
def zmodFourFrequencyOneComplexUnitCharacter :
    Multiplicative (ZMod 4) →* ℂˣ where
  toFun z :=
    Circle.toUnits
      (ZMod.toCircle (Multiplicative.toAdd z))
  map_one' := by
    apply Units.ext
    simp
  map_mul' z w := by
    apply Units.ext
    change
      (ZMod.toCircle
          (Multiplicative.toAdd z +
            Multiplicative.toAdd w) : ℂ) =
        (ZMod.toCircle (Multiplicative.toAdd z) : ℂ) *
          (ZMod.toCircle (Multiplicative.toAdd w) : ℂ)
    rw [AddChar.map_add_eq_mul]
    exact map_mul Circle.coeHom _ _

/-- A faithful complex unit character of `(ZMod 5)ˣ`. -/
def zmodFiveComplexUnitCharacter :
    (ZMod 5)ˣ →* ℂˣ :=
  zmodFourFrequencyOneComplexUnitCharacter.comp
    zmodFiveUnitLog

@[simp]
theorem zmodFiveComplexUnitCharacter_one :
    zmodFiveComplexUnitCharacter 1 = 1 := by
  exact map_one zmodFiveComplexUnitCharacter

@[simp]
theorem zmodFiveComplexUnitCharacter_four :
    zmodFiveComplexUnitCharacter zmodFiveUnitFour = -1 := by
  apply Units.ext
  change
    ((ZMod.toCircle (2 : ZMod 4) : Circle) : ℂ) = -1
  calc
    _ = Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * (2 : ℂ) / (4 : ℂ)) :=
      ZMod.toCircle_natCast (N := 4) 2
    _ = -1 := by
      convert Complex.exp_pi_mul_I using 1 <;> ring_nf

end McKayConjecture
