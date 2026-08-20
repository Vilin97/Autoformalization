/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.UnlinkDeckGraphIndex
public import SplittingSpheres.Geometry.UnlinkMeridianCharacter

/-!
# Meridian monodromy in the common `ZMod` deck index

The explicit positive primitive root acquired by the right-meridian lift is exactly the root
indexed by `1 : ZMod m` under the standard circle character.  Thus the two computed meridians
have indices `1` and `0`, matching respectively the advancing and stationary edge labels of the
cyclic rose cover.

These are exact endpoint/action calculations for two explicit loops.  They do not say that the
loops generate the unlink-complement fundamental group or identify that group with a rose.
-/

@[expose] public section

noncomputable section

namespace SplittingSpheres

/-- The primitive root used by the right-meridian lift is the standard character value at
`1 : ZMod m`. -/
theorem standardUnlinkPowerDeckGenerator_eq_standardZMod_one
    (m : ℕ) [NeZero m] :
    standardUnlinkPowerDeckGenerator m =
      standardRootsOfUnityZModMulEquiv m
        (Multiplicative.ofAdd (1 : ZMod m)) := by
  apply Subtype.ext
  apply Units.ext
  rw [standardUnlinkPowerDeckGenerator_coe]
  change Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (m : ℂ)) =
    ((ZMod.toCircle (N := m) (1 : ZMod m) : Circle) : ℂ)
  symm
  simpa [mul_assoc] using (ZMod.toCircle_natCast (N := m) 1)

/-- Exact indexed monodromy law: the positive right meridian advances by `1 : ZMod m`. -/
theorem standardUnlinkRightMeridianLift_one_eq_zmodOne_smul_zero
    (m : ℕ) [NeZero m] (x : Sphere 2) :
    standardUnlinkRightMeridianLift m x 1 =
      standardUnlinkPowerDeckZModHom m
          (Multiplicative.ofAdd (1 : ZMod m))
        (standardUnlinkRightMeridianLift m x 0) := by
  rw [standardUnlinkRightMeridianLift_one_eq_generator_smul_zero,
    standardUnlinkPowerDeckGenerator_eq_standardZMod_one]
  rfl

/-- Exact indexed monodromy law: the left meridian has index `0 : ZMod m`. -/
theorem standardUnlinkLeftMeridianLift_one_eq_zmodZero_smul_zero
    (m : ℕ) [NeZero m] (x : Sphere 2) :
    standardUnlinkLeftMeridianLift m x 1 =
      standardUnlinkPowerDeckZModHom m
          (Multiplicative.ofAdd (0 : ZMod m))
        (standardUnlinkLeftMeridianLift m x 0) := by
  rw [standardUnlinkLeftMeridianLift_one_eq_zero]
  simp

/-- The same index `1` advances every cyclic-rose vertex by one. -/
theorem cyclicRoseCoverDeck_rightMeridianIndex (m : ℕ) [NeZero m]
    (v : ZMod m) :
    cyclicRoseCoverDeckZModHom m
        (Multiplicative.ofAdd (1 : ZMod m)) v = v + 1 :=
  rfl

/-- The same index `0` fixes every cyclic-rose vertex. -/
theorem cyclicRoseCoverDeck_leftMeridianIndex (m : ℕ) [NeZero m]
    (v : ZMod m) :
    cyclicRoseCoverDeckZModHom m
        (Multiplicative.ofAdd (0 : ZMod m)) v = v := by
  simp

end SplittingSpheres
