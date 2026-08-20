/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.UnlinkDeckZMod
public import SplittingSpheres.Geometry.UnlinkPowerFactor

/-!
# Compatible cyclic indices for unlink power-cover factors

The factor from degree `n = m * q` raises the power coordinate to the `q`-th power.  Using the
explicit standard circle characters, this file identifies its map on displayed deck groups with
reduction `ZMod n → ZMod m`.  The explicit character is essential: an arbitrary cyclic-group
equivalence need not commute with the factor maps.
-/

@[expose] public section

noncomputable section

namespace SplittingSpheres

/-- Reduction modulo `m`, regarded multiplicatively, for an explicit equation `n = m * q`. -/
def standardUnlinkPowerFactorZModHom {n m q : ℕ} (hnm : n = m * q) :
    Multiplicative (ZMod n) →* Multiplicative (ZMod m) :=
  (ZMod.castHom ⟨q, hnm⟩ (ZMod m)).toAddMonoidHom.toMultiplicative

@[simp]
theorem standardUnlinkPowerFactorZModHom_apply {n m q : ℕ}
    (hnm : n = m * q) (a : ZMod n) :
    (standardUnlinkPowerFactorZModHom hnm (Multiplicative.ofAdd a)).toAdd =
      ZMod.cast a :=
  rfl

/-- The standard complex root indexed by `1 : ZMod n`, raised to `q`, is the standard root
indexed by `1 : ZMod m`. -/
theorem standardUnlinkRootsOfUnityFactorHom_generator {n m q : ℕ}
    [NeZero n] [NeZero m] (hnm : n = m * q) :
    standardUnlinkRootsOfUnityFactorHom hnm
        (standardRootsOfUnityZModMulEquiv n (Multiplicative.ofAdd 1)) =
      standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd 1) := by
  have hnroot :
      (((standardRootsOfUnityZModMulEquiv n (Multiplicative.ofAdd 1)).1 : ℂˣ) : ℂ) =
        Complex.exp (2 * Real.pi * Complex.I * (1 : ℕ) / n) := by
    change ((ZMod.toCircle (N := n) (1 : ZMod n) : Circle) : ℂ) = _
    simpa using (ZMod.toCircle_natCast (N := n) 1)
  have hmroot :
      (((standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd 1)).1 : ℂˣ) : ℂ) =
        Complex.exp (2 * Real.pi * Complex.I * (1 : ℕ) / m) := by
    change ((ZMod.toCircle (N := m) (1 : ZMod m) : Circle) : ℂ) = _
    simpa using (ZMod.toCircle_natCast (N := m) 1)
  apply Subtype.ext
  rw [standardUnlinkRootsOfUnityFactorHom_coe]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hnroot, hmroot, ← Complex.exp_nat_mul]
  congr 1
  have hq : q ≠ 0 := by
    intro hq
    subst q
    apply NeZero.ne n
    simpa using hnm
  rw [hnm]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr hq, Nat.cast_ne_zero.mpr (NeZero.ne m)]

/-- Under the explicit standard character identifications, the roots-of-unity factor homomorphism
is exactly reduction modulo `m`. -/
theorem standardUnlinkRootsOfUnityFactorHom_standardZMod {n m q : ℕ}
    [NeZero n] [NeZero m] (hnm : n = m * q)
    (a : Multiplicative (ZMod n)) :
    standardUnlinkRootsOfUnityFactorHom hnm
        (standardRootsOfUnityZModMulEquiv n a) =
      standardRootsOfUnityZModMulEquiv m
        (standardUnlinkPowerFactorZModHom hnm a) := by
  change standardUnlinkRootsOfUnityFactorHom hnm
      (standardRootsOfUnityZModMulEquiv n
        (Multiplicative.ofAdd a.toAdd)) =
    standardRootsOfUnityZModMulEquiv m
      (standardUnlinkPowerFactorZModHom hnm
        (Multiplicative.ofAdd a.toAdd))
  rw [← ZMod.natCast_zmod_val a.toAdd]
  rw [show Multiplicative.ofAdd (a.toAdd.val : ZMod n) =
      (Multiplicative.ofAdd (1 : ZMod n)) ^ a.toAdd.val by
    apply Multiplicative.ext
    simp]
  rw [map_pow, map_pow, map_pow]
  rw [show standardUnlinkPowerFactorZModHom hnm
      (Multiplicative.ofAdd (1 : ZMod n)) =
        Multiplicative.ofAdd (1 : ZMod m) by
    apply Multiplicative.ext
    exact ZMod.cast_one ⟨q, hnm⟩]
  rw [map_pow]
  rw [standardUnlinkRootsOfUnityFactorHom_generator hnm]

/-- The geometric power-factor map is equivariant for reduction of the common `ZMod` deck
index. -/
theorem standardUnlinkPowerFactorMap_deckZMod_equivariant {n m q : ℕ}
    [NeZero n] [NeZero m] (hnm : n = m * q)
    (a : Multiplicative (ZMod n)) (z : StandardUnlinkPowerPullback n) :
    standardUnlinkPowerFactorMap hnm
        (standardUnlinkPowerDeckZModHom n a z) =
      standardUnlinkPowerDeckZModHom m
          (standardUnlinkPowerFactorZModHom hnm a)
        (standardUnlinkPowerFactorMap hnm z) := by
  change standardUnlinkPowerFactorMap hnm
      (standardRootsOfUnityZModMulEquiv n a • z) =
    standardRootsOfUnityZModMulEquiv m
        (standardUnlinkPowerFactorZModHom hnm a) •
      standardUnlinkPowerFactorMap hnm z
  rw [standardUnlinkPowerFactorMap_deck_equivariant,
    standardUnlinkRootsOfUnityFactorHom_standardZMod]

end SplittingSpheres
