/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.UnlinkExteriorPowerDeck
public import SplittingSpheres.Geometry.UnlinkPowerFactorZMod

/-!
# Factor maps between power covers of the compact coordinate exterior

For `n = m * q`, raising the power coordinate to `q` defines the corresponding factor map on
the closed radius-`1/8` exterior.  The map is the literal restriction of the strict-complement
factor map, so its identity, composition, and deck-equivariance laws agree exactly.

Only point-set continuity is asserted; no smooth boundary structure is used.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SplittingSpheres

/-- Raise the exterior-pullback power coordinate to the quotient exponent. -/
def coordinateUnlinkExteriorEighthPowerFactorMap {n m q : ℕ}
    (hnm : n = m * q) (z : CoordinateUnlinkExteriorEighthPowerPullback n) :
    CoordinateUnlinkExteriorEighthPowerPullback m :=
  ⟨(z.1.1, ⟨z.1.2.1 ^ q, pow_ne_zero q z.1.2.2⟩), by
    apply Subtype.ext
    change (coordinateUnlinkExteriorEighthRightNormalMap z.1.1 : ℂ) =
      (z.1.2.1 ^ q) ^ m
    calc
      (coordinateUnlinkExteriorEighthRightNormalMap z.1.1 : ℂ) = z.1.2.1 ^ n :=
        congrArg Subtype.val z.2
      _ = z.1.2.1 ^ (q * m) :=
        congrArg (fun e : ℕ ↦ z.1.2.1 ^ e)
          (hnm.trans (Nat.mul_comm m q))
      _ = (z.1.2.1 ^ q) ^ m := pow_mul _ _ _⟩

@[simp]
theorem coordinateUnlinkExteriorEighthPowerFactorMap_proj {n m q : ℕ}
    (hnm : n = m * q) (z : CoordinateUnlinkExteriorEighthPowerPullback n) :
    coordinateUnlinkExteriorEighthPowerPullbackProj m
        (coordinateUnlinkExteriorEighthPowerFactorMap hnm z) =
      coordinateUnlinkExteriorEighthPowerPullbackProj n z :=
  rfl

theorem continuous_coordinateUnlinkExteriorEighthPowerFactorMap
    {n m q : ℕ} (hnm : n = m * q) :
    Continuous (coordinateUnlinkExteriorEighthPowerFactorMap hnm) := by
  unfold coordinateUnlinkExteriorEighthPowerFactorMap
  apply Continuous.subtype_mk
  have hbase : Continuous
      (fun z : CoordinateUnlinkExteriorEighthPowerPullback n ↦ z.1.1) :=
    continuous_fst.comp continuous_subtype_val
  have hcoordinate : Continuous
      (fun z : CoordinateUnlinkExteriorEighthPowerPullback n ↦ z.1.2.1) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
  exact hbase.prodMk ((hcoordinate.pow q).subtype_mk _)

/-- Inclusion into the strict-complement pullback commutes literally with factor maps. -/
@[simp]
theorem coordinateUnlinkExteriorEighthPowerPullbackToComplement_factor
    {n m q : ℕ} (hnm : n = m * q)
    (z : CoordinateUnlinkExteriorEighthPowerPullback n) :
    coordinateUnlinkExteriorEighthPowerPullbackToComplement m
        (coordinateUnlinkExteriorEighthPowerFactorMap hnm z) =
      standardUnlinkPowerFactorMap hnm
        (coordinateUnlinkExteriorEighthPowerPullbackToComplement n z) :=
  rfl

/-- Factoring by exponent one is the identity on the exterior pullback. -/
@[simp]
theorem coordinateUnlinkExteriorEighthPowerFactorMap_one
    (m : ℕ) (hmm : m = m * 1)
    (z : CoordinateUnlinkExteriorEighthPowerPullback m) :
    coordinateUnlinkExteriorEighthPowerFactorMap hmm z = z := by
  apply coordinateUnlinkExteriorEighthPowerPullbackToComplement_injective m
  rw [coordinateUnlinkExteriorEighthPowerPullbackToComplement_factor,
    standardUnlinkPowerFactorMap_one]

/-- Exterior factor maps compose in the same order as their quotient exponents. -/
theorem coordinateUnlinkExteriorEighthPowerFactorMap_comp_apply
    {n m k q r : ℕ} (hnm : n = m * q) (hmk : m = k * r)
    (z : CoordinateUnlinkExteriorEighthPowerPullback n) :
    coordinateUnlinkExteriorEighthPowerFactorMap hmk
        (coordinateUnlinkExteriorEighthPowerFactorMap hnm z) =
      coordinateUnlinkExteriorEighthPowerFactorMap
        (standardUnlinkPowerFactor_degree_comp hnm hmk) z := by
  apply coordinateUnlinkExteriorEighthPowerPullbackToComplement_injective k
  rw [coordinateUnlinkExteriorEighthPowerPullbackToComplement_factor,
    coordinateUnlinkExteriorEighthPowerPullbackToComplement_factor,
    coordinateUnlinkExteriorEighthPowerPullbackToComplement_factor,
    standardUnlinkPowerFactorMap_comp_apply]

/-- The exterior factor map is equivariant for the displayed roots-of-unity deck actions. -/
theorem coordinateUnlinkExteriorEighthPowerFactorMap_deck_equivariant
    {n m q : ℕ} (hnm : n = m * q) (u : rootsOfUnity n ℂ)
    (z : CoordinateUnlinkExteriorEighthPowerPullback n) :
    coordinateUnlinkExteriorEighthPowerFactorMap hnm (u • z) =
      standardUnlinkRootsOfUnityFactorHom hnm u •
        coordinateUnlinkExteriorEighthPowerFactorMap hnm z := by
  apply coordinateUnlinkExteriorEighthPowerPullbackToComplement_injective m
  rw [coordinateUnlinkExteriorEighthPowerPullbackToComplement_factor,
    coordinateUnlinkExteriorEighthPowerPullbackToComplement_smul,
    standardUnlinkPowerFactorMap_deck_equivariant,
    coordinateUnlinkExteriorEighthPowerPullbackToComplement_smul,
    coordinateUnlinkExteriorEighthPowerPullbackToComplement_factor]

/-- Under the common standard index, exterior factor maps reduce `ZMod n` to `ZMod m`. -/
theorem coordinateUnlinkExteriorEighthPowerFactorMap_deckZMod_equivariant
    {n m q : ℕ} [NeZero n] [NeZero m] (hnm : n = m * q)
    (a : Multiplicative (ZMod n))
    (z : CoordinateUnlinkExteriorEighthPowerPullback n) :
    coordinateUnlinkExteriorEighthPowerFactorMap hnm
        (coordinateUnlinkExteriorEighthPowerDeckZModHom n a z) =
      coordinateUnlinkExteriorEighthPowerDeckZModHom m
          (standardUnlinkPowerFactorZModHom hnm a)
        (coordinateUnlinkExteriorEighthPowerFactorMap hnm z) := by
  change coordinateUnlinkExteriorEighthPowerFactorMap hnm
      (standardRootsOfUnityZModMulEquiv n a • z) =
    standardRootsOfUnityZModMulEquiv m
        (standardUnlinkPowerFactorZModHom hnm a) •
      coordinateUnlinkExteriorEighthPowerFactorMap hnm z
  rw [coordinateUnlinkExteriorEighthPowerFactorMap_deck_equivariant,
    standardUnlinkRootsOfUnityFactorHom_standardZMod]

end SplittingSpheres
