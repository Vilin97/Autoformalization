/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.UnlinkExteriorPowerFactor
public import SplittingSpheres.Handlebody.CoordinateExteriorPowerDeck

/-!
# Factor maps on the coordinate-exterior pushout covers

The divisibility factor maps on the literal closed exterior transport through the total-space
homeomorphisms to the one-handle/punctured-cap pushout covers.  Projection, composition, and deck
equivariance are retained exactly.  This supplies the point-set factor system required before a
future graph-thickening comparison; it does not itself identify the total spaces as handlebodies.
-/

@[expose] public section

noncomputable section

open Function Topology

namespace SplittingSpheres

/-- Transport the degree factor map to the power pullbacks over the exterior pushout. -/
def coordinateUnlinkExteriorPushoutPowerFactorMap {n m q : ℕ}
    (hnm : n = m * q) (z : CoordinateUnlinkExteriorPushoutPowerPullback n) :
    CoordinateUnlinkExteriorPushoutPowerPullback m :=
  (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m).symm
    (coordinateUnlinkExteriorEighthPowerFactorMap hnm
      (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph n z))

theorem continuous_coordinateUnlinkExteriorPushoutPowerFactorMap
    {n m q : ℕ} (hnm : n = m * q) :
    Continuous (coordinateUnlinkExteriorPushoutPowerFactorMap hnm) :=
  (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m).symm.continuous.comp
    ((continuous_coordinateUnlinkExteriorEighthPowerFactorMap hnm).comp
      (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph n).continuous)

/-- The total-space homeomorphisms commute exactly with the transported factor maps. -/
@[simp]
theorem coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_factor
    {n m q : ℕ} (hnm : n = m * q)
    (z : CoordinateUnlinkExteriorPushoutPowerPullback n) :
    coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m
        (coordinateUnlinkExteriorPushoutPowerFactorMap hnm z) =
      coordinateUnlinkExteriorEighthPowerFactorMap hnm
        (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph n z) :=
  (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m).apply_symm_apply _

/-- The transported factor map lies over the identity of the exterior pushout. -/
@[simp]
theorem coordinateUnlinkExteriorPushoutPowerFactorMap_proj
    {n m q : ℕ} (hnm : n = m * q)
    (z : CoordinateUnlinkExteriorPushoutPowerPullback n) :
    coordinateUnlinkExteriorPushoutPowerPullbackProj m
        (coordinateUnlinkExteriorPushoutPowerFactorMap hnm z) =
      coordinateUnlinkExteriorPushoutPowerPullbackProj n z := by
  apply coordinateUnlinkExteriorOneEighthHomeomorph.injective
  rw [← coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_proj,
    ← coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_proj,
    coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_factor,
    coordinateUnlinkExteriorEighthPowerFactorMap_proj]

/-- Factoring the pushout cover by exponent one is the identity. -/
@[simp]
theorem coordinateUnlinkExteriorPushoutPowerFactorMap_one
    (m : ℕ) (hmm : m = m * 1)
    (z : CoordinateUnlinkExteriorPushoutPowerPullback m) :
    coordinateUnlinkExteriorPushoutPowerFactorMap hmm z = z := by
  apply (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m).injective
  rw [coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_factor,
    coordinateUnlinkExteriorEighthPowerFactorMap_one]

/-- Transported factor maps compose in quotient-exponent order. -/
theorem coordinateUnlinkExteriorPushoutPowerFactorMap_comp_apply
    {n m k q r : ℕ} (hnm : n = m * q) (hmk : m = k * r)
    (z : CoordinateUnlinkExteriorPushoutPowerPullback n) :
    coordinateUnlinkExteriorPushoutPowerFactorMap hmk
        (coordinateUnlinkExteriorPushoutPowerFactorMap hnm z) =
      coordinateUnlinkExteriorPushoutPowerFactorMap
        (standardUnlinkPowerFactor_degree_comp hnm hmk) z := by
  apply (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph k).injective
  rw [coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_factor,
    coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_factor,
    coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_factor,
    coordinateUnlinkExteriorEighthPowerFactorMap_comp_apply]

/-- The transported factor maps are equivariant for the standard `ZMod` deck indices. -/
theorem coordinateUnlinkExteriorPushoutPowerFactorMap_deckZMod_equivariant
    {n m q : ℕ} [NeZero n] [NeZero m] (hnm : n = m * q)
    (a : Multiplicative (ZMod n))
    (z : CoordinateUnlinkExteriorPushoutPowerPullback n) :
    coordinateUnlinkExteriorPushoutPowerFactorMap hnm
        (coordinateUnlinkExteriorPushoutPowerDeckZModHom n a z) =
      coordinateUnlinkExteriorPushoutPowerDeckZModHom m
          (standardUnlinkPowerFactorZModHom hnm a)
        (coordinateUnlinkExteriorPushoutPowerFactorMap hnm z) := by
  apply (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m).injective
  change coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m
      (coordinateUnlinkExteriorPushoutPowerFactorMap hnm
        (standardRootsOfUnityZModMulEquiv n a • z)) =
    coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m
      (standardRootsOfUnityZModMulEquiv m
          (standardUnlinkPowerFactorZModHom hnm a) •
        coordinateUnlinkExteriorPushoutPowerFactorMap hnm z)
  rw [coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_factor,
    coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_smul,
    coordinateUnlinkExteriorEighthPowerFactorMap_deck_equivariant,
    standardUnlinkRootsOfUnityFactorHom_standardZMod,
    coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_smul,
    coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_factor]

end SplittingSpheres
