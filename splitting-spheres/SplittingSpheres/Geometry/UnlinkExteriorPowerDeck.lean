/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.UnlinkExteriorPowerCover
public import SplittingSpheres.Geometry.UnlinkDeckZMod

/-!
# Deck transformations over the compact coordinate exterior

Multiplying the power coordinate by an `m`-th root of unity preserves the pullback over the
closed radius-`1/8` exterior.  We construct the resulting homeomorphisms, compare them exactly
with the action on the strict-complement pullback, and prove fiberwise simple transitivity.

The action exists on the raw pullback for every `m`; its `ZMod m` indexing is stated only when
`m` is nonzero.  No smooth structure on the compact exterior is asserted.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SplittingSpheres

/-- Include the closed-exterior power pullback into the corresponding strict-complement
pullback. -/
def coordinateUnlinkExteriorEighthPowerPullbackToComplement (m : ℕ) :
    CoordinateUnlinkExteriorEighthPowerPullback m → StandardUnlinkPowerPullback m :=
  fun z ↦ ⟨(coordinateUnlinkExteriorToComplement (by norm_num) z.1.1, z.1.2), z.2⟩

@[simp]
theorem coordinateUnlinkExteriorEighthPowerPullbackToComplement_base (m : ℕ)
    (z : CoordinateUnlinkExteriorEighthPowerPullback m) :
    (coordinateUnlinkExteriorEighthPowerPullbackToComplement m z).1.1 =
      coordinateUnlinkExteriorToComplement (by norm_num) z.1.1 :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorEighthPowerPullbackToComplement_powerCoordinate
    (m : ℕ) (z : CoordinateUnlinkExteriorEighthPowerPullback m) :
    (coordinateUnlinkExteriorEighthPowerPullbackToComplement m z).1.2 = z.1.2 :=
  rfl

theorem continuous_coordinateUnlinkExteriorEighthPowerPullbackToComplement (m : ℕ) :
    Continuous (coordinateUnlinkExteriorEighthPowerPullbackToComplement m) := by
  apply Continuous.subtype_mk
  exact (continuous_coordinateUnlinkExteriorToComplement (by norm_num)).comp
      (continuous_fst.comp continuous_subtype_val) |>.prodMk
    (continuous_snd.comp continuous_subtype_val)

theorem coordinateUnlinkExteriorEighthPowerPullbackToComplement_injective (m : ℕ) :
    Injective (coordinateUnlinkExteriorEighthPowerPullbackToComplement m) := by
  intro z w h
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext (congrArg (fun q : StandardUnlinkPowerPullback m ↦ q.1.1.1) h)
  · exact congrArg (fun q : StandardUnlinkPowerPullback m ↦ q.1.2) h

/-- Multiply the exterior-pullback power coordinate by an `m`-th root of unity. -/
def coordinateUnlinkExteriorEighthPowerDeckMap (m : ℕ) (u : rootsOfUnity m ℂ)
    (z : CoordinateUnlinkExteriorEighthPowerPullback m) :
    CoordinateUnlinkExteriorEighthPowerPullback m :=
  ⟨(z.1.1, ⟨((u.1 : ℂˣ) : ℂ) * z.1.2.1,
      mul_ne_zero (Units.ne_zero u.1) z.1.2.2⟩), by
    apply Subtype.ext
    change (coordinateUnlinkExteriorEighthRightNormalMap z.1.1 : ℂ) =
      (((u.1 : ℂˣ) : ℂ) * z.1.2.1) ^ m
    rw [mul_pow, (mem_rootsOfUnity' m u.1).mp u.2, one_mul]
    exact congrArg Subtype.val z.2⟩

theorem coordinateUnlinkExteriorEighthPowerDeckMap_one (m : ℕ)
    (z : CoordinateUnlinkExteriorEighthPowerPullback m) :
    coordinateUnlinkExteriorEighthPowerDeckMap m 1 z = z := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change (1 : ℂ) * z.1.2.1 = z.1.2.1
    exact one_mul _

theorem coordinateUnlinkExteriorEighthPowerDeckMap_mul (m : ℕ)
    (u v : rootsOfUnity m ℂ) (z : CoordinateUnlinkExteriorEighthPowerPullback m) :
    coordinateUnlinkExteriorEighthPowerDeckMap m (u * v) z =
      coordinateUnlinkExteriorEighthPowerDeckMap m u
        (coordinateUnlinkExteriorEighthPowerDeckMap m v z) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change ((((u * v).1 : ℂˣ) : ℂ) * z.1.2.1) =
      ((u.1 : ℂˣ) : ℂ) * (((v.1 : ℂˣ) : ℂ) * z.1.2.1)
    rw [Subgroup.coe_mul, Units.val_mul]
    exact mul_assoc _ _ _

instance coordinateUnlinkExteriorEighthPowerPullbackMulAction (m : ℕ) :
    MulAction (rootsOfUnity m ℂ) (CoordinateUnlinkExteriorEighthPowerPullback m) where
  smul := coordinateUnlinkExteriorEighthPowerDeckMap m
  one_smul := coordinateUnlinkExteriorEighthPowerDeckMap_one m
  mul_smul := coordinateUnlinkExteriorEighthPowerDeckMap_mul m

theorem continuous_coordinateUnlinkExteriorEighthPowerDeckMap (m : ℕ)
    (u : rootsOfUnity m ℂ) :
    Continuous (coordinateUnlinkExteriorEighthPowerDeckMap m u) := by
  unfold coordinateUnlinkExteriorEighthPowerDeckMap
  apply Continuous.subtype_mk
  exact (continuous_fst.comp continuous_subtype_val).prodMk <|
    (continuous_const.mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _

/-- The displayed root-of-unity deck homeomorphism of the closed-exterior pullback. -/
def coordinateUnlinkExteriorEighthPowerDeckHomeomorph (m : ℕ)
    (u : rootsOfUnity m ℂ) :
    CoordinateUnlinkExteriorEighthPowerPullback m ≃ₜ
      CoordinateUnlinkExteriorEighthPowerPullback m where
  toFun := (u • ·)
  invFun := (u⁻¹ • ·)
  left_inv z := inv_smul_smul u z
  right_inv z := smul_inv_smul u z
  continuous_toFun := continuous_coordinateUnlinkExteriorEighthPowerDeckMap m u
  continuous_invFun := continuous_coordinateUnlinkExteriorEighthPowerDeckMap m u⁻¹

/-- The exterior action is the restriction of the strict-complement action. -/
theorem coordinateUnlinkExteriorEighthPowerPullbackToComplement_smul
    (m : ℕ) (u : rootsOfUnity m ℂ)
    (z : CoordinateUnlinkExteriorEighthPowerPullback m) :
    coordinateUnlinkExteriorEighthPowerPullbackToComplement m (u • z) =
      u • coordinateUnlinkExteriorEighthPowerPullbackToComplement m z :=
  rfl

/-- The displayed exterior deck homeomorphisms form a group homomorphism. -/
def coordinateUnlinkExteriorEighthPowerDeckHom (m : ℕ) :
    rootsOfUnity m ℂ →*
      Homeomorph (CoordinateUnlinkExteriorEighthPowerPullback m)
        (CoordinateUnlinkExteriorEighthPowerPullback m) where
  toFun := coordinateUnlinkExteriorEighthPowerDeckHomeomorph m
  map_one' := by
    apply Homeomorph.ext
    exact coordinateUnlinkExteriorEighthPowerDeckMap_one m
  map_mul' u v := by
    apply Homeomorph.ext
    exact coordinateUnlinkExteriorEighthPowerDeckMap_mul m u v

/-- Two points over the same closed-exterior point differ by a unique displayed deck action. -/
theorem existsUnique_coordinateUnlinkExteriorEighthPowerDeck_smul_eq (m : ℕ)
    (z w : CoordinateUnlinkExteriorEighthPowerPullback m)
    (hbase : coordinateUnlinkExteriorEighthPowerPullbackProj m z =
      coordinateUnlinkExteriorEighthPowerPullbackProj m w) :
    ∃! u : rootsOfUnity m ℂ, u • z = w := by
  let iz := coordinateUnlinkExteriorEighthPowerPullbackToComplement m z
  let iw := coordinateUnlinkExteriorEighthPowerPullbackToComplement m w
  have hibase : standardUnlinkPowerPullbackProj m iz =
      standardUnlinkPowerPullbackProj m iw := by
    exact congrArg (coordinateUnlinkExteriorToComplement (by norm_num)) hbase
  obtain ⟨u, hu, hu_unique⟩ :=
    existsUnique_standardUnlinkPowerDeck_smul_eq m iz iw hibase
  dsimp [iz, iw] at hu hu_unique
  refine ⟨u, ?_, ?_⟩
  · apply coordinateUnlinkExteriorEighthPowerPullbackToComplement_injective m
    rw [coordinateUnlinkExteriorEighthPowerPullbackToComplement_smul]
    exact hu
  · intro v hv
    apply hu_unique
    exact (coordinateUnlinkExteriorEighthPowerPullbackToComplement_smul m v z).symm.trans
      (congrArg (coordinateUnlinkExteriorEighthPowerPullbackToComplement m) hv)

/-- For nonzero degree, index the exterior deck homeomorphisms by the explicit standard
`ZMod m` character. -/
def coordinateUnlinkExteriorEighthPowerDeckZModHom (m : ℕ) [NeZero m] :
    Multiplicative (ZMod m) →*
      Homeomorph (CoordinateUnlinkExteriorEighthPowerPullback m)
        (CoordinateUnlinkExteriorEighthPowerPullback m) :=
  (coordinateUnlinkExteriorEighthPowerDeckHom m).comp
    (standardRootsOfUnityZModMulEquiv m).toMonoidHom

end SplittingSpheres
