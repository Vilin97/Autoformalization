/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Handlebody.CoordinateExteriorOneHandleCover
public import SplittingSpheres.Handlebody.CoordinateExteriorPowerPushout

/-!
# The coordinate-exterior power cover over the attaching boundary

The explicit trivialization of the power pullback over the whole `S¹ × B³` one-handle
restricts to its literal attaching boundary `S¹ × S²`.  For nonzero degree this identifies the
boundary pullback with another copy of `S¹ × S²`; its projection is degree `m` on the circle and
the identity on the sphere.

The final section records the restricted roots-of-unity deck action and its standard `ZMod m`
index.  All results are point-set topological statements.  No smooth or graph-thickening
structure is asserted.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SplittingSpheres

/-! ## Restricting the one-handle trivialization -/

/-- The displayed base map on the attaching boundary: degree `m` on `S¹` and the identity on
`S²`. -/
def coordinateUnlinkExteriorBoundaryBasePowerMap (m : ℕ)
    (x : OneHandleCapBoundary) : OneHandleCapBoundary :=
  (unlinkUnitCirclePow m x.1, x.2)

@[simp]
theorem coordinateUnlinkExteriorBoundaryBasePowerMap_fst (m : ℕ)
    (x : OneHandleCapBoundary) :
    (coordinateUnlinkExteriorBoundaryBasePowerMap m x).1 =
      unlinkUnitCirclePow m x.1 :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorBoundaryBasePowerMap_snd (m : ℕ)
    (x : OneHandleCapBoundary) :
    (coordinateUnlinkExteriorBoundaryBasePowerMap m x).2 = x.2 :=
  rfl

theorem continuous_coordinateUnlinkExteriorBoundaryBasePowerMap (m : ℕ) :
    Continuous (coordinateUnlinkExteriorBoundaryBasePowerMap m) :=
  (continuous_unlinkUnitCirclePow m).comp continuous_fst |>.prodMk continuous_snd

/-- The boundary base-power map is exactly the restriction of the one-handle base-power map. -/
@[simp]
theorem oneHandleBoundaryInclusion_boundaryBasePowerMap (m : ℕ)
    (x : OneHandleCapBoundary) :
    oneHandleBoundaryInclusion
        (coordinateUnlinkExteriorBoundaryBasePowerMap m x) =
      coordinateUnlinkExteriorOneHandleBasePowerMap m
        (oneHandleBoundaryInclusion x) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    rfl

/-- The forward boundary trivialization, obtained using the one-handle power coordinate. -/
def coordinateUnlinkExteriorBoundaryPowerTrivializationForward
    (m : ℕ) [NeZero m] (x : OneHandleCapBoundary) :
    CoordinateUnlinkExteriorBoundaryPowerPullback m :=
  ⟨(coordinateUnlinkExteriorBoundaryBasePowerMap m x,
      coordinateUnlinkExteriorOneHandleTrivializationPowerCoordinate m
        (oneHandleBoundaryInclusion x)), by
    apply Subtype.ext
    change (coordinateUnlinkExteriorPushoutRightNormalMap
        (coordinateUnlinkExteriorPushoutOneHandleInclusion
          (oneHandleBoundaryInclusion
            (coordinateUnlinkExteriorBoundaryBasePowerMap m x))) : ℂ) =
      (coordinateUnlinkExteriorOneHandleTrivializationPowerCoordinate m
        (oneHandleBoundaryInclusion x) : ℂ) ^ m
    rw [oneHandleBoundaryInclusion_boundaryBasePowerMap]
    exact (coordinateUnlinkExteriorOneHandleTrivializationPowerCoordinate_pow m
      (oneHandleBoundaryInclusion x)).symm⟩

@[simp]
theorem coordinateUnlinkExteriorBoundaryPowerPullbackProj_trivializationForward
    (m : ℕ) [NeZero m] (x : OneHandleCapBoundary) :
    coordinateUnlinkExteriorBoundaryPowerPullbackProj m
        (coordinateUnlinkExteriorBoundaryPowerTrivializationForward m x) =
      coordinateUnlinkExteriorBoundaryBasePowerMap m x :=
  rfl

theorem continuous_coordinateUnlinkExteriorBoundaryPowerTrivializationForward
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorBoundaryPowerTrivializationForward m) := by
  apply Continuous.subtype_mk
  exact (continuous_coordinateUnlinkExteriorBoundaryBasePowerMap m).prodMk
    ((continuous_coordinateUnlinkExteriorOneHandleTrivializationPowerCoordinate m).comp
      oneHandleBoundaryInclusion.continuous)

/-- The forward boundary map commutes exactly with inclusion into the one-handle pullback. -/
@[simp]
theorem coordinateUnlinkExteriorBoundaryPowerTrivializationForward_toOneHandle
    (m : ℕ) [NeZero m] (x : OneHandleCapBoundary) :
    coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m
        (coordinateUnlinkExteriorBoundaryPowerTrivializationForward m x) =
      coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m
        (oneHandleBoundaryInclusion x) := by
  apply Subtype.ext
  apply Prod.ext
  · exact oneHandleBoundaryInclusion_boundaryBasePowerMap m x
  · rfl

/-- Recover the boundary circle by the one-handle inverse and retain the literal sphere
coordinate of the boundary base. -/
def coordinateUnlinkExteriorBoundaryPowerTrivializationInverse
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorBoundaryPowerPullback m) :
    OneHandleCapBoundary :=
  (coordinateUnlinkExteriorOneHandlePowerTrivializationInverseCircle m
      (coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m z),
    z.1.1.2)

theorem continuous_coordinateUnlinkExteriorBoundaryPowerTrivializationInverse
    (m : ℕ) [NeZero m] :
    Continuous (coordinateUnlinkExteriorBoundaryPowerTrivializationInverse m) :=
  ((continuous_coordinateUnlinkExteriorOneHandlePowerTrivializationInverseCircle m).comp
      (continuous_coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m)).prodMk
    (continuous_snd.comp (continuous_fst.comp continuous_subtype_val))

/-- Inclusion of the boundary inverse is exactly the inverse of the one-handle trivialization. -/
@[simp]
theorem oneHandleBoundaryInclusion_boundaryPowerTrivializationInverse
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorBoundaryPowerPullback m) :
    oneHandleBoundaryInclusion
        (coordinateUnlinkExteriorBoundaryPowerTrivializationInverse m z) =
      coordinateUnlinkExteriorOneHandlePowerTrivializationInverse m
        (coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m z) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    rfl

theorem coordinateUnlinkExteriorBoundaryPowerTrivializationInverse_forward
    (m : ℕ) [NeZero m] (x : OneHandleCapBoundary) :
    coordinateUnlinkExteriorBoundaryPowerTrivializationInverse m
        (coordinateUnlinkExteriorBoundaryPowerTrivializationForward m x) = x := by
  apply Prod.ext
  · have h := congrArg Prod.fst
      (coordinateUnlinkExteriorOneHandlePowerTrivializationInverse_forward m
        (oneHandleBoundaryInclusion x))
    change coordinateUnlinkExteriorOneHandlePowerTrivializationInverseCircle m
        (coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m
          (coordinateUnlinkExteriorBoundaryPowerTrivializationForward m x)) = x.1
    rw [coordinateUnlinkExteriorBoundaryPowerTrivializationForward_toOneHandle]
    exact h
  · rfl

theorem coordinateUnlinkExteriorBoundaryPowerTrivializationForward_inverse
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorBoundaryPowerPullback m) :
    coordinateUnlinkExteriorBoundaryPowerTrivializationForward m
        (coordinateUnlinkExteriorBoundaryPowerTrivializationInverse m z) = z := by
  apply injective_coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m
  rw [coordinateUnlinkExteriorBoundaryPowerTrivializationForward_toOneHandle,
    oneHandleBoundaryInclusion_boundaryPowerTrivializationInverse]
  exact (coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m).apply_symm_apply _

/-- For nonzero degree, the power pullback over the attaching boundary is another literal
`S¹ × S²`. -/
def coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph
    (m : ℕ) [NeZero m] :
    OneHandleCapBoundary ≃ₜ CoordinateUnlinkExteriorBoundaryPowerPullback m where
  toFun := coordinateUnlinkExteriorBoundaryPowerTrivializationForward m
  invFun := coordinateUnlinkExteriorBoundaryPowerTrivializationInverse m
  left_inv := coordinateUnlinkExteriorBoundaryPowerTrivializationInverse_forward m
  right_inv := coordinateUnlinkExteriorBoundaryPowerTrivializationForward_inverse m
  continuous_toFun :=
    continuous_coordinateUnlinkExteriorBoundaryPowerTrivializationForward m
  continuous_invFun :=
    continuous_coordinateUnlinkExteriorBoundaryPowerTrivializationInverse m

@[simp]
theorem coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph_apply
    (m : ℕ) [NeZero m] (x : OneHandleCapBoundary) :
    coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m x =
      coordinateUnlinkExteriorBoundaryPowerTrivializationForward m x :=
  rfl

/-- The boundary-cover projection is degree `m` on the circle and the identity on `S²`. -/
@[simp]
theorem coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph_proj
    (m : ℕ) [NeZero m] (x : OneHandleCapBoundary) :
    coordinateUnlinkExteriorBoundaryPowerPullbackProj m
        (coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m x) =
      (unlinkUnitCirclePow m x.1, x.2) :=
  rfl

/-- The boundary homeomorphism is the exact restriction of the one-handle homeomorphism. -/
@[simp]
theorem coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph_toOneHandle
    (m : ℕ) [NeZero m] (x : OneHandleCapBoundary) :
    coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m
        (coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m x) =
      coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m
        (oneHandleBoundaryInclusion x) :=
  coordinateUnlinkExteriorBoundaryPowerTrivializationForward_toOneHandle m x

@[simp]
theorem oneHandleBoundaryInclusion_boundaryPowerPullbackHomeomorph_symm
    (m : ℕ) [NeZero m]
    (z : CoordinateUnlinkExteriorBoundaryPowerPullback m) :
    oneHandleBoundaryInclusion
        ((coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m).symm z) =
      (coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph m).symm
        (coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m z) :=
  oneHandleBoundaryInclusion_boundaryPowerTrivializationInverse m z

/-! ## Restricted deck translations -/

/-- Multiply the power coordinate in the boundary pullback by an `m`th root of unity. -/
def coordinateUnlinkExteriorBoundaryPowerDeckMap (m : ℕ)
    (u : rootsOfUnity m ℂ)
    (z : CoordinateUnlinkExteriorBoundaryPowerPullback m) :
    CoordinateUnlinkExteriorBoundaryPowerPullback m :=
  ⟨(z.1.1, ⟨((u.1 : ℂˣ) : ℂ) * z.1.2.1,
      mul_ne_zero (Units.ne_zero u.1) z.1.2.2⟩), by
    apply Subtype.ext
    change (coordinateUnlinkExteriorPushoutRightNormalMap
        (coordinateUnlinkExteriorPushoutOneHandleInclusion
          (oneHandleBoundaryInclusion z.1.1)) : ℂ) =
      (((u.1 : ℂˣ) : ℂ) * z.1.2.1) ^ m
    rw [mul_pow, (mem_rootsOfUnity' m u.1).mp u.2, one_mul]
    exact congrArg Subtype.val z.2⟩

@[simp]
theorem coordinateUnlinkExteriorBoundaryPowerDeckMap_proj (m : ℕ)
    (u : rootsOfUnity m ℂ)
    (z : CoordinateUnlinkExteriorBoundaryPowerPullback m) :
    coordinateUnlinkExteriorBoundaryPowerPullbackProj m
        (coordinateUnlinkExteriorBoundaryPowerDeckMap m u z) =
      coordinateUnlinkExteriorBoundaryPowerPullbackProj m z :=
  rfl

@[simp]
theorem coordinateUnlinkExteriorBoundaryPowerDeckMap_powerCoordinate (m : ℕ)
    (u : rootsOfUnity m ℂ)
    (z : CoordinateUnlinkExteriorBoundaryPowerPullback m) :
    ((coordinateUnlinkExteriorBoundaryPowerDeckMap m u z).1.2 : ℂ) =
      ((u.1 : ℂˣ) : ℂ) * z.1.2.1 :=
  rfl

theorem coordinateUnlinkExteriorBoundaryPowerDeckMap_one (m : ℕ)
    (z : CoordinateUnlinkExteriorBoundaryPowerPullback m) :
    coordinateUnlinkExteriorBoundaryPowerDeckMap m 1 z = z := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp

theorem coordinateUnlinkExteriorBoundaryPowerDeckMap_mul (m : ℕ)
    (u v : rootsOfUnity m ℂ)
    (z : CoordinateUnlinkExteriorBoundaryPowerPullback m) :
    coordinateUnlinkExteriorBoundaryPowerDeckMap m (u * v) z =
      coordinateUnlinkExteriorBoundaryPowerDeckMap m u
        (coordinateUnlinkExteriorBoundaryPowerDeckMap m v z) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change ((((u * v).1 : ℂˣ) : ℂ) * z.1.2.1) =
      ((u.1 : ℂˣ) : ℂ) * (((v.1 : ℂˣ) : ℂ) * z.1.2.1)
    rw [Subgroup.coe_mul, Units.val_mul]
    exact mul_assoc _ _ _

instance coordinateUnlinkExteriorBoundaryPowerPullbackMulAction (m : ℕ) :
    MulAction (rootsOfUnity m ℂ)
      (CoordinateUnlinkExteriorBoundaryPowerPullback m) where
  smul := coordinateUnlinkExteriorBoundaryPowerDeckMap m
  one_smul := coordinateUnlinkExteriorBoundaryPowerDeckMap_one m
  mul_smul := coordinateUnlinkExteriorBoundaryPowerDeckMap_mul m

theorem continuous_coordinateUnlinkExteriorBoundaryPowerDeckMap (m : ℕ)
    (u : rootsOfUnity m ℂ) :
    Continuous (coordinateUnlinkExteriorBoundaryPowerDeckMap m u) := by
  unfold coordinateUnlinkExteriorBoundaryPowerDeckMap
  apply Continuous.subtype_mk
  exact (continuous_fst.comp continuous_subtype_val).prodMk <|
    (continuous_const.mul
      (continuous_subtype_val.comp
        (continuous_snd.comp continuous_subtype_val))).subtype_mk _

/-- The root-of-unity deck homeomorphism of the boundary pullback. -/
def coordinateUnlinkExteriorBoundaryPowerDeckHomeomorph (m : ℕ)
    (u : rootsOfUnity m ℂ) :
    CoordinateUnlinkExteriorBoundaryPowerPullback m ≃ₜ
      CoordinateUnlinkExteriorBoundaryPowerPullback m where
  toFun := (u • ·)
  invFun := (u⁻¹ • ·)
  left_inv z := inv_smul_smul u z
  right_inv z := smul_inv_smul u z
  continuous_toFun := continuous_coordinateUnlinkExteriorBoundaryPowerDeckMap m u
  continuous_invFun := continuous_coordinateUnlinkExteriorBoundaryPowerDeckMap m u⁻¹

@[simp]
theorem coordinateUnlinkExteriorBoundaryPowerDeckHomeomorph_apply (m : ℕ)
    (u : rootsOfUnity m ℂ)
    (z : CoordinateUnlinkExteriorBoundaryPowerPullback m) :
    coordinateUnlinkExteriorBoundaryPowerDeckHomeomorph m u z =
      coordinateUnlinkExteriorBoundaryPowerDeckMap m u z :=
  rfl

/-- Boundary deck transformations commute with inclusion into the one-handle pullback. -/
@[simp]
theorem coordinateUnlinkExteriorBoundaryPowerDeckMap_toOneHandle (m : ℕ)
    (u : rootsOfUnity m ℂ)
    (z : CoordinateUnlinkExteriorBoundaryPowerPullback m) :
    coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m
        (coordinateUnlinkExteriorBoundaryPowerDeckMap m u z) =
      coordinateUnlinkExteriorOneHandlePowerDeckMap m u
        (coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m z) := by
  apply Subtype.ext
  apply Prod.ext <;> rfl

/-- The boundary deck homeomorphisms form a group homomorphism. -/
def coordinateUnlinkExteriorBoundaryPowerDeckHom (m : ℕ) :
    rootsOfUnity m ℂ →*
      Homeomorph (CoordinateUnlinkExteriorBoundaryPowerPullback m)
        (CoordinateUnlinkExteriorBoundaryPowerPullback m) where
  toFun := coordinateUnlinkExteriorBoundaryPowerDeckHomeomorph m
  map_one' := by
    apply Homeomorph.ext
    exact coordinateUnlinkExteriorBoundaryPowerDeckMap_one m
  map_mul' u v := by
    apply Homeomorph.ext
    exact coordinateUnlinkExteriorBoundaryPowerDeckMap_mul m u v

/-- The boundary deck homomorphism with the standard `ZMod m` index. -/
def coordinateUnlinkExteriorBoundaryPowerDeckZModHom (m : ℕ) [NeZero m] :
    Multiplicative (ZMod m) →*
      Homeomorph (CoordinateUnlinkExteriorBoundaryPowerPullback m)
        (CoordinateUnlinkExteriorBoundaryPowerPullback m) :=
  (coordinateUnlinkExteriorBoundaryPowerDeckHom m).comp
    (standardRootsOfUnityZModMulEquiv m).toMonoidHom

@[simp]
theorem coordinateUnlinkExteriorBoundaryPowerDeckZModHom_apply
    (m : ℕ) [NeZero m] (a : ZMod m)
    (z : CoordinateUnlinkExteriorBoundaryPowerPullback m) :
    coordinateUnlinkExteriorBoundaryPowerDeckZModHom m
        (Multiplicative.ofAdd a) z =
      coordinateUnlinkExteriorBoundaryPowerDeckMap m
        (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)) z :=
  rfl

/-- Translate only the circle coordinate of the trivializing attaching boundary. -/
def coordinateUnlinkExteriorBoundaryDeckTranslation
    (m : ℕ) [NeZero m] (u : rootsOfUnity m ℂ)
    (x : OneHandleCapBoundary) : OneHandleCapBoundary :=
  (coordinateUnlinkExteriorOneHandleCircleDeckTranslation m u x.1, x.2)

@[simp]
theorem oneHandleBoundaryInclusion_boundaryDeckTranslation
    (m : ℕ) [NeZero m] (u : rootsOfUnity m ℂ)
    (x : OneHandleCapBoundary) :
    oneHandleBoundaryInclusion
        (coordinateUnlinkExteriorBoundaryDeckTranslation m u x) =
      coordinateUnlinkExteriorOneHandleDeckTranslation m u
        (oneHandleBoundaryInclusion x) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    rfl

@[simp]
theorem coordinateUnlinkExteriorBoundaryBasePowerMap_deckTranslation
    (m : ℕ) [NeZero m] (u : rootsOfUnity m ℂ)
    (x : OneHandleCapBoundary) :
    coordinateUnlinkExteriorBoundaryBasePowerMap m
        (coordinateUnlinkExteriorBoundaryDeckTranslation m u x) =
      coordinateUnlinkExteriorBoundaryBasePowerMap m x := by
  apply Prod.ext
  · exact unlinkUnitCirclePow_circleDeckTranslation m u x.1
  · rfl

theorem continuous_coordinateUnlinkExteriorBoundaryDeckTranslation
    (m : ℕ) [NeZero m] (u : rootsOfUnity m ℂ) :
    Continuous (coordinateUnlinkExteriorBoundaryDeckTranslation m u) :=
  (continuous_coordinateUnlinkExteriorOneHandleCircleDeckTranslation m u).comp continuous_fst
    |>.prodMk continuous_snd

/-- The boundary trivialization is equivariant for the same root-of-unity deck translation. -/
@[simp]
theorem coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph_deckTranslation
    (m : ℕ) [NeZero m] (u : rootsOfUnity m ℂ)
    (x : OneHandleCapBoundary) :
    coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m
        (coordinateUnlinkExteriorBoundaryDeckTranslation m u x) =
      coordinateUnlinkExteriorBoundaryPowerDeckHomeomorph m u
        (coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m x) := by
  apply injective_coordinateUnlinkExteriorBoundaryPowerPullbackToOneHandle m
  rw [coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph_toOneHandle,
    coordinateUnlinkExteriorBoundaryPowerDeckHomeomorph_apply,
    coordinateUnlinkExteriorBoundaryPowerDeckMap_toOneHandle,
    coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph_toOneHandle,
    oneHandleBoundaryInclusion_boundaryDeckTranslation]
  exact coordinateUnlinkExteriorOneHandlePowerPullbackHomeomorph_deckTranslation m u
    (oneHandleBoundaryInclusion x)

/-- Boundary source translation under the common additive `ZMod m` deck index. -/
def coordinateUnlinkExteriorBoundaryDeckTranslationZMod
    (m : ℕ) [NeZero m] (a : ZMod m)
    (x : OneHandleCapBoundary) : OneHandleCapBoundary :=
  coordinateUnlinkExteriorBoundaryDeckTranslation m
    (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)) x

@[simp]
theorem unlinkUnitCircleComplex_boundaryDeckTranslationZMod
    (m : ℕ) [NeZero m] (a : ZMod m) (x : OneHandleCapBoundary) :
    unlinkUnitCircleComplex
        (coordinateUnlinkExteriorBoundaryDeckTranslationZMod m a x).1 =
      Complex.exp (2 * Real.pi * Complex.I * a.val / m) *
        unlinkUnitCircleComplex x.1 := by
  change unlinkUnitCircleComplex
      (coordinateUnlinkExteriorOneHandleCircleDeckTranslation m
        (standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)) x.1) = _
  rw [unlinkUnitCircleComplex_circleDeckTranslation,
    standardRootsOfUnityZModMulEquiv_val]

/-- The standard `ZMod m` index agrees on the source boundary and its pullback deck action. -/
@[simp]
theorem coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph_deckZModHom
    (m : ℕ) [NeZero m] (a : ZMod m) (x : OneHandleCapBoundary) :
    coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m
        (coordinateUnlinkExteriorBoundaryDeckTranslationZMod m a x) =
      coordinateUnlinkExteriorBoundaryPowerDeckZModHom m
        (Multiplicative.ofAdd a)
        (coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph m x) :=
  coordinateUnlinkExteriorBoundaryPowerPullbackHomeomorph_deckTranslation m _ x

end SplittingSpheres
