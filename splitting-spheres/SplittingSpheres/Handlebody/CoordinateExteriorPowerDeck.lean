/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.UnlinkDeckGraphIndex
public import SplittingSpheres.Handlebody.CoordinateExteriorPowerCover

/-!
# Cyclic deck action on the coordinate-exterior pushout cover

Conjugating through the total-space homeomorphism transports the roots-of-unity deck action from
the literal closed exterior to its one-handle/punctured-cap pushout.  For nonzero degree we index
this action by the same explicit `ZMod m` character as the geometric complement cover and pair it
with translation of the cyclic rose vertices.

The paired homomorphism records a common index, not a map or equivalence between the topological
pushout cover and a thickening of the rose.
-/

@[expose] public section

noncomputable section

open Function

namespace SplittingSpheres

/-- Transport the exterior deck action to the power pullback over the exterior pushout. -/
def coordinateUnlinkExteriorPushoutPowerDeckMap (m : ℕ)
    (u : rootsOfUnity m ℂ) (z : CoordinateUnlinkExteriorPushoutPowerPullback m) :
    CoordinateUnlinkExteriorPushoutPowerPullback m :=
  (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m).symm
    (u • coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m z)

theorem coordinateUnlinkExteriorPushoutPowerDeckMap_one (m : ℕ)
    (z : CoordinateUnlinkExteriorPushoutPowerPullback m) :
    coordinateUnlinkExteriorPushoutPowerDeckMap m 1 z = z := by
  rw [coordinateUnlinkExteriorPushoutPowerDeckMap, one_smul,
    (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m).symm_apply_apply]

theorem coordinateUnlinkExteriorPushoutPowerDeckMap_mul (m : ℕ)
    (u v : rootsOfUnity m ℂ) (z : CoordinateUnlinkExteriorPushoutPowerPullback m) :
    coordinateUnlinkExteriorPushoutPowerDeckMap m (u * v) z =
      coordinateUnlinkExteriorPushoutPowerDeckMap m u
        (coordinateUnlinkExteriorPushoutPowerDeckMap m v z) := by
  unfold coordinateUnlinkExteriorPushoutPowerDeckMap
  rw [(coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m).apply_symm_apply,
    mul_smul]

instance coordinateUnlinkExteriorPushoutPowerPullbackMulAction (m : ℕ) :
    MulAction (rootsOfUnity m ℂ) (CoordinateUnlinkExteriorPushoutPowerPullback m) where
  smul := coordinateUnlinkExteriorPushoutPowerDeckMap m
  one_smul := coordinateUnlinkExteriorPushoutPowerDeckMap_one m
  mul_smul := coordinateUnlinkExteriorPushoutPowerDeckMap_mul m

/-- The transported action is exactly equivariant for the total-space homeomorphism. -/
@[simp]
theorem coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_smul
    (m : ℕ) (u : rootsOfUnity m ℂ)
    (z : CoordinateUnlinkExteriorPushoutPowerPullback m) :
    coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m (u • z) =
      u • coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m z := by
  exact (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m).apply_symm_apply _

/-- The displayed deck homeomorphism on the pushout pullback. -/
def coordinateUnlinkExteriorPushoutPowerDeckHomeomorph (m : ℕ)
    (u : rootsOfUnity m ℂ) :
    CoordinateUnlinkExteriorPushoutPowerPullback m ≃ₜ
      CoordinateUnlinkExteriorPushoutPowerPullback m :=
  (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m).trans
    ((coordinateUnlinkExteriorEighthPowerDeckHomeomorph m u).trans
      (coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m).symm)

@[simp]
theorem coordinateUnlinkExteriorPushoutPowerDeckHomeomorph_apply (m : ℕ)
    (u : rootsOfUnity m ℂ) (z : CoordinateUnlinkExteriorPushoutPowerPullback m) :
    coordinateUnlinkExteriorPushoutPowerDeckHomeomorph m u z = u • z :=
  rfl

/-- The transported deck homeomorphisms form a group homomorphism. -/
def coordinateUnlinkExteriorPushoutPowerDeckHom (m : ℕ) :
    rootsOfUnity m ℂ →*
      Homeomorph (CoordinateUnlinkExteriorPushoutPowerPullback m)
        (CoordinateUnlinkExteriorPushoutPowerPullback m) where
  toFun := coordinateUnlinkExteriorPushoutPowerDeckHomeomorph m
  map_one' := by
    apply Homeomorph.ext
    exact coordinateUnlinkExteriorPushoutPowerDeckMap_one m
  map_mul' u v := by
    apply Homeomorph.ext
    exact coordinateUnlinkExteriorPushoutPowerDeckMap_mul m u v

/-- On every pushout-cover fiber, the transported roots action is simply transitive. -/
theorem existsUnique_coordinateUnlinkExteriorPushoutPowerDeck_smul_eq (m : ℕ)
    (z w : CoordinateUnlinkExteriorPushoutPowerPullback m)
    (hbase : coordinateUnlinkExteriorPushoutPowerPullbackProj m z =
      coordinateUnlinkExteriorPushoutPowerPullbackProj m w) :
    ∃! u : rootsOfUnity m ℂ, u • z = w := by
  let H := coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph m
  have hHbase : coordinateUnlinkExteriorEighthPowerPullbackProj m (H z) =
      coordinateUnlinkExteriorEighthPowerPullbackProj m (H w) := by
    rw [coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_proj,
      coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_proj, hbase]
  obtain ⟨u, hu, hu_unique⟩ :=
    existsUnique_coordinateUnlinkExteriorEighthPowerDeck_smul_eq m (H z) (H w) hHbase
  refine ⟨u, ?_, ?_⟩
  · apply H.injective
    rw [coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_smul]
    exact hu
  · intro v hv
    apply hu_unique
    rw [← coordinateUnlinkExteriorPushoutPowerPullbackHomeomorph_smul]
    exact congrArg H hv

/-- For nonzero degree, index the pushout deck action by the standard `ZMod m` character. -/
def coordinateUnlinkExteriorPushoutPowerDeckZModHom (m : ℕ) [NeZero m] :
    Multiplicative (ZMod m) →*
      Homeomorph (CoordinateUnlinkExteriorPushoutPowerPullback m)
        (CoordinateUnlinkExteriorPushoutPowerPullback m) :=
  (coordinateUnlinkExteriorPushoutPowerDeckHom m).comp
    (standardRootsOfUnityZModMulEquiv m).toMonoidHom

/-- The transported geometric action and cyclic-rose vertex translation, paired at their common
`ZMod m` index. -/
def coordinateUnlinkExteriorPushoutAndRoseDeckHom (m : ℕ) [NeZero m] :
    Multiplicative (ZMod m) →*
      (Homeomorph (CoordinateUnlinkExteriorPushoutPowerPullback m)
          (CoordinateUnlinkExteriorPushoutPowerPullback m) ×
        Equiv.Perm (cyclicRoseCover m).Vertex) :=
  (coordinateUnlinkExteriorPushoutPowerDeckZModHom m).prod
    (cyclicRoseCoverDeckZModHom m)

/-- The paired action retains the full cyclic index, already on its graph component. -/
theorem coordinateUnlinkExteriorPushoutAndRoseDeckHom_injective
    (m : ℕ) [NeZero m] :
    Injective (coordinateUnlinkExteriorPushoutAndRoseDeckHom m) := by
  intro a b hab
  apply cyclicRoseCoverDeckZModHom_injective m
  exact congrArg Prod.snd hab

end SplittingSpheres
