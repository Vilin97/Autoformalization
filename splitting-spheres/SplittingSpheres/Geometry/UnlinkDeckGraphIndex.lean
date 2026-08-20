/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.UnlinkDeckZMod
public import SplittingSpheres.Handlebody.CyclicGraphPieces

/-!
# A common cyclic index for the geometric and graph deck actions

The power pullback and the cyclic rose cover both carry actions indexed by `ZMod m`.  This file
packages the graph translations as a homomorphism and pairs them with the already constructed
geometric deck homeomorphisms.  It proves only that the two displayed actions use the same cyclic
index.  It does not identify their underlying spaces or assert that the rose is a deformation
retract of the geometric cover.
-/

@[expose] public section

noncomputable section

open Function

namespace SplittingSpheres

/-- Translation gives the displayed cyclic deck action on the vertices of the rose cover. -/
def cyclicRoseCoverDeckZModHom (m : ℕ) [NeZero m] :
    Multiplicative (ZMod m) →* Equiv.Perm (cyclicRoseCover m).Vertex where
  toFun a := cyclicRoseCover.deckTranslation m a.toAdd
  map_one' := by
    ext v
    simp
  map_mul' a b := by
    ext v
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    change v + (a.toAdd + b.toAdd) = (v + b.toAdd) + a.toAdd
    abel

@[simp]
theorem cyclicRoseCoverDeckZModHom_apply (m : ℕ) [NeZero m]
    (a v : ZMod m) :
    cyclicRoseCoverDeckZModHom m (Multiplicative.ofAdd a) v = v + a :=
  rfl

/-- The displayed graph deck action is faithful. -/
theorem cyclicRoseCoverDeckZModHom_injective (m : ℕ) [NeZero m] :
    Injective (cyclicRoseCoverDeckZModHom m) := by
  intro a b hab
  have hzero := DFunLike.congr_fun hab (0 : ZMod m)
  have hadd : a.toAdd = b.toAdd := by
    change (0 : ZMod m) + a.toAdd = 0 + b.toAdd at hzero
    simpa using hzero
  exact Multiplicative.ext hadd

/-- The geometric power-cover action and graph translation action, paired at their common
`ZMod m` index. -/
def standardUnlinkPowerAndRoseDeckHom (m : ℕ) [NeZero m] :
    Multiplicative (ZMod m) →*
      (Homeomorph (StandardUnlinkPowerPullback m) (StandardUnlinkPowerPullback m) ×
        Equiv.Perm (cyclicRoseCover m).Vertex) :=
  (standardUnlinkPowerDeckZModHom m).prod (cyclicRoseCoverDeckZModHom m)

@[simp]
theorem standardUnlinkPowerAndRoseDeckHom_fst (m : ℕ) [NeZero m]
    (a : Multiplicative (ZMod m)) :
    (standardUnlinkPowerAndRoseDeckHom m a).1 =
      standardUnlinkPowerDeckZModHom m a :=
  rfl

@[simp]
theorem standardUnlinkPowerAndRoseDeckHom_snd (m : ℕ) [NeZero m]
    (a : Multiplicative (ZMod m)) :
    (standardUnlinkPowerAndRoseDeckHom m a).2 =
      cyclicRoseCoverDeckZModHom m a :=
  rfl

/-- Pairing with the geometric action loses no cyclic-index information. -/
theorem standardUnlinkPowerAndRoseDeckHom_injective (m : ℕ) [NeZero m] :
    Injective (standardUnlinkPowerAndRoseDeckHom m) := by
  intro a b hab
  apply cyclicRoseCoverDeckZModHom_injective m
  exact congrArg Prod.snd hab

end SplittingSpheres
