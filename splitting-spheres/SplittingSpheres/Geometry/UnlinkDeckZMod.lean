/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import SplittingSpheres.Geometry.UnlinkPowerDeck

/-!
# Indexing the power-cover deck action by `ZMod`

The geometric power pullback is acted on by the complex `m`-th roots of unity, while the cyclic
rose cover is indexed additively by `ZMod m`.  The standard circle character gives a concrete
isomorphism between these groups.  This file records that bridge and the resulting `ZMod`-indexed
deck homeomorphisms.

This is a group-index identification only.  It does not identify the geometric total space with
a thickening of the cyclic rose cover.
-/

@[expose] public section

noncomputable section

open Function

namespace SplittingSpheres

/-- The standard multiplicative form of the character from `ZMod m` to complex `m`-th roots of
unity. -/
def standardRootsOfUnityZModHom (m : ℕ) [NeZero m] :
    Multiplicative (ZMod m) →* rootsOfUnity m ℂ :=
  (rootsOfUnityCircleEquiv m).toMonoidHom.comp
    (ZMod.rootsOfUnityAddChar m).toMonoidHom

@[simp]
theorem standardRootsOfUnityZModHom_apply (m : ℕ) [NeZero m]
    (a : Multiplicative (ZMod m)) :
    standardRootsOfUnityZModHom m a =
      rootsOfUnityCircleEquiv m (ZMod.rootsOfUnityAddChar m a.toAdd) :=
  rfl

theorem standardRootsOfUnityZModHom_bijective (m : ℕ) [NeZero m] :
    Bijective (standardRootsOfUnityZModHom m) := by
  exact (rootsOfUnityCircleEquiv m).bijective.comp
    (bijective_rootsOfUnityAddChar m)

/-- The standard multiplicative identification of `ZMod m` with the complex `m`-th roots of
unity. -/
def standardRootsOfUnityZModMulEquiv (m : ℕ) [NeZero m] :
    Multiplicative (ZMod m) ≃* rootsOfUnity m ℂ :=
  MulEquiv.ofBijective (standardRootsOfUnityZModHom m)
    (standardRootsOfUnityZModHom_bijective m)

@[simp]
theorem standardRootsOfUnityZModMulEquiv_apply (m : ℕ) [NeZero m]
    (a : Multiplicative (ZMod m)) :
    standardRootsOfUnityZModMulEquiv m a = standardRootsOfUnityZModHom m a :=
  rfl

/-- The underlying complex value of the standard root indexed by `a : ZMod m`. -/
theorem standardRootsOfUnityZModMulEquiv_val (m : ℕ) [NeZero m]
    (a : ZMod m) :
    (((standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a)).1 : ℂˣ) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I * a.val / m) := by
  exact rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar_val m a

/-- The geometric deck-action homomorphism with its acting group indexed by multiplicative
`ZMod m`. -/
def standardUnlinkPowerDeckZModHom (m : ℕ) [NeZero m] :
    Multiplicative (ZMod m) →*
      Homeomorph (StandardUnlinkPowerPullback m) (StandardUnlinkPowerPullback m) :=
  (standardUnlinkPowerDeckHom m).comp
    (standardRootsOfUnityZModMulEquiv m).toMonoidHom

@[simp]
theorem standardUnlinkPowerDeckZModHom_apply (m : ℕ) [NeZero m]
    (a : ZMod m) (z : StandardUnlinkPowerPullback m) :
    standardUnlinkPowerDeckZModHom m (Multiplicative.ofAdd a) z =
      standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd a) • z :=
  rfl

/-- The `ZMod`-indexed displayed deck action is faithful. -/
theorem standardUnlinkPowerDeckZModHom_injective (m : ℕ) [NeZero m]
    (z : StandardUnlinkPowerPullback m) :
    Injective (fun a : ZMod m ↦
      standardUnlinkPowerDeckZModHom m (Multiplicative.ofAdd a) z) := by
  intro a b hab
  apply Multiplicative.ofAdd.injective
  apply (standardRootsOfUnityZModMulEquiv m).injective
  exact standardUnlinkPowerDeck_smul_right_injective m z hab

/-- On every projection fiber, the `ZMod m`-indexed deck action is simply transitive. -/
theorem existsUnique_standardUnlinkPowerDeckZMod_eq (m : ℕ) [NeZero m]
    (z w : StandardUnlinkPowerPullback m)
    (hbase : standardUnlinkPowerPullbackProj m z =
      standardUnlinkPowerPullbackProj m w) :
    ∃! a : ZMod m,
      standardUnlinkPowerDeckZModHom m (Multiplicative.ofAdd a) z = w := by
  obtain ⟨u, hu, hu_unique⟩ :=
    existsUnique_standardUnlinkPowerDeck_smul_eq m z w hbase
  let a : Multiplicative (ZMod m) := (standardRootsOfUnityZModMulEquiv m).symm u
  refine ⟨a.toAdd, ?_, ?_⟩
  · change standardRootsOfUnityZModMulEquiv m a • z = w
    rw [(standardRootsOfUnityZModMulEquiv m).apply_symm_apply]
    exact hu
  · intro b hb
    apply Multiplicative.ofAdd.injective
    apply (standardRootsOfUnityZModMulEquiv m).injective
    change standardRootsOfUnityZModMulEquiv m (Multiplicative.ofAdd b) =
      standardRootsOfUnityZModMulEquiv m a
    have ha : standardRootsOfUnityZModMulEquiv m a = u := by
      dsimp [a]
      exact (standardRootsOfUnityZModMulEquiv m).apply_symm_apply u
    rw [ha]
    apply hu_unique
    exact hb

end SplittingSpheres
