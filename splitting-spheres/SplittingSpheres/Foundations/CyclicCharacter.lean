/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Index

/-!
# The cyclic character of the two-generator free group

The finite cyclic cover in the splitting-spheres argument is classified by the homomorphism
from the free group on the left and right one-handles which kills the left generator and sends the
right generator to `1 mod m`.  This file defines that homomorphism and proves the divisibility and
surjectivity facts used by the tower of covers.
-/

@[expose] public section

namespace SplittingSpheres

/-- The cyclic character which sends generator `0` to zero and generator `1` to one.  The
additive cyclic group is tagged multiplicatively so it can be the codomain of a group
homomorphism. -/
def cyclicCharacter (m : ℕ) : FreeGroup (Fin 2) →* Multiplicative (ZMod m) :=
  FreeGroup.lift fun i ↦ if i = 0 then 1 else Multiplicative.ofAdd 1

@[simp]
theorem cyclicCharacter_generator_zero (m : ℕ) :
    cyclicCharacter m (FreeGroup.of (0 : Fin 2)) = 1 := by
  simp [cyclicCharacter]

@[simp]
theorem cyclicCharacter_generator_one (m : ℕ) :
    cyclicCharacter m (FreeGroup.of (1 : Fin 2)) = Multiplicative.ofAdd 1 := by
  simp [cyclicCharacter]

/-- Reduction modulo `k` as a homomorphism of multiplicatively tagged cyclic groups. -/
def cyclicReduction {k m : ℕ} (h : k ∣ m) :
    Multiplicative (ZMod m) →* Multiplicative (ZMod k) :=
  AddMonoidHom.toMultiplicative (ZMod.castHom h (ZMod k)).toAddMonoidHom

/-- When `k` divides `m`, the mod-`k` character is the mod-`m` character followed by reduction. -/
theorem cyclicReduction_comp_cyclicCharacter {k m : ℕ} (h : k ∣ m) :
    (cyclicReduction h).comp (cyclicCharacter m) = cyclicCharacter k := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i
  · simp [cyclicReduction]
  · simp [cyclicCharacter, cyclicReduction, ZMod.cast_one (R := ZMod k) h]

/-- The subgroup defining the degree-`m` cover lies in the subgroup defining the degree-`k`
cover whenever `k` divides `m`. -/
theorem cyclicCharacter_ker_mono {k m : ℕ} (h : k ∣ m) :
    (cyclicCharacter m).ker ≤ (cyclicCharacter k).ker := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx ⊢
  have hcomp := DFunLike.congr_fun
    (cyclicReduction_comp_cyclicCharacter (k := k) (m := m) h) x
  rw [← hcomp]
  change cyclicReduction h (cyclicCharacter m x) = 1
  rw [hx, map_one]

/-- The cyclic character is onto. -/
theorem cyclicCharacter_surjective (m : ℕ) : Function.Surjective (cyclicCharacter m) := by
  intro z
  obtain ⟨i, hi⟩ := ZMod.intCast_surjective z.toAdd
  refine ⟨(FreeGroup.of (1 : Fin 2)) ^ i, ?_⟩
  rw [map_zpow, cyclicCharacter_generator_one]
  change i • (1 : ZMod m) = z.toAdd
  simpa using hi

/-- The subgroup defining the cyclic cover has index exactly `m`. -/
theorem cyclicCharacter_ker_index (m : ℕ) [NeZero m] :
    (cyclicCharacter m).ker.index = m := by
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (cyclicCharacter_surjective m)]
  rw [Nat.card_congr Subgroup.topEquiv.toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod m) ≃ ZMod m),
    Nat.card_eq_fintype_card, ZMod.card]

end SplittingSpheres
