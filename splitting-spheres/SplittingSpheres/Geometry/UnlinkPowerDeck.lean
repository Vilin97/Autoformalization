/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.UnlinkCyclicCover

/-!
# Deck transformations of the unlink power pullback

The `m`-th roots of unity act on the power-pullback coordinate by multiplication.  This file
constructs that action explicitly, proves that every action map is a homeomorphism over the
strict unlink complement, and proves that the action is free and transitive on every fiber.

For `m ≠ 0`, the acting group has exactly `m` elements and is cyclic.  Thus the previously
constructed `m`-sheeted power pullback carries a concrete regular cyclic deck action.  No
meridian-winding statement is made here.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SplittingSpheres

/-- Multiply the power coordinate of the pullback by an `m`-th root of unity. -/
def standardUnlinkPowerDeckMap (m : ℕ) (u : rootsOfUnity m ℂ)
    (z : StandardUnlinkPowerPullback m) : StandardUnlinkPowerPullback m :=
  ⟨(z.1.1, ⟨((u.1 : ℂˣ) : ℂ) * z.1.2.1,
      mul_ne_zero (Units.ne_zero u.1) z.1.2.2⟩), by
    apply Subtype.ext
    change (standardUnlinkRightNormalMap z.1.1 : ℂ) =
      (((u.1 : ℂˣ) : ℂ) * z.1.2.1) ^ m
    rw [mul_pow, (mem_rootsOfUnity' m u.1).mp u.2, one_mul]
    exact congrArg Subtype.val z.2⟩

@[simp]
theorem standardUnlinkPowerDeckMap_base (m : ℕ) (u : rootsOfUnity m ℂ)
    (z : StandardUnlinkPowerPullback m) :
    (standardUnlinkPowerDeckMap m u z).1.1 = z.1.1 :=
  rfl

@[simp]
theorem standardUnlinkPowerDeckMap_powerCoordinate (m : ℕ)
    (u : rootsOfUnity m ℂ) (z : StandardUnlinkPowerPullback m) :
    ((standardUnlinkPowerDeckMap m u z).1.2 : ℂ) =
      ((u.1 : ℂˣ) : ℂ) * z.1.2.1 :=
  rfl

theorem standardUnlinkPowerDeckMap_one (m : ℕ) (z : StandardUnlinkPowerPullback m) :
    standardUnlinkPowerDeckMap m 1 z = z := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp

theorem standardUnlinkPowerDeckMap_mul (m : ℕ) (u v : rootsOfUnity m ℂ)
    (z : StandardUnlinkPowerPullback m) :
    standardUnlinkPowerDeckMap m (u * v) z =
      standardUnlinkPowerDeckMap m u (standardUnlinkPowerDeckMap m v z) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change ((((u * v).1 : ℂˣ) : ℂ) * z.1.2.1) =
      ((u.1 : ℂˣ) : ℂ) * (((v.1 : ℂˣ) : ℂ) * z.1.2.1)
    rw [Subgroup.coe_mul, Units.val_mul]
    exact mul_assoc _ _ _

/-- The roots-of-unity action on the raw power pullback. -/
instance standardUnlinkPowerPullbackMulAction (m : ℕ) :
    MulAction (rootsOfUnity m ℂ) (StandardUnlinkPowerPullback m) where
  smul := standardUnlinkPowerDeckMap m
  one_smul := standardUnlinkPowerDeckMap_one m
  mul_smul := standardUnlinkPowerDeckMap_mul m

@[simp]
theorem standardUnlinkPowerPullback_smul_apply (m : ℕ) (u : rootsOfUnity m ℂ)
    (z : StandardUnlinkPowerPullback m) :
    u • z = standardUnlinkPowerDeckMap m u z :=
  rfl

/-- Multiplication by a fixed root of unity is continuous on the power pullback. -/
theorem continuous_standardUnlinkPowerDeckMap (m : ℕ) (u : rootsOfUnity m ℂ) :
    Continuous (standardUnlinkPowerDeckMap m u) := by
  unfold standardUnlinkPowerDeckMap
  apply Continuous.subtype_mk
  exact (continuous_fst.comp continuous_subtype_val).prodMk <|
    (continuous_const.mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _

/-- The deck homeomorphism associated to an `m`-th root of unity. -/
def standardUnlinkPowerDeckHomeomorph (m : ℕ) (u : rootsOfUnity m ℂ) :
    StandardUnlinkPowerPullback m ≃ₜ StandardUnlinkPowerPullback m where
  toFun := (u • ·)
  invFun := (u⁻¹ • ·)
  left_inv z := by
    change u⁻¹ • (u • z) = z
    exact inv_smul_smul u z
  right_inv z := by
    change u • (u⁻¹ • z) = z
    exact smul_inv_smul u z
  continuous_toFun := continuous_standardUnlinkPowerDeckMap m u
  continuous_invFun := continuous_standardUnlinkPowerDeckMap m u⁻¹

@[simp]
theorem standardUnlinkPowerDeckHomeomorph_apply (m : ℕ)
    (u : rootsOfUnity m ℂ) (z : StandardUnlinkPowerPullback m) :
    standardUnlinkPowerDeckHomeomorph m u z = u • z :=
  rfl

/-- Every displayed deck homeomorphism lies over the identity of the strict complement. -/
@[simp]
theorem standardUnlinkPowerPullbackProj_deck (m : ℕ) (u : rootsOfUnity m ℂ)
    (z : StandardUnlinkPowerPullback m) :
    standardUnlinkPowerPullbackProj m (standardUnlinkPowerDeckHomeomorph m u z) =
      standardUnlinkPowerPullbackProj m z :=
  rfl

/-- The explicit deck homeomorphisms form a group homomorphism. -/
def standardUnlinkPowerDeckHom (m : ℕ) :
    rootsOfUnity m ℂ →* Homeomorph (StandardUnlinkPowerPullback m)
    (StandardUnlinkPowerPullback m) where
  toFun := standardUnlinkPowerDeckHomeomorph m
  map_one' := by
    apply Homeomorph.ext
    intro z
    exact standardUnlinkPowerDeckMap_one m z
  map_mul' u v := by
    apply Homeomorph.ext
    intro z
    exact standardUnlinkPowerDeckMap_mul m u v z

@[simp]
theorem standardUnlinkPowerDeckHom_apply (m : ℕ) (u : rootsOfUnity m ℂ)
    (z : StandardUnlinkPowerPullback m) :
    standardUnlinkPowerDeckHom m u z = u • z :=
  rfl

/-- The roots-of-unity action is free at every point of the total space. -/
theorem standardUnlinkPowerDeck_smul_right_injective (m : ℕ)
    (z : StandardUnlinkPowerPullback m) :
    Injective (fun u : rootsOfUnity m ℂ ↦ u • z) := by
  intro u v huv
  apply Subtype.ext
  apply Units.ext
  have hcoordinate := congrArg (fun q : StandardUnlinkPowerPullback m ↦
    ((q.1.2 : {z : ℂ // z ≠ 0}) : ℂ)) huv
  change ((u.1 : ℂˣ) : ℂ) * z.1.2.1 =
    ((v.1 : ℂˣ) : ℂ) * z.1.2.1 at hcoordinate
  have huvval : ((u.1 : ℂˣ) : ℂ) = ((v.1 : ℂˣ) : ℂ) :=
    mul_right_cancel₀ z.1.2.2 hcoordinate
  exact huvval

/-- Two points over the same base point differ by a unique root-of-unity action. -/
theorem existsUnique_standardUnlinkPowerDeck_smul_eq (m : ℕ)
    (z w : StandardUnlinkPowerPullback m)
    (hbase : standardUnlinkPowerPullbackProj m z =
      standardUnlinkPowerPullbackProj m w) :
    ∃! u : rootsOfUnity m ℂ, u • z = w := by
  let a : ℂ := z.1.2.1
  let b : ℂ := w.1.2.1
  have ha : a ≠ 0 := z.1.2.2
  have hb : b ≠ 0 := w.1.2.2
  have hpowers : b ^ m = a ^ m := by
    change w.1.2.1 ^ m = z.1.2.1 ^ m
    calc
      w.1.2.1 ^ m = (standardUnlinkRightNormalMap w.1.1 : ℂ) :=
        (congrArg Subtype.val w.2).symm
      _ = (standardUnlinkRightNormalMap z.1.1 : ℂ) :=
        congrArg (fun x ↦ (standardUnlinkRightNormalMap x : ℂ)) hbase.symm
      _ = z.1.2.1 ^ m := congrArg Subtype.val z.2
  let q : ℂˣ := Units.mk0 (b / a) (div_ne_zero hb ha)
  have hq : (q : ℂ) ^ m = 1 := by
    change (b / a) ^ m = 1
    rw [div_pow, hpowers, div_self (pow_ne_zero m ha)]
  let u : rootsOfUnity m ℂ := ⟨q, (mem_rootsOfUnity' m q).mpr hq⟩
  have hu : u • z = w := by
    apply Subtype.ext
    apply Prod.ext
    · change z.1.1 = w.1.1
      exact hbase
    · apply Subtype.ext
      change (b / a) * a = b
      exact div_mul_cancel₀ b ha
  refine ⟨u, hu, ?_⟩
  intro v hv
  exact standardUnlinkPowerDeck_smul_right_injective m z (hv.trans hu.symm)

/-- Restricted to any projection fiber, the roots-of-unity action is simply transitive. -/
theorem standardUnlinkPowerDeck_fiber_torsor (m : ℕ)
    (x : StandardUnlinkComplement)
    (z w : standardUnlinkPowerPullbackProj m ⁻¹' {x}) :
    ∃! u : rootsOfUnity m ℂ, u • z.1 = w.1 := by
  apply existsUnique_standardUnlinkPowerDeck_smul_eq m z.1 w.1
  exact z.2.trans w.2.symm

/-- For nonzero `m`, the explicit deck group is cyclic and has exactly `m` elements. -/
theorem standardUnlinkPowerDeckGroup_isCyclic_card (m : ℕ) [NeZero m] :
    IsCyclic (rootsOfUnity m ℂ) ∧ Nat.card (rootsOfUnity m ℂ) = m :=
  ⟨inferInstance, Complex.card_rootsOfUnity m⟩

end SplittingSpheres
