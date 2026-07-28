/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.Tactic

/-!
# Homomorphisms out of generalized quaternion groups

This file supplies the universal two-generator construction for
`QuaternionGroup n`.  Mathlib defines the concrete multiplication on the
dicyclic normal forms `a i` and `xa i`; the constructor below maps these
normal forms into any group containing elements satisfying the standard
dicyclic relations.
-/

namespace QuaternionGroup

variable {H : Type*} [Group H]
variable {n : ℕ}

/-- Powers of an element whose `m`-th power is one, indexed without a
choice of representative by `ZMod m`. -/
def zmodPower {m : ℕ} (A : H) (hA : A ^ m = 1)
    (i : ZMod m) : H :=
  Additive.toMul
    (ZMod.lift m
      ⟨(zpowersHom H A).toAdditive, by
        change A ^ (m : ℤ) = 1
        simpa using hA⟩ i)

@[simp]
theorem zmodPower_zero {m : ℕ} (A : H) (hA : A ^ m = 1) :
    zmodPower A hA 0 = 1 := by
  simp [zmodPower]

@[simp]
theorem zmodPower_add {m : ℕ} (A : H) (hA : A ^ m = 1)
    (i j : ZMod m) :
    zmodPower A hA (i + j) =
      zmodPower A hA i * zmodPower A hA j := by
  exact
    congrArg Additive.toMul
      ((ZMod.lift m
        ⟨(zpowersHom H A).toAdditive, by
          change A ^ (m : ℤ) = 1
          simpa using hA⟩).map_add i j)

@[simp]
theorem zmodPower_neg {m : ℕ} (A : H) (hA : A ^ m = 1)
    (i : ZMod m) :
    zmodPower A hA (-i) =
      (zmodPower A hA i)⁻¹ := by
  exact
    congrArg Additive.toMul
      ((ZMod.lift m
        ⟨(zpowersHom H A).toAdditive, by
          change A ^ (m : ℤ) = 1
          simpa using hA⟩).map_neg i)

@[simp]
theorem zmodPower_sub {m : ℕ} (A : H) (hA : A ^ m = 1)
    (i j : ZMod m) :
    zmodPower A hA (i - j) =
      zmodPower A hA i * (zmodPower A hA j)⁻¹ := by
  rw [sub_eq_add_neg, zmodPower_add, zmodPower_neg]

@[simp]
theorem zmodPower_intCast {m : ℕ} (A : H) (hA : A ^ m = 1)
    (z : ℤ) :
    zmodPower A hA (z : ZMod m) = A ^ z := by
  unfold zmodPower
  rw [ZMod.lift_coe]
  exact zpowersHom_apply H A (Multiplicative.ofAdd z)

@[simp]
theorem zmodPower_natCast {m : ℕ} (A : H) (hA : A ^ m = 1)
    (k : ℕ) :
    zmodPower A hA (k : ZMod m) = A ^ k := by
  rw [show (k : ZMod m) = ((k : ℤ) : ZMod m) by norm_num]
  rw [zmodPower_intCast]
  change A ^ (k : ℤ) = A ^ k
  simp

/-- It is enough to check the inversion relation on the chosen cyclic
generator; it then holds for every `ZMod`-indexed power. -/
theorem zmodPower_mul_eq_mul_zmodPower_neg
    {m : ℕ} (A X : H) (hA : A ^ m = 1)
    (hAX : A * X = X * A⁻¹)
    (i : ZMod m) :
    zmodPower A hA i * X =
      X * zmodPower A hA (-i) := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective i
  rw [zmodPower_intCast]
  rw [show -((z : ℤ) : ZMod m) = ((-z : ℤ) : ZMod m) by simp]
  rw [zmodPower_intCast]
  have hsemi : SemiconjBy X A⁻¹ A :=
    hAX.symm
  simpa using (hsemi.zpow_right z).eq.symm

/-- The standard dicyclic relations give a homomorphism out of
`QuaternionGroup n`. -/
def lift
    (A X : H)
    (hA : A ^ (2 * n) = 1)
    (hXsq : X * X = zmodPower A hA n)
    (hconj :
      ∀ i : ZMod (2 * n),
        zmodPower A hA i * X =
          X * zmodPower A hA (-i)) :
    QuaternionGroup n →* H where
  toFun
    | a i => zmodPower A hA i
    | xa i => X * zmodPower A hA i
  map_one' := zmodPower_zero A hA
  map_mul' := by
    intro g h
    rcases g with i | i <;>
      rcases h with j | j
    · exact zmodPower_add A hA i j
    · simp only [a_mul_xa]
      symm
      calc
        zmodPower A hA i *
              (X * zmodPower A hA j) =
            (zmodPower A hA i * X) *
              zmodPower A hA j := by group
        _ =
            (X * zmodPower A hA (-i)) *
              zmodPower A hA j := by rw [hconj]
        _ =
            X *
              (zmodPower A hA (-i) *
                zmodPower A hA j) := by group
        _ =
            X * zmodPower A hA (-i + j) := by
              rw [zmodPower_add]
        _ =
            X * zmodPower A hA (j - i) := by
              congr 2
              abel
    · simp only [xa_mul_a]
      rw [zmodPower_add]
      group
    · simp only [xa_mul_xa]
      symm
      calc
        X * zmodPower A hA i *
              (X * zmodPower A hA j) =
            X * (zmodPower A hA i * X) *
              zmodPower A hA j := by group
        _ =
            X * (X * zmodPower A hA (-i)) *
              zmodPower A hA j := by
              rw [hconj]
        _ =
            (X * X) * zmodPower A hA (-i) *
              zmodPower A hA j := by group
        _ =
            zmodPower A hA n *
              zmodPower A hA (-i) *
                zmodPower A hA j := by rw [hXsq]
        _ =
            zmodPower A hA (n + (-i) + j) := by
              rw [zmodPower_add, zmodPower_add]
        _ =
            zmodPower A hA (n + j - i) := by
              congr 2
              abel

@[simp]
theorem lift_apply_a
    (A X : H)
    (hA : A ^ (2 * n) = 1)
    (hXsq : X * X = zmodPower A hA n)
    (hconj :
      ∀ i : ZMod (2 * n),
        zmodPower A hA i * X =
          X * zmodPower A hA (-i))
    (i : ZMod (2 * n)) :
    lift A X hA hXsq hconj (a i) =
      zmodPower A hA i :=
  rfl

@[simp]
theorem lift_apply_xa
    (A X : H)
    (hA : A ^ (2 * n) = 1)
    (hXsq : X * X = zmodPower A hA n)
    (hconj :
      ∀ i : ZMod (2 * n),
        zmodPower A hA i * X =
          X * zmodPower A hA (-i))
    (i : ZMod (2 * n)) :
    lift A X hA hXsq hconj (xa i) =
      X * zmodPower A hA i :=
  rfl

end QuaternionGroup
