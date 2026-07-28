/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic

/-!
# The center and automorphisms of the dihedral group of order eight

This file records an explicit parametrization and decoding of the eight
automorphisms of `DihedralGroup 4`.  Keeping the finite computation here
makes it reusable independently of the application to Sylow subgroups of
the alternating group.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- The center of `D₈` has order two. -/
@[simp]
theorem natCard_center_dihedralGroup_four :
    Nat.card (Subgroup.center (DihedralGroup 4)) = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- Negate a rotation coordinate when the Boolean parameter is set. -/
def dihedralFourSignedIndex
    (negate : Bool) (i : ZMod 4) :
    ZMod 4 :=
  if negate then -i else i

/-- The eight standard automorphisms of `D₈`.  The first parameter moves
the chosen reflection and the Boolean parameter optionally inverts the
rotation. -/
def dihedralFourParametricAutomorphism
    (k : ZMod 4) (negate : Bool) :
    MulAut (DihedralGroup 4) where
  toFun
    | DihedralGroup.r i =>
        DihedralGroup.r (dihedralFourSignedIndex negate i)
    | DihedralGroup.sr i =>
        DihedralGroup.sr
          (k + dihedralFourSignedIndex negate i)
  invFun
    | DihedralGroup.r i =>
        DihedralGroup.r (dihedralFourSignedIndex negate i)
    | DihedralGroup.sr i =>
        DihedralGroup.sr
          (dihedralFourSignedIndex negate (i - k))
  left_inv x := by
    rcases x with i | i <;>
      cases negate <;>
        simp [dihedralFourSignedIndex]
  right_inv x := by
    rcases x with i | i <;>
      cases negate <;>
        simp [dihedralFourSignedIndex]
  map_mul' x y := by
    rcases x with i | i <;>
      rcases y with j | j <;>
        cases negate <;>
          simp [dihedralFourSignedIndex] <;>
            ring

/-- Package the eight parameters as a single map to the automorphism
group. -/
def dihedralFourAutomorphismParameter :
    ZMod 4 × Bool → MulAut (DihedralGroup 4) :=
  fun parameter =>
    dihedralFourParametricAutomorphism
      parameter.1 parameter.2

/-- Distinct parameters give distinct automorphisms. -/
theorem dihedralFourAutomorphismParameter_injective :
    Function.Injective dihedralFourAutomorphismParameter := by
  rintro ⟨k, negate⟩ ⟨l, negate'⟩ h
  have hr :=
    DFunLike.congr_fun h
      (DihedralGroup.r (1 : ZMod 4))
  have hs :=
    DFunLike.congr_fun h
      (DihedralGroup.sr (0 : ZMod 4))
  cases negate <;> cases negate'
  · have hkl : k = l := by
      simpa [dihedralFourAutomorphismParameter,
        dihedralFourParametricAutomorphism,
        dihedralFourSignedIndex] using
          DihedralGroup.sr.inj hs
    subst l
    rfl
  · have hone :
        (1 : ZMod 4) = -1 := by
      simpa [dihedralFourAutomorphismParameter,
        dihedralFourParametricAutomorphism,
        dihedralFourSignedIndex] using
          DihedralGroup.r.inj hr
    exact False.elim ((by decide : (1 : ZMod 4) ≠ -1) hone)
  · have hone :
        -(1 : ZMod 4) = 1 := by
      simpa [dihedralFourAutomorphismParameter,
        dihedralFourParametricAutomorphism,
        dihedralFourSignedIndex] using
          DihedralGroup.r.inj hr
    exact False.elim ((by decide : -(1 : ZMod 4) ≠ 1) hone)
  · have hkl : k = l := by
      simpa [dihedralFourAutomorphismParameter,
        dihedralFourParametricAutomorphism,
        dihedralFourSignedIndex] using
          DihedralGroup.sr.inj hs
    subst l
    rfl

/-- Decode whether an order-four rotation is the chosen rotation or its
inverse.  The irrelevant branches are assigned `false`. -/
def dihedralFourRotationCode :
    DihedralGroup 4 → Bool
  | DihedralGroup.r i => i = -(1 : ZMod 4)
  | DihedralGroup.sr _ => false

/-- Decode the coordinate of a reflection.  The irrelevant rotation branch
is assigned zero. -/
def dihedralFourReflectionCode :
    DihedralGroup 4 → ZMod 4
  | DihedralGroup.r _ => 0
  | DihedralGroup.sr i => i

/-- The two finite coordinates of an automorphism of `D₈`. -/
def dihedralFourAutomorphismCode
    (φ : MulAut (DihedralGroup 4)) :
    Bool × ZMod 4 :=
  (dihedralFourRotationCode
      (φ (DihedralGroup.r (1 : ZMod 4))),
    dihedralFourReflectionCode
      (φ (DihedralGroup.sr (0 : ZMod 4))))

/-- The half-turn commutes with every element of `D₈`. -/
theorem dihedralFour_r_two_commute
    (x : DihedralGroup 4) :
    Commute x (DihedralGroup.r (2 : ZMod 4)) := by
  rcases x with i | i
  · change
      DihedralGroup.r i * DihedralGroup.r (2 : ZMod 4) =
        DihedralGroup.r (2 : ZMod 4) * DihedralGroup.r i
    simp
    ring
  · change
      DihedralGroup.sr i * DihedralGroup.r (2 : ZMod 4) =
        DihedralGroup.r (2 : ZMod 4) * DihedralGroup.sr i
    simp only [DihedralGroup.sr_mul_r,
      DihedralGroup.r_mul_sr]
    congr 1
    rw [sub_eq_add_neg,
      show -(2 : ZMod 4) = 2 by decide]

/-- The standard rotation and reflection of `D₈` do not commute. -/
theorem dihedralFour_rotation_not_commute_reflection :
    ¬Commute
      (DihedralGroup.r (1 : ZMod 4))
      (DihedralGroup.sr (0 : ZMod 4)) := by
  intro hcommute
  have hindex :
      -(1 : ZMod 4) = 1 := by
    simpa [Commute, SemiconjBy] using
      DihedralGroup.sr.inj hcommute
  exact ((by decide : -(1 : ZMod 4) ≠ 1) hindex)

/-- The rotation coordinate recovers the image of the standard
order-four rotation. -/
theorem dihedralFourAutomorphismCode_rotation
    (φ : MulAut (DihedralGroup 4)) :
    φ (DihedralGroup.r (1 : ZMod 4)) =
      if (dihedralFourAutomorphismCode φ).1 then
        DihedralGroup.r (-(1 : ZMod 4))
      else
        DihedralGroup.r (1 : ZMod 4) := by
  have horder :
      orderOf
          (φ (DihedralGroup.r (1 : ZMod 4))) =
        4 := by
    simp
  generalize himage :
      φ (DihedralGroup.r (1 : ZMod 4)) = image
  rw [himage] at horder
  rcases image with i | i
  · fin_cases i
    · change
        orderOf (DihedralGroup.r (0 : ZMod 4)) = 4
          at horder
      simp at horder
    · change
        φ (DihedralGroup.r (1 : ZMod 4)) =
          DihedralGroup.r (1 : ZMod 4) at himage
      change
        DihedralGroup.r (1 : ZMod 4) =
          if (dihedralFourAutomorphismCode φ).1 then
            DihedralGroup.r (-(1 : ZMod 4))
          else
            DihedralGroup.r (1 : ZMod 4)
      simp [dihedralFourAutomorphismCode,
        dihedralFourRotationCode, himage]
    · change
        orderOf (DihedralGroup.r (2 : ZMod 4)) = 4
          at horder
      rw [DihedralGroup.orderOf_r] at horder
      rw [show (2 : ZMod 4).val = 2 by
        exact ZMod.val_cast_of_lt (by norm_num)] at horder
      norm_num at horder
    · change
        φ (DihedralGroup.r (1 : ZMod 4)) =
          DihedralGroup.r (3 : ZMod 4) at himage
      change
        DihedralGroup.r (3 : ZMod 4) =
          if (dihedralFourAutomorphismCode φ).1 then
            DihedralGroup.r (-(1 : ZMod 4))
          else
            DihedralGroup.r (1 : ZMod 4)
      simp [dihedralFourAutomorphismCode,
        dihedralFourRotationCode, himage,
        show (3 : ZMod 4) = -1 by decide]
  · rw [DihedralGroup.orderOf_sr] at horder
    omega

/-- The reflection coordinate recovers the image of the standard
reflection. -/
theorem dihedralFourAutomorphismCode_reflection
    (φ : MulAut (DihedralGroup 4)) :
    φ (DihedralGroup.sr (0 : ZMod 4)) =
      DihedralGroup.sr
        (dihedralFourAutomorphismCode φ).2 := by
  have horder :
      orderOf
          (φ (DihedralGroup.sr (0 : ZMod 4))) =
        2 := by
    simp
  have hnotCommute :
      ¬Commute
        (φ (DihedralGroup.r (1 : ZMod 4)))
        (φ (DihedralGroup.sr (0 : ZMod 4))) := by
    intro hcommute
    have hback :=
      hcommute.map φ.symm
    have :
        Commute
          (DihedralGroup.r (1 : ZMod 4))
          (DihedralGroup.sr (0 : ZMod 4)) := by
      simpa using hback
    exact dihedralFour_rotation_not_commute_reflection this
  generalize himage :
      φ (DihedralGroup.sr (0 : ZMod 4)) = image
  rw [himage] at horder hnotCommute
  rcases image with i | i
  · exfalso
    apply hnotCommute
    rw [dihedralFourAutomorphismCode_rotation]
    split <;>
      simp [Commute, SemiconjBy] <;>
        ring
  · simp [dihedralFourAutomorphismCode,
      dihedralFourReflectionCode, himage]

/-- An automorphism of `D₈` is determined by its two finite coordinates. -/
theorem dihedralFourAutomorphismCode_injective :
    Function.Injective dihedralFourAutomorphismCode := by
  intro φ ψ hcode
  have hrotationCode :
      (dihedralFourAutomorphismCode φ).1 =
        (dihedralFourAutomorphismCode ψ).1 :=
    congrArg Prod.fst hcode
  have hreflectionCode :
      (dihedralFourAutomorphismCode φ).2 =
        (dihedralFourAutomorphismCode ψ).2 :=
    congrArg Prod.snd hcode
  have hr :
      φ (DihedralGroup.r (1 : ZMod 4)) =
        ψ (DihedralGroup.r (1 : ZMod 4)) := by
    rw [dihedralFourAutomorphismCode_rotation,
      dihedralFourAutomorphismCode_rotation,
      hrotationCode]
  have hs :
      φ (DihedralGroup.sr (0 : ZMod 4)) =
        ψ (DihedralGroup.sr (0 : ZMod 4)) := by
    rw [dihedralFourAutomorphismCode_reflection,
      dihedralFourAutomorphismCode_reflection,
      hreflectionCode]
  apply MulEquiv.ext
  intro x
  rcases x with i | i
  · have hi :
        (DihedralGroup.r (1 : ZMod 4)) ^ i.val =
          DihedralGroup.r i := by
      calc
        (DihedralGroup.r (1 : ZMod 4)) ^ i.val =
            DihedralGroup.r (i.val : ZMod 4) :=
          DihedralGroup.r_one_pow i.val
        _ = DihedralGroup.r i :=
          congrArg DihedralGroup.r
            (ZMod.natCast_zmod_val i)
    rw [← hi, map_pow, map_pow, hr]
  · have hrotation :
        φ (DihedralGroup.r i) =
          ψ (DihedralGroup.r i) := by
      have hi :
          (DihedralGroup.r (1 : ZMod 4)) ^ i.val =
            DihedralGroup.r i := by
        calc
          (DihedralGroup.r (1 : ZMod 4)) ^ i.val =
              DihedralGroup.r (i.val : ZMod 4) :=
            DihedralGroup.r_one_pow i.val
          _ = DihedralGroup.r i :=
            congrArg DihedralGroup.r
              (ZMod.natCast_zmod_val i)
      rw [← hi, map_pow, map_pow, hr]
    rw [show
        DihedralGroup.sr i =
          DihedralGroup.sr (0 : ZMod 4) *
            DihedralGroup.r i by simp,
      map_mul, map_mul, hs, hrotation]

/-- The automorphism group of `D₈` has order eight. -/
@[simp]
theorem natCard_mulAut_dihedralGroup_four :
    Nat.card (MulAut (DihedralGroup 4)) = 8 := by
  apply Nat.le_antisymm
  · simpa using
      Nat.card_le_card_of_injective
        dihedralFourAutomorphismCode
        dihedralFourAutomorphismCode_injective
  · have hlower :=
      Nat.card_le_card_of_injective
        dihedralFourAutomorphismParameter
        dihedralFourAutomorphismParameter_injective
    simpa [Nat.card_prod] using hlower

end GroupTheory
end McKayConjecture
