/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverThreeCycleLifts

/-!
# The exponent-three Heisenberg Sylow subgroup of `6.A₆`

Correcting the two raw three-cycle lifts by the central element `k₀`
produces elements `x` and `y` of order three.  With `z = k₀²`, the
relations are

* `x³ = y³ = z³ = 1`;
* `z` is central; and
* `[x,y] = z²`, equivalently `yx = zxy`.

The 27 elements `zᵃxᵇyᶜ`, with `a,b,c : Fin 3`, form a subgroup.  Its
coordinate parametrization is injective, so this is a Sylow `3`-subgroup
of the explicit sixfold cover.
-/

noncomputable section

open scoped commutatorElement

namespace McKayConjecture
namespace GroupTheory

local instance alternatingSixSchurSylowThreeFactPrime :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-! ### Heisenberg generators -/

/-- The central order-three generator `z = k₀²`. -/
def alternatingSixSchurSylowThreeZ :
    AlternatingSixSchurPresentedGroup :=
  alternatingSixSchurPresentedK 0 ^ 2

/-- The order-three lift of `(0 1 2)`. -/
def alternatingSixSchurSylowThreeX :
    AlternatingSixSchurPresentedGroup :=
  alternatingSixSchurRawLeftThreeCycleLift *
    alternatingSixSchurPresentedK 0

/-- The order-three lift of `(3 4 5)`. -/
def alternatingSixSchurSylowThreeY :
    AlternatingSixSchurPresentedGroup :=
  alternatingSixSchurRawRightThreeCycleLift *
    alternatingSixSchurPresentedK 0

theorem alternatingSixSchurPresentedK0_commute
    (g : AlternatingSixSchurPresentedGroup) :
    Commute (alternatingSixSchurPresentedK 0) g :=
  (Subgroup.mem_center_iff.mp
    (alternatingSixSchurPresentedK_mem_center 0) g).symm

theorem alternatingSixSchurSylowThreeZ_mem_center :
    alternatingSixSchurSylowThreeZ ∈
      Subgroup.center AlternatingSixSchurPresentedGroup :=
  (Subgroup.center AlternatingSixSchurPresentedGroup).pow_mem
    (alternatingSixSchurPresentedK_mem_center 0) 2

theorem alternatingSixSchurSylowThreeZ_commute
    (g : AlternatingSixSchurPresentedGroup) :
    Commute alternatingSixSchurSylowThreeZ g :=
  (Subgroup.mem_center_iff.mp
    alternatingSixSchurSylowThreeZ_mem_center g).symm

@[simp]
theorem alternatingSixSchurSylowThreeZ_cube :
    alternatingSixSchurSylowThreeZ ^ 3 = 1 := by
  simpa [alternatingSixSchurSylowThreeZ, ← pow_mul] using
    alternatingSixSchurPresentedK0_pow_six

theorem orderOf_alternatingSixSchurSylowThreeZ :
    orderOf alternatingSixSchurSylowThreeZ = 3 := by
  apply orderOf_eq_prime
  · exact alternatingSixSchurSylowThreeZ_cube
  · intro h
    have hdiv :
        orderOf (alternatingSixSchurPresentedK 0) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one h
    rw [orderOf_alternatingSixSchurPresentedK0] at hdiv
    norm_num at hdiv

@[simp]
theorem alternatingSixSchurProjection_sylowThreeZ :
    alternatingSixSchurProjection alternatingSixSchurSylowThreeZ = 1 := by
  simp [alternatingSixSchurSylowThreeZ,
    alternatingSixSchurProjection_k]

@[simp]
theorem alternatingSixSchurProjection_sylowThreeX :
    alternatingSixSchurProjection alternatingSixSchurSylowThreeX =
      alternatingSixLeftThreeCycle := by
  simp [alternatingSixSchurSylowThreeX,
    alternatingSixSchurRawLeftThreeCycleLift,
    alternatingSixSchurProjection_k]

@[simp]
theorem alternatingSixSchurProjection_sylowThreeY :
    alternatingSixSchurProjection alternatingSixSchurSylowThreeY =
      alternatingSixRightThreeCycle := by
  simp [alternatingSixSchurSylowThreeY,
    alternatingSixSchurRawRightThreeCycleLift,
    alternatingSixSchurProjection_k]

@[simp]
theorem alternatingSixSchurSylowThreeX_cube :
    alternatingSixSchurSylowThreeX ^ 3 = 1 := by
  rw [alternatingSixSchurSylowThreeX,
    (alternatingSixSchurPresentedK0_commute
      alternatingSixSchurRawLeftThreeCycleLift).symm.mul_pow,
    alternatingSixSchurRawLeftThreeCycleLift_cube,
    ← pow_add,
    alternatingSixSchurPresentedK0_pow_six]

@[simp]
theorem alternatingSixSchurSylowThreeY_cube :
    alternatingSixSchurSylowThreeY ^ 3 = 1 := by
  rw [alternatingSixSchurSylowThreeY,
    (alternatingSixSchurPresentedK0_commute
      alternatingSixSchurRawRightThreeCycleLift).symm.mul_pow,
    alternatingSixSchurRawRightThreeCycleLift_cube,
    ← pow_add,
    alternatingSixSchurPresentedK0_pow_six]

theorem orderOf_alternatingSixSchurSylowThreeX :
    orderOf alternatingSixSchurSylowThreeX = 3 := by
  apply orderOf_eq_prime
  · exact alternatingSixSchurSylowThreeX_cube
  · intro h
    have hp :=
      congrArg alternatingSixSchurProjection h
    simp at hp
    have hne : alternatingSixLeftThreeCycle ≠ 1 := by
      decide
    exact hne hp

theorem orderOf_alternatingSixSchurSylowThreeY :
    orderOf alternatingSixSchurSylowThreeY = 3 := by
  apply orderOf_eq_prime
  · exact alternatingSixSchurSylowThreeY_cube
  · intro h
    have hp :=
      congrArg alternatingSixSchurProjection h
    simp at hp
    have hne : alternatingSixRightThreeCycle ≠ 1 := by
      decide
    exact hne hp

/-- Central correction does not change the commutator. -/
@[simp]
theorem alternatingSixSchurSylowThreeXY_commutator :
    ⁅alternatingSixSchurSylowThreeX,
      alternatingSixSchurSylowThreeY⁆ =
        alternatingSixSchurSylowThreeZ ^ 2 := by
  have hkLeft :=
    alternatingSixSchurPresentedK0_commute
      alternatingSixSchurRawLeftThreeCycleLift
  have hkRight :=
    alternatingSixSchurPresentedK0_commute
      alternatingSixSchurRawRightThreeCycleLift
  calc
    ⁅alternatingSixSchurSylowThreeX,
        alternatingSixSchurSylowThreeY⁆ =
        ⁅alternatingSixSchurRawLeftThreeCycleLift,
          alternatingSixSchurRawRightThreeCycleLift⁆ := by
      rw [alternatingSixSchurSylowThreeX,
        alternatingSixSchurSylowThreeY,
        commutatorElement_mul_left_eq_conj_mul]
      have hkProduct :
          Commute
            (alternatingSixSchurPresentedK 0)
            (alternatingSixSchurRawRightThreeCycleLift *
              alternatingSixSchurPresentedK 0) :=
        hkRight.mul_right (Commute.refl _)
      rw [commutatorElement_eq_one_iff_commute.mpr hkProduct]
      simp only [mul_one, one_mul]
      rw [commutatorElement_mul_right_eq_mul_conj,
        commutatorElement_eq_one_iff_commute.mpr hkLeft.symm]
      simp
    _ = alternatingSixSchurPresentedK 0 ^ 4 :=
      alternatingSixSchurRawThreeCycleLifts_commutator
    _ = alternatingSixSchurSylowThreeZ ^ 2 := by
      simp [alternatingSixSchurSylowThreeZ, ← pow_mul]

/-- The collection relation in normal-form orientation. -/
theorem alternatingSixSchurSylowThreeY_mul_X :
    alternatingSixSchurSylowThreeY *
        alternatingSixSchurSylowThreeX =
      alternatingSixSchurSylowThreeZ *
        alternatingSixSchurSylowThreeX *
          alternatingSixSchurSylowThreeY := by
  let z := alternatingSixSchurSylowThreeZ
  let x := alternatingSixSchurSylowThreeX
  let y := alternatingSixSchurSylowThreeY
  have hcomm : ⁅x, y⁆ = z ^ 2 := by
    simpa [x, y, z] using
      alternatingSixSchurSylowThreeXY_commutator
  have hxy : x * y = z ^ 2 * y * x := by
    calc
      x * y = ⁅x, y⁆ * y * x := by
        simp [commutatorElement_def, mul_assoc]
      _ = z ^ 2 * y * x := by rw [hcomm]
  calc
    y * x = z ^ 3 * (y * x) := by
      rw [alternatingSixSchurSylowThreeZ_cube, one_mul]
    _ = z * (z ^ 2 * y * x) := by group
    _ = z * (x * y) := by rw [← hxy]
    _ = z * x * y := by rw [mul_assoc]

/-! ### Collected coordinates -/

/-- Move one `x` past an arbitrary power of `y`. -/
theorem alternatingSixSchurSylowThreeY_pow_mul_X
    (n : ℕ) :
    alternatingSixSchurSylowThreeY ^ n *
        alternatingSixSchurSylowThreeX =
      alternatingSixSchurSylowThreeZ ^ n *
        alternatingSixSchurSylowThreeX *
          alternatingSixSchurSylowThreeY ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      let z := alternatingSixSchurSylowThreeZ
      let x := alternatingSixSchurSylowThreeX
      let y := alternatingSixSchurSylowThreeY
      have hzy : Commute z (y ^ n) :=
        (alternatingSixSchurSylowThreeZ_commute y).pow_right n
      change y ^ (n + 1) * x = z ^ (n + 1) * x * y ^ (n + 1)
      calc
        y ^ (n + 1) * x =
            y ^ n * (y * x) := by
          rw [pow_succ, mul_assoc]
        _ = y ^ n * (z * x * y) := by
          rw [alternatingSixSchurSylowThreeY_mul_X]
        _ = (y ^ n * z) * x * y := by
          simp only [mul_assoc]
        _ = (z * y ^ n) * x * y := by
          rw [← hzy.eq]
        _ = z * (y ^ n * x) * y := by
          simp only [mul_assoc]
        _ = z * (z ^ n * x * y ^ n) * y := by
          rw [ih]
        _ = z ^ (n + 1) * x * y ^ (n + 1) := by
          rw [pow_succ', pow_succ]
          simp only [mul_assoc]

/-- Move an arbitrary power of `x` past an arbitrary power of `y`. -/
theorem alternatingSixSchurSylowThreeY_pow_mul_X_pow
    (m n : ℕ) :
    alternatingSixSchurSylowThreeY ^ m *
        alternatingSixSchurSylowThreeX ^ n =
      alternatingSixSchurSylowThreeZ ^ (m * n) *
        alternatingSixSchurSylowThreeX ^ n *
          alternatingSixSchurSylowThreeY ^ m := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      let z := alternatingSixSchurSylowThreeZ
      let x := alternatingSixSchurSylowThreeX
      let y := alternatingSixSchurSylowThreeY
      have hzx : Commute z (x ^ n) :=
        (alternatingSixSchurSylowThreeZ_commute x).pow_right n
      change
        y ^ m * x ^ (n + 1) =
          z ^ (m * (n + 1)) * x ^ (n + 1) * y ^ m
      calc
        y ^ m * x ^ (n + 1) =
            (y ^ m * x ^ n) * x := by
          rw [pow_succ, mul_assoc]
        _ = (z ^ (m * n) * x ^ n * y ^ m) * x := by
          rw [ih]
        _ =
            (z ^ (m * n) * x ^ n) * (y ^ m * x) := by
          simp only [mul_assoc]
        _ =
            (z ^ (m * n) * x ^ n) *
              (z ^ m * x * y ^ m) := by
          rw [alternatingSixSchurSylowThreeY_pow_mul_X]
        _ =
            z ^ (m * n + m) * x ^ (n + 1) * y ^ m := by
          have hzxPow : Commute (z ^ m) (x ^ n) :=
            (alternatingSixSchurSylowThreeZ_commute x).pow_pow m n
          calc
            (z ^ (m * n) * x ^ n) *
                  (z ^ m * x * y ^ m) =
                z ^ (m * n) * (x ^ n * z ^ m) * x * y ^ m := by
              simp only [mul_assoc]
            _ =
                z ^ (m * n) * (z ^ m * x ^ n) * x * y ^ m := by
              rw [← hzxPow.eq]
            _ =
                z ^ (m * n + m) * x ^ (n + 1) * y ^ m := by
              rw [pow_add, pow_succ]
              simp only [mul_assoc]
        _ =
            z ^ (m * (n + 1)) * x ^ (n + 1) * y ^ m := by
          rw [Nat.mul_succ]

/-- Collection of two Heisenberg normal forms. -/
theorem alternatingSixSchurSylowThree_collect
    (a b c d e f : ℕ) :
    (alternatingSixSchurSylowThreeZ ^ a *
          alternatingSixSchurSylowThreeX ^ b *
          alternatingSixSchurSylowThreeY ^ c) *
        (alternatingSixSchurSylowThreeZ ^ d *
          alternatingSixSchurSylowThreeX ^ e *
          alternatingSixSchurSylowThreeY ^ f) =
      alternatingSixSchurSylowThreeZ ^ (a + d + c * e) *
        alternatingSixSchurSylowThreeX ^ (b + e) *
          alternatingSixSchurSylowThreeY ^ (c + f) := by
  let z := alternatingSixSchurSylowThreeZ
  let x := alternatingSixSchurSylowThreeX
  let y := alternatingSixSchurSylowThreeY
  have hzx : Commute (z ^ d) (x ^ b) :=
    (alternatingSixSchurSylowThreeZ_commute x).pow_pow d b
  have hzy : Commute (z ^ d) (y ^ c) :=
    (alternatingSixSchurSylowThreeZ_commute y).pow_pow d c
  have hcollect :
      y ^ c * x ^ e = z ^ (c * e) * x ^ e * y ^ c := by
    simpa [x, y, z] using
      alternatingSixSchurSylowThreeY_pow_mul_X_pow c e
  have hcentral :
      Commute (z ^ (c * e)) (x ^ b) :=
    (alternatingSixSchurSylowThreeZ_commute x).pow_pow (c * e) b
  change
    (z ^ a * x ^ b * y ^ c) * (z ^ d * x ^ e * y ^ f) =
      z ^ (a + d + c * e) * x ^ (b + e) * y ^ (c + f)
  calc
    (z ^ a * x ^ b * y ^ c) * (z ^ d * x ^ e * y ^ f) =
        z ^ a * x ^ b * (y ^ c * z ^ d) * x ^ e * y ^ f := by
      simp only [mul_assoc]
    _ =
        z ^ a * x ^ b * (z ^ d * y ^ c) * x ^ e * y ^ f := by
      rw [← hzy.eq]
    _ =
        z ^ a * (x ^ b * z ^ d) * (y ^ c * x ^ e) * y ^ f := by
      simp only [mul_assoc]
    _ =
        z ^ a * (z ^ d * x ^ b) * (y ^ c * x ^ e) * y ^ f := by
      rw [← hzx.eq]
    _ =
        (z ^ a * z ^ d) * x ^ b *
            (z ^ (c * e) * x ^ e * y ^ c) * y ^ f := by
      rw [hcollect]
      simp only [mul_assoc]
    _ =
        (z ^ a * z ^ d) * (x ^ b * z ^ (c * e)) *
            x ^ e * y ^ c * y ^ f := by
      simp only [mul_assoc]
    _ =
        (z ^ a * z ^ d) * (z ^ (c * e) * x ^ b) *
            x ^ e * y ^ c * y ^ f := by
      rw [← hcentral.eq]
    _ =
        z ^ (a + d + c * e) * x ^ (b + e) * y ^ (c + f) := by
      simp only [pow_add, mul_assoc]

/-- Coordinates for the 27 collected normal forms. -/
@[ext]
structure AlternatingSixSchurSylowThreeCoordinates where
  z : Fin 3
  x : Fin 3
  y : Fin 3
deriving DecidableEq, Fintype

/-- Evaluate one collected coordinate triple. -/
def alternatingSixSchurSylowThreeParameterizedElement
    (c : AlternatingSixSchurSylowThreeCoordinates) :
    AlternatingSixSchurPresentedGroup :=
  alternatingSixSchurSylowThreeZ ^ c.z.val *
    alternatingSixSchurSylowThreeX ^ c.x.val *
      alternatingSixSchurSylowThreeY ^ c.y.val

/-- Every collected element has cube one. -/
theorem alternatingSixSchurSylowThreeParameterizedElement_cube
    (q : AlternatingSixSchurSylowThreeCoordinates) :
    alternatingSixSchurSylowThreeParameterizedElement q ^ 3 = 1 := by
  rcases q with ⟨a, b, c⟩
  change
    (alternatingSixSchurSylowThreeZ ^ a.val *
        alternatingSixSchurSylowThreeX ^ b.val *
          alternatingSixSchurSylowThreeY ^ c.val) ^ 3 = 1
  rw [show
      (alternatingSixSchurSylowThreeZ ^ a.val *
          alternatingSixSchurSylowThreeX ^ b.val *
            alternatingSixSchurSylowThreeY ^ c.val) ^ 3 =
        ((alternatingSixSchurSylowThreeZ ^ a.val *
            alternatingSixSchurSylowThreeX ^ b.val *
              alternatingSixSchurSylowThreeY ^ c.val) *
          (alternatingSixSchurSylowThreeZ ^ a.val *
            alternatingSixSchurSylowThreeX ^ b.val *
              alternatingSixSchurSylowThreeY ^ c.val)) *
          (alternatingSixSchurSylowThreeZ ^ a.val *
            alternatingSixSchurSylowThreeX ^ b.val *
              alternatingSixSchurSylowThreeY ^ c.val) by
        simp [pow_succ, mul_assoc]]
  rw [alternatingSixSchurSylowThree_collect,
    alternatingSixSchurSylowThree_collect]
  have hzExponent :
      a.val + a.val + c.val * b.val + a.val +
          (c.val + c.val) * b.val =
        3 * (a.val + c.val * b.val) := by
    ring
  have hxExponent :
      b.val + b.val + b.val = 3 * b.val := by
    omega
  have hyExponent :
      c.val + c.val + c.val = 3 * c.val := by
    omega
  rw [hzExponent, hxExponent, hyExponent,
    pow_mul, pow_mul, pow_mul,
    alternatingSixSchurSylowThreeZ_cube,
    alternatingSixSchurSylowThreeX_cube,
    alternatingSixSchurSylowThreeY_cube]
  simp

@[simp]
theorem alternatingSixSchurProjection_sylowThreeParameterizedElement
    (q : AlternatingSixSchurSylowThreeCoordinates) :
    alternatingSixSchurProjection
        (alternatingSixSchurSylowThreeParameterizedElement q) =
      alternatingSixSylowThreeParameterizedElement (q.x, q.y) := by
  simp [alternatingSixSchurSylowThreeParameterizedElement,
    alternatingSixSylowThreeParameterizedElement]

/-- The 27 collected normal forms are distinct. -/
theorem alternatingSixSchurSylowThreeParameterizedElement_injective :
    Function.Injective
      alternatingSixSchurSylowThreeParameterizedElement := by
  rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h
  have hprojection :=
    congrArg alternatingSixSchurProjection h
  have htarget :
      (b, c) = (e, f) :=
    alternatingSixSylowThreeParameterizedElement_injective (by
      simpa using hprojection)
  have hb : b = e := congrArg Prod.fst htarget
  have hc : c = f := congrArg Prod.snd htarget
  subst e
  subst f
  change
    alternatingSixSchurSylowThreeZ ^ a.val *
          alternatingSixSchurSylowThreeX ^ b.val *
          alternatingSixSchurSylowThreeY ^ c.val =
      alternatingSixSchurSylowThreeZ ^ d.val *
          alternatingSixSchurSylowThreeX ^ b.val *
          alternatingSixSchurSylowThreeY ^ c.val at h
  have hzpow :
      alternatingSixSchurSylowThreeZ ^ a.val =
        alternatingSixSchurSylowThreeZ ^ d.val := by
    apply mul_right_cancel
    apply mul_right_cancel
    simpa only [mul_assoc] using h
  have hmod :=
    (pow_inj_mod
      (x := alternatingSixSchurSylowThreeZ)).mp hzpow
  rw [orderOf_alternatingSixSchurSylowThreeZ,
    Nat.mod_eq_of_lt a.isLt,
    Nat.mod_eq_of_lt d.isLt] at hmod
  have ha : a = d := Fin.ext hmod
  subst d
  rfl

/-- The product of two collected elements again has collected
coordinates. -/
theorem alternatingSixSchurSylowThreeParameterizedElement_mul_exists
    (q r : AlternatingSixSchurSylowThreeCoordinates) :
    ∃ s : AlternatingSixSchurSylowThreeCoordinates,
      alternatingSixSchurSylowThreeParameterizedElement s =
        alternatingSixSchurSylowThreeParameterizedElement q *
          alternatingSixSchurSylowThreeParameterizedElement r := by
  let zExponent :=
    q.z.val + r.z.val + q.y.val * r.x.val
  let xExponent :=
    q.x.val + r.x.val
  let yExponent :=
    q.y.val + r.y.val
  let zCoordinate : Fin 3 :=
    ⟨zExponent % 3, Nat.mod_lt _ (by norm_num)⟩
  let xCoordinate : Fin 3 :=
    ⟨xExponent % 3, Nat.mod_lt _ (by norm_num)⟩
  let yCoordinate : Fin 3 :=
    ⟨yExponent % 3, Nat.mod_lt _ (by norm_num)⟩
  refine
    ⟨⟨zCoordinate, xCoordinate, yCoordinate⟩, ?_⟩
  change
    alternatingSixSchurSylowThreeZ ^ (zExponent % 3) *
          alternatingSixSchurSylowThreeX ^ (xExponent % 3) *
          alternatingSixSchurSylowThreeY ^ (yExponent % 3) =
      (alternatingSixSchurSylowThreeZ ^ q.z.val *
          alternatingSixSchurSylowThreeX ^ q.x.val *
          alternatingSixSchurSylowThreeY ^ q.y.val) *
        (alternatingSixSchurSylowThreeZ ^ r.z.val *
          alternatingSixSchurSylowThreeX ^ r.x.val *
          alternatingSixSchurSylowThreeY ^ r.y.val)
  rw [← pow_eq_pow_mod zExponent
      alternatingSixSchurSylowThreeZ_cube,
    ← pow_eq_pow_mod xExponent
      alternatingSixSchurSylowThreeX_cube,
    ← pow_eq_pow_mod yExponent
      alternatingSixSchurSylowThreeY_cube]
  exact
    (alternatingSixSchurSylowThree_collect
      q.z.val q.x.val q.y.val
      r.z.val r.x.val r.y.val).symm

/-- The explicit Heisenberg subgroup of the sixfold cover. -/
def alternatingSixSchurSylowThreeSubgroup :
    Subgroup AlternatingSixSchurPresentedGroup where
  carrier :=
    Set.range alternatingSixSchurSylowThreeParameterizedElement
  one_mem' := by
    refine ⟨⟨0, 0, 0⟩, ?_⟩
    simp [alternatingSixSchurSylowThreeParameterizedElement]
  mul_mem' := fun {g h} hg hh => by
    obtain ⟨q, rfl⟩ := hg
    obtain ⟨r, rfl⟩ := hh
    obtain ⟨s, hs⟩ :=
      alternatingSixSchurSylowThreeParameterizedElement_mul_exists q r
    exact ⟨s, hs⟩
  inv_mem' := fun {g} hg => by
    obtain ⟨q, rfl⟩ := hg
    obtain ⟨s, hs⟩ :=
      alternatingSixSchurSylowThreeParameterizedElement_mul_exists q q
    refine ⟨s, ?_⟩
    rw [hs]
    symm
    apply inv_eq_iff_mul_eq_one.mpr
    simpa [pow_succ, mul_assoc] using
      alternatingSixSchurSylowThreeParameterizedElement_cube q

/-- Coordinates are equivalent to the explicit subgroup. -/
noncomputable def alternatingSixSchurSylowThreeCoordinateEquiv :
    AlternatingSixSchurSylowThreeCoordinates ≃
      alternatingSixSchurSylowThreeSubgroup where
  toFun q :=
    ⟨alternatingSixSchurSylowThreeParameterizedElement q,
      ⟨q, rfl⟩⟩
  invFun g :=
    Classical.choose g.property
  left_inv q := by
    apply alternatingSixSchurSylowThreeParameterizedElement_injective
    exact Classical.choose_spec
      ((⟨alternatingSixSchurSylowThreeParameterizedElement q,
        ⟨q, rfl⟩⟩ :
          alternatingSixSchurSylowThreeSubgroup).property)
  right_inv g := by
    apply Subtype.ext
    exact Classical.choose_spec g.property

/-- The explicit Heisenberg subgroup has order 27. -/
@[simp]
theorem natCard_alternatingSixSchurSylowThreeSubgroup :
    Nat.card alternatingSixSchurSylowThreeSubgroup = 27 := by
  rw [Nat.card_congr
    alternatingSixSchurSylowThreeCoordinateEquiv.symm]
  rw [Nat.card_eq_fintype_card]
  decide

/-- The order-27 subgroup is a Sylow `3`-subgroup of the order-2160
sixfold cover. -/
def alternatingSixSchurSylowThree :
    Sylow 3 AlternatingSixSchurPresentedGroup :=
  Sylow.ofCard alternatingSixSchurSylowThreeSubgroup (by
    rw [natCard_alternatingSixSchurSylowThreeSubgroup,
      natCard_alternatingSixSchurPresentedGroup]
    have hfactorization :
        Nat.factorization 2160 3 = 3 := by
      conv_lhs =>
        rw [show 2160 = 2 ^ 4 * 3 ^ 3 * 5 by norm_num]
      rw [Nat.factorization_mul (by norm_num) (by norm_num),
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply, Finsupp.add_apply,
        Nat.prime_two.factorization_pow,
        Nat.prime_three.factorization_pow,
        Nat.prime_five.factorization]
      norm_num [Finsupp.single_apply]
    rw [hfactorization]
    norm_num)

@[simp]
theorem alternatingSixSchurSylowThree_coe :
    (alternatingSixSchurSylowThree :
        Subgroup AlternatingSixSchurPresentedGroup) =
      alternatingSixSchurSylowThreeSubgroup :=
  rfl

end GroupTheory
end McKayConjecture
