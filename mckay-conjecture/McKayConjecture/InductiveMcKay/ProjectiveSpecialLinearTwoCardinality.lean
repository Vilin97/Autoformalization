/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.Multiplicity
import McKayConjecture.InductiveMcKay.ProjectiveSpecialLinearTwoCanonicalCover

/-!
# Cardinalities in the simple PSL₂ family

This file derives the orders of the canonical special-linear cover, its
center, and the projective quotient from mathlib's cardinality theorem for
`GL`, determinant surjectivity, the cyclicity of finite-field units, and the
quotient-cardinality formula.

No order formula is postulated.  In particular, these calculations are
independent of whether the special-linear central cover is universal.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- `SL(2,F)` is the kernel of the determinant on `GL(2,F)`. -/
private def specialLinearTwoEquivDetKernel
    (F : Type) [Field F] :
    Matrix.SpecialLinearGroup (Fin 2) F ≃*
      (Matrix.GeneralLinearGroup.det :
        Matrix.GeneralLinearGroup (Fin 2) F →* Fˣ).ker where
  toFun g :=
    ⟨Matrix.SpecialLinearGroup.toGL g, by simp⟩
  invFun g :=
    ⟨(g.1 : Matrix.GeneralLinearGroup (Fin 2) F).1, by
      exact
        congrArg Units.val
          (MonoidHom.mem_ker.mp g.2)⟩
  left_inv g := by
    apply Subtype.ext
    rfl
  right_inv g := by
    apply Subtype.ext
    apply Units.ext
    rfl
  map_mul' _ _ := by
    apply Subtype.ext
    apply Units.ext
    rfl

/-- The order of the canonical special-linear cover is
`q(q² - 1)`, where `q = r^n`. -/
theorem natCard_projectiveSpecialLinearTwoSpecialLinearCover
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    Nat.card (projectiveSpecialLinearTwoSpecialLinearCover a) =
      (a.characteristic ^ a.degree) *
        ((a.characteristic ^ a.degree) ^ 2 - 1) := by
  letI : Fact a.characteristic.Prime :=
    ⟨a.characteristic_prime⟩
  let F := GaloisField a.characteristic a.degree
  let q := a.characteristic ^ a.degree
  letI : Fintype F :=
    Fintype.ofFinite F
  have hq : 4 ≤ q :=
    a.four_le_card
  have hFcard : Nat.card F = q := by
    dsimp only [F, q]
    exact
      GaloisField.card
        a.characteristic a.degree a.degree_ne_zero
  let det :
      Matrix.GeneralLinearGroup (Fin 2) F →* Fˣ :=
    Matrix.GeneralLinearGroup.det
  have hdetSurjective :
      Function.Surjective det :=
    Matrix.GeneralLinearGroup.det_surjective
  have hGL :
      Nat.card (Matrix.GeneralLinearGroup (Fin 2) F) =
        (q ^ 2 - 1) * (q ^ 2 - q) := by
    have hFintypeCard :
        Fintype.card F = q := by
      simpa [Nat.card_eq_fintype_card] using hFcard
    rw [Matrix.card_GL_field, Fin.prod_univ_two,
      hFintypeCard]
    norm_num
  have hSLker :
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
        Nat.card det.ker :=
    Nat.card_congr
      (specialLinearTwoEquivDetKernel F).toEquiv
  have hdetCard :
      Nat.card (Matrix.GeneralLinearGroup (Fin 2) F) =
        Nat.card det.ker * Nat.card Fˣ := by
    calc
      Nat.card (Matrix.GeneralLinearGroup (Fin 2) F) =
          Nat.card det.ker * det.ker.index :=
        det.ker.card_mul_index.symm
      _ = Nat.card det.ker * Nat.card det.range := by
        rw [Subgroup.index_ker]
      _ = Nat.card det.ker * Nat.card Fˣ := by
        rw [MonoidHom.range_eq_top.mpr hdetSurjective]
        simp
  have hunits :
      Nat.card Fˣ = q - 1 := by
    rw [Nat.card_units, hFcard]
  have hqSub :
      q ^ 2 - q = q * (q - 1) := by
    rw [pow_two, Nat.mul_sub_left_distrib]
    simp
  have hmul :
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) *
          (q - 1) =
        (q * (q ^ 2 - 1)) * (q - 1) := by
    calc
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) *
          (q - 1) =
          Nat.card det.ker * Nat.card Fˣ := by
        rw [hSLker, hunits]
      _ = Nat.card (Matrix.GeneralLinearGroup (Fin 2) F) :=
        hdetCard.symm
      _ = (q ^ 2 - 1) * (q ^ 2 - q) :=
        hGL
      _ = (q * (q ^ 2 - 1)) * (q - 1) := by
        rw [hqSub]
        ac_rfl
  have hqSubNe : q - 1 ≠ 0 := by
    omega
  change
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
      q * (q ^ 2 - 1)
  exact mul_right_cancel₀ hqSubNe hmul

/-- The center of the canonical special-linear cover has order
`gcd(q - 1, 2)`. -/
theorem natCard_center_projectiveSpecialLinearTwoSpecialLinearCover
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    Nat.card
        (Subgroup.center
          (projectiveSpecialLinearTwoSpecialLinearCover a)) =
      (a.characteristic ^ a.degree - 1).gcd 2 := by
  letI : Fact a.characteristic.Prime :=
    ⟨a.characteristic_prime⟩
  let F := GaloisField a.characteristic a.degree
  let q := a.characteristic ^ a.degree
  have hFcard : Nat.card F = q := by
    dsimp only [F, q]
    exact
      GaloisField.card
        a.characteristic a.degree a.degree_ne_zero
  letI : IsCyclic Fˣ := by
    infer_instance
  change
    Nat.card
        (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) F)) =
      (q - 1).gcd 2
  calc
    Nat.card
        (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) F)) =
        Nat.card (rootsOfUnity 2 F) :=
      Nat.card_congr
        (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity
          (n := Fin 2) (R := F)).toEquiv
    _ = Nat.card (powMonoidHom 2 : Fˣ →* Fˣ).ker := by
      rw [rootsOfUnity_eq_ker]
    _ = (Nat.card Fˣ).gcd 2 :=
      IsCyclic.card_powMonoidHom_ker Fˣ 2
    _ = (q - 1).gcd 2 := by
      rw [Nat.card_units, hFcard]

/-- Multiplicative form of the projective order formula.  It avoids
division and is often the most convenient form for divisibility arguments. -/
theorem natCard_projectiveSpecialLinearTwoRepresentative_mul_center
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    Nat.card (projectiveSpecialLinearTwoRepresentative a) *
        (a.characteristic ^ a.degree - 1).gcd 2 =
      (a.characteristic ^ a.degree) *
        ((a.characteristic ^ a.degree) ^ 2 - 1) := by
  rw [← natCard_center_projectiveSpecialLinearTwoSpecialLinearCover a,
    ← natCard_projectiveSpecialLinearTwoSpecialLinearCover a]
  exact
    (Subgroup.center
      (projectiveSpecialLinearTwoSpecialLinearCover
        a)).card_eq_card_quotient_mul_card_subgroup.symm

/-- The usual quotient form of the projective order formula. -/
theorem natCard_projectiveSpecialLinearTwoRepresentative
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    Nat.card (projectiveSpecialLinearTwoRepresentative a) =
      ((a.characteristic ^ a.degree) *
        ((a.characteristic ^ a.degree) ^ 2 - 1)) /
          (a.characteristic ^ a.degree - 1).gcd 2 := by
  apply Nat.eq_div_of_mul_eq_left
  · exact
      (Nat.gcd_pos_of_pos_left 2 (by
        have hq := a.four_le_card
        omega : 0 < a.characteristic ^ a.degree - 1)).ne'
  · exact
      natCard_projectiveSpecialLinearTwoRepresentative_mul_center a

/-! ### The even- and odd-characteristic split -/

/-- In characteristic two the special-linear center is trivial. -/
theorem natCard_center_projectiveSpecialLinearTwoSpecialLinearCover_of_characteristic_two
    (a : ProjectiveSpecialLinearTwoSimpleParameter)
    (ha : a.characteristic = 2) :
    Nat.card
        (Subgroup.center
          (projectiveSpecialLinearTwoSpecialLinearCover a)) =
      1 := by
  rw [natCard_center_projectiveSpecialLinearTwoSpecialLinearCover]
  have hqEven :
      Even (a.characteristic ^ a.degree) := by
    rw [ha]
    exact even_two.pow_of_ne_zero a.degree_ne_zero
  have hq := a.four_le_card
  have hqSubOdd :
      Odd (a.characteristic ^ a.degree - 1) :=
    Nat.Even.sub_odd (by omega) hqEven odd_one
  exact Nat.coprime_two_right.mpr hqSubOdd

/-- In odd characteristic the special-linear center has order two. -/
theorem natCard_center_projectiveSpecialLinearTwoSpecialLinearCover_of_characteristic_ne_two
    (a : ProjectiveSpecialLinearTwoSimpleParameter)
    (ha : a.characteristic ≠ 2) :
    Nat.card
        (Subgroup.center
          (projectiveSpecialLinearTwoSpecialLinearCover a)) =
      2 := by
  rw [natCard_center_projectiveSpecialLinearTwoSpecialLinearCover]
  have hqOdd :
      Odd (a.characteristic ^ a.degree) :=
    (a.characteristic_prime.odd_of_ne_two ha).pow
  exact
    Nat.gcd_eq_right_iff_dvd.mpr
      (even_iff_two_dvd.mp
        (hqOdd.tsub_odd odd_one))

/-- In characteristic two, `SL(2,q)` and `PSL(2,q)` have the same order. -/
theorem natCard_projectiveSpecialLinearTwoRepresentative_of_characteristic_two
    (a : ProjectiveSpecialLinearTwoSimpleParameter)
    (ha : a.characteristic = 2) :
    Nat.card (projectiveSpecialLinearTwoRepresentative a) =
      (a.characteristic ^ a.degree) *
        ((a.characteristic ^ a.degree) ^ 2 - 1) := by
  have h :=
    natCard_projectiveSpecialLinearTwoRepresentative_mul_center a
  rw [show
      (a.characteristic ^ a.degree - 1).gcd 2 = 1 by
        simpa only [
          natCard_center_projectiveSpecialLinearTwoSpecialLinearCover a]
          using
            natCard_center_projectiveSpecialLinearTwoSpecialLinearCover_of_characteristic_two
              a ha,
    mul_one] at h
  exact h

/-- In odd characteristic, the projective order is half the
special-linear order. -/
theorem natCard_projectiveSpecialLinearTwoRepresentative_of_characteristic_ne_two
    (a : ProjectiveSpecialLinearTwoSimpleParameter)
    (ha : a.characteristic ≠ 2) :
    Nat.card (projectiveSpecialLinearTwoRepresentative a) =
      ((a.characteristic ^ a.degree) *
        ((a.characteristic ^ a.degree) ^ 2 - 1)) / 2 := by
  rw [natCard_projectiveSpecialLinearTwoRepresentative]
  congr 1
  simpa only [
    natCard_center_projectiveSpecialLinearTwoSpecialLinearCover a]
    using
      natCard_center_projectiveSpecialLinearTwoSpecialLinearCover_of_characteristic_ne_two
        a ha

/-! ### Prime support -/

/-- Factorization of the special-linear order into the three standard
rank-one factors. -/
theorem natCard_projectiveSpecialLinearTwoSpecialLinearCover_factorization
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    Nat.card (projectiveSpecialLinearTwoSpecialLinearCover a) =
      (a.characteristic ^ a.degree) *
        (a.characteristic ^ a.degree - 1) *
          (a.characteristic ^ a.degree + 1) := by
  rw [natCard_projectiveSpecialLinearTwoSpecialLinearCover]
  have hq := a.four_le_card
  have hfactor :
      (a.characteristic ^ a.degree) ^ 2 - 1 =
        (a.characteristic ^ a.degree - 1) *
          (a.characteristic ^ a.degree + 1) := by
    have hsquare :
        1 ≤ (a.characteristic ^ a.degree) ^ 2 := by
      nlinarith
    apply
      (tsub_eq_iff_eq_add_of_le hsquare).2
    have hqSub :
        a.characteristic ^ a.degree - 1 + 1 =
          a.characteristic ^ a.degree :=
      Nat.sub_add_cancel (by omega)
    nlinarith
  rw [hfactor, mul_assoc]

/-- Exact prime support of the special-linear cover. -/
theorem prime_dvd_natCard_projectiveSpecialLinearTwoSpecialLinearCover_iff
    (a : ProjectiveSpecialLinearTwoSimpleParameter)
    {p : ℕ}
    (hp : p.Prime) :
    p ∣ Nat.card (projectiveSpecialLinearTwoSpecialLinearCover a) ↔
      p ∣ a.characteristic ^ a.degree ∨
        p ∣ a.characteristic ^ a.degree - 1 ∨
          p ∣ a.characteristic ^ a.degree + 1 := by
  rw [natCard_projectiveSpecialLinearTwoSpecialLinearCover_factorization]
  simp only [hp.dvd_mul]
  tauto

/-- Every prime occurring in the projective quotient already occurs in
one of the three standard rank-one factors. -/
theorem prime_dvd_natCard_projectiveSpecialLinearTwoRepresentative_factors
    (a : ProjectiveSpecialLinearTwoSimpleParameter)
    {p : ℕ}
    (hp : p.Prime)
    (hdiv :
      p ∣ Nat.card (projectiveSpecialLinearTwoRepresentative a)) :
    p ∣ a.characteristic ^ a.degree ∨
      p ∣ a.characteristic ^ a.degree - 1 ∨
        p ∣ a.characteristic ^ a.degree + 1 := by
  apply
    (prime_dvd_natCard_projectiveSpecialLinearTwoSpecialLinearCover_iff
      a hp).mp
  exact
    hdiv.trans
      ((Subgroup.center
        (projectiveSpecialLinearTwoSpecialLinearCover
          a)).card_quotient_dvd_card)

/-- Exact prime support of the projective quotient.  Quotienting by the
center removes no prime from the support: in odd characteristic the center
has order two, while `q² - 1` is divisible by eight. -/
theorem prime_dvd_natCard_projectiveSpecialLinearTwoRepresentative_iff
    (a : ProjectiveSpecialLinearTwoSimpleParameter)
    {p : ℕ}
    (hp : p.Prime) :
    p ∣ Nat.card (projectiveSpecialLinearTwoRepresentative a) ↔
      p ∣ a.characteristic ^ a.degree ∨
        p ∣ a.characteristic ^ a.degree - 1 ∨
          p ∣ a.characteristic ^ a.degree + 1 := by
  constructor
  · exact
      prime_dvd_natCard_projectiveSpecialLinearTwoRepresentative_factors
        a hp
  · intro hfactors
    have hSL :
        p ∣ Nat.card
          (projectiveSpecialLinearTwoSpecialLinearCover a) :=
      (prime_dvd_natCard_projectiveSpecialLinearTwoSpecialLinearCover_iff
        a hp).mpr hfactors
    have horder :
        p ∣
          (a.characteristic ^ a.degree) *
            ((a.characteristic ^ a.degree) ^ 2 - 1) := by
      rw [← natCard_projectiveSpecialLinearTwoSpecialLinearCover]
      exact hSL
    by_cases hpTwo : p = 2
    · subst p
      by_cases hcharacteristic :
          a.characteristic = 2
      · rw [
          natCard_projectiveSpecialLinearTwoRepresentative_of_characteristic_two
            a hcharacteristic]
        exact horder
      · rw [
          natCard_projectiveSpecialLinearTwoRepresentative_of_characteristic_ne_two
            a hcharacteristic]
        have hqOdd :
            Odd (a.characteristic ^ a.degree) :=
          (a.characteristic_prime.odd_of_ne_two
            hcharacteristic).pow
        have hEight :
            8 ∣ (a.characteristic ^ a.degree) ^ 2 - 1 :=
          Nat.eight_dvd_sq_sub_one_of_odd hqOdd
        have hFour :
            4 ∣
              (a.characteristic ^ a.degree) *
                ((a.characteristic ^ a.degree) ^ 2 - 1) :=
          dvd_mul_of_dvd_right
            ((by norm_num : 4 ∣ 8).trans hEight)
            (a.characteristic ^ a.degree)
        have hTwo :
            2 ∣
              (a.characteristic ^ a.degree) *
                ((a.characteristic ^ a.degree) ^ 2 - 1) :=
          (by norm_num : 2 ∣ 4).trans hFour
        apply (Nat.dvd_div_iff_mul_dvd hTwo).2
        simpa using hFour
    · by_cases hcharacteristic :
          a.characteristic = 2
      · rw [
          natCard_projectiveSpecialLinearTwoRepresentative_of_characteristic_two
            a hcharacteristic]
        exact horder
      · have hcenter :
            (a.characteristic ^ a.degree - 1).gcd 2 = 2 := by
          have h :=
            natCard_center_projectiveSpecialLinearTwoSpecialLinearCover_of_characteristic_ne_two
              a hcharacteristic
          rw [
            natCard_center_projectiveSpecialLinearTwoSpecialLinearCover]
            at h
          exact h
        have hproduct :=
          natCard_projectiveSpecialLinearTwoRepresentative_mul_center a
        rw [hcenter] at hproduct
        have hpProduct :
            p ∣
              Nat.card
                  (projectiveSpecialLinearTwoRepresentative a) *
                2 := by
          rw [hproduct]
          exact horder
        exact
          (hp.dvd_mul.mp hpProduct).resolve_right (by
            intro hpDvdTwo
            exact
              hpTwo
                ((Nat.prime_dvd_prime_iff_eq
                  hp Nat.prime_two).mp hpDvdTwo))

/-- The defining field characteristic occurs in the prime support of every
parameterized projective representative. -/
theorem characteristic_dvd_natCard_projectiveSpecialLinearTwoRepresentative
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    a.characteristic ∣
      Nat.card (projectiveSpecialLinearTwoRepresentative a) := by
  apply
    (prime_dvd_natCard_projectiveSpecialLinearTwoRepresentative_iff
      a a.characteristic_prime).mpr
  exact
    Or.inl
      (dvd_pow_self a.characteristic a.degree_ne_zero)

/-- A prime dividing the projective representative has size at most
`q + 1`. -/
theorem prime_le_card_parameter_add_one_of_dvd_projectiveSpecialLinearTwoRepresentative
    (a : ProjectiveSpecialLinearTwoSimpleParameter)
    {p : ℕ}
    (hp : p.Prime)
    (hdiv :
      p ∣ Nat.card (projectiveSpecialLinearTwoRepresentative a)) :
    p ≤ a.characteristic ^ a.degree + 1 := by
  have hq := a.four_le_card
  rcases
      prime_dvd_natCard_projectiveSpecialLinearTwoRepresentative_factors
        a hp hdiv with
    h | h | h
  · exact
      (Nat.le_of_dvd (by omega) h).trans (by omega)
  · exact
      (Nat.le_of_dvd (by omega) h).trans (by omega)
  · exact
      Nat.le_of_dvd (by omega) h

end InductiveMcKay
end McKayConjecture
