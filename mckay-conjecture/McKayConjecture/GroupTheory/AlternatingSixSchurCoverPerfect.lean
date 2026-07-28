/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Tactic.Abel
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverPresentation

/-!
# Perfectness of the presented sixfold cover of `A₆`

The exponent-sum matrix of the six defining noncentral and lattice
relations, in the variables `a,b,k₀,k₁,k₂,k₃`, is unimodular.  We record
an integral inverse explicitly.  Consequently every generator has
trivial image in the abelianization, so the presented group is perfect.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- The abelianization images of all six generators in the Schur-cover
presentation are trivial. -/
theorem alternatingSixSchurPresented_generators_mem_commutator :
    Abelianization.of alternatingSixSchurPresentedA = 1 ∧
      Abelianization.of alternatingSixSchurPresentedB = 1 ∧
      Abelianization.of (alternatingSixSchurPresentedK 0) = 1 ∧
      Abelianization.of (alternatingSixSchurPresentedK 1) = 1 ∧
      Abelianization.of (alternatingSixSchurPresentedK 2) = 1 ∧
      Abelianization.of (alternatingSixSchurPresentedK 3) = 1 := by
  let A :=
    Abelianization AlternatingSixSchurPresentedGroup
  let qa : Additive A :=
    Additive.ofMul
      (Abelianization.of alternatingSixSchurPresentedA)
  let qb : Additive A :=
    Additive.ofMul
      (Abelianization.of alternatingSixSchurPresentedB)
  let qk0 : Additive A :=
    Additive.ofMul
      (Abelianization.of (alternatingSixSchurPresentedK 0))
  let qk1 : Additive A :=
    Additive.ofMul
      (Abelianization.of (alternatingSixSchurPresentedK 1))
  let qk2 : Additive A :=
    Additive.ofMul
      (Abelianization.of (alternatingSixSchurPresentedK 2))
  let qk3 : Additive A :=
    Additive.ofMul
      (Abelianization.of (alternatingSixSchurPresentedK 3))
  have h0Group :
      alternatingSixSchurPresentedA ^ 2 =
        alternatingSixSchurPresentedK 0 := by
    simpa [alternatingSixSchurBaseRelator,
      alternatingSixSchurFreeA,
      alternatingSixSchurFreeK,
      alternatingSixSchurPresentedA,
      alternatingSixSchurPresentedK,
      alternatingSixSchurPresentedGenerator,
      alternatingSixSchurGenerator,
      PresentedGroup.of] using
        (alternatingSixSchurPresented_baseRelator 0)
  have h1Group :
      alternatingSixSchurPresentedB ^ 4 =
        alternatingSixSchurPresentedK 1 := by
    simpa [alternatingSixSchurBaseRelator,
      alternatingSixSchurFreeB,
      alternatingSixSchurFreeK,
      alternatingSixSchurPresentedB,
      alternatingSixSchurPresentedK,
      alternatingSixSchurPresentedGenerator,
      alternatingSixSchurGenerator,
      PresentedGroup.of] using
        (alternatingSixSchurPresented_baseRelator 1)
  have h2Group :
      (alternatingSixSchurPresentedA *
          alternatingSixSchurPresentedB) ^ 5 =
        alternatingSixSchurPresentedK 2 := by
    simpa [alternatingSixSchurBaseRelator,
      alternatingSixSchurFreeA,
      alternatingSixSchurFreeB,
      alternatingSixSchurFreeK,
      alternatingSixSchurPresentedA,
      alternatingSixSchurPresentedB,
      alternatingSixSchurPresentedK,
      alternatingSixSchurPresentedGenerator,
      alternatingSixSchurGenerator,
      PresentedGroup.of] using
        (alternatingSixSchurPresented_baseRelator 2)
  have h3Group :
      (alternatingSixSchurPresentedA *
          alternatingSixSchurPresentedB ^ 2) ^ 5 =
        alternatingSixSchurPresentedK 3 := by
    simpa [alternatingSixSchurBaseRelator,
      alternatingSixSchurFreeA,
      alternatingSixSchurFreeB,
      alternatingSixSchurFreeK,
      alternatingSixSchurPresentedA,
      alternatingSixSchurPresentedB,
      alternatingSixSchurPresentedK,
      alternatingSixSchurPresentedGenerator,
      alternatingSixSchurGenerator,
      PresentedGroup.of] using
        (alternatingSixSchurPresented_baseRelator 3)
  have h4Group :
      alternatingSixSchurPresentedK 0 ^ 3 *
          alternatingSixSchurPresentedK 2 ^ (-2 : ℤ) *
          alternatingSixSchurPresentedK 3 = 1 := by
    have h :=
      alternatingSixSchurRelator_eq_one
        (show alternatingSixSchurLatticeRelatorOne ∈
            alternatingSixSchurRelators by
          simp [alternatingSixSchurRelators])
    simpa [alternatingSixSchurLatticeRelatorOne,
      alternatingSixSchurFreeK,
      alternatingSixSchurPresentedK,
      alternatingSixSchurPresentedGenerator,
      alternatingSixSchurGenerator,
      PresentedGroup.of, mul_assoc] using h
  have h5Group :
      alternatingSixSchurPresentedK 1 ^ 4 *
          alternatingSixSchurPresentedK 2 ^ 3 *
          alternatingSixSchurPresentedK 3 ^ (-3 : ℤ) = 1 := by
    have h :=
      alternatingSixSchurRelator_eq_one
        (show alternatingSixSchurLatticeRelatorTwo ∈
            alternatingSixSchurRelators by
          simp [alternatingSixSchurRelators])
    simpa [alternatingSixSchurLatticeRelatorTwo,
      alternatingSixSchurFreeK,
      alternatingSixSchurPresentedK,
      alternatingSixSchurPresentedGenerator,
      alternatingSixSchurGenerator,
      PresentedGroup.of, mul_assoc] using h
  have h0Mul := congrArg Abelianization.of h0Group
  have h1Mul := congrArg Abelianization.of h1Group
  have h2Mul := congrArg Abelianization.of h2Group
  have h3Mul := congrArg Abelianization.of h3Group
  have h4Mul := congrArg Abelianization.of h4Group
  have h5Mul := congrArg Abelianization.of h5Group
  simp only [map_pow] at h0Mul h1Mul
  simp only [map_pow, map_mul] at h2Mul h3Mul
  simp only [map_pow, map_zpow, map_mul, map_one] at h4Mul h5Mul
  have h0 : 2 • qa = qk0 := by
    exact h0Mul
  have h1 : 4 • qb = qk1 := by
    exact h1Mul
  have h2 : 5 • (qa + qb) = qk2 := by
    exact h2Mul
  have h3 : 5 • (qa + 2 • qb) = qk3 := by
    exact h3Mul
  have h4 :
      3 • qk0 + (-2 : ℤ) • qk2 + qk3 = 0 := by
    exact h4Mul
  have h5 :
      4 • qk1 + 3 • qk2 + (-3 : ℤ) • qk3 = 0 := by
    exact h5Mul
  let r0 : Additive A := 2 • qa - qk0
  let r1 : Additive A := 4 • qb - qk1
  let r2 : Additive A := 5 • qa + 5 • qb - qk2
  let r3 : Additive A := 5 • qa + 10 • qb - qk3
  let r4 : Additive A := 3 • qk0 - 2 • qk2 + qk3
  let r5 : Additive A := 4 • qk1 + 3 • qk2 - 3 • qk3
  have hr0 : r0 = 0 :=
    sub_eq_zero.mpr h0
  have hr1 : r1 = 0 :=
    sub_eq_zero.mpr h1
  have hr2 : r2 = 0 := by
    dsimp [r2]
    calc
      5 • qa + 5 • qb - qk2 =
          5 • (qa + qb) - qk2 := by
        abel
      _ = 0 := sub_eq_zero.mpr h2
  have hr3 : r3 = 0 := by
    dsimp [r3]
    calc
      5 • qa + 10 • qb - qk3 =
          5 • (qa + 2 • qb) - qk3 := by
        abel
      _ = 0 := sub_eq_zero.mpr h3
  have hr4 : r4 = 0 := by
    dsimp [r4]
    calc
      3 • qk0 - 2 • qk2 + qk3 =
          3 • qk0 + (-2 : ℤ) • qk2 + qk3 := by
        abel
      _ = 0 := h4
  have hr5 : r5 = 0 := by
    dsimp [r5]
    calc
      4 • qk1 + 3 • qk2 - 3 • qk3 =
          4 • qk1 + 3 • qk2 + (-3 : ℤ) • qk3 := by
        abel
      _ = 0 := h5
  have hqa :
      qa =
        (3 : ℤ) • r0 +
          (-2 : ℤ) • r2 +
          r3 + r4 := by
    dsimp [r0, r1, r2, r3, r4, r5]
    abel
  have hqb :
      qb =
        (4 : ℤ) • r1 +
          (3 : ℤ) • r2 +
          (-3 : ℤ) • r3 +
          r5 := by
    dsimp [r0, r1, r2, r3, r4, r5]
    abel
  have hqk0 :
      qk0 =
        (5 : ℤ) • r0 +
          (-4 : ℤ) • r2 +
          (2 : ℤ) • r3 +
          (2 : ℤ) • r4 := by
    dsimp [r0, r1, r2, r3, r4, r5]
    abel
  have hqk1 :
      qk1 =
        (15 : ℤ) • r1 +
          (12 : ℤ) • r2 +
          (-12 : ℤ) • r3 +
          (4 : ℤ) • r5 := by
    dsimp [r0, r1, r2, r3, r4, r5]
    abel
  have hqk2 :
      qk2 =
        (15 : ℤ) • r0 +
          (20 : ℤ) • r1 +
          (4 : ℤ) • r2 +
          (-10 : ℤ) • r3 +
          (5 : ℤ) • r4 +
          (5 : ℤ) • r5 := by
    dsimp [r0, r1, r2, r3, r4, r5]
    abel
  have hqk3 :
      qk3 =
        (15 : ℤ) • r0 +
          (40 : ℤ) • r1 +
          (20 : ℤ) • r2 +
          (-26 : ℤ) • r3 +
          (5 : ℤ) • r4 +
          (10 : ℤ) • r5 := by
    dsimp [r0, r1, r2, r3, r4, r5]
    abel
  simp only [hr0, hr1, hr2, hr3, hr4, hr5, smul_zero, add_zero] at hqa hqb hqk0 hqk1 hqk2 hqk3
  exact ⟨hqa, hqb, hqk0, hqk1, hqk2, hqk3⟩

/-- The canonical map from the presented Schur cover to its abelianization
is trivial. -/
theorem alternatingSixSchurPresented_abelianization_of_eq_one :
    (Abelianization.of :
      AlternatingSixSchurPresentedGroup →*
        Abelianization AlternatingSixSchurPresentedGroup) = 1 := by
  apply PresentedGroup.ext
  intro i
  fin_cases i
  · exact
      alternatingSixSchurPresented_generators_mem_commutator.1
  · exact
      alternatingSixSchurPresented_generators_mem_commutator.2.1
  · exact
      alternatingSixSchurPresented_generators_mem_commutator.2.2.1
  · exact
      alternatingSixSchurPresented_generators_mem_commutator.2.2.2.1
  · exact
      alternatingSixSchurPresented_generators_mem_commutator.2.2.2.2.1
  · exact
      alternatingSixSchurPresented_generators_mem_commutator.2.2.2.2.2

/-- The presented sixfold central cover of `A₆` is perfect. -/
instance alternatingSixSchurPresentedGroup_isPerfect :
    Group.IsPerfect AlternatingSixSchurPresentedGroup where
  commutator_eq_top := by
    rw [← Abelianization.ker_of]
    rw [alternatingSixSchurPresented_abelianization_of_eq_one]
    simp

end GroupTheory
end McKayConjecture
