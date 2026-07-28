/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.CoprimeActionSemidirect

/-!
# The fixed-point product in a coprime-action semidirect product

Let a finite `p`-group `P` act on a finite `p′`-group `A`.  The direct
product `A^P × P` has a canonical embedding in `A ⋊ P`.  This file proves
the group-theoretic parts of the restriction seam used by
Dade--Glauberman--Nagao arguments:

* the fixed-point product embedding is injective;
* the canonical `A`-kernel times its range is the whole semidirect product;
* its intersection with the canonical kernel is exactly `A^P`; and
* under the coprimality hypotheses, containment of the centralizer of the
  canonical kernel in that range is equivalent to the explicit condition
  `Z(A) ≤ A^P`.

The final condition cannot be deleted.  For example, let `P = C₂` act on
`A = C₃ × C₃` by inversion on the first coordinate and trivially on the
second.  Then `A` is abelian, so the canonical copy of every element of
`A` centralizes the `A`-kernel, whereas the fixed-point product contains
only the second `C₃` coordinate.

Coprimality is used honestly in the positive direction: if an element
`(a,g)` centralizes the `A`-kernel, then the automorphism induced by `g`
is conjugation by `a⁻¹`.  Its order divides both the `p`-power order of
`g` and the prime-to-`p` order of `a`, hence it is trivial.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

variable (P A : Type*) [Group P] [Group A]
variable [MulDistribMulAction P A]

/-- The direct product of the fixed-point subgroup with the acting group. -/
abbrev actionFixedPointProduct : Type _ :=
  FixedPoints.subgroup P A × P

/-- The canonical embedding `A^P × P → A ⋊ P`. -/
def actionFixedPointProductEmbedding :
    actionFixedPointProduct P A →*
      actionSemidirectProduct P A where
  toFun x :=
    SemidirectProduct.inl (x.1 : A) *
      SemidirectProduct.inr x.2
  map_one' := by
    apply SemidirectProduct.ext <;> simp
  map_mul' x y := by
    apply SemidirectProduct.ext
    · simp only [SemidirectProduct.mul_left,
        SemidirectProduct.mul_right,
        SemidirectProduct.left_inl,
        SemidirectProduct.right_inl,
        SemidirectProduct.left_inr,
        SemidirectProduct.right_inr,
        map_one, one_mul, mul_one,
        Prod.fst_mul, Subgroup.coe_mul, Prod.snd_mul]
      have hyfixed :
          (actionHom P A x.2) (y.1 : A) =
            (y.1 : A) := by
        exact y.1.2 x.2
      rw [hyfixed]
    · simp

@[simp]
theorem actionFixedPointProductEmbedding_left
    (x : actionFixedPointProduct P A) :
    (actionFixedPointProductEmbedding P A x).left =
      (x.1 : A) := by
  simp [actionFixedPointProductEmbedding]

@[simp]
theorem actionFixedPointProductEmbedding_right
    (x : actionFixedPointProduct P A) :
    (actionFixedPointProductEmbedding P A x).right =
      x.2 := by
  simp [actionFixedPointProductEmbedding]

/-- The fixed-point product embeds injectively in the action semidirect
product. -/
theorem actionFixedPointProductEmbedding_injective :
    Function.Injective
      (actionFixedPointProductEmbedding P A) := by
  intro x y hxy
  apply Prod.ext
  · apply Subtype.ext
    simpa only [
      actionFixedPointProductEmbedding_left] using
      congrArg SemidirectProduct.left hxy
  · simpa only [
      actionFixedPointProductEmbedding_right] using
      congrArg SemidirectProduct.right hxy

/-- Membership in the fixed-point product range is detected by the left
semidirect coordinate. -/
theorem mem_range_actionFixedPointProductEmbedding_iff
    (z : actionSemidirectProduct P A) :
    z ∈ MonoidHom.range
        (actionFixedPointProductEmbedding P A) ↔
      z.left ∈ FixedPoints.subgroup P A := by
  constructor
  · rintro ⟨x, rfl⟩
    simpa only [
      actionFixedPointProductEmbedding_left] using x.1.2
  · intro hz
    refine ⟨(⟨z.left, hz⟩, z.right), ?_⟩
    simpa [actionFixedPointProductEmbedding] using
      (SemidirectProduct.inl_left_mul_inr_right z).symm

/-- The normal subgroup in the fixed-point product which consists of its
first factor. -/
abbrev actionFixedPointProductKernel :
    Subgroup (actionFixedPointProduct P A) :=
  MonoidHom.range
    (MonoidHom.inl (FixedPoints.subgroup P A) P)

/-- The canonical action kernel times the embedded fixed-point product is
the whole semidirect product. -/
theorem actionKernel_mul_fixedPointProduct_range
    (z : actionSemidirectProduct P A) :
    ∃ x : actionKernel P A,
      ∃ h : actionFixedPointProduct P A,
        (x : actionSemidirectProduct P A) *
            actionFixedPointProductEmbedding P A h =
          z := by
  refine
    ⟨⟨SemidirectProduct.inl z.left, ⟨z.left, rfl⟩⟩,
      (1, z.right), ?_⟩
  simpa [actionFixedPointProductEmbedding] using
    SemidirectProduct.inl_left_mul_inr_right z

/-- The intersection of the canonical action kernel with the embedded
fixed-point product is exactly the embedded first factor `A^P`. -/
theorem actionKernel_inf_fixedPointProduct_range :
    actionKernel P A ⊓
        MonoidHom.range
          (actionFixedPointProductEmbedding P A) =
      (actionFixedPointProductKernel P A).map
        (actionFixedPointProductEmbedding P A) := by
  ext z
  change
    (z ∈ actionKernel P A ∧
        z ∈ MonoidHom.range
          (actionFixedPointProductEmbedding P A)) ↔
      z ∈ (actionFixedPointProductKernel P A).map
        (actionFixedPointProductEmbedding P A)
  constructor
  · rintro ⟨hzKernel, hzRange⟩
    rw [mem_range_actionFixedPointProductEmbedding_iff
      P A] at hzRange
    have hzRight : z.right = 1 := by
      have hzKer :
          SemidirectProduct.rightHom z = 1 := by
        rw [← MonoidHom.mem_ker,
          ← SemidirectProduct.range_inl_eq_ker_rightHom]
        exact hzKernel
      simpa only [
        SemidirectProduct.rightHom_eq_right] using hzKer
    refine ⟨(⟨z.left, hzRange⟩, 1), ?_, ?_⟩
    · exact
        ⟨⟨z.left, hzRange⟩, rfl⟩
    · apply SemidirectProduct.ext
      · simp
      · simpa using hzRight.symm
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨a, rfl⟩ := hh
    constructor
    · refine ⟨(a : A), ?_⟩
      apply SemidirectProduct.ext <;>
        simp [actionFixedPointProductEmbedding]
    · exact
        ⟨(MonoidHom.inl
            (FixedPoints.subgroup P A) P a), rfl⟩

section Coprime

variable {p : ℕ}

/-- Coprimality rules out a nontrivial acting automorphism for an element
which centralizes the canonical action kernel. -/
theorem actionHom_eq_one_of_mem_centralizer_actionKernel
    (hP : IsPGroup p P)
    (hA : IsPPrimeGroup p A)
    (z : actionSemidirectProduct P A)
    (hz :
      z ∈ Subgroup.centralizer
        (actionKernel P A :
          Set (actionSemidirectProduct P A))) :
    actionHom P A z.right = 1 := by
  have hcomm (a : A) :
      SemidirectProduct.inl a * z =
        z * SemidirectProduct.inl a :=
    Subgroup.mem_centralizer_iff.mp hz
      (SemidirectProduct.inl a) ⟨a, rfl⟩
  have haction :
      actionHom P A z.right =
        MulAut.conj z.left⁻¹ := by
    apply MulEquiv.ext
    intro a
    have hleft :=
      congrArg SemidirectProduct.left (hcomm a)
    simp only [SemidirectProduct.mul_left,
      SemidirectProduct.right_inl,
      SemidirectProduct.left_inl,
      map_one, MulAut.one_apply] at hleft
    rw [MulAut.conj_apply]
    calc
      (actionHom P A z.right) a =
          z.left⁻¹ * (a * z.left) := by
        rw [hleft]
        group
      _ = z.left⁻¹ * a * (z.left⁻¹)⁻¹ := by
        simp [mul_assoc]
  have horderRight :
      orderOf (actionHom P A z.right) ∣
        orderOf z.right :=
    orderOf_map_dvd (actionHom P A) z.right
  have horderLeft :
      orderOf (actionHom P A z.right) ∣
        orderOf z.left := by
    rw [haction]
    simpa only [orderOf_inv] using
      (orderOf_map_dvd MulAut.conj z.left⁻¹)
  have hleftPrime :
      p.Coprime (orderOf z.left) :=
    hA.coprime_dvd_right
      (orderOf_dvd_natCard z.left)
  have hcoprime :
      (orderOf z.right).Coprime
        (orderOf z.left) :=
    hP.orderOf_coprime hleftPrime z.right
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes
    hcoprime horderRight horderLeft

/-- Under coprimality, an element centralizing the action kernel has central
left coordinate and trivial acting automorphism. -/
theorem mem_centralizer_actionKernel_iff
    (hP : IsPGroup p P)
    (hA : IsPPrimeGroup p A)
    (z : actionSemidirectProduct P A) :
    z ∈ Subgroup.centralizer
        (actionKernel P A :
          Set (actionSemidirectProduct P A)) ↔
      z.left ∈ Subgroup.center A ∧
        actionHom P A z.right = 1 := by
  constructor
  · intro hz
    have haction :=
      actionHom_eq_one_of_mem_centralizer_actionKernel
        P A hP hA z hz
    refine ⟨Subgroup.mem_center_iff.mpr ?_, haction⟩
    intro a
    have hcomm :=
      Subgroup.mem_centralizer_iff.mp hz
        (SemidirectProduct.inl a) ⟨a, rfl⟩
    have hleft :=
      congrArg SemidirectProduct.left hcomm
    simpa [haction] using hleft
  · rintro ⟨hzCenter, haction⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    obtain ⟨a, rfl⟩ := hx
    apply SemidirectProduct.ext
    · simpa [haction] using
        Subgroup.mem_center_iff.mp hzCenter a
    · simp

/-- The exact extra condition for the DGN centralizer containment.

For a coprime action, the centralizer of the canonical `A`-kernel lies in
the fixed-point product precisely when every central element of `A` is
fixed by `P`. -/
theorem centralizer_actionKernel_le_fixedPointProduct_range_iff
    (hP : IsPGroup p P)
    (hA : IsPPrimeGroup p A) :
    Subgroup.centralizer
          (actionKernel P A :
            Set (actionSemidirectProduct P A)) ≤
        MonoidHom.range
          (actionFixedPointProductEmbedding P A) ↔
      Subgroup.center A ≤
        FixedPoints.subgroup P A := by
  constructor
  · intro h a ha
    have haCentralizer :
        SemidirectProduct.inl a ∈
          Subgroup.centralizer
            (actionKernel P A :
              Set (actionSemidirectProduct P A)) := by
      rw [mem_centralizer_actionKernel_iff
        P A hP hA]
      exact ⟨ha, map_one (actionHom P A)⟩
    exact
      (mem_range_actionFixedPointProductEmbedding_iff
        P A (SemidirectProduct.inl a)).mp
        (h haCentralizer)
  · intro h z hz
    rw [mem_range_actionFixedPointProductEmbedding_iff
      P A]
    exact h
      ((mem_centralizer_actionKernel_iff
        P A hP hA z).mp hz).1

/-- A convenient one-way form of the exact centralizer criterion. -/
theorem centralizer_actionKernel_le_fixedPointProduct_range
    (hP : IsPGroup p P)
    (hA : IsPPrimeGroup p A)
    (hcenter :
      Subgroup.center A ≤
        FixedPoints.subgroup P A) :
    Subgroup.centralizer
          (actionKernel P A :
            Set (actionSemidirectProduct P A)) ≤
        MonoidHom.range
          (actionFixedPointProductEmbedding P A) :=
  (centralizer_actionKernel_le_fixedPointProduct_range_iff
    P A hP hA).mpr hcenter

end Coprime

end GroupTheory
end McKayConjecture
