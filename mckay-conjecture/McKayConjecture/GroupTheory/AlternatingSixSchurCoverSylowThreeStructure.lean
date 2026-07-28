/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverSylowThree

/-!
# Center, commutator, and quotient of the Sylow-three subgroup of `6.A₆`

The explicit Heisenberg subgroup projects onto the concrete elementary
abelian Sylow subgroup of `A₆`.  This file identifies the restricted kernel,
the center, and the commutator subgroup.  All three have order three, and the
quotient is the concrete group `(C₃)²`.
-/

noncomputable section

open scoped commutatorElement

namespace McKayConjecture
namespace GroupTheory

local instance alternatingSixSchurSylowThreeStructureFactPrime :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-- The central generator as an element of the explicit Sylow subgroup. -/
def alternatingSixSchurSylowThreeZElement :
    alternatingSixSchurSylowThreeSubgroup :=
  ⟨alternatingSixSchurSylowThreeZ,
    ⟨⟨1, 0, 0⟩, by
      simp [alternatingSixSchurSylowThreeParameterizedElement]⟩⟩

/-- The first noncentral generator as an element of the explicit Sylow
subgroup. -/
def alternatingSixSchurSylowThreeXElement :
    alternatingSixSchurSylowThreeSubgroup :=
  ⟨alternatingSixSchurSylowThreeX,
    ⟨⟨0, 1, 0⟩, by
      simp [alternatingSixSchurSylowThreeParameterizedElement]⟩⟩

/-- The second noncentral generator as an element of the explicit Sylow
subgroup. -/
def alternatingSixSchurSylowThreeYElement :
    alternatingSixSchurSylowThreeSubgroup :=
  ⟨alternatingSixSchurSylowThreeY,
    ⟨⟨0, 0, 1⟩, by
      simp [alternatingSixSchurSylowThreeParameterizedElement]⟩⟩

/-- Projection restricted from the explicit Sylow subgroup to the concrete
Sylow subgroup in `A₆`. -/
def alternatingSixSchurSylowThreeProjection :
    alternatingSixSchurSylowThreeSubgroup →*
      alternatingSixConcreteSylowThreeSubgroup where
  toFun g :=
    ⟨alternatingSixSchurProjection g.1, by
      obtain ⟨q, hq⟩ := g.property
      refine ⟨(q.x, q.y), ?_⟩
      rw [← hq]
      exact
        (alternatingSixSchurProjection_sylowThreeParameterizedElement q).symm⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' g h := by
    apply Subtype.ext
    simp

@[simp]
theorem alternatingSixSchurSylowThreeProjection_apply
    (g : alternatingSixSchurSylowThreeSubgroup) :
    (alternatingSixSchurSylowThreeProjection g :
      AlternatingSix) =
        alternatingSixSchurProjection g.1 :=
  rfl

/-- The restricted projection is onto. -/
theorem alternatingSixSchurSylowThreeProjection_surjective :
    Function.Surjective alternatingSixSchurSylowThreeProjection := by
  intro g
  obtain ⟨⟨b, c⟩, hbc⟩ := g.property
  let q : AlternatingSixSchurSylowThreeCoordinates :=
    ⟨0, b, c⟩
  let lift : alternatingSixSchurSylowThreeSubgroup :=
    ⟨alternatingSixSchurSylowThreeParameterizedElement q,
      ⟨q, rfl⟩⟩
  refine ⟨lift, ?_⟩
  apply Subtype.ext
  change
    alternatingSixSchurProjection
        (alternatingSixSchurSylowThreeParameterizedElement q) =
      g.1
  rw [alternatingSixSchurProjection_sylowThreeParameterizedElement]
  exact hbc

private theorem alternatingSixSchurSylowThree_coordinateY_eq_zero_of_commuteX
    (a b c : Fin 3)
    (hcomm :
      Commute
        (alternatingSixSchurSylowThreeParameterizedElement ⟨a, b, c⟩)
        alternatingSixSchurSylowThreeX) :
    c = 0 := by
  have heq :
      alternatingSixSchurSylowThreeZ ^ (a.val + c.val) *
            alternatingSixSchurSylowThreeX ^ (b.val + 1) *
            alternatingSixSchurSylowThreeY ^ c.val =
        alternatingSixSchurSylowThreeZ ^ a.val *
            alternatingSixSchurSylowThreeX ^ (b.val + 1) *
            alternatingSixSchurSylowThreeY ^ c.val := by
    calc
      _ =
          alternatingSixSchurSylowThreeParameterizedElement ⟨a, b, c⟩ *
            (alternatingSixSchurSylowThreeZ ^ 0 *
              alternatingSixSchurSylowThreeX ^ 1 *
              alternatingSixSchurSylowThreeY ^ 0) :=
        by
          simpa [alternatingSixSchurSylowThreeParameterizedElement] using
            (alternatingSixSchurSylowThree_collect
              a.val b.val c.val 0 1 0).symm
      _ =
          alternatingSixSchurSylowThreeX *
            alternatingSixSchurSylowThreeParameterizedElement ⟨a, b, c⟩ := by
        simpa [alternatingSixSchurSylowThreeParameterizedElement] using
          hcomm.eq
      _ =
          alternatingSixSchurSylowThreeZ ^ a.val *
            alternatingSixSchurSylowThreeX ^ (b.val + 1) *
            alternatingSixSchurSylowThreeY ^ c.val := by
        simpa [Nat.add_comm,
          alternatingSixSchurSylowThreeParameterizedElement] using
          alternatingSixSchurSylowThree_collect
            0 1 0 a.val b.val c.val
  have hzpow :
      alternatingSixSchurSylowThreeZ ^ (a.val + c.val) =
        alternatingSixSchurSylowThreeZ ^ a.val := by
    apply mul_right_cancel
    apply mul_right_cancel
    simpa only [mul_assoc] using heq
  have hmod :=
    (pow_inj_mod
      (x := alternatingSixSchurSylowThreeZ)).mp hzpow
  rw [orderOf_alternatingSixSchurSylowThreeZ] at hmod
  apply Fin.ext
  fin_cases a <;> fin_cases c
  all_goals norm_num at hmod
  all_goals rfl

private theorem alternatingSixSchurSylowThree_coordinateX_eq_zero_of_commuteY
    (a b c : Fin 3)
    (hcomm :
      Commute
        (alternatingSixSchurSylowThreeParameterizedElement ⟨a, b, c⟩)
        alternatingSixSchurSylowThreeY) :
    b = 0 := by
  have heq :
      alternatingSixSchurSylowThreeZ ^ a.val *
            alternatingSixSchurSylowThreeX ^ b.val *
            alternatingSixSchurSylowThreeY ^ (c.val + 1) =
        alternatingSixSchurSylowThreeZ ^ (a.val + b.val) *
            alternatingSixSchurSylowThreeX ^ b.val *
            alternatingSixSchurSylowThreeY ^ (c.val + 1) := by
    calc
      _ =
          alternatingSixSchurSylowThreeParameterizedElement ⟨a, b, c⟩ *
            (alternatingSixSchurSylowThreeZ ^ 0 *
              alternatingSixSchurSylowThreeX ^ 0 *
              alternatingSixSchurSylowThreeY ^ 1) :=
        by
          simpa [alternatingSixSchurSylowThreeParameterizedElement] using
            (alternatingSixSchurSylowThree_collect
              a.val b.val c.val 0 0 1).symm
      _ =
          alternatingSixSchurSylowThreeY *
            alternatingSixSchurSylowThreeParameterizedElement ⟨a, b, c⟩ := by
        simpa [alternatingSixSchurSylowThreeParameterizedElement] using
          hcomm.eq
      _ =
          alternatingSixSchurSylowThreeZ ^ (a.val + b.val) *
            alternatingSixSchurSylowThreeX ^ b.val *
            alternatingSixSchurSylowThreeY ^ (c.val + 1) := by
        simpa [Nat.add_comm,
          alternatingSixSchurSylowThreeParameterizedElement] using
          alternatingSixSchurSylowThree_collect
            0 0 1 a.val b.val c.val
  have hzpow :
      alternatingSixSchurSylowThreeZ ^ a.val =
        alternatingSixSchurSylowThreeZ ^ (a.val + b.val) := by
    apply mul_right_cancel
    apply mul_right_cancel
    simpa only [mul_assoc] using heq
  have hmod :=
    (pow_inj_mod
      (x := alternatingSixSchurSylowThreeZ)).mp hzpow
  rw [orderOf_alternatingSixSchurSylowThreeZ] at hmod
  apply Fin.ext
  fin_cases a <;> fin_cases b
  all_goals norm_num at hmod
  all_goals rfl

/-- Kernel membership is exactly having only a central coordinate. -/
theorem alternatingSixSchurSylowThreeProjection_mem_ker_iff
    (g : alternatingSixSchurSylowThreeSubgroup) :
    g ∈ alternatingSixSchurSylowThreeProjection.ker ↔
      ∃ a : Fin 3,
        g.1 = alternatingSixSchurSylowThreeZ ^ a.val := by
  constructor
  · intro hg
    obtain ⟨q, hq⟩ := g.property
    have hprojection :
        alternatingSixSchurSylowThreeProjection g = 1 :=
      MonoidHom.mem_ker.mp hg
    have htarget :
        alternatingSixSylowThreeParameterizedElement (q.x, q.y) =
          alternatingSixSylowThreeParameterizedElement (0, 0) := by
      calc
        alternatingSixSylowThreeParameterizedElement (q.x, q.y) =
            alternatingSixSchurProjection
              (alternatingSixSchurSylowThreeParameterizedElement q) :=
          (alternatingSixSchurProjection_sylowThreeParameterizedElement q).symm
        _ = alternatingSixSchurProjection g.1 := by rw [hq]
        _ = 1 := by
          exact congrArg Subtype.val hprojection
        _ =
            alternatingSixSylowThreeParameterizedElement (0, 0) := by
          simp [alternatingSixSylowThreeParameterizedElement]
    have hcoordinates :
        (q.x, q.y) = ((0 : Fin 3), (0 : Fin 3)) :=
      alternatingSixSylowThreeParameterizedElement_injective htarget
    have hx : q.x = 0 := congrArg Prod.fst hcoordinates
    have hy : q.y = 0 := congrArg Prod.snd hcoordinates
    refine ⟨q.z, ?_⟩
    rw [← hq]
    simp [alternatingSixSchurSylowThreeParameterizedElement,
      hx, hy]
  · rintro ⟨a, ha⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change alternatingSixSchurProjection g.1 = 1
    rw [ha, map_pow,
      alternatingSixSchurProjection_sylowThreeZ, one_pow]

/-- The center is exactly the restricted projection kernel. -/
theorem alternatingSixSchurSylowThree_center_eq_projection_ker :
    Subgroup.center alternatingSixSchurSylowThreeSubgroup =
      alternatingSixSchurSylowThreeProjection.ker := by
  apply le_antisymm
  · intro g hg
    obtain ⟨q, hq⟩ := g.property
    have hgcomm :
        ∀ h : alternatingSixSchurSylowThreeSubgroup,
          Commute g h := fun h =>
      (Subgroup.mem_center_iff.mp hg h).symm
    have hcommX :
        Commute
          (alternatingSixSchurSylowThreeParameterizedElement q)
          alternatingSixSchurSylowThreeX := by
      have h := hgcomm alternatingSixSchurSylowThreeXElement
      have hambient := congrArg Subtype.val h.eq
      change g.1 * alternatingSixSchurSylowThreeX =
          alternatingSixSchurSylowThreeX * g.1 at hambient
      rw [← hq] at hambient
      exact hambient
    have hcommY :
        Commute
          (alternatingSixSchurSylowThreeParameterizedElement q)
          alternatingSixSchurSylowThreeY := by
      have h := hgcomm alternatingSixSchurSylowThreeYElement
      have hambient := congrArg Subtype.val h.eq
      change g.1 * alternatingSixSchurSylowThreeY =
          alternatingSixSchurSylowThreeY * g.1 at hambient
      rw [← hq] at hambient
      exact hambient
    have hy :
        q.y = 0 :=
      alternatingSixSchurSylowThree_coordinateY_eq_zero_of_commuteX
        q.z q.x q.y hcommX
    have hx :
        q.x = 0 :=
      alternatingSixSchurSylowThree_coordinateX_eq_zero_of_commuteY
        q.z q.x q.y hcommY
    rw [alternatingSixSchurSylowThreeProjection_mem_ker_iff]
    refine ⟨q.z, ?_⟩
    rw [← hq]
    simp [alternatingSixSchurSylowThreeParameterizedElement,
      hx, hy]
  · intro g hg
    obtain ⟨a, ha⟩ :=
      (alternatingSixSchurSylowThreeProjection_mem_ker_iff g).mp hg
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    change h.1 * g.1 = g.1 * h.1
    rw [ha]
    exact
      ((alternatingSixSchurSylowThreeZ_commute h.1).pow_left
        a.val).eq.symm

/-- The central kernel has order three. -/
@[simp]
theorem natCard_alternatingSixSchurSylowThreeProjection_ker :
    Nat.card alternatingSixSchurSylowThreeProjection.ker = 3 := by
  let f := alternatingSixSchurSylowThreeProjection
  have hrange : f.range = ⊤ :=
    MonoidHom.range_eq_top.mpr
      alternatingSixSchurSylowThreeProjection_surjective
  have hcard :
      Nat.card f.ker * Nat.card f.range =
        Nat.card alternatingSixSchurSylowThreeSubgroup := by
    calc
      Nat.card f.ker * Nat.card f.range =
          Nat.card f.ker * f.ker.index := by
        rw [Subgroup.index_ker]
      _ = Nat.card alternatingSixSchurSylowThreeSubgroup :=
        f.ker.card_mul_index
  change Nat.card f.ker = 3
  rw [hrange, Subgroup.card_top,
    natCard_alternatingSixConcreteSylowThreeSubgroup,
    natCard_alternatingSixSchurSylowThreeSubgroup] at hcard
  omega

/-- The center of the Heisenberg Sylow subgroup has order three. -/
@[simp]
theorem natCard_center_alternatingSixSchurSylowThreeSubgroup :
    Nat.card
        (Subgroup.center alternatingSixSchurSylowThreeSubgroup) =
      3 := by
  rw [alternatingSixSchurSylowThree_center_eq_projection_ker,
    natCard_alternatingSixSchurSylowThreeProjection_ker]

/-- The center of the Heisenberg Sylow subgroup is cyclic. -/
theorem alternatingSixSchurSylowThree_center_isCyclic :
    IsCyclic
      (Subgroup.center alternatingSixSchurSylowThreeSubgroup) :=
  isCyclic_of_prime_card
    natCard_center_alternatingSixSchurSylowThreeSubgroup

/-- Quotienting by the center recovers the concrete `(C₃)²` subgroup. -/
def alternatingSixSchurSylowThreeQuotientCenterEquiv :
    alternatingSixSchurSylowThreeSubgroup ⧸
        Subgroup.center alternatingSixSchurSylowThreeSubgroup ≃*
      alternatingSixConcreteSylowThreeSubgroup :=
  (QuotientGroup.quotientMulEquivOfEq
      alternatingSixSchurSylowThree_center_eq_projection_ker).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      alternatingSixSchurSylowThreeProjection
      alternatingSixSchurSylowThreeProjection_surjective)

/-- Every element of the explicit Sylow subgroup has exponent dividing
three. -/
theorem alternatingSixSchurSylowThreeSubgroup_cube
    (g : alternatingSixSchurSylowThreeSubgroup) :
    g ^ 3 = 1 := by
  obtain ⟨q, hq⟩ := g.property
  apply Subtype.ext
  change g.1 ^ 3 = 1
  rw [← hq]
  exact
    alternatingSixSchurSylowThreeParameterizedElement_cube q

/-! ### The commutator subgroup -/

/-- The central generator belongs to the derived subgroup. -/
theorem alternatingSixSchurSylowThreeZElement_mem_commutator :
    alternatingSixSchurSylowThreeZElement ∈
      _root_.commutator alternatingSixSchurSylowThreeSubgroup := by
  have hcommutator :
      ⁅alternatingSixSchurSylowThreeXElement,
        alternatingSixSchurSylowThreeYElement⁆ =
          alternatingSixSchurSylowThreeZElement ^ 2 := by
    apply Subtype.ext
    exact alternatingSixSchurSylowThreeXY_commutator
  have hzSquare :
      alternatingSixSchurSylowThreeZElement ^ 2 ∈
        _root_.commutator alternatingSixSchurSylowThreeSubgroup := by
    rw [← hcommutator, _root_.commutator_def]
    exact
      Subgroup.commutator_mem_commutator
        (by simp) (by simp)
  have hzFourth :
      (alternatingSixSchurSylowThreeZElement ^ 2) ^ 2 =
        alternatingSixSchurSylowThreeZElement := by
    apply Subtype.ext
    change
      (alternatingSixSchurSylowThreeZ ^ 2) ^ 2 =
        alternatingSixSchurSylowThreeZ
    calc
      (alternatingSixSchurSylowThreeZ ^ 2) ^ 2 =
          alternatingSixSchurSylowThreeZ ^ 4 := by
        rw [← pow_mul]
      _ =
          alternatingSixSchurSylowThreeZ ^ 3 *
            alternatingSixSchurSylowThreeZ := by
        rw [show 4 = 3 + 1 by norm_num, pow_add, pow_one]
      _ = alternatingSixSchurSylowThreeZ := by
        rw [alternatingSixSchurSylowThreeZ_cube, one_mul]
  rw [← hzFourth]
  exact
    (_root_.commutator
      alternatingSixSchurSylowThreeSubgroup).pow_mem hzSquare 2

/-- The derived subgroup is contained in the center because the projected
quotient is abelian. -/
theorem alternatingSixSchurSylowThree_commutator_le_center :
    _root_.commutator alternatingSixSchurSylowThreeSubgroup ≤
      Subgroup.center alternatingSixSchurSylowThreeSubgroup := by
  rw [alternatingSixSchurSylowThree_center_eq_projection_ker,
    _root_.commutator_def]
  apply Subgroup.commutator_le.mpr
  intro g _ h _
  rw [MonoidHom.mem_ker, map_commutatorElement]
  have hcentralize :=
    sylowThree_alternatingSix_le_centralizer
      alternatingSixConcreteSylowThree
  rw [alternatingSixConcreteSylowThree_coe] at hcentralize
  have hgcentral :=
    hcentralize
      (alternatingSixSchurSylowThreeProjection g).property
  rw [Subgroup.mem_centralizer_iff] at hgcentral
  have hambient :=
    hgcentral
      (alternatingSixSchurSylowThreeProjection h).1
      (alternatingSixSchurSylowThreeProjection h).property
  have hcomm :
      Commute
        (alternatingSixSchurSylowThreeProjection g)
        (alternatingSixSchurSylowThreeProjection h) := by
    apply Subtype.ext
    exact hambient.symm
  exact
    commutatorElement_eq_one_iff_commute.mpr
      hcomm

/-- The Sylow subgroup is extraspecial: its center and derived subgroup
coincide (and have order three). -/
theorem alternatingSixSchurSylowThree_commutator_eq_center :
    _root_.commutator alternatingSixSchurSylowThreeSubgroup =
      Subgroup.center alternatingSixSchurSylowThreeSubgroup := by
  apply le_antisymm
  · exact alternatingSixSchurSylowThree_commutator_le_center
  · intro g hg
    have hgker :
        g ∈ alternatingSixSchurSylowThreeProjection.ker := by
      rw [←
        alternatingSixSchurSylowThree_center_eq_projection_ker]
      exact hg
    obtain ⟨a, ha⟩ :=
      (alternatingSixSchurSylowThreeProjection_mem_ker_iff g).mp
        hgker
    have hzpow :
        alternatingSixSchurSylowThreeZElement ^ a.val = g := by
      apply Subtype.ext
      change
        alternatingSixSchurSylowThreeZ ^ a.val = g.1
      exact ha.symm
    rw [← hzpow]
    exact
      (_root_.commutator
        alternatingSixSchurSylowThreeSubgroup).pow_mem
          alternatingSixSchurSylowThreeZElement_mem_commutator
          a.val

/-- The derived subgroup has order three. -/
@[simp]
theorem natCard_commutator_alternatingSixSchurSylowThreeSubgroup :
    Nat.card
        (_root_.commutator alternatingSixSchurSylowThreeSubgroup) =
      3 := by
  rw [alternatingSixSchurSylowThree_commutator_eq_center,
    natCard_center_alternatingSixSchurSylowThreeSubgroup]

/-- The derived subgroup is cyclic. -/
theorem alternatingSixSchurSylowThree_commutator_isCyclic :
    IsCyclic
      (_root_.commutator alternatingSixSchurSylowThreeSubgroup) :=
  isCyclic_of_prime_card
    natCard_commutator_alternatingSixSchurSylowThreeSubgroup

/-- A compact statement of the exponent-three extraspecial structure. -/
theorem alternatingSixSchurSylowThree_is_extraspecial_exponent_three :
    Nat.card alternatingSixSchurSylowThreeSubgroup = 27 ∧
      Nat.card
          (Subgroup.center alternatingSixSchurSylowThreeSubgroup) =
        3 ∧
      _root_.commutator alternatingSixSchurSylowThreeSubgroup =
        Subgroup.center alternatingSixSchurSylowThreeSubgroup ∧
      (∀ g : alternatingSixSchurSylowThreeSubgroup, g ^ 3 = 1) :=
  ⟨natCard_alternatingSixSchurSylowThreeSubgroup,
    natCard_center_alternatingSixSchurSylowThreeSubgroup,
    alternatingSixSchurSylowThree_commutator_eq_center,
    alternatingSixSchurSylowThreeSubgroup_cube⟩

end GroupTheory
end McKayConjecture
