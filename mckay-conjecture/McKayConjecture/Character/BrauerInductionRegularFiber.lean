/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerInductionFixedPointValue
import McKayConjecture.Character.ElementaryRestriction
import McKayConjecture.Character.PRegularElementarySubgroup

/-!
# The regular-fibre function in Bernstein's Brauer-induction argument

Let `S = D × P` be a `p`-elementary subgroup of a finite group `C`, where
the cyclic factor `D` is central in `C`.  For `a ∈ D`, the regular-fibre
class function on `S` has value `m` when the `D`-coordinate is `a`, and
vanishes otherwise.

This file proves the concrete support identity omitted by the abstract
fixed-point calculation: at `a * t`, for a `p`-element `t`, the summand
indexed by a coset `q` is `m` exactly when `q` is fixed by `t`.  Consequently,
if `S` contains a Sylow `p`-subgroup of `C`, the induced value at `a * t` is
an integer prime to `p` when `m` is prime to `p`.
-/

noncomputable section

namespace McKayConjecture

open MulAction

variable {p : ℕ}
variable {C : Type} [Group C]

namespace IsPElement

/-- Conjugation preserves `p`-elements. -/
theorem conj {t : C} (ht : IsPElement p t) (x : C) :
    IsPElement p (x⁻¹ * t * x) := by
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
    ht.map p (MulAut.conj x⁻¹).toMonoidHom

/-- A `p`-element lying in a subgroup remains a `p`-element when regarded
as an element of that subgroup. -/
theorem subgroupElement
    (S : Subgroup C) {t : C} (ht : IsPElement p t)
    (htS : t ∈ S) :
    IsPElement p (⟨t, htS⟩ : S) := by
  obtain ⟨k, hk⟩ := ht
  refine ⟨k, ?_⟩
  exact Subtype.ext hk

end IsPElement

namespace PElementaryDecomposition

variable {E : Type} [Group E]

/-- A `p`-element of a `p`-elementary group has trivial coordinate in the
cyclic prime-to-`p` factor. -/
theorem cyclicCoordinate_eq_one_of_isPElement
    [Finite E]
    (D : PElementaryDecomposition p E)
    {x : E} (hx : IsPElement p x) :
    (D.multiplicationEquiv.symm x).1 = 1 := by
  let c : D.cyclicPart :=
    (D.multiplicationEquiv.symm x).1
  have hc : IsPElement p c := by
    exact hx.map p
      ((MonoidHom.fst D.cyclicPart D.pPart).comp
        D.multiplicationEquiv.symm.toMonoidHom)
  obtain ⟨k, hk⟩ := hc
  have horder_pow :
      orderOf c ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one hk
  have horder_card :
      orderOf c ∣ Nat.card D.cyclicPart :=
    orderOf_dvd_natCard c
  have horder_one :
      orderOf c = 1 :=
    Nat.eq_one_of_dvd_coprimes
      (D.cyclicPart_coprime.pow_left k)
      horder_pow horder_card
  exact orderOf_eq_one_iff.mp horder_one

end PElementaryDecomposition

namespace ClassFunction

variable {E : Type} [Group E]

/-- On the displayed direct product, the regular-fibre function is the
indicator of one element of the cyclic coordinate. -/
noncomputable def regularFiberOnProduct
    (D : PElementaryDecomposition p E)
    (a : D.cyclicPart) (m : ℕ) :
    ClassFunction (D.cyclicPart × D.pPart) := by
  classical
  refine
    ⟨fun z =>
      if z.1 = a then (m : ℂ) else 0,
      ?_⟩
  intro z w
  have hcomm :
      w.1 * z.1 = z.1 * w.1 :=
    D.cyclic.isMulCommutative.is_comm.comm w.1 z.1
  have hfirst :
      (w * z * w⁻¹).1 = z.1 := by
    change w.1 * z.1 * w.1⁻¹ = z.1
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  change
    (if (w * z * w⁻¹).1 = a then (m : ℂ) else 0) =
      if z.1 = a then (m : ℂ) else 0
  rw [hfirst]

/-- The regular-fibre class function transported from direct-product
coordinates to the elementary group. -/
noncomputable def regularFiber
    (D : PElementaryDecomposition p E)
    (a : D.cyclicPart) (m : ℕ) :
    ClassFunction E :=
  comapLinearMap
    D.multiplicationEquiv.symm.toMonoidHom
    (regularFiberOnProduct D a m)

@[simp]
theorem regularFiber_apply_of_cyclicCoordinate_eq
    (D : PElementaryDecomposition p E)
    (a : D.cyclicPart) (m : ℕ) (x : E)
    (hx : (D.multiplicationEquiv.symm x).1 = a) :
    regularFiber D a m x = (m : ℂ) := by
  classical
  simp [regularFiber, regularFiberOnProduct, hx]

@[simp]
theorem regularFiber_apply_of_cyclicCoordinate_ne
    (D : PElementaryDecomposition p E)
    (a : D.cyclicPart) (m : ℕ) (x : E)
    (hx : (D.multiplicationEquiv.symm x).1 ≠ a) :
    regularFiber D a m x = 0 := by
  classical
  simp [regularFiber, regularFiberOnProduct, hx]

/-- A coset is fixed under left multiplication by `t` exactly when the
conjugate of `t` by its chosen representative lies in the subgroup. -/
theorem mem_fixedBy_quotient_iff_conjugate_mem
    (S : Subgroup C) (t : C) (q : C ⧸ S) :
    q ∈ fixedBy (C ⧸ S) t ↔
      q.out⁻¹ * t * q.out ∈ S := by
  rw [MulAction.mem_fixedBy]
  constructor
  · intro hfixed
    have hquot :
        ((t * q.out : C) : C ⧸ S) =
          ((q.out : C) : C ⧸ S) := by
      rw [← smul_eq_mul, Quotient.mk_smul_out, hfixed,
        QuotientGroup.out_eq']
    have hinv :=
      S.inv_mem (QuotientGroup.eq.mp hquot)
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using hinv
  · intro hconj
    have hrel :
        (t * q.out)⁻¹ * q.out ∈ S := by
      have hinv := S.inv_mem hconj
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using hinv
    have hquot :
        ((t * q.out : C) : C ⧸ S) =
          ((q.out : C) : C ⧸ S) :=
      QuotientGroup.eq.mpr hrel
    calc
      t • q =
          ((t * q.out : C) : C ⧸ S) := by
            rw [← Quotient.mk_smul_out S t q]
            simp only [smul_eq_mul]
      _ = ((q.out : C) : C ⧸ S) := hquot
      _ = q := QuotientGroup.out_eq' q

/-- Bernstein's support identity for the regular-fibre function.  The
centrality hypothesis is exactly what one obtains by taking `C` to be the
centralizer of the chosen `p`-regular element. -/
theorem inductionTerm_regularFiber_eq_fixedCosetIndicator
    [Finite C]
    (S : Subgroup C)
    (D : PElementaryDecomposition p S)
    (a : D.cyclicPart)
    (haCentral : (((a : S) : C)) ∈ Subgroup.center C)
    (t : C) (ht : IsPElement p t)
    (m : ℕ) (q : C ⧸ S) :
    inductionTerm S (regularFiber D a m)
        q.out (((a : S) : C) * t) =
      fixedCosetIndicator S t m q := by
  classical
  let aC : C := ((a : S) : C)
  let u : C := q.out⁻¹ * t * q.out
  have haS : aC ∈ S :=
    (a : S).property
  have hconjA :
      q.out⁻¹ * aC * q.out = aC := by
    rw [Subgroup.mem_center_iff.mp haCentral q.out⁻¹,
      mul_assoc, inv_mul_cancel, mul_one]
  have hconjMul :
      q.out⁻¹ * (aC * t) * q.out =
        aC * u := by
    dsimp only [u]
    calc
      q.out⁻¹ * (aC * t) * q.out =
          (q.out⁻¹ * aC * q.out) *
            (q.out⁻¹ * t * q.out) := by
              group
      _ = aC * (q.out⁻¹ * t * q.out) := by
            rw [hconjA]
  by_cases hfixed :
      q ∈ fixedBy (C ⧸ S) t
  · have huS : u ∈ S := by
      exact
        (mem_fixedBy_quotient_iff_conjugate_mem
          S t q).mp hfixed
    have hwhole :
        q.out⁻¹ * (aC * t) * q.out ∈ S := by
      rw [hconjMul]
      exact S.mul_mem haS huS
    rw [inductionTerm_of_mem S
      (regularFiber D a m) hwhole]
    have huP :
        IsPElement p (⟨u, huS⟩ : S) :=
      (ht.conj q.out).subgroupElement S huS
    have huFirst :
        (D.multiplicationEquiv.symm
          (⟨u, huS⟩ : S)).1 = 1 :=
      D.cyclicCoordinate_eq_one_of_isPElement huP
    have haCoordinates :
        D.multiplicationEquiv.symm (a : S) =
          (a, 1) := by
      apply D.multiplicationEquiv.injective
      simp
    have hsubtype :
        (⟨q.out⁻¹ * (aC * t) * q.out, hwhole⟩ : S) =
          (a : S) * (⟨u, huS⟩ : S) := by
      apply Subtype.ext
      exact hconjMul
    rw [hsubtype]
    have hfirst :
        (D.multiplicationEquiv.symm
          ((a : S) * (⟨u, huS⟩ : S))).1 = a := by
      rw [map_mul, haCoordinates]
      simp only [Prod.fst_mul, huFirst, mul_one]
    rw [regularFiber_apply_of_cyclicCoordinate_eq
      D a m _ hfirst]
    simp [fixedCosetIndicator, hfixed]
  · have huNot : u ∉ S := by
      exact
        mt
          (mem_fixedBy_quotient_iff_conjugate_mem
            S t q).mpr hfixed
    have hwholeNot :
        q.out⁻¹ * (aC * t) * q.out ∉ S := by
      intro hwhole
      apply huNot
      have hproduct : aC * u ∈ S := by
        rwa [← hconjMul]
      have hcancel :=
        S.mul_mem (S.inv_mem haS) hproduct
      simpa only [← mul_assoc, inv_mul_cancel,
        one_mul] using hcancel
    rw [inductionTerm_of_not_mem S
      (regularFiber D a m) hwholeNot]
    simp [fixedCosetIndicator, hfixed]

/-- The local numerical conclusion of Bernstein's construction.  The
integer obtained by inducing the regular-fibre function at `a * t` is
prime to `p`. -/
theorem exists_coprime_nat_induce_regularFiber
    [Fintype C] [Fact p.Prime]
    (P : Sylow p C)
    (S : Subgroup C)
    (hPS : (P : Subgroup C) ≤ S)
    (D : PElementaryDecomposition p S)
    (a : D.cyclicPart)
    (haCentral : (((a : S) : C)) ∈ Subgroup.center C)
    (t : C) (ht : IsPElement p t)
    (m : ℕ) (hm : p.Coprime m) :
    ∃ k : ℕ, p.Coprime k ∧
      induce S (regularFiber D a m)
          (((a : S) : C) * t) =
        (k : ℂ) := by
  apply
    exists_coprime_nat_induced_value_of_fixedBy_indicator
      P S hPS (regularFiber D a m)
        (((a : S) : C) * t) t ht m hm
  intro q
  exact
    inductionTerm_regularFiber_eq_fixedCosetIndicator
      S D a haCentral t ht m q

/-- Bernstein's regular-fibre function on the canonical elementary subgroup
attached to a central `p`-regular element.  The fibre constant is the order
of the displayed cyclic factor, which is prime to `p`. -/
noncomputable def centralPRegularFiber
    [Finite C] [Fact p.Prime]
    (a : C)
    (haCentral : a ∈ Subgroup.center C)
    (haRegular : IsPRegular p a)
    (P : Sylow p C) :
    ClassFunction
      (centralPRegularElementarySubgroup a P) := by
  let D :=
    centralPRegularElementaryDecomposition
      a haCentral haRegular P
  exact
    regularFiber D
      (centralPRegularCyclicCoordinate
        a haCentral haRegular P)
      (Nat.card D.cyclicPart)

/-- Fully instantiated local Bernstein calculation.  For every central
`p`-regular `a` and every `p`-element `t`, inducing the canonical
regular-fibre function from `⟨a⟩ P` to the ambient centralizer gives a
natural-number value prime to `p` at `a * t`. -/
theorem exists_coprime_nat_induce_centralPRegularFiber
    [Fintype C] [Fact p.Prime]
    (a : C)
    (haCentral : a ∈ Subgroup.center C)
    (haRegular : IsPRegular p a)
    (P : Sylow p C)
    (t : C) (ht : IsPElement p t) :
    ∃ k : ℕ, p.Coprime k ∧
      induce
          (centralPRegularElementarySubgroup a P)
          (centralPRegularFiber
            a haCentral haRegular P)
          (a * t) =
        (k : ℂ) := by
  let S :=
    centralPRegularElementarySubgroup a P
  let D :=
    centralPRegularElementaryDecomposition
      a haCentral haRegular P
  let aD :=
    centralPRegularCyclicCoordinate
      a haCentral haRegular P
  have haDcentral :
      (((aD : S) : C)) ∈ Subgroup.center C := by
    simpa only [aD, S,
      centralPRegularCyclicCoordinate_coe] using
      haCentral
  have hlocal :=
    exists_coprime_nat_induce_regularFiber
      P S
      (sylow_le_centralPRegularElementarySubgroup
        a P)
      D aD haDcentral t ht
      (Nat.card D.cyclicPart)
      D.cyclicPart_coprime
  simpa only [S, D, aD,
    centralPRegularFiber,
    centralPRegularCyclicCoordinate_coe] using
    hlocal

end ClassFunction
end McKayConjecture
