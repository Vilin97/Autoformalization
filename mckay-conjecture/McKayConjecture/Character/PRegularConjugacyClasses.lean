/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Group.ConjFinite
import McKayConjecture.Character.PRegularDecompositionUniqueness

/-!
# Conjugacy classes of `p`-regular elements

This file packages the finite set of conjugacy classes that contain a
`p`-regular element.  Each such class is assigned a chosen `p`-regular
representative.  We then send every group element to the class of its
canonical `p`-regular part.

The final normal-form theorem says that an arbitrary element is conjugate
to the product of the chosen representative of its `p`-regular class and
a commuting `p`-element.  This is the class-theoretic indexing needed in
Bernstein's proof of Brauer induction.
-/

noncomputable section

namespace McKayConjecture

universe u

variable {G : Type u} [Group G]

namespace IsPRegular

/-- Conjugacy preserves `p`-regularity in a finite group. -/
theorem isConj
    [Finite G] (p : ℕ) {a b : G}
    (ha : IsPRegular p a)
    (hab : IsConj a b) :
    IsPRegular p b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hab
  have hmap :=
    ha.map p (MulAut.conj c).toMonoidHom
  simpa only [MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, hc] using hmap

end IsPRegular

/-- The conjugacy classes of a finite group that contain a `p`-regular
element. -/
def PRegularConjClasses (p : ℕ) (G : Type u) [Group G] :=
  {q : ConjClasses G //
    ∃ a : G,
      IsPRegular p a ∧ ConjClasses.mk a = q}

namespace PRegularConjClasses

variable {p : ℕ}

/-- A chosen `p`-regular representative of a `p`-regular conjugacy class. -/
noncomputable def representative
    (q : PRegularConjClasses p G) : G :=
  Classical.choose q.property

/-- The chosen representative is `p`-regular. -/
theorem representative_isPRegular
    (q : PRegularConjClasses p G) :
    IsPRegular p q.representative :=
  (Classical.choose_spec q.property).1

/-- The chosen representative belongs to the specified conjugacy class. -/
theorem mk_representative
    (q : PRegularConjClasses p G) :
    ConjClasses.mk q.representative = q.1 :=
  (Classical.choose_spec q.property).2

/-- A `p`-regular element determines a `p`-regular conjugacy class. -/
def ofElement
    (a : G) (ha : IsPRegular p a) :
    PRegularConjClasses p G :=
  ⟨ConjClasses.mk a, ⟨a, ha, rfl⟩⟩

@[simp]
theorem ofElement_val
    (a : G) (ha : IsPRegular p a) :
    (ofElement a ha).1 =
      ConjClasses.mk a :=
  rfl

/-- The chosen representative is conjugate to every `p`-regular element
that defines its class. -/
theorem representative_isConj
    (q : PRegularConjClasses p G)
    {a : G} (_ha : IsPRegular p a)
    (hclass : ConjClasses.mk a = q.1) :
    IsConj q.representative a := by
  rw [← ConjClasses.mk_eq_mk_iff_isConj]
  exact q.mk_representative.trans hclass.symm

/-- Two `p`-regular elements define the same indexed class exactly when
they are conjugate. -/
theorem ofElement_eq_iff_isConj
    {a b : G}
    (ha : IsPRegular p a)
    (hb : IsPRegular p b) :
    ofElement a ha = ofElement b hb ↔
      IsConj a b := by
  constructor
  · intro h
    apply ConjClasses.mk_eq_mk_iff_isConj.mp
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr h

/-- The representative chosen for the class of `a` is conjugate to `a`. -/
theorem representative_ofElement_isConj
    (a : G) (ha : IsPRegular p a) :
    IsConj (ofElement a ha).representative a :=
  representative_isConj (ofElement a ha) ha rfl

/-- Distinct indexed classes have distinct chosen representatives. -/
theorem representative_injective :
    Function.Injective
      (representative :
        PRegularConjClasses p G → G) := by
  intro q r h
  apply Subtype.ext
  rw [← q.mk_representative,
    ← r.mk_representative, h]

variable [Finite G] [Fact p.Prime]

/-- The indexed `p`-regular conjugacy class of an arbitrary element. -/
noncomputable def classOfElement
    (g : G) :
    PRegularConjClasses p G :=
  ofElement
    (PRegularDecomposition.chosen p g).regularPart
    (PRegularDecomposition.chosen p g).isPRegular

@[simp]
theorem classOfElement_val
    (g : G) :
    (classOfElement (p := p) g).1 =
      ConjClasses.mk
        (PRegularDecomposition.chosen p g).regularPart :=
  rfl

/-- Two elements have the same indexed `p`-regular class exactly when
their `p`-regular parts are conjugate. -/
theorem classOfElement_eq_iff
    (x y : G) :
    classOfElement (p := p) x =
        classOfElement (p := p) y ↔
      IsConj
        (PRegularDecomposition.chosen p x).regularPart
        (PRegularDecomposition.chosen p y).regularPart :=
  ofElement_eq_iff_isConj
    (PRegularDecomposition.chosen p x).isPRegular
    (PRegularDecomposition.chosen p y).isPRegular

/-- Conjugate elements have the same indexed `p`-regular class. -/
theorem classOfElement_conj
    (c g : G) :
    classOfElement (p := p) (c * g * c⁻¹) =
      classOfElement (p := p) g := by
  rw [classOfElement_eq_iff]
  apply IsConj.symm
  rw [isConj_iff]
  refine ⟨c, ?_⟩
  exact
    (PRegularDecomposition.chosen_regularPart_conj
      p c g).symm

/-- The chosen representative of the indexed class of `g` is conjugate
to the chosen `p`-regular part of `g`. -/
theorem representative_classOfElement_isConj
    (g : G) :
    IsConj
        (classOfElement (p := p) g).representative
        (PRegularDecomposition.chosen p g).regularPart :=
  representative_ofElement_isConj
    (PRegularDecomposition.chosen p g).regularPart
    (PRegularDecomposition.chosen p g).isPRegular

/-- An element has indexed class `q` exactly when its chosen regular part
is conjugate to the representative of `q`. -/
theorem classOfElement_eq_iff_isConj_representative
    (g : G) (q : PRegularConjClasses p G) :
    classOfElement (p := p) g = q ↔
      IsConj
        (PRegularDecomposition.chosen p g).regularPart
        q.representative := by
  constructor
  · intro h
    apply ConjClasses.mk_eq_mk_iff_isConj.mp
    exact
      (congrArg Subtype.val h).trans
        q.mk_representative.symm
  · intro h
    apply Subtype.ext
    exact
      (ConjClasses.mk_eq_mk_iff_isConj.mpr h).trans
        q.mk_representative

/-- Taking the class of the representative recovers the original indexed
`p`-regular conjugacy class. -/
theorem classOfElement_representative
    (q : PRegularConjClasses p G) :
    classOfElement (p := p) q.representative = q := by
  have hregularPart :
      (PRegularDecomposition.chosen
        p q.representative).regularPart =
        q.representative := by
    let e :
        PRegularDecomposition p q.representative :=
      { pPart := 1
        regularPart := q.representative
        pPart_mem_zpowers := Subgroup.one_mem _
        regularPart_mem_zpowers :=
          Subgroup.mem_zpowers q.representative
        commute := Commute.one_left q.representative
        mul_eq := one_mul q.representative
        isPElement := IsPElement.one p
        isPRegular := q.representative_isPRegular }
    exact
      PRegularDecomposition.regularPart_eq
        (PRegularDecomposition.chosen
          p q.representative) e
  apply Subtype.ext
  change
    ConjClasses.mk
        (PRegularDecomposition.chosen
          p q.representative).regularPart =
      q.1
  rw [hregularPart]
  exact q.mk_representative

/-- Every element is conjugate to the product of the chosen representative
of its `p`-regular class and a commuting `p`-element. -/
theorem exists_conjugate_eq_representative_mul_pElement
    (g : G) :
    ∃ (c t : G),
      IsPElement p t ∧
      Commute
        (classOfElement (p := p) g).representative t ∧
      c * g * c⁻¹ =
        (classOfElement (p := p) g).representative * t := by
  let d := PRegularDecomposition.chosen p g
  let a :=
    (classOfElement (p := p) g).representative
  have hra :
      IsConj d.regularPart a :=
    (representative_classOfElement_isConj
      (p := p) g).symm
  obtain ⟨c, hc⟩ := isConj_iff.mp hra
  let t : G := c * d.pPart * c⁻¹
  have ht : IsPElement p t := by
    have hmap :=
      d.isPElement.map p
        (MulAut.conj c).toMonoidHom
    simpa only [MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply] using hmap
  have hta : Commute t a := by
    have hmap :=
      d.commute.map
        (MulAut.conj c).toMonoidHom
    have hmap' :
        Commute t
          (c * d.regularPart * c⁻¹) := by
      simpa only [MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply] using hmap
    rw [hc] at hmap'
    exact hmap'
  refine ⟨c, t, ht, hta.symm, ?_⟩
  change c * g * c⁻¹ = a * t
  calc
    c * g * c⁻¹ =
        c * (d.pPart * d.regularPart) * c⁻¹ := by
          rw [d.mul_eq]
    _ = (c * d.pPart * c⁻¹) *
          (c * d.regularPart * c⁻¹) := by
            symm
            calc
              (c * d.pPart * c⁻¹) *
                    (c * d.regularPart * c⁻¹) =
                  c * d.pPart * (c⁻¹ * c) *
                    d.regularPart * c⁻¹ := by
                      ac_rfl
              _ = c * (d.pPart * d.regularPart) *
                    c⁻¹ := by
                      rw [inv_mul_cancel]
                      simp only [mul_one, mul_assoc]
    _ = t * a := by rw [hc]
    _ = a * t := hta.eq

end PRegularConjClasses

end McKayConjecture
