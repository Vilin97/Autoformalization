/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerTraceIdeal
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Brauer quotients and equivariant algebra equivalences

An equivariant algebra equivalence identifies fixed subalgebras,
commutes with every relative trace, and therefore identifies the
corresponding algebra Brauer quotients.  This file records that
functoriality for equivalences between two different algebras.

The construction is deliberately phrased for the same acting group
on both sides.  This is the form needed to descend the left-right
multiplication equivalence

`A ⊗[k] Aᵐᵒᵖ ≃ₐ[k] Endₖ(A)`

in the split-Dade calculation.
-/

noncomputable section

open scoped BigOperators

namespace Representation

section FixedSubalgebra

variable {k G A D : Type}
variable [CommRing k] [Group G]
variable [Ring A] [Algebra k A]
variable [Ring D] [Algebra k D]
variable [MulSemiringAction G A] [SMulCommClass G k A]
variable [MulSemiringAction G D] [SMulCommClass G k D]

/-- An equivariant algebra equivalence restricts to an equivalence of
fixed subalgebras. -/
def equivariantFixedSubalgebraAlgEquiv
    (e : A ≃ₐ[k] D)
    (he : ∀ (g : G) (a : A), e (g • a) = g • e a) :
    fixedSubalgebra (k := k) (P := G) (A := A) ≃ₐ[k]
      fixedSubalgebra (k := k) (P := G) (A := D) where
  toFun x :=
    ⟨e x, fun g => by
      rw [← he, x.property]⟩
  invFun y :=
    ⟨e.symm y, fun g => by
      apply e.injective
      rw [e.apply_symm_apply, he, e.apply_symm_apply, y.property]⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x
  right_inv y := by
    apply Subtype.ext
    exact e.apply_symm_apply y
  map_add' x y := by
    apply Subtype.ext
    exact map_add e (x : A) (y : A)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul e (x : A) (y : A)
  commutes' r := by
    apply Subtype.ext
    exact e.commutes r

@[simp]
theorem equivariantFixedSubalgebraAlgEquiv_coe
    (e : A ≃ₐ[k] D)
    (he : ∀ (g : G) (a : A), e (g • a) = g • e a)
    (x : fixedSubalgebra (k := k) (P := G) (A := A)) :
    ((equivariantFixedSubalgebraAlgEquiv e he x :
        fixedSubalgebra (k := k) (P := G) (A := D)) : D) =
      e (x : A) :=
  rfl

omit [SMulCommClass G k A] [SMulCommClass G k D] in
/-- Equivariance of the inverse algebra equivalence. -/
theorem equivariantAlgEquiv_symm
    (e : A ≃ₐ[k] D)
    (he : ∀ (g : G) (a : A), e (g • a) = g • e a)
    (g : G) (d : D) :
    e.symm (g • d) = g • e.symm d := by
  apply e.injective
  rw [e.apply_symm_apply, he, e.apply_symm_apply]

end FixedSubalgebra

section BrauerQuotient

variable {k P A D : Type}
variable [CommRing k] [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [Ring D] [Algebra k D]
variable [MulSemiringAction P A] [SMulCommClass P k A]
variable [MulSemiringAction P D] [SMulCommClass P k D]

variable
  (e : A ≃ₐ[k] D)
  (he : ∀ (g : P) (a : A), e (g • a) = g • e a)

noncomputable local instance brauerAlgEquivLeftCosetFintype
    (Q : Subgroup P) :
    Fintype (P ⧸ Q) :=
  Fintype.ofFinite (P ⧸ Q)

/-- The fixed-algebra equivalence commutes with a relative trace from
the same subgroup on both sides. -/
theorem equivariantFixedSubalgebraAlgEquiv_fixedRelativeTrace
    (Q : Subgroup P)
    (x : fixedSubalgebra (k := k) (P := Q) (A := A)) :
    equivariantFixedSubalgebraAlgEquiv e he
        (fixedRelativeTrace (k := k) (P := P) (A := A) Q x) =
      fixedRelativeTrace (k := k) (P := P) (A := D) Q
        (equivariantFixedSubalgebraAlgEquiv
          (k := k) (G := Q) (A := A) (D := D) e
          (fun q a => he (q : P) a) x) := by
  apply Subtype.ext
  change
    e (∑ c : P ⧸ Q, c.out • (x : A)) =
      ∑ c : P ⧸ Q, c.out • e (x : A)
  rw [map_sum]
  apply Fintype.sum_congr
  intro c
  exact he c.out x

/-- Pointwise preservation of the total Brauer trace ideal by an
equivariant algebra equivalence. -/
theorem equivariantFixedSubalgebraAlgEquiv_mem_brauerTraceIdeal
    (x : fixedSubalgebra (k := k) (P := P) (A := A))
    (hx :
      x ∈ brauerTraceIdeal (k := k) (P := P) (A := A)) :
    equivariantFixedSubalgebraAlgEquiv e he x ∈
      brauerTraceIdeal (k := k) (P := P) (A := D) := by
  let IA :=
    brauerTraceIdeal (k := k) (P := P) (A := A)
  let ID :=
    brauerTraceIdeal (k := k) (P := P) (A := D)
  change x ∈ IA at hx
  change equivariantFixedSubalgebraAlgEquiv e he x ∈ ID
  refine Submodule.iSup_induction
    (fun Q : Subgroup P =>
      ⨆ _hQ : Q < ⊤,
        fixedRelativeTraceIdeal (k := k) (P := P) (A := A) Q)
    (motive := fun y =>
      equivariantFixedSubalgebraAlgEquiv e he y ∈ ID)
    hx ?_ ?_ ?_
  · intro Q y hy
    refine Submodule.iSup_induction
      (fun _hQ : Q < ⊤ =>
        fixedRelativeTraceIdeal (k := k) (P := P) (A := A) Q)
      (motive := fun z =>
        equivariantFixedSubalgebraAlgEquiv e he z ∈ ID)
      hy ?_ ?_ ?_
    · intro hQ z hz
      obtain ⟨w, rfl⟩ := hz
      rw [equivariantFixedSubalgebraAlgEquiv_fixedRelativeTrace]
      exact
        fixedRelativeTrace_mem_brauerTraceIdeal
          (k := k) (P := P) (A := D) Q hQ _
    · simp
    · intro u v hu hv
      rw [map_add]
      exact ID.add_mem hu hv
  · simp
  · intro u v hu hv
    rw [map_add]
    exact ID.add_mem hu hv

/-- The equivariant fixed-algebra equivalence maps the source Brauer
trace ideal exactly onto the target Brauer trace ideal. -/
theorem map_brauerTraceIdeal_equivariantFixedSubalgebraAlgEquiv :
    brauerTraceIdeal (k := k) (P := P) (A := D) =
      (brauerTraceIdeal (k := k) (P := P) (A := A)).map
        (equivariantFixedSubalgebraAlgEquiv e he :
          fixedSubalgebra (k := k) (P := P) (A := A) →+*
            fixedSubalgebra (k := k) (P := P) (A := D)) := by
  apply le_antisymm
  · intro y hy
    let f :=
      equivariantFixedSubalgebraAlgEquiv e he
    let x :
        fixedSubalgebra (k := k) (P := P) (A := A) :=
      f.symm y
    have hsymm :
        ∀ (g : P) (d : D),
          e.symm (g • d) = g • e.symm d :=
      equivariantAlgEquiv_symm e he
    have hx :
        x ∈ brauerTraceIdeal (k := k) (P := P) (A := A) :=
      equivariantFixedSubalgebraAlgEquiv_mem_brauerTraceIdeal
        e.symm hsymm y hy
    have hfx : f x = y :=
      f.apply_symm_apply y
    rw [← hfx]
    exact Ideal.mem_map_of_mem f.toRingEquiv.toRingHom hx
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact
      equivariantFixedSubalgebraAlgEquiv_mem_brauerTraceIdeal
        e he x hx

/-- An equivariant algebra equivalence descends canonically to an
algebra equivalence of algebra Brauer quotients. -/
def brauerQuotientAlgEquiv :
    BrauerQuotientAlgebra (k := k) (P := P) (A := A) ≃ₐ[k]
      BrauerQuotientAlgebra (k := k) (P := P) (A := D) :=
  Ideal.quotientEquivAlg
    (brauerTraceIdeal (k := k) (P := P) (A := A))
    (brauerTraceIdeal (k := k) (P := P) (A := D))
    (equivariantFixedSubalgebraAlgEquiv e he)
    (map_brauerTraceIdeal_equivariantFixedSubalgebraAlgEquiv e he)

/-- The descended equivalence carries the source Brauer projection
to the target Brauer projection. -/
@[simp]
theorem brauerQuotientAlgEquiv_brauerAlgebraProjection
    (x : fixedSubalgebra (k := k) (P := P) (A := A)) :
    brauerQuotientAlgEquiv e he
        (brauerAlgebraProjection
          (k := k) (P := P) (A := A) x) =
      brauerAlgebraProjection
        (k := k) (P := P) (A := D)
        (equivariantFixedSubalgebraAlgEquiv e he x) := by
  rfl

end BrauerQuotient

end Representation
