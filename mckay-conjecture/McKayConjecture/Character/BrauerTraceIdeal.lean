/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerFixedAlgebra
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# The Brauer trace ideal of an algebra action

For a finite group `P` acting by automorphisms on a `k`-algebra `A`,
the relative trace from `Q ≤ P` maps `A^Q` into `A^P`.  Its image is a
two-sided ideal of `A^P`: multiplication by a `P`-fixed element can be
moved through every summand of the trace.

The sum of these ideals over the proper subgroups is the Brauer trace
ideal.  Its quotient is the multiplicative Brauer quotient used in
Dade's theory of `P`-algebras.
-/

noncomputable section

open scoped BigOperators

namespace Representation

variable {k P A : Type}
variable [CommRing k] [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

noncomputable local instance brauerTraceLeftCosetFintype
    (Q : Subgroup P) :
    Fintype (P ⧸ Q) :=
  Fintype.ofFinite (P ⧸ Q)

/-- Relative trace between fixed subalgebras, regarded as a `k`-linear
map. -/
def fixedRelativeTrace
    (Q : Subgroup P) :
    fixedSubalgebra (k := k) (P := Q) (A := A) →ₗ[k]
      fixedSubalgebra (k := k) (P := P) (A := A) where
  toFun x :=
    invariantsEquivFixedSubalgebra
      (k := k) (P := P) (A := A)
      (relativeTrace
        (algebraActionRepresentation (k := k) (P := P) (A := A))
        Q
        ⟨x, x.property⟩)
  map_add' x y := by
    apply Subtype.ext
    exact congr_arg Subtype.val
      (map_add
        (relativeTrace
          (algebraActionRepresentation (k := k) (P := P) (A := A))
          Q)
        (⟨x, x.property⟩ :
          invariants
            ((algebraActionRepresentation
              (k := k) (P := P) (A := A)).comp Q.subtype))
        ⟨y, y.property⟩)
  map_smul' r x := by
    apply Subtype.ext
    exact congr_arg Subtype.val
      (map_smul
        (relativeTrace
          (algebraActionRepresentation (k := k) (P := P) (A := A))
          Q)
        r
        (⟨x, x.property⟩ :
          invariants
            ((algebraActionRepresentation
              (k := k) (P := P) (A := A)).comp Q.subtype)))

@[simp]
theorem fixedRelativeTrace_apply_coe
    (Q : Subgroup P)
    (x : fixedSubalgebra (k := k) (P := Q) (A := A)) :
    ((fixedRelativeTrace (k := k) (P := P) (A := A) Q x :
        fixedSubalgebra (k := k) (P := P) (A := A)) : A) =
      ∑ c : P ⧸ Q, c.out • (x : A) :=
  rfl

/-- A relative trace commutes with left multiplication by a globally
fixed element. -/
theorem fixedRelativeTrace_mul_left
    (Q : Subgroup P)
    (a : fixedSubalgebra (k := k) (P := P) (A := A))
    (x : fixedSubalgebra (k := k) (P := Q) (A := A)) :
    fixedRelativeTrace (k := k) (P := P) (A := A) Q
        (fixedSubalgebraRestriction
          (k := k) (P := P) (A := A) Q a * x) =
      a * fixedRelativeTrace (k := k) (P := P) (A := A) Q x := by
  apply Subtype.ext
  change
    (∑ c : P ⧸ Q, c.out • ((a : A) * (x : A))) =
      (a : A) * ∑ c : P ⧸ Q, c.out • (x : A)
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro c
  rw [MulSemiringAction.smul_mul, a.property c.out]

/-- A relative trace commutes with right multiplication by a globally
fixed element. -/
theorem fixedRelativeTrace_mul_right
    (Q : Subgroup P)
    (x : fixedSubalgebra (k := k) (P := Q) (A := A))
    (a : fixedSubalgebra (k := k) (P := P) (A := A)) :
    fixedRelativeTrace (k := k) (P := P) (A := A) Q
        (x * fixedSubalgebraRestriction
          (k := k) (P := P) (A := A) Q a) =
      fixedRelativeTrace (k := k) (P := P) (A := A) Q x * a := by
  apply Subtype.ext
  change
    (∑ c : P ⧸ Q, c.out • ((x : A) * (a : A))) =
      (∑ c : P ⧸ Q, c.out • (x : A)) * (a : A)
  rw [Finset.sum_mul]
  apply Fintype.sum_congr
  intro c
  rw [MulSemiringAction.smul_mul, a.property c.out]

/-- The image of one relative trace, as a left ideal of `A^P`. -/
def fixedRelativeTraceIdeal
    (Q : Subgroup P) :
    Ideal (fixedSubalgebra (k := k) (P := P) (A := A)) where
  carrier :=
    Set.range
      (fixedRelativeTrace (k := k) (P := P) (A := A) Q)
  zero_mem' := ⟨0, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ x y⟩
  smul_mem' a := by
    rintro _ ⟨x, rfl⟩
    refine
      ⟨fixedSubalgebraRestriction
          (k := k) (P := P) (A := A) Q a * x, ?_⟩
    exact
      fixedRelativeTrace_mul_left
        (k := k) (P := P) (A := A) Q a x

/-- The image of one relative trace is also closed under right
multiplication. -/
instance fixedRelativeTraceIdeal_isTwoSided
    (Q : Subgroup P) :
    (fixedRelativeTraceIdeal
      (k := k) (P := P) (A := A) Q).IsTwoSided where
  mul_mem_of_left a := by
    rintro ⟨x, rfl⟩
    refine
      ⟨x * fixedSubalgebraRestriction
          (k := k) (P := P) (A := A) Q a, ?_⟩
    exact
      fixedRelativeTrace_mul_right
        (k := k) (P := P) (A := A) Q x a

/-- The sum of relative-trace ideals from all proper subgroups. -/
def brauerTraceIdeal :
    Ideal (fixedSubalgebra (k := k) (P := P) (A := A)) :=
  ⨆ (Q : Subgroup P) (_hQ : Q < ⊤),
    fixedRelativeTraceIdeal (k := k) (P := P) (A := A) Q

/-- Every trace ideal from a proper subgroup is contained in the total
Brauer trace ideal. -/
theorem fixedRelativeTraceIdeal_le_brauerTraceIdeal
    (Q : Subgroup P)
    (hQ : Q < ⊤) :
    fixedRelativeTraceIdeal (k := k) (P := P) (A := A) Q ≤
      brauerTraceIdeal (k := k) (P := P) (A := A) :=
  le_iSup_of_le Q (le_iSup_of_le hQ le_rfl)

/-- Pointwise membership of a relative trace in the total trace
ideal. -/
theorem fixedRelativeTrace_mem_brauerTraceIdeal
    (Q : Subgroup P)
    (hQ : Q < ⊤)
    (x : fixedSubalgebra (k := k) (P := Q) (A := A)) :
    fixedRelativeTrace (k := k) (P := P) (A := A) Q x ∈
      brauerTraceIdeal (k := k) (P := P) (A := A) :=
  fixedRelativeTraceIdeal_le_brauerTraceIdeal
    (k := k) (P := P) (A := A) Q hQ ⟨x, rfl⟩

noncomputable instance brauerTraceIdeal_isTwoSided :
    (brauerTraceIdeal
      (k := k) (P := P) (A := A)).IsTwoSided :=
  ⟨fun a hx ↦ by
    let B :=
      brauerTraceIdeal (k := k) (P := P) (A := A)
    change _ ∈ B
    refine Submodule.iSup_induction
      (fun Q : Subgroup P ↦
        ⨆ _hQ : Q < ⊤,
          fixedRelativeTraceIdeal
            (k := k) (P := P) (A := A) Q)
      (motive := fun x ↦ x * a ∈ B) hx ?_ ?_ ?_
    · intro Q x hxQ
      refine Submodule.iSup_induction
        (fun _hQ : Q < ⊤ ↦
          fixedRelativeTraceIdeal
            (k := k) (P := P) (A := A) Q)
        (motive := fun y ↦ y * a ∈ B) hxQ ?_ ?_ ?_
      · intro hQ y hy
        change
          y * a ∈
            brauerTraceIdeal (k := k) (P := P) (A := A)
        exact
          (le_iSup
            (fun R : Subgroup P ↦
              ⨆ _hR : R < ⊤,
                fixedRelativeTraceIdeal
                  (k := k) (P := P) (A := A) R)
            Q)
            ((le_iSup
              (fun _hQ : Q < ⊤ ↦
                fixedRelativeTraceIdeal
                  (k := k) (P := P) (A := A) Q)
              hQ)
              (Ideal.mul_mem_right a
                (fixedRelativeTraceIdeal
                  (k := k) (P := P) (A := A) Q) hy))
      · rw [zero_mul]
        exact B.zero_mem
      · intro y z hy hz
        rw [add_mul]
        exact B.add_mem hy hz
    · rw [zero_mul]
      exact B.zero_mem
    · intro x y hx hy
      rw [add_mul]
      exact B.add_mem hx hy⟩

/-- The multiplicative Brauer quotient `A(P)`. -/
abbrev BrauerQuotientAlgebra :=
  fixedSubalgebra (k := k) (P := P) (A := A) ⧸
    brauerTraceIdeal (k := k) (P := P) (A := A)

/-- The canonical ring homomorphism from `A^P` to its Brauer
quotient. -/
def brauerAlgebraProjection :
    fixedSubalgebra (k := k) (P := P) (A := A) →+*
      BrauerQuotientAlgebra (k := k) (P := P) (A := A) :=
  Ideal.Quotient.mk
    (brauerTraceIdeal (k := k) (P := P) (A := A))

@[simp]
theorem brauerAlgebraProjection_fixedRelativeTrace
    (Q : Subgroup P)
    (hQ : Q < ⊤)
    (x : fixedSubalgebra (k := k) (P := Q) (A := A)) :
    brauerAlgebraProjection (k := k) (P := P) (A := A)
        (fixedRelativeTrace (k := k) (P := P) (A := A) Q x) =
      0 := by
  rw [brauerAlgebraProjection, Ideal.Quotient.eq_zero_iff_mem]
  exact
    fixedRelativeTrace_mem_brauerTraceIdeal
      (k := k) (P := P) (A := A) Q hQ x

/-- The Brauer algebra projection is onto. -/
theorem brauerAlgebraProjection_surjective :
    Function.Surjective
      (brauerAlgebraProjection (k := k) (P := P) (A := A)) :=
  Ideal.Quotient.mk_surjective

end Representation
