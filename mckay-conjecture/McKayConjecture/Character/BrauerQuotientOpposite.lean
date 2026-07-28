/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeAlgebraOpposite
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Brauer quotients of opposite algebras

The fixed algebra of an opposite action is the opposite of the fixed
algebra, and taking relative traces commutes with `op` and `unop`.
Consequently

`Aᵐᵒᵖ(P) ≃ₐ[k] A(P)ᵐᵒᵖ`.

This is the lower-left identification in the elementary split-Dade
proof.
-/

noncomputable section

open scoped BigOperators

namespace Representation

variable {k P A : Type}
variable [CommRing k] [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

noncomputable local instance oppositeBrauerLeftCosetFintype
    (Q : Subgroup P) :
    Fintype (P ⧸ Q) :=
  Fintype.ofFinite (P ⧸ Q)

/-- Unop an element fixed in the opposite algebra. -/
def unopFixedSubalgebra
    (x : fixedSubalgebra (k := k) (P := P) (A := Aᵐᵒᵖ)) :
    fixedSubalgebra (k := k) (P := P) (A := A) where
  val := MulOpposite.unop x
  property g := by
    have hx := x.property g
    exact congrArg MulOpposite.unop hx

/-- Opposite an element of the original fixed algebra. -/
def opFixedSubalgebra
    (x : fixedSubalgebra (k := k) (P := P) (A := A)) :
    fixedSubalgebra (k := k) (P := P) (A := Aᵐᵒᵖ) where
  val := MulOpposite.op x
  property g := by
    apply MulOpposite.unop_injective
    exact x.property g

omit [Fintype P] in
@[simp]
theorem unopFixedSubalgebra_coe
    (x : fixedSubalgebra (k := k) (P := P) (A := Aᵐᵒᵖ)) :
    (unopFixedSubalgebra x :
      fixedSubalgebra (k := k) (P := P) (A := A)) =
      MulOpposite.unop (x : Aᵐᵒᵖ) :=
  rfl

omit [Fintype P] in
@[simp]
theorem opFixedSubalgebra_coe
    (x : fixedSubalgebra (k := k) (P := P) (A := A)) :
    (opFixedSubalgebra x :
      fixedSubalgebra (k := k) (P := P) (A := Aᵐᵒᵖ)) =
      MulOpposite.op (x : A) :=
  rfl

omit [Fintype P] in
@[simp]
theorem unopFixedSubalgebra_opFixedSubalgebra
    (x : fixedSubalgebra (k := k) (P := P) (A := A)) :
    unopFixedSubalgebra (opFixedSubalgebra x) = x :=
  rfl

omit [Fintype P] in
@[simp]
theorem opFixedSubalgebra_unopFixedSubalgebra
    (x : fixedSubalgebra (k := k) (P := P) (A := Aᵐᵒᵖ)) :
    opFixedSubalgebra (unopFixedSubalgebra x) = x := by
  apply Subtype.ext
  rfl

/-- Unop commutes with a fixed-algebra relative trace. -/
theorem unopFixedSubalgebra_fixedRelativeTrace
    (Q : Subgroup P)
    (x : fixedSubalgebra (k := k) (P := Q) (A := Aᵐᵒᵖ)) :
    unopFixedSubalgebra
        (fixedRelativeTrace (k := k) (P := P) (A := Aᵐᵒᵖ) Q x) =
      fixedRelativeTrace (k := k) (P := P) (A := A) Q
        (unopFixedSubalgebra x) := by
  apply Subtype.ext
  change
    MulOpposite.unop
        (∑ c : P ⧸ Q, c.out • (x : Aᵐᵒᵖ)) =
      ∑ c : P ⧸ Q, c.out • MulOpposite.unop (x : Aᵐᵒᵖ)
  simp

/-- Op commutes with a fixed-algebra relative trace. -/
theorem opFixedSubalgebra_fixedRelativeTrace
    (Q : Subgroup P)
    (x : fixedSubalgebra (k := k) (P := Q) (A := A)) :
    opFixedSubalgebra
        (fixedRelativeTrace (k := k) (P := P) (A := A) Q x) =
      fixedRelativeTrace (k := k) (P := P) (A := Aᵐᵒᵖ) Q
        (opFixedSubalgebra x) := by
  apply Subtype.ext
  apply MulOpposite.unop_injective
  change
    ∑ c : P ⧸ Q, c.out • (x : A) =
      MulOpposite.unop
        (∑ c : P ⧸ Q,
          c.out • MulOpposite.op (x : A))
  simp

/-- Unop carries the opposite trace ideal into the original trace
ideal. -/
theorem unopFixedSubalgebra_mem_brauerTraceIdeal
    (x : fixedSubalgebra (k := k) (P := P) (A := Aᵐᵒᵖ))
    (hx :
      x ∈ brauerTraceIdeal (k := k) (P := P) (A := Aᵐᵒᵖ)) :
    unopFixedSubalgebra x ∈
      brauerTraceIdeal (k := k) (P := P) (A := A) := by
  let I :=
    brauerTraceIdeal (k := k) (P := P) (A := A)
  change unopFixedSubalgebra x ∈ I
  refine Submodule.iSup_induction
    (fun Q : Subgroup P =>
      ⨆ _hQ : Q < ⊤,
        fixedRelativeTraceIdeal
          (k := k) (P := P) (A := Aᵐᵒᵖ) Q)
    (motive := fun y => unopFixedSubalgebra y ∈ I)
    hx ?_ ?_ ?_
  · intro Q y hy
    refine Submodule.iSup_induction
      (fun _hQ : Q < ⊤ =>
        fixedRelativeTraceIdeal
          (k := k) (P := P) (A := Aᵐᵒᵖ) Q)
      (motive := fun z => unopFixedSubalgebra z ∈ I)
      hy ?_ ?_ ?_
    · intro hQ z hz
      obtain ⟨w, rfl⟩ := hz
      rw [unopFixedSubalgebra_fixedRelativeTrace]
      exact
        fixedRelativeTrace_mem_brauerTraceIdeal
          (k := k) (P := P) (A := A) Q hQ _
    · exact I.zero_mem
    · intro u v hu hv
      exact I.add_mem hu hv
  · exact I.zero_mem
  · intro u v hu hv
    exact I.add_mem hu hv

/-- Op carries the original trace ideal into the opposite trace
ideal. -/
theorem opFixedSubalgebra_mem_brauerTraceIdeal
    (x : fixedSubalgebra (k := k) (P := P) (A := A))
    (hx :
      x ∈ brauerTraceIdeal (k := k) (P := P) (A := A)) :
    opFixedSubalgebra x ∈
      brauerTraceIdeal (k := k) (P := P) (A := Aᵐᵒᵖ) := by
  let I :=
    brauerTraceIdeal (k := k) (P := P) (A := Aᵐᵒᵖ)
  change opFixedSubalgebra x ∈ I
  refine Submodule.iSup_induction
    (fun Q : Subgroup P =>
      ⨆ _hQ : Q < ⊤,
        fixedRelativeTraceIdeal
          (k := k) (P := P) (A := A) Q)
    (motive := fun y => opFixedSubalgebra y ∈ I)
    hx ?_ ?_ ?_
  · intro Q y hy
    refine Submodule.iSup_induction
      (fun _hQ : Q < ⊤ =>
        fixedRelativeTraceIdeal
          (k := k) (P := P) (A := A) Q)
      (motive := fun z => opFixedSubalgebra z ∈ I)
      hy ?_ ?_ ?_
    · intro hQ z hz
      obtain ⟨w, rfl⟩ := hz
      rw [opFixedSubalgebra_fixedRelativeTrace]
      exact
        fixedRelativeTrace_mem_brauerTraceIdeal
          (k := k) (P := P) (A := Aᵐᵒᵖ) Q hQ _
    · exact I.zero_mem
    · intro u v hu hv
      exact I.add_mem hu hv
  · exact I.zero_mem
  · intro u v hu hv
    exact I.add_mem hu hv

/-- Project an opposite fixed element to the opposite of the original
Brauer quotient. -/
def oppositeFixedToBrauerOpposite :
    fixedSubalgebra (k := k) (P := P) (A := Aᵐᵒᵖ) →ₐ[k]
      (BrauerQuotientAlgebra (k := k) (P := P) (A := A))ᵐᵒᵖ where
  toFun x :=
    MulOpposite.op
      (brauerAlgebraProjection
        (k := k) (P := P) (A := A)
        (unopFixedSubalgebra x))
  map_zero' := by
    apply MulOpposite.unop_injective
    rfl
  map_add' x y := by
    apply MulOpposite.unop_injective
    rfl
  map_one' := by
    apply MulOpposite.unop_injective
    rfl
  map_mul' x y := by
    apply MulOpposite.unop_injective
    rfl
  commutes' r := by
    apply MulOpposite.unop_injective
    rfl

/-- The preceding map kills the opposite Brauer trace ideal. -/
theorem oppositeFixedToBrauerOpposite_eq_zero_of_mem
    (x : fixedSubalgebra (k := k) (P := P) (A := Aᵐᵒᵖ))
    (hx :
      x ∈ brauerTraceIdeal (k := k) (P := P) (A := Aᵐᵒᵖ)) :
    oppositeFixedToBrauerOpposite
        (k := k) (P := P) (A := A) x = 0 := by
  apply MulOpposite.unop_injective
  change
    brauerAlgebraProjection
        (k := k) (P := P) (A := A)
        (unopFixedSubalgebra x) =
      0
  rw [brauerAlgebraProjection, Ideal.Quotient.eq_zero_iff_mem]
  exact
    unopFixedSubalgebra_mem_brauerTraceIdeal
      (k := k) (P := P) (A := A) x hx

/-- The algebra homomorphism
`Aᵐᵒᵖ(P) → A(P)ᵐᵒᵖ`. -/
def brauerQuotientOppositeAlgHom :
    BrauerQuotientAlgebra (k := k) (P := P) (A := Aᵐᵒᵖ) →ₐ[k]
      (BrauerQuotientAlgebra (k := k) (P := P) (A := A))ᵐᵒᵖ :=
  Ideal.Quotient.liftₐ
    (brauerTraceIdeal (k := k) (P := P) (A := Aᵐᵒᵖ))
    (oppositeFixedToBrauerOpposite
      (k := k) (P := P) (A := A))
    (oppositeFixedToBrauerOpposite_eq_zero_of_mem
      (k := k) (P := P) (A := A))

@[simp]
theorem brauerQuotientOppositeAlgHom_projection
    (x : fixedSubalgebra (k := k) (P := P) (A := Aᵐᵒᵖ)) :
    brauerQuotientOppositeAlgHom
        (k := k) (P := P) (A := A)
        (brauerAlgebraProjection
          (k := k) (P := P) (A := Aᵐᵒᵖ) x) =
      MulOpposite.op
        (brauerAlgebraProjection
          (k := k) (P := P) (A := A)
          (unopFixedSubalgebra x)) :=
  rfl

/-- The opposite Brauer homomorphism is surjective. -/
theorem brauerQuotientOppositeAlgHom_surjective :
    Function.Surjective
      (brauerQuotientOppositeAlgHom
        (k := k) (P := P) (A := A)) := by
  intro y
  obtain ⟨x, hx⟩ :=
    brauerAlgebraProjection_surjective
      (k := k) (P := P) (A := A)
      (MulOpposite.unop y)
  refine
    ⟨brauerAlgebraProjection
        (k := k) (P := P) (A := Aᵐᵒᵖ)
        (opFixedSubalgebra (k := k) (P := P) (A := A) x), ?_⟩
  rw [brauerQuotientOppositeAlgHom_projection
    (k := k) (P := P) (A := A)]
  rw [unopFixedSubalgebra_opFixedSubalgebra, hx]
  exact MulOpposite.op_unop y

/-- The opposite Brauer homomorphism is injective. -/
theorem brauerQuotientOppositeAlgHom_injective :
    Function.Injective
      (brauerQuotientOppositeAlgHom
        (k := k) (P := P) (A := A)) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨x, rfl⟩ :=
    brauerAlgebraProjection_surjective
      (k := k) (P := P) (A := Aᵐᵒᵖ) y
  rw [brauerQuotientOppositeAlgHom_projection
    (k := k) (P := P) (A := A)] at hy
  have hunop :
      brauerAlgebraProjection
          (k := k) (P := P) (A := A)
          (unopFixedSubalgebra x) =
        0 := by
    exact MulOpposite.op_injective hy
  rw [brauerAlgebraProjection, Ideal.Quotient.eq_zero_iff_mem]
  have hu :
      unopFixedSubalgebra x ∈
        brauerTraceIdeal (k := k) (P := P) (A := A) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact hunop
  have ho :=
    opFixedSubalgebra_mem_brauerTraceIdeal
      (k := k) (P := P) (A := A)
      (unopFixedSubalgebra x) hu
  simpa using ho

/-- Brauer quotients commute with passage to the opposite algebra. -/
def brauerQuotientOppositeAlgEquiv :
    BrauerQuotientAlgebra (k := k) (P := P) (A := Aᵐᵒᵖ) ≃ₐ[k]
      (BrauerQuotientAlgebra (k := k) (P := P) (A := A))ᵐᵒᵖ :=
  AlgEquiv.ofBijective
    (brauerQuotientOppositeAlgHom
      (k := k) (P := P) (A := A))
    ⟨brauerQuotientOppositeAlgHom_injective
        (k := k) (P := P) (A := A),
      brauerQuotientOppositeAlgHom_surjective
        (k := k) (P := P) (A := A)⟩

@[simp]
theorem brauerQuotientOppositeAlgEquiv_projection
    (x : fixedSubalgebra (k := k) (P := P) (A := Aᵐᵒᵖ)) :
    brauerQuotientOppositeAlgEquiv
        (k := k) (P := P) (A := A)
        (brauerAlgebraProjection
          (k := k) (P := P) (A := Aᵐᵒᵖ) x) =
      MulOpposite.op
        (brauerAlgebraProjection
          (k := k) (P := P) (A := A)
          (unopFixedSubalgebra x)) :=
  rfl

end Representation
