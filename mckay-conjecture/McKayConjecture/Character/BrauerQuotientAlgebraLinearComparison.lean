/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerQuotient
import McKayConjecture.Character.BrauerTraceIdeal
import Mathlib.Algebra.Module.Submodule.RestrictScalars

/-!
# Comparing algebra and linear Brauer quotients

For an action on an algebra, the multiplicative Brauer quotient and
the Brauer quotient of the underlying linear representation have the
same underlying module.  This file gives the comparison without any
permutation-basis hypotheses.
-/

noncomputable section

namespace Representation

variable {k P A : Type}
variable [CommRing k] [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

/-- The Brauer trace ideal, regarded as a `k`-submodule of the fixed
algebra. -/
def brauerTraceIdealAsSubmodule :
    Submodule k
      (fixedSubalgebra (k := k) (P := P) (A := A)) :=
  (brauerTraceIdeal
    (k := k) (P := P) (A := A)).restrictScalars k

/-- The ideal image of one algebra relative trace has the same
underlying submodule as the corresponding linear trace range. -/
theorem fixedRelativeTraceIdeal_restrictScalars
    (Q : Subgroup P) :
    (fixedRelativeTraceIdeal
      (k := k) (P := P) (A := A) Q).restrictScalars k =
      relativeTraceRange
        (algebraActionRepresentation
          (k := k) (P := P) (A := A)) Q := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, x.property⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, x.property⟩, rfl⟩

/-- The total algebra trace ideal and the total linear trace submodule
have the same underlying `k`-submodule. -/
theorem brauerTraceIdealAsSubmodule_eq_brauerTraceSubmodule :
    brauerTraceIdealAsSubmodule (k := k) (P := P) (A := A) =
      brauerTraceSubmodule
        (algebraActionRepresentation
          (k := k) (P := P) (A := A)) := by
  simp only [brauerTraceIdealAsSubmodule, brauerTraceIdeal,
    brauerTraceSubmodule, Submodule.restrictScalars_iSup]
  congr with Q

/-- The algebra Brauer quotient and the Brauer quotient of the
underlying linear representation are canonically linearly
equivalent. -/
def brauerQuotientAlgebraLinearEquiv :
    BrauerQuotientAlgebra (k := k) (P := P) (A := A) ≃ₗ[k]
      BrauerQuotient
        (algebraActionRepresentation
          (k := k) (P := P) (A := A)) :=
  (Submodule.Quotient.restrictScalarsEquiv k
      (brauerTraceIdeal
        (k := k) (P := P) (A := A))).symm.trans
    (Submodule.quotEquivOfEq
      (brauerTraceIdealAsSubmodule
        (k := k) (P := P) (A := A))
      (brauerTraceSubmodule
        (algebraActionRepresentation
          (k := k) (P := P) (A := A)))
      (brauerTraceIdealAsSubmodule_eq_brauerTraceSubmodule
        (k := k) (P := P) (A := A)))

/-- A fixed algebra element regarded as an invariant vector. -/
def fixedSubalgebraToInvariant
    (x : fixedSubalgebra (k := k) (P := P) (A := A)) :
    invariants
      (algebraActionRepresentation
        (k := k) (P := P) (A := A)) :=
  ⟨x, x.property⟩

/-- The comparison carries the algebra projection to the linear
Brauer projection. -/
@[simp]
theorem brauerQuotientAlgebraLinearEquiv_projection
    (x : fixedSubalgebra (k := k) (P := P) (A := A)) :
    brauerQuotientAlgebraLinearEquiv
        (k := k) (P := P) (A := A)
        (brauerAlgebraProjection
          (k := k) (P := P) (A := A) x) =
      brauerProjection
        (algebraActionRepresentation
          (k := k) (P := P) (A := A))
        (fixedSubalgebraToInvariant
          (k := k) (P := P) (A := A) x) := by
  rfl

/-- Transport invariant vectors along equality of representations. -/
def invariantsLinearEquivOfRepresentationEq
    {V : Type} [AddCommGroup V] [Module k V]
    {rho sigma : Representation k P V}
    (h : rho = sigma) :
    invariants rho ≃ₗ[k] invariants sigma := by
  subst sigma
  exact LinearEquiv.refl k _

omit [Fintype P] in
/-- Transport along representation equality does not change the
underlying vector. -/
@[simp]
theorem coe_invariantsLinearEquivOfRepresentationEq
    {V : Type} [AddCommGroup V] [Module k V]
    {rho sigma : Representation k P V}
    (h : rho = sigma)
    (x : invariants rho) :
    ((invariantsLinearEquivOfRepresentationEq h x :
        invariants sigma) : V) =
      x := by
  subst sigma
  rfl

omit [Fintype P] in
/-- The inverse transport along representation equality also leaves
the underlying vector unchanged. -/
@[simp]
theorem coe_invariantsLinearEquivOfRepresentationEq_symm
    {V : Type} [AddCommGroup V] [Module k V]
    {rho sigma : Representation k P V}
    (h : rho = sigma)
    (x : invariants sigma) :
    (((invariantsLinearEquivOfRepresentationEq h).symm x :
        invariants rho) : V) =
      x := by
  subst sigma
  rfl

/-- Transport Brauer quotients along equality of representations. -/
def brauerQuotientLinearEquivOfRepresentationEq
    {V : Type} [AddCommGroup V] [Module k V]
    {rho sigma : Representation k P V}
    (h : rho = sigma) :
    BrauerQuotient rho ≃ₗ[k] BrauerQuotient sigma := by
  subst sigma
  exact LinearEquiv.refl k _

/-- Transport of Brauer quotients along representation equality
commutes with quotient projection. -/
@[simp]
theorem brauerQuotientLinearEquivOfRepresentationEq_projection
    {V : Type} [AddCommGroup V] [Module k V]
    {rho sigma : Representation k P V}
    (h : rho = sigma)
    (x : invariants rho) :
    brauerQuotientLinearEquivOfRepresentationEq h
        (brauerProjection rho x) =
      brauerProjection sigma
        (invariantsLinearEquivOfRepresentationEq h x) := by
  subst sigma
  rfl

end Representation
