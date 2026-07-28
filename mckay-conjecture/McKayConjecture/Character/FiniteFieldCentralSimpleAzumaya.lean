/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.FiniteFieldCentralSimpleSplitting
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.Algebra.Azumaya.Matrix

/-!
# Central simple algebras over finite fields are Azumaya

The finite-field splitting theorem identifies a finite-dimensional
central simple algebra with a nonzero matrix algebra.  Matrix
algebras are Azumaya, and the property transports across algebra
equivalences.

This packages the canonical left-right multiplication isomorphism
needed in the split-Dade Brauer-quotient calculation.
-/

noncomputable section

namespace Representation

universe u v

variable (k : Type u) (A : Type v)
variable [Field k] [Finite k]
variable [Ring A] [Algebra k A]

/-- A finite-dimensional central simple algebra over a finite field
is Azumaya. -/
theorem isAzumaya_of_finiteField
    [Algebra.IsCentral k A] [IsSimpleRing A]
    [FiniteDimensional k A] :
    IsAzumaya k A := by
  obtain ⟨n, hn, ⟨e⟩⟩ :=
    exists_algEquiv_matrix_of_finiteField k A
  letI : NeZero n := hn
  letI : Nonempty (Fin n) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  letI : IsAzumaya k (Matrix (Fin n) (Fin n) k) :=
    IsAzumaya.matrix k (Fin n)
  exact
    IsAzumaya.of_AlgEquiv
      k (Matrix (Fin n) (Fin n) k) A e.symm

end Representation
