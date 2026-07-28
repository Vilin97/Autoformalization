/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Data.Matrix.Basic

/-!
# Entrywise criteria for scalar matrices

This file packages two small entrywise criteria for proving that a square
matrix is a scalar multiple of the identity.  `HasScalarIdentityRow` is
intended for large explicit matrices: each row can be certified in a separate
small declaration, and `eq_smul_one_of_scalar_identity_rows` then assembles
the row certificates without expanding all pairs of indices at once.
-/

namespace McKayConjecture
namespace Matrix

universe u v

variable {ι : Type u} {R : Type v}

/-- `A` has scalar-identity row `i` with scalar `c` when its diagonal entry
in that row is `c` and all other entries in the row are zero. -/
def HasScalarIdentityRow [DecidableEq ι] [Zero R]
    (A : Matrix ι ι R) (c : R) (i : ι) : Prop :=
  ∀ j, A i j = if i = j then c else 0

/-- A square matrix whose diagonal entries are all `c` and whose
off-diagonal entries all vanish is `c` times the identity matrix. -/
theorem eq_smul_one_of_diagonal_eq_of_off_diagonal_eq_zero
    [DecidableEq ι] [Semiring R]
    (A : Matrix ι ι R) (c : R)
    (diagonal_eq : ∀ i, A i i = c)
    (off_diagonal_eq_zero : ∀ i j, i ≠ j → A i j = 0) :
    A = c • (1 : Matrix ι ι R) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [diagonal_eq]
  · simp [hij, off_diagonal_eq_zero i j hij]

/-- Assemble a scalar-matrix equality from one entrywise certificate for
each row.  This is useful for generated high-dimensional matrix proofs,
because the finite case split for each row can live in its own declaration. -/
theorem eq_smul_one_of_scalar_identity_rows
    [DecidableEq ι] [Semiring R]
    (A : Matrix ι ι R) (c : R)
    (rows : ∀ i, HasScalarIdentityRow A c i) :
    A = c • (1 : Matrix ι ι R) := by
  apply eq_smul_one_of_diagonal_eq_of_off_diagonal_eq_zero A c
  · intro i
    simpa [HasScalarIdentityRow] using rows i i
  · intro i j hij
    simpa [HasScalarIdentityRow, hij] using rows i j

end Matrix
end McKayConjecture
