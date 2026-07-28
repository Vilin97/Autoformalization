/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.PermutationAlgebraBasis
import Mathlib.Algebra.Central.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Dade algebras

For a finite `p`-group `P` and a field `k` of characteristic `p`, a
Dade `P`-algebra is a finite-dimensional central simple `k`-algebra
with a `P`-stable basis containing `1`.

Classically this is equivalent to asking for a permutation `P`-algebra
whose Brauer quotient at `P` is nonzero.  The nonzero implication is
proved constructively by
`PointedPermutationAlgebraBasis.brauerQuotientAlgebra_nontrivial`.
-/

noncomputable section

namespace Representation

section Definition

variable (p : ℕ) [Fact p.Prime]
variable (k P A : Type)
variable [Field k] [CharP k p]
variable [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

/-- Constructive data of a Dade `P`-algebra.  Central simplicity and
finite dimensionality are carried by the surrounding typeclass
parameters; the fields contain the `p`-group proof and the pointed
permutation basis. -/
structure DadeAlgebra where
  /-- The algebra is central over its coefficient field. -/
  isCentral : Algebra.IsCentral k A
  /-- The algebra has no nontrivial two-sided ideals. -/
  isSimple : IsSimpleRing A
  /-- The algebra is finite-dimensional over its coefficient field. -/
  finiteDimensional : FiniteDimensional k A
  /-- The acting group is a `p`-group. -/
  isPGroup : IsPGroup p P
  /-- A stable algebra basis containing `1`. -/
  permutationBasis :
    PointedPermutationAlgebraBasis (k := k) (P := P) (A := A)

end Definition

namespace DadeAlgebra

variable
  {p k P A}
  [Fact p.Prime]
  [Field k] [CharP k p]
  [Group P] [Fintype P]
  [Ring A] [Algebra k A]
  [MulSemiringAction P A] [SMulCommClass P k A]

/-- The Brauer trace ideal of a Dade algebra is proper. -/
theorem brauerTraceIdeal_ne_top
    (S : DadeAlgebra p k P A) :
    brauerTraceIdeal (k := k) (P := P) (A := A) ≠ ⊤ :=
  PointedPermutationAlgebraBasis.brauerTraceIdeal_ne_top
    (B := S.permutationBasis) S.isPGroup

/-- The Brauer quotient of a Dade algebra is nontrivial. -/
theorem brauerQuotientAlgebra_nontrivial
    (S : DadeAlgebra p k P A) :
    Nontrivial
      (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) :=
  PointedPermutationAlgebraBasis.brauerQuotientAlgebra_nontrivial
    (B := S.permutationBasis) S.isPGroup

end DadeAlgebra
end Representation
