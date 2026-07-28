/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerScalarIdentificationFinrankOne
import McKayConjecture.Character.PermutationAlgebraBrauerQuotientBasis

/-!
# Scalar Brauer quotients of pointed permutation algebras

The distinguished unit vector in a pointed permutation basis is always
fixed.  If it is the only fixed basis vector, the algebra Brauer quotient
is one-dimensional and therefore canonically identified with the
coefficient field.
-/

noncomputable section

namespace Representation
namespace PointedPermutationAlgebraBasis

variable {p : ℕ} [Fact p.Prime]
variable {k P A : Type}
variable [Field k] [CharP k p]
variable [Group P] [Finite P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

variable
  (B : PointedPermutationAlgebraBasis
    (k := k) (P := P) (A := A))

noncomputable local instance permutationAlgebraScalarGroupFintype :
    Fintype P :=
  Fintype.ofFinite P

variable [Finite B.index]

/-- The distinguished basis index of `1` is globally fixed. -/
def oneFixedIndex : B.FixedIndex :=
  ⟨B.oneIndex, fun g ↦ by
    change B.indexAction g B.oneIndex = B.oneIndex
    exact B.indexAction_oneIndex g⟩

omit [Finite P] [Finite B.index] [SMulCommClass P k A] in
@[simp]
theorem oneFixedIndex_coe :
    (B.oneFixedIndex : B.index) = B.oneIndex :=
  rfl

/-- If the distinguished unit is the unique fixed basis vector, the
algebra Brauer quotient has dimension one. -/
theorem finrank_brauerQuotientAlgebra_eq_one
    (hP : IsPGroup p P)
    [Subsingleton B.FixedIndex] :
    Module.finrank k
        (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) =
      1 := by
  rw [B.finrank_brauerQuotientAlgebra_eq_card_fixedIndex hP]
  exact
    Fintype.card_eq_one_iff.mpr
      ⟨B.oneFixedIndex, fun i ↦
        Subsingleton.elim i B.oneFixedIndex⟩

/-- Canonical scalar-unit identification for a pointed permutation
algebra with a unique fixed basis vector. -/
def brauerScalarIdentification
    (hP : IsPGroup p P)
    [Subsingleton B.FixedIndex] :
    BrauerScalarIdentification (k := k) (P := P) (A := A) :=
  brauerScalarIdentificationOfFinrankOne
    (B.finrank_brauerQuotientAlgebra_eq_one hP)

end PointedPermutationAlgebraBasis
end Representation
