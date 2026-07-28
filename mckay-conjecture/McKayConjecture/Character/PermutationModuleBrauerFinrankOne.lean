/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.PermutationModuleBrauerQuotientBasis

/-!
# One-dimensional permutation-module Brauer quotients

The fixed-basis theorem immediately makes the Brauer quotient
one-dimensional when the action has a unique fixed basis index.
-/

noncomputable section

namespace Representation
namespace PermutationModuleBasis

variable {p : ℕ} [Fact p.Prime]
variable {k P V ι : Type}
variable [Field k] [CharP k p]
variable [Group P] [Finite P]
variable [AddCommGroup V] [Module k V]
variable [DistribMulAction P V] [SMulCommClass P k V]
variable [MulAction P ι] [Finite ι]

variable (B : PermutationModuleBasis
  (k := k) (P := P) (V := V) (ι := ι))

noncomputable local instance permutationBrauerFinrankGroupFintype :
    Fintype P :=
  Fintype.ofFinite P

noncomputable local instance permutationBrauerFinrankIndexFintype :
    Fintype ι :=
  Fintype.ofFinite ι

/-- A unique globally fixed basis index forces the Brauer quotient to
have dimension one. -/
theorem finrank_brauerQuotient_eq_one
    (hP : IsPGroup p P)
    [Unique (MulAction.fixedPoints P ι)] :
    Module.finrank k (BrauerQuotient B.representation) = 1 := by
  rw [B.finrank_brauerQuotient_eq_card_fixedPoints hP]
  exact Fintype.card_unique

/-- Pointed form of the preceding result: a specified fixed index and
subsingleton fixed-point type force dimension one. -/
theorem finrank_brauerQuotient_eq_one_of_subsingleton
    (hP : IsPGroup p P)
    (i : MulAction.fixedPoints P ι)
    [Subsingleton (MulAction.fixedPoints P ι)] :
    Module.finrank k (BrauerQuotient B.representation) = 1 := by
  letI : Unique (MulAction.fixedPoints P ι) :=
    { default := i
      uniq := fun j ↦ Subsingleton.elim j i }
  exact B.finrank_brauerQuotient_eq_one hP

end PermutationModuleBasis
end Representation
