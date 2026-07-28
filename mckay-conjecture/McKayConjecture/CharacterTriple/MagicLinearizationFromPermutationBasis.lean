/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.PermutationModuleBrauerNormalizerExtension
import McKayConjecture.CharacterTriple.MagicLinearizationFromFinrankOne

/-!
# Magic linearization from a faithful permutation basis

A faithful permutation representation has the Brauer-normalizer
extension required by the Puig--Turull correction.  When its basis
action has one global fixed point, the endomorphism-algebra Brauer
quotient is one-dimensional.  This file combines those two conclusions
with covariance to produce a magic linearization.

This is the complete elementary permutation-module case of the local
extension argument.  General capped endopermutation modules still
require the Dade-theoretic extension theorem.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

open Representation

variable {p : ℕ} [Fact p.Prime]
variable {K P G V ι : Type}
variable [Field K] [CharP K p]
variable [Group P] [Finite P] [Group G]
variable [AddCommGroup V] [Module K V]
variable [DistribMulAction P V] [SMulCommClass P K V]
variable [MulAction P ι] [Finite ι]

/-- A normalized projective action covariant with a faithful
permutation representation admits a magic linearization when the
permuted basis has one global fixed index. -/
def magicLinearizationOfFaithfulPermutationBasis
    (Q : ProjectiveRepresentation K G V)
    (B : PermutationModuleBasis
      (k := K) (P := P) (V := V) (ι := ι))
    (φ : G →* MulAut P)
    (hcov :
      Q.IsCovariantWith
        (representationLinearAction B.representation) φ)
    (operator_one : Q.operator 1 = 1)
    (hP : IsPGroup p P)
    (hfaithful : Function.Injective B.representation)
    [Unique (MulAction.fixedPoints P ι)] :
    MagicLinearization Q := by
  letI : Fintype P := Fintype.ofFinite P
  exact
    magicLinearizationOfCovariantNormalizerDataOfFinrankOne
      Q (representationLinearAction B.representation) φ hcov
      operator_one
      (B.brauerNormalizerExtensionOfFaithfulPermutationBasis
        hP hfaithful)
      (B.finrank_endomorphismBrauerQuotientAlgebra_eq_one hP)

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
