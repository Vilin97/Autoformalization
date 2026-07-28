/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeAlgebraBrauerQuotientBasis
import McKayConjecture.Character.EndopermutationNormalizerExtension
import McKayConjecture.CharacterTriple.MagicLinearizationFromFinrankOne

/-!
# Magic linearization from an endopermutation comparison

This file combines the direct endomorphism-Brauer comparison criterion
for a pointed endopermutation module with the one-dimensional
Brauer-quotient criterion.  It isolates the exact two Dade-theoretic
conclusions needed by the magic-representation construction.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

open Representation

variable {p : ℕ} [Fact p.Prime]
variable {K P G V : Type}
variable [Field K] [CharP K p]
variable [Group P] [Fintype P] [Group G]
variable [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Nontrivial V]

/-- A faithful pointed endopermutation module whose direct
endomorphism-Brauer comparison is an isomorphism supplies the
normalizer extension.  If its pointed permutation basis has no second
fixed index, covariance then yields a magic linearization. -/
def magicLinearizationOfEndopermutationComparison
    (Q : ProjectiveRepresentation K G V)
    (M : PointedEndopermutationModule p K P V)
    (φ : G →* MulAut P)
    (hcov : Q.IsCovariantWith M.action φ)
    (operator_one : Q.operator 1 = 1)
    (hfaithful : Function.Injective M.action)
    (hcomparison : M.HasEndomorphismBrauerComparison)
    (hfixed :
      letI :=
        endomorphismConjugationMulSemiringAction M.action
      letI :=
        endomorphismConjugation_smulCommClass M.action
      Subsingleton M.toDadeAlgebra.FixedIndex) :
    MagicLinearization Q := by
  letI :=
    endomorphismConjugationMulSemiringAction M.action
  letI :=
    endomorphismConjugation_smulCommClass M.action
  letI : Subsingleton M.toDadeAlgebra.FixedIndex := hfixed
  let ρ := linearActionRepresentation M.action
  have hρ : Function.Injective ρ :=
    linearActionRepresentation_injective M.action hfaithful
  have haction :
      representationLinearAction ρ = M.action := by
    simp only [ρ,
      representationLinearAction_linearActionRepresentation]
  have hcovρ :
      Q.IsCovariantWith (representationLinearAction ρ) φ := by
    rw [haction]
    exact hcov
  have hfinρ :
      letI :=
        endomorphismConjugationMulSemiringAction
          (representationLinearAction ρ)
      letI :=
        endomorphismConjugation_smulCommClass
          (representationLinearAction ρ)
      Module.finrank K
          (BrauerQuotientAlgebra
            (k := K) (P := P) (A := Module.End K V)) =
        1 := by
    rw [haction]
    exact M.toDadeAlgebra.finrank_brauerQuotientAlgebra_eq_one
  exact
    magicLinearizationOfCovariantNormalizerDataOfFinrankOne
      Q (representationLinearAction ρ) φ hcovρ operator_one
      (brauerNormalizerExtensionOfEndomorphismComparison
        ρ hρ hcomparison)
      hfinρ

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
