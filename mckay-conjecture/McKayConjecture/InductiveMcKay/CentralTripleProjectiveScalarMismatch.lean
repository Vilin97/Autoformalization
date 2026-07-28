/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralProjectiveScalarMismatch
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveTraceComparison

/-!
# Central-triple comparisons from a trivial scalar mismatch

After two associated projective lifts have matching factor sets, their
remaining central-isomorphism obstruction is a linear character of the
matched centralizer.  This file specializes the generic scalar-mismatch
construction to `CentralRestrictionGroupData` and supplies a constructor for
`CompleteCentralProjectiveComparisonData`.

Thus a Dade--Glauberman--Nagao input can be split into two independent
claims:

* literal agreement of the two factor sets; and
* triviality of the resulting centralizer mismatch character.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple

variable {A B : Type}
variable [Group A] [Finite A] [Group B] [Finite B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {e : B →* A}

namespace CentralRestrictionGroupData

/-- Exact intersection and injectivity imply that the inverse image of the
left centralizer lies in the right centralizer. -/
theorem projectiveComparisonCentralizer_le_rightCentralizer
    (g : CentralRestrictionGroupData T U e) :
    projectiveComparisonCentralizer T e ≤
      Subgroup.centralizer
        (U.normalSubgroup : Set B) := by
  intro b hb
  exact
    g.mem_rightCentralizer_of_embedding_mem_leftCentralizer
      b hb

end CentralRestrictionGroupData

namespace CompleteCentralProjectiveComparisonData

variable {V W : Type}
variable [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W]
  [Module.Finite ℂ W] [Nontrivial W]
variable {P : ProjectiveRepresentation ℂ A V}
variable {Q : ProjectiveRepresentation ℂ B W}

/-- Construct a complete projective comparison from associated lifts,
literal factor agreement, and triviality of their scalar mismatch
character. -/
def ofAssociatedFactorAgreementMismatchTrivial
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (factorAgreement :
      ∀ b c : B,
        P.factor (e b) (e c) =
          Q.factor b c)
    (mismatch_trivial :
      R.comparisonCentralScalarMismatch S
          g.projectiveComparisonCentralizer_le_rightCentralizer
          factorAgreement =
        1) :
    CompleteCentralProjectiveComparisonData T U e where
  leftSpace := V
  rightSpace := W
  leftProjective := P
  leftAssociated := R
  rightProjective := Q
  rightAssociated := S
  factor_agreement := factorAgreement
  scalar_agreement :=
    (R.scalarAgreement_iff_comparisonCentralScalarMismatch_eq_one
      S g.projectiveComparisonCentralizer_le_rightCentralizer
      factorAgreement).mpr mismatch_trivial

/-- For fixed associated lifts and fixed factor agreement, scalar agreement
is equivalent to triviality of the canonical mismatch character. -/
theorem scalarAgreement_iff_mismatchTrivial
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (factorAgreement :
      ∀ b c : B,
        P.factor (e b) (e c) =
          Q.factor b c) :
    (∀ b : B,
        e b ∈
            Subgroup.centralizer
              (T.normalSubgroup : Set A) →
          ∃ c : ℂˣ,
            P.operator (e b) =
                scalarLinearEquiv ℂ V c ∧
              Q.operator b =
                scalarLinearEquiv ℂ W c) ↔
      R.comparisonCentralScalarMismatch S
          g.projectiveComparisonCentralizer_le_rightCentralizer
          factorAgreement =
        1 :=
  R.scalarAgreement_iff_comparisonCentralScalarMismatch_eq_one
    S g.projectiveComparisonCentralizer_le_rightCentralizer
    factorAgreement

end CompleteCentralProjectiveComparisonData

/-- Associated projective lifts with matching factors, with their remaining
centralizer obstruction recorded as triviality of the scalar-mismatch
character.

This is equivalent to `CompleteCentralProjectiveComparisonData` once the
ordinary restriction-group data is fixed, but exposes the two DGN claims as
separate fields. -/
structure FactorMatchedAssociatedProjectiveComparisonData
    (T : CharacterTriple A) (U : CharacterTriple B)
    (e : B →* A)
    (g : CentralRestrictionGroupData T U e) where
  leftSpace : Type
  rightSpace : Type
  [leftAddCommGroup : AddCommGroup leftSpace]
  [leftModule : Module ℂ leftSpace]
  [leftModuleFinite : Module.Finite ℂ leftSpace]
  [leftNontrivial : Nontrivial leftSpace]
  [rightAddCommGroup : AddCommGroup rightSpace]
  [rightModule : Module ℂ rightSpace]
  [rightModuleFinite : Module.Finite ℂ rightSpace]
  [rightNontrivial : Nontrivial rightSpace]
  leftProjective :
    ProjectiveRepresentation ℂ A leftSpace
  leftAssociated :
    AssociatedProjectiveRepresentation
      T leftSpace leftProjective
  rightProjective :
    ProjectiveRepresentation ℂ B rightSpace
  rightAssociated :
    AssociatedProjectiveRepresentation
      U rightSpace rightProjective
  factor_agreement :
    ∀ b c : B,
      leftProjective.factor (e b) (e c) =
        rightProjective.factor b c
  mismatch_trivial :
    leftAssociated.comparisonCentralScalarMismatch
        rightAssociated
        g.projectiveComparisonCentralizer_le_rightCentralizer
        factor_agreement =
      1

namespace FactorMatchedAssociatedProjectiveComparisonData

/-- Forget the obstruction-theoretic presentation and obtain the standard
complete projective-comparison package. -/
def toCompleteCentralProjectiveComparisonData
    (d :
      FactorMatchedAssociatedProjectiveComparisonData
        T U e g) :
    CompleteCentralProjectiveComparisonData T U e := by
  letI := d.leftAddCommGroup
  letI := d.leftModule
  letI := d.leftModuleFinite
  letI := d.leftNontrivial
  letI := d.rightAddCommGroup
  letI := d.rightModule
  letI := d.rightModuleFinite
  letI := d.rightNontrivial
  exact
    CompleteCentralProjectiveComparisonData.ofAssociatedFactorAgreementMismatchTrivial
      d.leftAssociated d.rightAssociated g
      d.factor_agreement d.mismatch_trivial

/-- Every complete comparison has trivial scalar mismatch.  Hence the
mismatch presentation loses no information. -/
def ofCompleteCentralProjectiveComparisonData
    (d : CompleteCentralProjectiveComparisonData T U e)
    (g : CentralRestrictionGroupData T U e) :
    FactorMatchedAssociatedProjectiveComparisonData
      T U e g := by
  letI := d.leftAddCommGroup
  letI := d.leftModule
  letI := d.leftModuleFinite
  letI := d.leftNontrivial
  letI := d.rightAddCommGroup
  letI := d.rightModule
  letI := d.rightModuleFinite
  letI := d.rightNontrivial
  refine
    { leftSpace := d.leftSpace
      rightSpace := d.rightSpace
      leftProjective := d.leftProjective
      leftAssociated := d.leftAssociated
      rightProjective := d.rightProjective
      rightAssociated := d.rightAssociated
      factor_agreement := d.factor_agreement
      mismatch_trivial := ?_ }
  exact
    (d.leftAssociated
      |>.scalarAgreement_iff_comparisonCentralScalarMismatch_eq_one
        d.rightAssociated
        g.projectiveComparisonCentralizer_le_rightCentralizer
        d.factor_agreement).mp d.scalar_agreement

end FactorMatchedAssociatedProjectiveComparisonData

end InductiveMcKay
end McKayConjecture
