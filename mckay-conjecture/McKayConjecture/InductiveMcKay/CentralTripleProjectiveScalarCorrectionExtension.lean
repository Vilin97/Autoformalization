/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.ComplexLinearCharacterExtension
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveNormalCentralMismatch
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveScalarCorrection
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Extending the projective scalar correction

Normalized equality on the matched normal-central subgroup makes the
factor-matched scalar mismatch trivial on the kernel of the map from the
comparison centralizer to the right outer quotient.  If that quotient is
abelian, injectivity of the divisible group `ℂˣ` extends the mismatch to the
whole right group.  Its pullback is automatically trivial on the
distinguished normal subgroup and is therefore the correction character
required by `H2ScalarCorrectableProjectiveComparisonData`.

The cyclic-quotient result is included as a direct corollary.
-/

noncomputable section

open scoped IsMulCommutative

namespace McKayConjecture

namespace CharacterTriple
namespace AssociatedProjectiveRepresentation

open InductiveMcKay

variable {A B : Type}
variable [Group A] [Finite A] [Group B] [Finite B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {e : B →* A}
variable {V W : Type}
variable [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W]
  [Module.Finite ℂ W] [Nontrivial W]
variable {P : ProjectiveRepresentation ℂ A V}
variable {Q : ProjectiveRepresentation ℂ B W}

/-- The exact kernel condition for extending the scalar mismatch to an
ambient character which is trivial on the right normal subgroup.

The extra commutator subgroup is forced: every homomorphism from `B` to
`ℂˣ` kills it. -/
def ComparisonCentralScalarCorrectionKernelCondition
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (factorAgreement :
      ∀ b c : B,
        P.factor (e b) (e c) =
          Q.factor b c) : Prop :=
  ((U.normalSubgroup ⊔ _root_.commutator B).comap
      (projectiveComparisonCentralizer T e).subtype) ≤
    (R.comparisonCentralScalarMismatch
      S
      g.projectiveComparisonCentralizer_le_rightCentralizer
      factorAgreement).ker

/-- The sharp kernel condition constructs the ambient scalar correction.

The proof passes to `B / (U.normalSubgroup ⊔ commutator B)`, extends the
induced subgroup character there, and pulls it back to `B`. -/
theorem exists_comparisonCentralScalarCorrection_of_kernelCondition
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (factorAgreement :
      ∀ b c : B,
        P.factor (e b) (e c) =
          Q.factor b c)
    (hkernel :
      R.ComparisonCentralScalarCorrectionKernelCondition
        S g factorAgreement) :
    ∃ χ : B →* ℂˣ,
      (∀ x : U.normalSubgroup, χ (x : B) = 1) ∧
      ∀ b : projectiveComparisonCentralizer T e,
        χ b =
          R.comparisonCentralScalarMismatch
            S
            g.projectiveComparisonCentralizer_le_rightCentralizer
            factorAgreement b := by
  let correctionKernel : Subgroup B :=
    U.normalSubgroup ⊔ _root_.commutator B
  letI : correctionKernel.Normal :=
    inferInstance
  letI : IsMulCommutative (B ⧸ correctionKernel) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
      (show _root_.commutator B ≤ correctionKernel from
        le_sup_right)
  let q : B →* B ⧸ correctionKernel :=
    QuotientGroup.mk' correctionKernel
  let inclusion :
      projectiveComparisonCentralizer T e →* B :=
    (projectiveComparisonCentralizer T e).subtype
  let mismatch :
      projectiveComparisonCentralizer T e →* ℂˣ :=
    R.comparisonCentralScalarMismatch
      S
      g.projectiveComparisonCentralizer_le_rightCentralizer
      factorAgreement
  have hker :
      (q.comp inclusion).ker ≤ mismatch.ker := by
    intro b hb
    apply hkernel
    change (b : B) ∈ correctionKernel
    exact
      (QuotientGroup.eq_one_iff (b : B)).mp
        (MonoidHom.mem_ker.mp hb)
  obtain ⟨χ, hχker, hχrestrict⟩ :=
    GroupTheory.exists_complexLinearCharacter_extension_trivial_on_ker
      inclusion q mismatch hker
  refine ⟨χ, ?_, ?_⟩
  · intro x
    have hxCorrectionKernel :
        (x : B) ∈ correctionKernel :=
      Subgroup.mem_sup_left x.property
    simpa only using
      hχker
        ⟨(x : B), MonoidHom.mem_ker.mpr
          ((QuotientGroup.eq_one_iff (x : B)).mpr
            hxCorrectionKernel)⟩
  · intro b
    exact DFunLike.congr_fun hχrestrict b

/-- The intersection-with-normal-and-commutator condition is not only
sufficient but necessary for an ambient normal-trivial correction. -/
theorem exists_comparisonCentralScalarCorrection_iff_kernelCondition
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (factorAgreement :
      ∀ b c : B,
        P.factor (e b) (e c) =
          Q.factor b c) :
    (∃ χ : B →* ℂˣ,
        (∀ x : U.normalSubgroup, χ (x : B) = 1) ∧
        ∀ b : projectiveComparisonCentralizer T e,
          χ b =
            R.comparisonCentralScalarMismatch
              S
              g.projectiveComparisonCentralizer_le_rightCentralizer
              factorAgreement b) ↔
      R.ComparisonCentralScalarCorrectionKernelCondition
        S g factorAgreement := by
  constructor
  · rintro ⟨χ, hχnormal, hχrestrict⟩
    have hnormal : U.normalSubgroup ≤ χ.ker := by
      intro x hx
      exact
        MonoidHom.mem_ker.mpr
          (hχnormal ⟨x, hx⟩)
    have hcommutator :
        _root_.commutator B ≤ χ.ker :=
      Abelianization.commutator_subset_ker χ
    intro b hb
    apply MonoidHom.mem_ker.mpr
    rw [← hχrestrict b]
    exact
      MonoidHom.mem_ker.mp
        (sup_le hnormal hcommutator hb)
  · exact
      R.exists_comparisonCentralScalarCorrection_of_kernelCondition
        S g factorAgreement

/-- If the right outer quotient is abelian, equality of normalized values
on the matched normal-central subgroup supplies an ambient scalar
correction. -/
theorem exists_comparisonCentralScalarCorrection_of_commutator_le_normal
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (factorAgreement :
      ∀ b c : B,
        P.factor (e b) (e c) =
          Q.factor b c)
    (hvalues : g.NormalizedNormalCentralValuesAgree)
    (hcommutator :
      _root_.commutator B ≤ U.normalSubgroup) :
    ∃ χ : B →* ℂˣ,
      (∀ x : U.normalSubgroup, χ (x : B) = 1) ∧
      ∀ b : projectiveComparisonCentralizer T e,
        χ b =
          R.comparisonCentralScalarMismatch
            S
            g.projectiveComparisonCentralizer_le_rightCentralizer
            factorAgreement b := by
  letI : IsMulCommutative (B ⧸ U.normalSubgroup) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
      hcommutator
  let q : B →* B ⧸ U.normalSubgroup :=
    QuotientGroup.mk' U.normalSubgroup
  let inclusion :
      projectiveComparisonCentralizer T e →* B :=
    (projectiveComparisonCentralizer T e).subtype
  let mismatch :
      projectiveComparisonCentralizer T e →* ℂˣ :=
    R.comparisonCentralScalarMismatch
      S
      g.projectiveComparisonCentralizer_le_rightCentralizer
      factorAgreement
  have hker :
      (q.comp inclusion).ker ≤ mismatch.ker := by
    intro b hb
    have hbNormal :
        (b : B) ∈ U.normalSubgroup := by
      exact
        (QuotientGroup.eq_one_iff (b : B)).mp
          (MonoidHom.mem_ker.mp hb)
    apply MonoidHom.mem_ker.mpr
    exact
      R.comparisonCentralScalarMismatch_apply_eq_one_of_normalizedNormalCentralValuesAgree
        S g factorAgreement hvalues
        ⟨b, hbNormal⟩
  obtain ⟨χ, hχker, hχrestrict⟩ :=
    GroupTheory.exists_complexLinearCharacter_extension_trivial_on_ker
      inclusion q mismatch hker
  refine ⟨χ, ?_, ?_⟩
  · intro x
    simpa only using
      hχker
        ⟨(x : B), MonoidHom.mem_ker.mpr
          ((QuotientGroup.eq_one_iff (x : B)).mpr
            x.property)⟩
  · intro b
    exact DFunLike.congr_fun hχrestrict b

/-- A cyclic right outer quotient is abelian, so the same extension
construction applies. -/
theorem exists_comparisonCentralScalarCorrection_of_isCyclic_quotient
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (factorAgreement :
      ∀ b c : B,
        P.factor (e b) (e c) =
          Q.factor b c)
    (hvalues : g.NormalizedNormalCentralValuesAgree)
    (hcyclic : IsCyclic (B ⧸ U.normalSubgroup)) :
    ∃ χ : B →* ℂˣ,
      (∀ x : U.normalSubgroup, χ (x : B) = 1) ∧
      ∀ b : projectiveComparisonCentralizer T e,
        χ b =
          R.comparisonCentralScalarMismatch
            S
            g.projectiveComparisonCentralizer_le_rightCentralizer
            factorAgreement b := by
  letI : IsCyclic (B ⧸ U.normalSubgroup) :=
    hcyclic
  apply
    R.exists_comparisonCentralScalarCorrection_of_commutator_le_normal
      S g factorAgreement hvalues
  exact
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      (inferInstance : IsMulCommutative
        (B ⧸ U.normalSubgroup))

end AssociatedProjectiveRepresentation
end CharacterTriple

namespace InductiveMcKay

open CharacterTriple

variable {A B : Type}
variable [Group A] [Finite A] [Group B] [Finite B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {e : B →* A}

namespace H2ScalarCorrectableProjectiveComparisonData

variable {V W : Type}
variable [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W]
  [Module.Finite ℂ W] [Nontrivial W]
variable {P : ProjectiveRepresentation ℂ A V}
variable {Q : ProjectiveRepresentation ℂ B W}

/-- The sharp scalar-correction criterion after the quotient factor classes
have been matched in `H²`. -/
def KernelCondition
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (hH2 : R.QuotientFactorH2ClassAgreement S g) : Prop :=
  let factorAgreement :=
    R.quotientFactorCohomologyAgreement_of_h2Class
      S g hH2
  let factorMatchedRight :=
    R.factorMatchedRightAssociated
      S g factorAgreement
  R.ComparisonCentralScalarCorrectionKernelCondition
    factorMatchedRight g
    (R.factorMatchedRightAssociated_factor_agreement
      S g factorAgreement)

/-- `H²` agreement and the sharp intersection-with-commutator kernel
condition automatically construct the scalar-correctable comparison
package. -/
def ofAssociatedOfKernelCondition
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (hH2 : R.QuotientFactorH2ClassAgreement S g)
    (hkernel : KernelCondition R S g hH2) :
    H2ScalarCorrectableProjectiveComparisonData
      T U e g := by
  let factorAgreement :=
    R.quotientFactorCohomologyAgreement_of_h2Class
      S g hH2
  let factorMatchedRight :=
    R.factorMatchedRightAssociated
      S g factorAgreement
  let literalFactorAgreement :=
    R.factorMatchedRightAssociated_factor_agreement
      S g factorAgreement
  have hkernelLiteral :
      R.ComparisonCentralScalarCorrectionKernelCondition
        factorMatchedRight g literalFactorAgreement := by
    exact hkernel
  let correctionExists :=
    R.exists_comparisonCentralScalarCorrection_of_kernelCondition
      factorMatchedRight g literalFactorAgreement
      hkernelLiteral
  let χ := Classical.choose correctionExists
  let hχnormal := (Classical.choose_spec correctionExists).1
  let hχrestrict := (Classical.choose_spec correctionExists).2
  exact
    { leftSpace := V
      rightSpace := W
      leftProjective := P
      leftAssociated := R
      rightProjective := Q
      rightAssociated := S
      quotientFactorH2ClassAgreement := hH2
      scalarCorrection := χ
      scalarCorrection_normal := hχnormal
      scalarCorrection_restrict := by
        simpa only using hχrestrict }

/-- `H²` agreement, normalized normal-central values, and an abelian right
outer quotient automatically construct the scalar-correctable comparison
package. -/
def ofAssociatedOfNormalizedValuesOfCommutatorLeNormal
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (hH2 : R.QuotientFactorH2ClassAgreement S g)
    (hvalues : g.NormalizedNormalCentralValuesAgree)
    (hcommutator :
      _root_.commutator B ≤ U.normalSubgroup) :
    H2ScalarCorrectableProjectiveComparisonData
      T U e g := by
  let factorAgreement :=
    R.quotientFactorCohomologyAgreement_of_h2Class
      S g hH2
  let factorMatchedRight :=
    R.factorMatchedRightAssociated
      S g factorAgreement
  let literalFactorAgreement :=
    R.factorMatchedRightAssociated_factor_agreement
      S g factorAgreement
  let correctionExists :=
    R.exists_comparisonCentralScalarCorrection_of_commutator_le_normal
      factorMatchedRight g literalFactorAgreement
      hvalues hcommutator
  let χ := Classical.choose correctionExists
  let hχnormal := (Classical.choose_spec correctionExists).1
  let hχrestrict := (Classical.choose_spec correctionExists).2
  exact
    { leftSpace := V
      rightSpace := W
      leftProjective := P
      leftAssociated := R
      rightProjective := Q
      rightAssociated := S
      quotientFactorH2ClassAgreement := hH2
      scalarCorrection := χ
      scalarCorrection_normal := hχnormal
      scalarCorrection_restrict := by
        simpa only using hχrestrict }

/-- Cyclic right outer quotient specialization of the automatic
scalar-correction constructor. -/
def ofAssociatedOfNormalizedValuesOfIsCyclicQuotient
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (hH2 : R.QuotientFactorH2ClassAgreement S g)
    (hvalues : g.NormalizedNormalCentralValuesAgree)
    (hcyclic : IsCyclic (B ⧸ U.normalSubgroup)) :
    H2ScalarCorrectableProjectiveComparisonData
      T U e g := by
  letI : IsCyclic (B ⧸ U.normalSubgroup) :=
    hcyclic
  apply
    ofAssociatedOfNormalizedValuesOfCommutatorLeNormal
      R S g hH2 hvalues
  exact
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      (inferInstance : IsMulCommutative
        (B ⧸ U.normalSubgroup))

end H2ScalarCorrectableProjectiveComparisonData

end InductiveMcKay
end McKayConjecture
