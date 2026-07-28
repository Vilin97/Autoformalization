/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveCohomologyMismatch

/-!
# The residual scalar mismatch beyond matched normal-central elements

Let two associated projective lifts have matching factors along a central
restriction.  The scalar mismatch is a linear character of the inverse image
of the left centralizer.  On elements which also lie in the right normal
subgroup, the two projective traces are the values of the two distinguished
normal characters.  Equality of those normalized character values therefore
forces the mismatch to be one.

Consequently the mismatch descends through the quotient by this matched
normal-central subgroup.  After quotient-factor cohomology has been used to
match the factors, this quotient character is the exact remaining scalar
obstruction.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple

variable {A B : Type}
variable [Group A] [Finite A] [Group B] [Finite B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {e : B →* A}

/-- The part of the projective-comparison centralizer lying in the right
normal subgroup.  Under exact central-restriction group data it is the
matched normal-central part. -/
abbrev projectiveComparisonNormalCentralSubgroup
    (T : CharacterTriple A) (U : CharacterTriple B)
    (e : B →* A) :
    Subgroup (projectiveComparisonCentralizer T e) :=
  U.normalSubgroup.comap
    (projectiveComparisonCentralizer T e).subtype

namespace CentralRestrictionGroupData

/-- A matched normal-central element viewed in the right normal subgroup. -/
def comparisonRightNormalElement
    (_g : CentralRestrictionGroupData T U e)
    (b : projectiveComparisonNormalCentralSubgroup T U e) :
    U.normalSubgroup :=
  ⟨(b.1 : B), b.2⟩

/-- A matched normal-central element transported to the left normal
subgroup. -/
def comparisonLeftNormalElement
    (g : CentralRestrictionGroupData T U e)
    (b : projectiveComparisonNormalCentralSubgroup T U e) :
    T.normalSubgroup :=
  ⟨e (b.1 : B), g.rightNormal_le_comap_leftNormal b.2⟩

@[simp]
theorem comparisonRightNormalElement_coe
    (g : CentralRestrictionGroupData T U e)
    (b : projectiveComparisonNormalCentralSubgroup T U e) :
    (g.comparisonRightNormalElement b : B) =
      (b.1 : B) :=
  rfl

@[simp]
theorem comparisonLeftNormalElement_coe
    (g : CentralRestrictionGroupData T U e)
    (b : projectiveComparisonNormalCentralSubgroup T U e) :
    (g.comparisonLeftNormalElement b : A) =
      e (b.1 : B) :=
  rfl

/-- Cross-multiplied equality of the normalized values of the two
distinguished triple characters on every matched normal-central element. -/
def NormalizedNormalCentralValuesAgree
    (g : CentralRestrictionGroupData T U e) : Prop :=
  ∀ b : projectiveComparisonNormalCentralSubgroup T U e,
    T.character.values (g.comparisonLeftNormalElement b) *
        (U.character.degree : ℂ) =
      U.character.values (g.comparisonRightNormalElement b) *
        (T.character.degree : ℂ)

end CentralRestrictionGroupData

end InductiveMcKay

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

/-- Normalized equality of the two triple-character values at one matched
normal-central element forces its scalar mismatch to be one. -/
theorem comparisonCentralScalarMismatch_apply_eq_one_of_normalizedNormalCentralValue
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (factorAgreement :
      ∀ b c : B,
        P.factor (e b) (e c) =
          Q.factor b c)
    (b : projectiveComparisonNormalCentralSubgroup T U e)
    (hvalue :
      T.character.values (g.comparisonLeftNormalElement b) *
          (U.character.degree : ℂ) =
        U.character.values (g.comparisonRightNormalElement b) *
          (T.character.degree : ℂ)) :
    R.comparisonCentralScalarMismatch
        S
        g.projectiveComparisonCentralizer_le_rightCentralizer
        factorAgreement b.1 =
      1 := by
  let x : T.normalSubgroup :=
    g.comparisonLeftNormalElement b
  let y : U.normalSubgroup :=
    g.comparisonRightNormalElement b
  have htrace :
      LinearMap.trace ℂ V
            (P.operator (e (b.1 : B)) : V →ₗ[ℂ] V) *
          (Module.finrank ℂ W : ℂ) =
        LinearMap.trace ℂ W
            (Q.operator (b.1 : B) : W →ₗ[ℂ] W) *
          (Module.finrank ℂ V : ℂ) := by
    change
      P.traceFunction (x : A) *
          (Module.finrank ℂ W : ℂ) =
        Q.traceFunction (y : B) *
          (Module.finrank ℂ V : ℂ)
    rw [R.traceFunction_normal x, S.traceFunction_normal y,
      R.finrank_eq_character_degree,
      S.finrank_eq_character_degree]
    exact hvalue
  obtain ⟨c, hleft, hright⟩ :=
    CompleteCentralProjectiveComparisonData.exists_common_scalar_of_trace_cross
      R S (e (b.1 : B)) (b.1 : B)
      b.1.2
      (g.mem_rightCentralizer_of_embedding_mem_leftCentralizer
        (b.1 : B) b.1.2)
      htrace
  have hleftScalar :
      R.leftComparisonCentralScalar b.1 = c := by
    apply scalarLinearEquiv_injective ℂ V
    exact
      (R.operator_leftComparisonCentralScalar b.1).symm.trans
        hleft
  have hrightScalar :
      S.rightComparisonCentralScalar
          g.projectiveComparisonCentralizer_le_rightCentralizer b.1 =
        c := by
    apply scalarLinearEquiv_injective ℂ W
    exact
      (S.operator_rightComparisonCentralScalar
        g.projectiveComparisonCentralizer_le_rightCentralizer
        b.1).symm.trans hright
  rw [R.comparisonCentralScalarMismatch_apply,
    hleftScalar, hrightScalar]
  simp

/-- Normalized equality on the whole matched normal-central subgroup forces
the mismatch to be one at each of its elements. -/
theorem comparisonCentralScalarMismatch_apply_eq_one_of_normalizedNormalCentralValuesAgree
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (factorAgreement :
      ∀ b c : B,
        P.factor (e b) (e c) =
          Q.factor b c)
    (hvalues : g.NormalizedNormalCentralValuesAgree)
    (b : projectiveComparisonNormalCentralSubgroup T U e) :
    R.comparisonCentralScalarMismatch
        S
        g.projectiveComparisonCentralizer_le_rightCentralizer
        factorAgreement b.1 =
      1 :=
  R.comparisonCentralScalarMismatch_apply_eq_one_of_normalizedNormalCentralValue
    S g factorAgreement b (hvalues b)

/-- The scalar mismatch restricts trivially to the matched normal-central
subgroup. -/
theorem comparisonCentralScalarMismatch_comp_normalCentralSubgroup_eq_one
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (factorAgreement :
      ∀ b c : B,
        P.factor (e b) (e c) =
          Q.factor b c)
    (hvalues : g.NormalizedNormalCentralValuesAgree) :
    (R.comparisonCentralScalarMismatch
        S
        g.projectiveComparisonCentralizer_le_rightCentralizer
        factorAgreement).comp
          (projectiveComparisonNormalCentralSubgroup
            T U e).subtype =
      1 := by
  apply MonoidHom.ext
  intro b
  change
    R.comparisonCentralScalarMismatch
        S
        g.projectiveComparisonCentralizer_le_rightCentralizer
        factorAgreement b.1 =
      (1 : ℂˣ)
  exact
    R.comparisonCentralScalarMismatch_apply_eq_one_of_normalizedNormalCentralValuesAgree
      S g factorAgreement hvalues b

/-- The residual scalar mismatch after quotienting by the matched
normal-central subgroup. -/
def comparisonCentralScalarMismatchQuotient
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (factorAgreement :
      ∀ b c : B,
        P.factor (e b) (e c) =
          Q.factor b c)
    (hvalues : g.NormalizedNormalCentralValuesAgree) :
    (projectiveComparisonCentralizer T e ⧸
        projectiveComparisonNormalCentralSubgroup T U e) →*
      ℂˣ :=
  QuotientGroup.lift
    (projectiveComparisonNormalCentralSubgroup T U e)
    (R.comparisonCentralScalarMismatch
      S
      g.projectiveComparisonCentralizer_le_rightCentralizer
      factorAgreement)
    (by
      intro b hb
      exact
        MonoidHom.mem_ker.mpr
          (R.comparisonCentralScalarMismatch_apply_eq_one_of_normalizedNormalCentralValuesAgree
            S g factorAgreement hvalues ⟨b, hb⟩))

@[simp]
theorem comparisonCentralScalarMismatchQuotient_mk
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (factorAgreement :
      ∀ b c : B,
        P.factor (e b) (e c) =
          Q.factor b c)
    (hvalues : g.NormalizedNormalCentralValuesAgree)
    (b : projectiveComparisonCentralizer T e) :
    R.comparisonCentralScalarMismatchQuotient
        S g factorAgreement hvalues
        (QuotientGroup.mk'
          (projectiveComparisonNormalCentralSubgroup T U e) b) =
      R.comparisonCentralScalarMismatch
        S
        g.projectiveComparisonCentralizer_le_rightCentralizer
        factorAgreement b :=
  rfl

/-- Triviality of the full mismatch is exactly triviality of its residual
quotient character. -/
theorem comparisonCentralScalarMismatchQuotient_eq_one_iff
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (factorAgreement :
      ∀ b c : B,
        P.factor (e b) (e c) =
          Q.factor b c)
    (hvalues : g.NormalizedNormalCentralValuesAgree) :
    R.comparisonCentralScalarMismatchQuotient
          S g factorAgreement hvalues =
        1 ↔
      R.comparisonCentralScalarMismatch
          S
          g.projectiveComparisonCentralizer_le_rightCentralizer
          factorAgreement =
        1 := by
  constructor
  · intro h
    apply MonoidHom.ext
    intro b
    change
      R.comparisonCentralScalarMismatch
          S
          g.projectiveComparisonCentralizer_le_rightCentralizer
          factorAgreement b =
        (1 : ℂˣ)
    have hb :=
      congrArg
        (fun f :
          (projectiveComparisonCentralizer T e ⧸
              projectiveComparisonNormalCentralSubgroup T U e) →*
            ℂˣ ↦
          f
            (QuotientGroup.mk'
              (projectiveComparisonNormalCentralSubgroup T U e) b))
        h
    change
      R.comparisonCentralScalarMismatchQuotient
          S g factorAgreement hvalues
          (QuotientGroup.mk'
            (projectiveComparisonNormalCentralSubgroup T U e) b) =
        (1 : ℂˣ) at hb
    rw [R.comparisonCentralScalarMismatchQuotient_mk
      S g factorAgreement hvalues] at hb
    exact hb
  · intro h
    apply MonoidHom.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H b =>
        change
          R.comparisonCentralScalarMismatchQuotient
              S g factorAgreement hvalues
              (QuotientGroup.mk'
                (projectiveComparisonNormalCentralSubgroup
                  T U e) b) =
            (1 : ℂˣ)
        rw [R.comparisonCentralScalarMismatchQuotient_mk
          S g factorAgreement hvalues]
        exact
          DFunLike.congr_fun h b

/-- The residual quotient character after quotient-factor cohomology has
canonically matched the two factor sets. -/
def postFactorMatchingScalarMismatchQuotient
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (hcoh : R.QuotientFactorCohomologyAgreement S g)
    (hvalues : g.NormalizedNormalCentralValuesAgree) :
    (projectiveComparisonCentralizer T e ⧸
        projectiveComparisonNormalCentralSubgroup T U e) →*
      ℂˣ :=
  R.comparisonCentralScalarMismatchQuotient
    (R.factorMatchedRightAssociated S g hcoh)
    g
    (R.factorMatchedRightAssociated_factor_agreement
      S g hcoh)
    hvalues

/-- The post-factor-matching scalar obstruction is now exactly the residual
quotient character. -/
theorem postFactorMatchingScalarMismatchQuotient_eq_one_iff
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (hcoh : R.QuotientFactorCohomologyAgreement S g)
    (hvalues : g.NormalizedNormalCentralValuesAgree) :
    R.postFactorMatchingScalarMismatchQuotient
          S g hcoh hvalues =
        1 ↔
      R.comparisonCentralScalarMismatch
          (R.factorMatchedRightAssociated S g hcoh)
          g.projectiveComparisonCentralizer_le_rightCentralizer
          (R.factorMatchedRightAssociated_factor_agreement
            S g hcoh) =
        1 :=
  R.comparisonCentralScalarMismatchQuotient_eq_one_iff
    (R.factorMatchedRightAssociated S g hcoh)
    g
    (R.factorMatchedRightAssociated_factor_agreement
      S g hcoh)
    hvalues

end AssociatedProjectiveRepresentation
end CharacterTriple

end McKayConjecture
