/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedFiniteFactorCentralExtensionCharacter
import McKayConjecture.Character.ExtensionLinearTwist
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveFactorCohomology
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveObstructionClass
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveScalarCorrectionExtension
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveScalarMismatch
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveTraceComparison

/-!
# Central-triple comparison from a lifted factor-extension correspondence

Fix ordinary central-restriction data from `(A, N, theta)` to
`(B, M, phi)`, an associated projective lift on `A`, and one fixed finite
normalization of that lift.  The finite factor set defines:

* an honest irreducible character on its central extension over `A`; and
* by literal pullback along `B → A`, a central extension over `B`.

This file isolates the exact character-theoretic property needed from a
Dade--Glauberman--Nagao correspondence on those extensions.  Its image of
the source extension character must

1. have the same defining action on the coefficient subgroup;
2. restrict along the canonical lifted copy of `M` to `phi`; and
3. preserve normalized values at the matched centralizer base lifts.

These are properties of an ordinary irreducible character, not a disguised
restatement of projective comparison data.  From them, the base-lift
operators give a right associated projective representation whose factor is
literally the pullback of the left factor.  The normalized-value condition
then kills the scalar mismatch.  In particular, intrinsic `H²` agreement
and the complete central projective comparison are both consequences.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple
open CharacterTriple.AssociatedProjectiveRepresentation
open IrreducibleCharacter.Representation

variable {A B : Type}
variable [Group A] [Finite A] [Group B] [Finite B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {e : B →* A}
variable {V : Type}
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}

namespace LiftedFactorCorrespondence

variable
  (R : AssociatedProjectiveRepresentation T V P)
  (F : R.AssociatedFiniteFactorNormalization)
  (g : CentralRestrictionGroupData T U e)

/-- The fixed finite factor set pulled back literally along the central
restriction embedding. -/
def targetFactorSet :
    FactorSet B
      (rootsOfUnity (associatedFactorExponent T V) ℂ) :=
  let _ := g
  F.factorSet.comap e

/-- The pulled-back factor set is normalized. -/
theorem targetFactorSet_isNormalized :
    (targetFactorSet R F g).IsNormalized :=
  FactorSet.comap_isNormalized
    F.factorSet e (F.factorSet_isNormalized R)

/-- The concrete factor extension on the right ambient group. -/
abbrev TargetFactorCentralExtensionGroup :=
  FactorSet.CentralExtensionGroup
    (targetFactorSet R F g)
    (targetFactorSet_isNormalized R F g)

/-- The source factor extension attached to the fixed finite normalization. -/
abbrev SourceFactorCentralExtensionGroup :=
  let _ := g
  F.AmbientFactorCentralExtensionGroup R

/-- The honest irreducible source character afforded by the associated
finite-factor lift. -/
abbrev sourceCharacter :
    IrreducibleCharacter
      (SourceFactorCentralExtensionGroup R F g) :=
  F.ambientFactorCentralExtensionCharacter R

/-- The defining coefficient homomorphism for both factor extensions. -/
abbrev coefficientHom :
    rootsOfUnity (associatedFactorExponent T V) ℂ →* ℂˣ :=
  let _ := R
  let _ := F
  let _ := g
  (rootsOfUnity (associatedFactorExponent T V) ℂ).subtype

/-- The embedding sends a right normal element into the left normal
subgroup. -/
theorem embedding_normal_mem
    (g : CentralRestrictionGroupData T U e)
    (x : U.normalSubgroup) :
    e (x : B) ∈ T.normalSubgroup :=
  CentralRestrictionGroupData.rightNormal_le_comap_leftNormal
    g x.property

/-- The pulled-back finite factor is one when its first argument is in the
right normal subgroup. -/
theorem targetFactorSet_normal_left
    (x : U.normalSubgroup) (b : B) :
    targetFactorSet R F g (x : B) b = 1 := by
  apply Subtype.ext
  change
    ((F.factorSet (e (x : B)) (e b) :
      rootsOfUnity (associatedFactorExponent T V) ℂ) : ℂˣ) = 1
  rw [F.factorSet_coe]
  exact
    F.associated.factor_normal_left
      ⟨e (x : B), embedding_normal_mem g x⟩
      (e b)

/-- The pulled-back finite factor is one when its second argument is in the
right normal subgroup. -/
theorem targetFactorSet_normal_right
    (b : B) (x : U.normalSubgroup) :
    targetFactorSet R F g b (x : B) = 1 := by
  apply Subtype.ext
  change
    ((F.factorSet (e b) (e (x : B)) :
      rootsOfUnity (associatedFactorExponent T V) ℂ) : ℂˣ) = 1
  rw [F.factorSet_coe]
  exact
    F.associated.factor_normal_right
      (e b)
      ⟨e (x : B), embedding_normal_mem g x⟩

/-- The canonical lifted copy `(m, 1)` of the right normal subgroup in the
pulled-back factor extension. -/
def targetNormalLift :
    U.normalSubgroup →*
      TargetFactorCentralExtensionGroup R F g where
  toFun x :=
    FactorSet.CentralExtensionGroup.baseLift
      (targetFactorSet R F g)
      (targetFactorSet_isNormalized R F g)
      (x : B)
  map_one' := by
    apply FactorSet.CentralExtensionGroup.ext
    · rfl
    · rfl
  map_mul' x y := by
    apply FactorSet.CentralExtensionGroup.ext
    · rfl
    · simp [FactorSet.CentralExtensionGroup.baseLift,
        targetFactorSet_normal_left R F g x (y : B)]

@[simp]
theorem targetNormalLift_apply
    (x : U.normalSubgroup) :
    targetNormalLift R F g x =
      FactorSet.CentralExtensionGroup.baseLift
        (targetFactorSet R F g)
        (targetFactorSet_isNormalized R F g)
        (x : B) :=
  rfl

/-- Extract the right projective representation from a target extension
character with the defining coefficient action. -/
abbrev targetProjective
    (psi :
      IrreducibleCharacter
        (TargetFactorCentralExtensionGroup R F g))
    (hcoeff :
      FactorSet.CentralExtensionGroup.HasCoefficientCharacter
        (targetFactorSet R F g)
        (targetFactorSet_isNormalized R F g)
        (coefficientHom R F g) psi) :
    ProjectiveRepresentation ℂ B psi.realization :=
  FactorSet.CentralExtensionGroup.projectiveOfCoefficientCharacter
    (targetFactorSet R F g)
    (targetFactorSet_isNormalized R F g)
    (coefficientHom R F g) psi hcoeff

/-- The extracted factor is literally the restriction of the fixed left
factor; no gauge change or cohomology choice remains. -/
theorem targetProjective_factor_agreement
    (psi :
      IrreducibleCharacter
        (TargetFactorCentralExtensionGroup R F g))
    (hcoeff :
      FactorSet.CentralExtensionGroup.HasCoefficientCharacter
        (targetFactorSet R F g)
        (targetFactorSet_isNormalized R F g)
        (coefficientHom R F g) psi)
    (b c : B) :
    F.projective.factor (e b) (e c) =
      (targetProjective R F g psi hcoeff).factor b c := by
  change
    F.projective.factor (e b) (e c) =
      ((F.factorSet (e b) (e c) :
        rootsOfUnity (associatedFactorExponent T V) ℂ) : ℂˣ)
  exact (F.factorSet_coe (e b) (e c)).symm

/-- The extracted right projective lift is associated with `U` as soon as
the target extension character restricts to `U.character` along the
canonical lifted normal subgroup. -/
def targetAssociated
    (psi :
      IrreducibleCharacter
        (TargetFactorCentralExtensionGroup R F g))
    (hcoeff :
      FactorSet.CentralExtensionGroup.HasCoefficientCharacter
        (targetFactorSet R F g)
        (targetFactorSet_isNormalized R F g)
        (coefficientHom R F g) psi)
    (hextension :
      IrreducibleCharacter.IsExtensionAlong
        (targetNormalLift R F g) U.character psi) :
    AssociatedProjectiveRepresentation
      U psi.realization
      (targetProjective R F g psi hcoeff) := by
  let rhoU : Representation ℂ U.normalSubgroup U.character.realization :=
    U.character.realization.ρ
  let res : Representation ℂ U.normalSubgroup psi.realization :=
    psi.realization.ρ.comp (targetNormalLift R F g)
  letI : Representation.IsIrreducible rhoU :=
    CliffordRestriction.isIrreducible_of_simple
      U.character.realization
  have hchar : res.character = rhoU.character := by
    funext x
    calc
      res.character x =
          psi.realization.character
            (targetNormalLift R F g x) := rfl
      _ = psi.values (targetNormalLift R F g x) :=
        congrFun psi.realization_character
          (targetNormalLift R F g x)
      _ = U.character.values x :=
        hextension x
      _ = U.character.realization.character x :=
        (congrFun U.character.realization_character x).symm
      _ = rhoU.character x := rfl
  let Phi :=
    Classical.choice
      (nonempty_equiv_of_character_eq_irreducible
        rhoU res hchar)
  letI : Representation.IsIrreducible res :=
    McKayConjecture.IrreducibleCharacter.Representation.IsIrreducible.of_equiv
      Phi
  refine
    { restriction :=
        (IrreducibleCharacter.extensionRealizationAction
          (ψ := psi)).comp (targetNormalLift R F g)
      restriction_apply := fun _ ↦ rfl
      restriction_simple := ?_
      restriction_character := ?_
      normal_mul := ?_
      mul_normal := ?_ }
  · change Simple (FDRep.of res)
    exact
      RepresentationTheory.simple_fdRep_of_isIrreducible res
  · funext x
    change
      psi.realization.character (targetNormalLift R F g x) =
        U.character.values x
    rw [psi.realization_character]
    exact hextension x
  · intro x b
    have hmul :=
      (targetProjective R F g psi hcoeff).map_mul
        (x : B) b
    simpa only
      [FactorSet.CentralExtensionGroup.projectiveOfCoefficientCharacter_factor,
        targetFactorSet_normal_left R F g x b,
        map_one, one_mul] using hmul.symm
  · intro b x
    have hmul :=
      (targetProjective R F g psi hcoeff).map_mul
        b (x : B)
    simpa only
      [FactorSet.CentralExtensionGroup.projectiveOfCoefficientCharacter_factor,
        targetFactorSet_normal_right R F g b x,
        map_one, one_mul] using hmul.symm

/-- The exact character-theoretic output required at the fixed source
character from a lifted DGN correspondence.

The last field is a cross-multiplied normalized-value equality, so it makes
sense even when the source and target character degrees differ. -/
structure ImageData where
  /-- The image irreducible character on the pulled-back factor extension. -/
  targetCharacter :
    IrreducibleCharacter
      (TargetFactorCentralExtensionGroup R F g)
  /-- The coefficient subgroup retains the defining scalar character. -/
  coefficientCharacter :
    FactorSet.CentralExtensionGroup.HasCoefficientCharacter
      (targetFactorSet R F g)
      (targetFactorSet_isNormalized R F g)
      (coefficientHom R F g)
      targetCharacter
  /-- The image restricts to the desired right normal character. -/
  extendsTargetNormalCharacter :
    IrreducibleCharacter.IsExtensionAlong
      (targetNormalLift R F g)
      U.character targetCharacter
  /-- Normalized values agree on base lifts above the matched
  centralizer. -/
  normalizedBaseLiftValues :
    ∀ b : B,
      e b ∈
          Subgroup.centralizer
            (T.normalSubgroup : Set A) →
        (sourceCharacter R F g).values
              (FactorSet.CentralExtensionGroup.baseLift
                F.factorSet (F.factorSet_isNormalized R) (e b)) *
            (targetCharacter.degree : ℂ) =
          targetCharacter.values
              (FactorSet.CentralExtensionGroup.baseLift
                (targetFactorSet R F g)
                (targetFactorSet_isNormalized R F g) b) *
            ((sourceCharacter R F g).degree : ℂ)

namespace ImageData

/-- The extracted right lift coming from the image character. -/
abbrev rightProjective
    (d : ImageData R F g) :
    ProjectiveRepresentation ℂ B d.targetCharacter.realization :=
  targetProjective R F g
    d.targetCharacter d.coefficientCharacter

/-- Association of the extracted right lift to the right character triple. -/
abbrev rightAssociated
    (d : ImageData R F g) :
    AssociatedProjectiveRepresentation
      U d.targetCharacter.realization d.rightProjective :=
  targetAssociated R F g
    d.targetCharacter d.coefficientCharacter
    d.extendsTargetNormalCharacter

/-- The lifted-character property gives exact factor agreement. -/
theorem factor_agreement
    (d : ImageData R F g)
    (b c : B) :
    F.projective.factor (e b) (e c) =
      d.rightProjective.factor b c :=
  targetProjective_factor_agreement
    R F g d.targetCharacter d.coefficientCharacter b c

/-- The normalized base-lift value condition is exactly the normalized
projective trace condition. -/
theorem trace_cross
    (d : ImageData R F g)
    (b : B)
    (hb :
      e b ∈
        Subgroup.centralizer
          (T.normalSubgroup : Set A)) :
    LinearMap.trace ℂ V
          (F.projective.operator (e b) : V →ₗ[ℂ] V) *
        (Module.finrank ℂ d.targetCharacter.realization : ℂ) =
      LinearMap.trace ℂ d.targetCharacter.realization
          (d.rightProjective.operator b :
            d.targetCharacter.realization →ₗ[ℂ]
              d.targetCharacter.realization) *
        (Module.finrank ℂ V : ℂ) := by
  have h := d.normalizedBaseLiftValues b hb
  rw [F.ambientFactorCentralExtensionCharacter_values_baseLift R,
    FactorSet.CentralExtensionGroup.values_baseLift_eq_projective_trace
      (targetFactorSet R F g)
      (targetFactorSet_isNormalized R F g)
      (coefficientHom R F g)
      d.targetCharacter d.coefficientCharacter,
    F.ambientFactorCentralExtensionCharacter_degree R,
    ← d.targetCharacter.realization_finrank] at h
  exact h

/-- A lifted DGN image with the three explicit character properties yields
the complete projective comparison. -/
def toCompleteCentralProjectiveComparisonData
    (d : ImageData R F g) :
    CompleteCentralProjectiveComparisonData T U e :=
  CompleteCentralProjectiveComparisonData.ofAssociatedFactorAgreementTraceCross
    F.associated d.rightAssociated g
    d.factor_agreement d.trace_cross

/-- The two associated quotient factor sets agree literally. -/
theorem quotientFactorSet_eq
    (d : ImageData R F g) :
    d.rightAssociated.quotientFactorSet =
      F.associated.quotientFactorSetAlong g := by
  apply FactorSet.ext
  intro q r
  induction q using QuotientGroup.induction_on with
  | H b =>
      induction r using QuotientGroup.induction_on with
      | H c =>
          calc
            d.rightAssociated.quotientFactorSet
                  (QuotientGroup.mk' U.normalSubgroup b)
                  (QuotientGroup.mk' U.normalSubgroup c) =
                d.rightProjective.factor b c :=
              d.rightAssociated.quotientFactorSet_mk b c
            _ =
                F.projective.factor (e b) (e c) :=
              (ImageData.factor_agreement R F g d b c).symm
            _ =
                F.associated.quotientFactorSetAlong g
                  (QuotientGroup.mk' U.normalSubgroup b)
                  (QuotientGroup.mk' U.normalSubgroup c) :=
              (F.associated.quotientFactorSetAlong_mk
                g b c).symm

/-- Literal quotient-factor equality gives gauge/cohomology agreement with
the constant-one gauge. -/
theorem quotientFactorCohomologyAgreement
    (d : ImageData R F g) :
    F.associated.QuotientFactorCohomologyAgreement
      d.rightAssociated g := by
  refine ⟨fun _ ↦ 1, ?_⟩
  rw [FactorSet.gauge_one]
  exact (d.quotientFactorSet_eq R F g).symm

/-- The lifted factor-extension construction gives the `H²` equality used
by the existing scalar-correction interface. -/
theorem quotientFactorH2ClassAgreement
    (d : ImageData R F g) :
    F.associated.QuotientFactorH2ClassAgreement
      d.rightAssociated g :=
  (F.associated
    |>.quotientFactorCohomologyAgreement_iff_h2Class
      d.rightAssociated g).mp
    (d.quotientFactorCohomologyAgreement R F g)

/-- The factor part of the lifted construction implies the intrinsic
projective-obstruction agreement of the two triples. -/
theorem projectiveObstructionClassAgreement
    (d : ImageData R F g) :
    g.ProjectiveObstructionClassAgreement := by
  exact
    (F.associated
      |>.quotientFactorH2ClassAgreement_iff_projectiveObstructionClass
        d.rightAssociated g).mp
      (d.quotientFactorH2ClassAgreement R F g)

/-- The scalar mismatch character of the extracted factor-matched lifts is
trivial. -/
theorem comparisonCentralScalarMismatch_eq_one
    (d : ImageData R F g) :
    F.associated.comparisonCentralScalarMismatch
        d.rightAssociated
        g.projectiveComparisonCentralizer_le_rightCentralizer
        d.factor_agreement =
      1 := by
  exact
    (F.associated
      |>.scalarAgreement_iff_comparisonCentralScalarMismatch_eq_one
        d.rightAssociated
        g.projectiveComparisonCentralizer_le_rightCentralizer
        d.factor_agreement).mp
      d.toCompleteCentralProjectiveComparisonData.scalar_agreement

/-- Consequently the scalar mismatch has full kernel. -/
theorem comparisonCentralScalarMismatch_ker_eq_top
    (d : ImageData R F g) :
    (F.associated.comparisonCentralScalarMismatch
        d.rightAssociated
        g.projectiveComparisonCentralizer_le_rightCentralizer
        d.factor_agreement).ker =
      ⊤ := by
  rw [d.comparisonCentralScalarMismatch_eq_one R F g]
  ext x
  simp

/-- In particular, the lifted character property discharges the sharp
kernel condition used by the existing scalar-correction construction. -/
theorem comparisonCentralScalarCorrectionKernelCondition
    (d : ImageData R F g) :
    F.associated.ComparisonCentralScalarCorrectionKernelCondition
      d.rightAssociated g d.factor_agreement := by
  intro x hx
  change
    F.associated.comparisonCentralScalarMismatch
        d.rightAssociated
        g.projectiveComparisonCentralizer_le_rightCentralizer
        d.factor_agreement x =
      1
  rw [d.comparisonCentralScalarMismatch_eq_one R F g]
  rfl

end ImageData

/-- The exact missing property of a proposed character map on the two
factor extensions, evaluated at the canonical source character. -/
def MapHasDGNImageProperty
    (kappa :
      IrreducibleCharacter
          (SourceFactorCentralExtensionGroup R F g) →
        IrreducibleCharacter
          (TargetFactorCentralExtensionGroup R F g)) : Prop :=
  let psi := kappa (sourceCharacter R F g)
  FactorSet.CentralExtensionGroup.HasCoefficientCharacter
      (targetFactorSet R F g)
      (targetFactorSet_isNormalized R F g)
      (coefficientHom R F g) psi ∧
    IrreducibleCharacter.IsExtensionAlong
      (targetNormalLift R F g) U.character psi ∧
    ∀ b : B,
      e b ∈
          Subgroup.centralizer
            (T.normalSubgroup : Set A) →
        (sourceCharacter R F g).values
              (FactorSet.CentralExtensionGroup.baseLift
                F.factorSet (F.factorSet_isNormalized R) (e b)) *
            (psi.degree : ℂ) =
          psi.values
              (FactorSet.CentralExtensionGroup.baseLift
                (targetFactorSet R F g)
                (targetFactorSet_isNormalized R F g) b) *
            ((sourceCharacter R F g).degree : ℂ)

/-- Package the image of a proposed lifted correspondence once the exact
DGN image property has been proved. -/
def ImageData.ofMap
    (kappa :
      IrreducibleCharacter
          (SourceFactorCentralExtensionGroup R F g) →
        IrreducibleCharacter
          (TargetFactorCentralExtensionGroup R F g))
    (hkappa : MapHasDGNImageProperty R F g kappa) :
    ImageData R F g where
  targetCharacter := kappa (sourceCharacter R F g)
  coefficientCharacter := hkappa.1
  extendsTargetNormalCharacter := hkappa.2.1
  normalizedBaseLiftValues := hkappa.2.2

end LiftedFactorCorrespondence
end InductiveMcKay
end McKayConjecture
