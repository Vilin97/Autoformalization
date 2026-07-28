/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralTripleLiftedFactorExtensionTriples
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveObstructionClass
import McKayConjecture.Character.ExtensionFromDegree

/-!
# The obstruction to extending the target normal character

Fix central-restriction data from `(A,N,theta)` to `(B,M,phi)`, an
associated projective representation of the left triple, and a finite
normalization of its factor.  Pulling that finite factor back to `B`
produces the target factor extension used in the lifted DGN construction.

This file proves that the existence of an irreducible character on that
target factor extension

* with the defining coefficient scalar, and
* restricting to `phi` on the canonical lift of `M`

is equivalent to equality of the intrinsic projective obstruction classes
of the two triples.

The forward implication extracts the associated projective representation
from the proposed extension character.  For the reverse implication, an
arbitrary associated lift of the target triple is rescaled by the quotient
cochain supplied by `H²` equality.  Its factor then agrees literally with
the pulled-back finite factor, so it linearizes on the desired finite
central extension.

Thus the target-normal restriction field is not a consequence of the
quotient-factor character alone: its precise missing input is the
projective-obstruction part of the Dade--Glauberman--Nagao theorem.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace InductiveMcKay
namespace LiftedFactorCorrespondence

open CharacterTriple
open CharacterTriple.AssociatedProjectiveRepresentation

variable {A B : Type}
variable [Group A] [Finite A] [Group B] [Finite B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {e : B →* A}
variable {V W : Type}
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W]
variable [Module.Finite ℂ W] [Nontrivial W]
variable {P : ProjectiveRepresentation ℂ A V}
variable {Q : ProjectiveRepresentation ℂ B W}

variable
  (R : AssociatedProjectiveRepresentation T V P)
  (F : R.AssociatedFiniteFactorNormalization)
  (g : CentralRestrictionGroupData T U e)

/-! ## Linearizing a factor-matched target lift -/

/-- The honest representation on the fixed target factor extension
obtained from any associated target lift whose factor agrees literally
with the pulled-back finite left factor. -/
def targetFactorExtensionRepresentationOfFactorAgreement
    (_S : AssociatedProjectiveRepresentation U W Q)
    (hfactor :
      ∀ b c : B,
        F.projective.factor (e b) (e c) =
          Q.factor b c) :
    Representation ℂ
      (TargetFactorCentralExtensionGroup R F g) W :=
  Q.centralExtensionRepresentation
    (targetFactorSet R F g)
    (targetFactorSet_isNormalized R F g)
    (coefficientHom R F g) (by
      intro b c
      change
        ((F.factorSet (e b) (e c) :
          rootsOfUnity (associatedFactorExponent T V) ℂ) : ℂˣ) =
            Q.factor b c
      rw [F.factorSet_coe]
      exact hfactor b c)

/-- The preceding target factor-extension representation is irreducible. -/
theorem targetFactorExtensionRepresentationOfFactorAgreement_isIrreducible
    (S : AssociatedProjectiveRepresentation U W Q)
    (hfactor :
      ∀ b c : B,
        F.projective.factor (e b) (e c) =
          Q.factor b c) :
    Representation.IsIrreducible
      (targetFactorExtensionRepresentationOfFactorAgreement
        R F g S hfactor) :=
  Q.centralExtensionRepresentation_isIrreducible
    (targetFactorSet R F g)
    (targetFactorSet_isNormalized R F g)
    (coefficientHom R F g) (by
      intro b c
      change
        ((F.factorSet (e b) (e c) :
          rootsOfUnity (associatedFactorExponent T V) ℂ) : ℂˣ) =
            Q.factor b c
      rw [F.factorSet_coe]
      exact hfactor b c)
    S.projective_isIrreducible

/-- The irreducible character obtained by linearizing a factor-matched
associated target lift on the fixed target factor extension. -/
def targetFactorExtensionCharacterOfFactorAgreement
    (S : AssociatedProjectiveRepresentation U W Q)
    (hfactor :
      ∀ b c : B,
        F.projective.factor (e b) (e c) =
          Q.factor b c) :
    IrreducibleCharacter
      (TargetFactorCentralExtensionGroup R F g) := by
  let rho :=
    targetFactorExtensionRepresentationOfFactorAgreement
      R F g S hfactor
  letI : Representation.IsIrreducible rho :=
    targetFactorExtensionRepresentationOfFactorAgreement_isIrreducible
      R F g S hfactor
  letI : Simple (FDRep.of rho) :=
    FDRep.simple_of_representation_isIrreducible rho
  exact IrreducibleCharacter.ofSimple (FDRep.of rho)

/-- The linearized character has the defining coefficient action. -/
theorem targetFactorExtensionCharacterOfFactorAgreement_hasCoefficientCharacter
    (S : AssociatedProjectiveRepresentation U W Q)
    (hfactor :
      ∀ b c : B,
        F.projective.factor (e b) (e c) =
          Q.factor b c) :
    FactorSet.CentralExtensionGroup.HasCoefficientCharacter
      (targetFactorSet R F g)
      (targetFactorSet_isNormalized R F g)
      (coefficientHom R F g)
      (targetFactorExtensionCharacterOfFactorAgreement
        R F g S hfactor) := by
  intro c
  let rho :=
    targetFactorExtensionRepresentationOfFactorAgreement
      R F g S hfactor
  letI : Representation.IsIrreducible rho :=
    targetFactorExtensionRepresentationOfFactorAgreement_isIrreducible
      R F g S hfactor
  letI : Simple (FDRep.of rho) :=
    FDRep.simple_of_representation_isIrreducible rho
  change
    LinearMap.trace ℂ W
        (rho
          (FactorSet.CentralExtensionGroup.coefficientEmbedding
            (targetFactorSet R F g)
            (targetFactorSet_isNormalized R F g) c)) =
      ((c : ℂˣ) : ℂ) * (Module.finrank ℂ W : ℂ)
  dsimp only [rho,
    targetFactorExtensionRepresentationOfFactorAgreement]
  rw [Q.centralExtensionRepresentation_apply_coefficientEmbedding]
  have hscalar :
      ((scalarLinearEquiv ℂ W
          ((coefficientHom R F g c : ℂˣ)) :
          W ≃ₗ[ℂ] W) : W →ₗ[ℂ] W) =
        ((c : ℂˣ) : ℂ) •
          (LinearMap.id : Module.End ℂ W) := by
    ext w
    simp [coefficientHom]
  rw [hscalar, map_smul, LinearMap.trace_id]
  rfl

/-- The linearized character restricts to the distinguished target normal
character along the canonical normal lift. -/
theorem targetFactorExtensionCharacterOfFactorAgreement_isExtension
    (S : AssociatedProjectiveRepresentation U W Q)
    (hfactor :
      ∀ b c : B,
        F.projective.factor (e b) (e c) =
          Q.factor b c) :
    IrreducibleCharacter.IsExtensionAlong
      (targetNormalLift R F g) U.character
      (targetFactorExtensionCharacterOfFactorAgreement
        R F g S hfactor) := by
  intro m
  let rho :=
    targetFactorExtensionRepresentationOfFactorAgreement
      R F g S hfactor
  letI : Representation.IsIrreducible rho :=
    targetFactorExtensionRepresentationOfFactorAgreement_isIrreducible
      R F g S hfactor
  letI : Simple (FDRep.of rho) :=
    FDRep.simple_of_representation_isIrreducible rho
  change
    LinearMap.trace ℂ W (rho (targetNormalLift R F g m)) =
      U.character.values m
  calc
    LinearMap.trace ℂ W (rho (targetNormalLift R F g m)) =
        LinearMap.trace ℂ W
          (Q.operator (m : B) : W →ₗ[ℂ] W) := by
      congr 1
      ext w
      simp only [rho,
        targetFactorExtensionRepresentationOfFactorAgreement,
        ProjectiveRepresentation.centralExtensionRepresentation_apply_vector,
        targetNormalLift_apply,
        FactorSet.CentralExtensionGroup.baseLift_coefficient,
        FactorSet.CentralExtensionGroup.baseLift_base,
        map_one, Units.val_one, one_smul]
      rfl
    _ = U.character.values m := by
      have hm := congrFun S.restriction_character m
      change
        LinearMap.trace ℂ W
            ((S.restriction m : W ≃ₗ[ℂ] W) :
              W →ₗ[ℂ] W) =
          U.character.values m at hm
      rw [S.restriction_apply] at hm
      exact hm

/-! ## The exact obstruction criterion -/

/-- For a fixed target factor-extension character, the exact normal
restriction is equivalent to positive restriction multiplicity together
with equality of degrees. -/
theorem hasTargetNormalRestriction_iff_liesOver_and_degree_eq
    (psi :
      IrreducibleCharacter
        (TargetFactorCentralExtensionGroup R F g)) :
    IrreducibleCharacter.IsExtensionAlong
        (targetNormalLift R F g) U.character psi ↔
      CliffordCorrespondence.LiesOverAlong
          (targetNormalLift R F g) U.character psi ∧
        psi.degree = U.character.degree := by
  constructor
  · intro h
    exact ⟨h.liesOver, h.degree_eq⟩
  · rintro ⟨hover, hdegree⟩
    exact
      IrreducibleCharacter.IsExtensionAlong.of_liesOver_of_degree_eq
        hover hdegree

/-- Literal factor agreement already gives equality of the two quotient
factor sets. -/
theorem quotientFactorSet_eq_of_factorAgreement
    (S : AssociatedProjectiveRepresentation U W Q)
    (hfactor :
      ∀ b c : B,
        F.projective.factor (e b) (e c) =
          Q.factor b c) :
    S.quotientFactorSet =
      F.associated.quotientFactorSetAlong g := by
  apply FactorSet.ext
  intro q r
  induction q using QuotientGroup.induction_on with
  | H b =>
      induction r using QuotientGroup.induction_on with
      | H c =>
          change
            S.quotientFactorSet
                (QuotientGroup.mk' U.normalSubgroup b)
                (QuotientGroup.mk' U.normalSubgroup c) =
              F.associated.quotientFactorSetAlong g
                (QuotientGroup.mk' U.normalSubgroup b)
                (QuotientGroup.mk' U.normalSubgroup c)
          rw [S.quotientFactorSet_mk,
            F.associated.quotientFactorSetAlong_mk]
          exact (hfactor b c).symm

/-- A proposed target extension character forces intrinsic projective
obstruction agreement. -/
theorem projectiveObstructionClassAgreement_of_targetNormalExtensionClaim
    (h :
      ∃ psi :
          IrreducibleCharacter
            (TargetFactorCentralExtensionGroup R F g),
        FactorSet.CentralExtensionGroup.HasCoefficientCharacter
            (targetFactorSet R F g)
            (targetFactorSet_isNormalized R F g)
            (coefficientHom R F g) psi ∧
          IrreducibleCharacter.IsExtensionAlong
            (targetNormalLift R F g) U.character psi) :
    g.ProjectiveObstructionClassAgreement := by
  obtain ⟨psi, hcoeff, hext⟩ := h
  let S :=
    targetAssociated R F g psi hcoeff hext
  have hsets :
      S.quotientFactorSet =
        F.associated.quotientFactorSetAlong g :=
    quotientFactorSet_eq_of_factorAgreement
      R F g S
      (targetProjective_factor_agreement
        R F g psi hcoeff)
  have hH2 :
      F.associated.QuotientFactorH2ClassAgreement S g := by
    letI :=
      trivialMulDistribMulAction
        (B ⧸ U.normalSubgroup) ℂˣ
    exact congrArg FactorSet.h2Class hsets
  exact
    (F.associated
      |>.quotientFactorH2ClassAgreement_iff_projectiveObstructionClass
        S g).mp hH2

/-- Intrinsic projective-obstruction agreement constructs the target
factor-extension character with its exact coefficient and normal
restriction properties. -/
theorem targetNormalExtensionClaim_of_projectiveObstructionClassAgreement
    (h : g.ProjectiveObstructionClassAgreement) :
    ∃ psi :
        IrreducibleCharacter
          (TargetFactorCentralExtensionGroup R F g),
      FactorSet.CentralExtensionGroup.HasCoefficientCharacter
          (targetFactorSet R F g)
          (targetFactorSet_isNormalized R F g)
          (coefficientHom R F g) psi ∧
        IrreducibleCharacter.IsExtensionAlong
          (targetNormalLift R F g) U.character psi := by
  let S := AssociatedGeneralExistence.associated U
  have hH2 :
      F.associated.QuotientFactorH2ClassAgreement S g :=
    (F.associated
      |>.quotientFactorH2ClassAgreement_iff_projectiveObstructionClass
        S g).mpr h
  let hcoh :=
    F.associated.quotientFactorCohomologyAgreement_of_h2Class
      S g hH2
  let S' :=
    F.associated.factorMatchedRightAssociated S g hcoh
  let hfactor :=
    F.associated.factorMatchedRightAssociated_factor_agreement
      S g hcoh
  let psi :=
    targetFactorExtensionCharacterOfFactorAgreement
      R F g S' hfactor
  exact
    ⟨psi,
      targetFactorExtensionCharacterOfFactorAgreement_hasCoefficientCharacter
        R F g S' hfactor,
      targetFactorExtensionCharacterOfFactorAgreement_isExtension
        R F g S' hfactor⟩

/-- The target-normal extension claim is exactly the intrinsic
projective-obstruction equality, with no residual numerical or
representation-choice condition. -/
theorem targetNormalExtensionClaim_iff_projectiveObstructionClassAgreement :
    (∃ psi :
        IrreducibleCharacter
          (TargetFactorCentralExtensionGroup R F g),
      FactorSet.CentralExtensionGroup.HasCoefficientCharacter
          (targetFactorSet R F g)
          (targetFactorSet_isNormalized R F g)
          (coefficientHom R F g) psi ∧
        IrreducibleCharacter.IsExtensionAlong
          (targetNormalLift R F g) U.character psi) ↔
      g.ProjectiveObstructionClassAgreement :=
  ⟨projectiveObstructionClassAgreement_of_targetNormalExtensionClaim
      R F g,
    targetNormalExtensionClaim_of_projectiveObstructionClassAgreement
      R F g⟩

end LiftedFactorCorrespondence
end InductiveMcKay
end McKayConjecture
