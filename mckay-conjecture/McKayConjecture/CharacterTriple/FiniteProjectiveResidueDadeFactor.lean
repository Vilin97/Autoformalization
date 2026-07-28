/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerPrimitiveNormalizerExtensionCriterion
import McKayConjecture.CharacterTriple.FiniteProjectiveResidueComplexNormalizerFactor
import McKayConjecture.CharacterTriple.ProjectiveCompatibleNormalizerSplitting

/-!
# Primitive Dade data on a projective residue lattice

This file packages the modular data attached to a reduced finite projective
representation: an honest finite-group action on the residue lattice, a
primitive Dade structure on its endomorphism algebra, the fixed-unit
character extension needed for the Brauer normalizer.  Faithfulness and
primitivity supply the remaining conjugation clause.  The package constructs
the normalizer lift and proves cross-characteristic splitting through the
unconditional complex character of residue-field units; callers do not need a
compatible embedding into a separately chosen finite field or to repeat the
dependent endomorphism-action instances.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

open Representation

variable {G V ι : Type}
variable [Group G] [Finite G]
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable [Finite ι]

private instance residueDadeFinrankNeZero :
    NeZero (Module.finrank ℂ V) :=
  ⟨Module.finrank_pos.ne'⟩

variable
  (P : ProjectiveRepresentation ℂ G V)
  (b : Module.Basis ι ℂ V)
  (q : ℕ) [Fact q.Prime]

/-- The chosen finite residue field, named so its instances need not be
rediscovered through a long reducible expression. -/
abbrev ResidueDadeField :=
  FiniteRootCoefficientRing.ResidueFieldAbovePrime
    q (Module.finrank ℂ V)

/-- The reduced integral lattice, named for the same elaboration reason. -/
abbrev ResidueDadeModule :=
  P.residueFieldLattice b q

noncomputable instance residueDadeFieldField :
    Field (ResidueDadeField (V := V) q) :=
  inferInstance

noncomputable instance residueDadeModuleAddCommGroup :
    AddCommGroup (ResidueDadeModule P b q) :=
  inferInstance

noncomputable instance residueDadeModuleModule :
    Module (ResidueDadeField (V := V) q) (ResidueDadeModule P b q) :=
  inferInstance

noncomputable instance residueDadeModuleMulAction :
    MulAction (ResidueDadeField (V := V) q) (ResidueDadeModule P b q) :=
  (residueDadeModuleModule (P := P) (b := b) (q := q)
    ).toDistribMulAction.toMulAction

/-- All modular data needed to split the retained factor of a projective
representation reduced at the chosen cyclotomic residue field. -/
structure ResidueDadeFactorData where
  /-- The finite `q`-group acting on the reduced module.  Its `q`-group
  property is carried by `dade`. -/
  R : Type
  [groupR : Group R]
  [fintypeR : Fintype R]
  /-- The honest action whose implementing image is normalized by the
  reduced projective operators. -/
  rho :
    R →*
      (ResidueDadeModule P b q ≃ₗ[
        ResidueDadeField (V := V) q]
        ResidueDadeModule P b q)
  /-- Replacing the acting group by its image loses no Dade information
  and makes the associated interior action faithful. -/
  rho_injective : Function.Injective rho
  /-- Pointwise normalization is the precise operator-level compatibility
  required to form the normalizer lift. -/
  normalizes :
    (P.residueFieldProjectiveRepresentation b q
      ).PointwiseNormalizesLinearAction rho
  /-- The endomorphism algebra of the reduced module is a Dade algebra for
  the conjugation action induced by `rho`. -/
  dade :
    letI : Field (ResidueDadeField (V := V) q) :=
      residueDadeFieldField (V := V) q
    letI : AddCommGroup (ResidueDadeModule P b q) :=
      residueDadeModuleAddCommGroup (P := P) (b := b) (q := q)
    letI : Module
        (ResidueDadeField (V := V) q)
        (ResidueDadeModule P b q) :=
      residueDadeModuleModule (P := P) (b := b) (q := q)
    letI : MulAction
        (ResidueDadeField (V := V) q)
        (ResidueDadeModule P b q) :=
      residueDadeModuleMulAction (P := P) (b := b) (q := q)
    letI := endomorphismConjugationMulSemiringAction rho
    letI := endomorphismConjugation_smulCommClass rho
    DadeAlgebra q (ResidueDadeField (V := V) q) R
      (Module.End
        (ResidueDadeField (V := V) q)
        (ResidueDadeModule P b q))
  /-- The Dade algebra is primitive. -/
  primitive :
    letI : Field (ResidueDadeField (V := V) q) :=
      residueDadeFieldField (V := V) q
    letI : AddCommGroup (ResidueDadeModule P b q) :=
      residueDadeModuleAddCommGroup (P := P) (b := b) (q := q)
    letI : Module
        (ResidueDadeField (V := V) q)
        (ResidueDadeModule P b q) :=
      residueDadeModuleModule (P := P) (b := b) (q := q)
    letI : MulAction
        (ResidueDadeField (V := V) q)
        (ResidueDadeModule P b q) :=
      residueDadeModuleMulAction (P := P) (b := b) (q := q)
    letI := endomorphismConjugationMulSemiringAction rho
    letI := endomorphismConjugation_smulCommClass rho
    dade.IsBrauerPrimitive
  /-- In the primitive faithful case, only the homomorphism extending
  the fixed-unit Brauer character remains to be supplied; conjugation
  compatibility follows automatically. -/
  hasNormalizerHomExtension :
    letI : Field (ResidueDadeField (V := V) q) :=
      residueDadeFieldField (V := V) q
    letI : AddCommGroup (ResidueDadeModule P b q) :=
      residueDadeModuleAddCommGroup (P := P) (b := b) (q := q)
    letI : Module
        (ResidueDadeField (V := V) q)
        (ResidueDadeModule P b q) :=
      residueDadeModuleModule (P := P) (b := b) (q := q)
    letI : MulAction
        (ResidueDadeField (V := V) q)
        (ResidueDadeModule P b q) :=
      residueDadeModuleMulAction (P := P) (b := b) (q := q)
    letI := endomorphismConjugationMulSemiringAction rho
    letI := endomorphismConjugation_smulCommClass rho
    HasBrauerNormalizerHomExtension
      (k := ResidueDadeField (V := V) q)
      (interiorActionOfLinearAction rho)

attribute [instance]
  ResidueDadeFactorData.groupR
  ResidueDadeFactorData.fintypeR

namespace ResidueDadeFactorData

/-- Primitive Dade data on the residue lattice split the original complex
projective obstruction whenever its complex dimension is prime to `q`. -/
theorem factorSet_h2Class_eq_zero
    (d : ResidueDadeFactorData P b q)
    (hdegree : ¬q ∣ Module.finrank ℂ V) :
    letI := trivialMulDistribMulAction G ℂˣ
    P.factorSet.h2Class = 0 := by
  letI : Field (ResidueDadeField (V := V) q) :=
    residueDadeFieldField (V := V) q
  letI : AddCommGroup (ResidueDadeModule P b q) :=
    residueDadeModuleAddCommGroup (P := P) (b := b) (q := q)
  letI : Module
      (ResidueDadeField (V := V) q)
      (ResidueDadeModule P b q) :=
    residueDadeModuleModule (P := P) (b := b) (q := q)
  letI : MulAction
      (ResidueDadeField (V := V) q)
      (ResidueDadeModule P b q) :=
    residueDadeModuleMulAction (P := P) (b := b) (q := q)
  letI := endomorphismConjugationMulSemiringAction d.rho
  letI := endomorphismConjugation_smulCommClass d.rho
  let I := interiorActionOfLinearAction d.rho
  have hI : Function.Injective I.unit := by
    intro x y hxy
    apply d.rho_injective
    exact (linearEquivUnit (k := ResidueDadeField (V := V) q)
      (V := ResidueDadeModule P b q)).injective hxy
  have hNormalizerExtension :
      HasBrauerNormalizerExtension
        (k := ResidueDadeField (V := V) q) I :=
    d.dade.hasBrauerNormalizerExtension_of_isBrauerPrimitive
      I hI d.primitive d.hasNormalizerHomExtension
  let T :=
    P.residueFieldProjectiveNormalizerLift
      b q d.rho d.normalizes
  apply
    P.factorSet_h2Class_eq_zero_of_retainedDadeFactor
      q hdegree d.dade d.primitive I T
      (Classical.choice hNormalizerExtension)
      (FiniteRootCoefficientRing.residueUnitsComplexCharacter
        q (Module.finrank ℂ V))
  intro g h
  exact
    P.residueUnitsComplexCharacter_residueFieldProjectiveNormalizerLift_factor
      b q d.rho d.normalizes g h

end ResidueDadeFactorData
end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
