/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CyclicExtensionConstruction
import McKayConjecture.CharacterTriple.AssociatedCoprimeLinearization
import McKayConjecture.CharacterTriple.ProjectiveObstructionClass

/-!
# Extension criterion for the projective obstruction class

The intrinsic class of a character triple in the second cohomology of its
outer quotient is exactly the obstruction to extending the distinguished
normal-subgroup character to the ambient group.

Both directions are constructive at the level used in this development.
An honest extension gives a factor-one associated projective
representation.  Conversely, if the intrinsic class vanishes, a gauge on
the quotient rescales the canonical associated lift to have factor one;
the resulting honest irreducible representation affords an extension.

As a first automatic case, the obstruction vanishes whenever the outer
quotient is cyclic.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple

variable {A : Type} [Finite A] [Group A]

namespace AssociatedProjectiveRepresentation

variable {T : CharacterTriple A}
variable {V : Type}
  [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}

/-- A factor-one associated lift forces the intrinsic obstruction class to
vanish. -/
theorem projectiveObstructionClass_eq_zero_of_factor_one
    (R : AssociatedProjectiveRepresentation T V P)
    (hfactor : ∀ a b : A, P.factor a b = 1) :
    letI :=
      trivialMulDistribMulAction
        (A ⧸ T.normalSubgroup) ℂˣ
    T.projectiveObstructionClass = 0 := by
  letI :=
    trivialMulDistribMulAction
      (A ⧸ T.normalSubgroup) ℂˣ
  have hquotient :
      R.quotientFactorSet =
        (FactorSet.one :
          FactorSet (A ⧸ T.normalSubgroup) ℂˣ) := by
    ext q r
    induction q using QuotientGroup.induction_on with
    | H a =>
        induction r using QuotientGroup.induction_on with
        | H b =>
            simpa only [← QuotientGroup.mk'_apply,
              R.quotientFactorSet_mk, hfactor,
              FactorSet.one_apply]
  rw [← R.quotientFactorSet_h2Class_eq_projectiveObstructionClass,
    hquotient, FactorSet.h2Class_one]

end AssociatedProjectiveRepresentation

end CharacterTriple

namespace IrreducibleCharacter

open CharacterTriple

variable {A : Type} [Finite A] [Group A]
variable {T : CharacterTriple A}

/-- The triple built from an honest extension is the original triple.
Only the proof of invariance changes. -/
theorem extensionCharacterTriple_eq
    (psi : IrreducibleCharacter A)
    (hpsi :
      IsExtensionAlong
        T.normalSubgroup.subtype T.character psi) :
    extensionCharacterTriple hpsi = T := by
  cases T
  rfl

/-- An honest extension kills the intrinsic projective obstruction. -/
theorem projectiveObstructionClass_eq_zero_of_isExtension
    (psi : IrreducibleCharacter A)
    (hpsi :
      IsExtensionAlong
        T.normalSubgroup.subtype T.character psi) :
    letI :=
      trivialMulDistribMulAction
        (A ⧸ T.normalSubgroup) ℂˣ
    T.projectiveObstructionClass = 0 := by
  letI : Nontrivial psi.realization :=
    CliffordRestriction.nontrivial_of_simple psi.realization
  let htriple :=
    extensionCharacterTriple_eq psi hpsi
  let R :
      AssociatedProjectiveRepresentation
        T psi.realization
        (extensionProjectiveRepresentation (ψ := psi)) := by
    rw [← htriple]
    exact extensionAssociatedProjectiveRepresentation hpsi
  exact
    R.projectiveObstructionClass_eq_zero_of_factor_one
      (fun a b ↦ extensionProjectiveRepresentation_factor
        (ψ := psi) a b)

end IrreducibleCharacter

namespace CharacterTriple

variable {A : Type} [Finite A] [Group A]
variable (T : CharacterTriple A)

/-- Vanishing of the intrinsic class produces an honest irreducible
extension of the distinguished normal-subgroup character. -/
theorem exists_extension_of_projectiveObstructionClass_eq_zero
    (hzero :
      letI :=
        trivialMulDistribMulAction
          (A ⧸ T.normalSubgroup) ℂˣ
      T.projectiveObstructionClass = 0) :
    ∃ psi : IrreducibleCharacter A,
      IrreducibleCharacter.IsExtensionAlong
        T.normalSubgroup.subtype T.character psi := by
  let R := AssociatedGeneralExistence.associated T
  have hclass :
      letI :=
        trivialMulDistribMulAction
          (A ⧸ T.normalSubgroup) ℂˣ
      R.quotientFactorSet.h2Class = 0 :=
    R.quotientFactorSet_h2Class_eq_projectiveObstructionClass.trans
      hzero
  have hcohomologous :
      R.quotientFactorSet.Cohomologous
        (FactorSet.one :
          FactorSet (A ⧸ T.normalSubgroup) ℂˣ) :=
    FactorSet.cohomologous_of_h2Class_eq
      (hclass.trans FactorSet.h2Class_one.symm)
  obtain ⟨c, hc⟩ := hcohomologous
  have hc_one : c 1 = 1 := by
    have hvalue :=
      congrArg
        (fun alpha :
          FactorSet (A ⧸ T.normalSubgroup) ℂˣ ↦
          alpha 1 1)
        hc
    simpa [R.quotientFactorSet_isNormalized.1 1] using hvalue.symm
  let Q : ProjectiveRepresentation ℂ A T.character.realization :=
    (AssociatedGeneralExistence.projectiveRepresentation T).rescale
      (AssociatedProjectiveRepresentation.quotientScalar c)
  let S :
      AssociatedProjectiveRepresentation
        T T.character.realization Q :=
    R.rescaleByQuotientScalar c hc_one
  have hfactor : ∀ a b : A, Q.factor a b = 1 := by
    intro a b
    let q := QuotientGroup.mk' T.normalSubgroup a
    let r := QuotientGroup.mk' T.normalSubgroup b
    have hvalue :=
      congrArg
        (fun alpha :
          FactorSet (A ⧸ T.normalSubgroup) ℂˣ ↦
          alpha q r)
        hc
    dsimp [Q]
    simpa only [q, r, ← QuotientGroup.mk'_apply,
      map_mul, R.quotientFactorSet_mk,
      FactorSet.one_apply, FactorSet.gauge_apply]
      using hvalue.symm
  exact
    ⟨S.extensionCharacterOfFactorOne hfactor,
      S.extensionCharacterOfFactorOne_isExtension hfactor⟩

/-- The projective obstruction vanishes exactly when the distinguished
character extends to the ambient group. -/
theorem projectiveObstructionClass_eq_zero_iff_exists_extension :
    (letI :=
      trivialMulDistribMulAction
        (A ⧸ T.normalSubgroup) ℂˣ;
      T.projectiveObstructionClass = 0) ↔
      ∃ psi : IrreducibleCharacter A,
        IrreducibleCharacter.IsExtensionAlong
          T.normalSubgroup.subtype T.character psi := by
  constructor
  · exact T.exists_extension_of_projectiveObstructionClass_eq_zero
  · rintro ⟨psi, hpsi⟩
    exact
      IrreducibleCharacter.projectiveObstructionClass_eq_zero_of_isExtension
        psi hpsi

/-- A cyclic outer quotient has no extension obstruction. -/
theorem projectiveObstructionClass_eq_zero_of_isCyclic_quotient
    (hcyclic : IsCyclic (A ⧸ T.normalSubgroup)) :
    letI :=
      trivialMulDistribMulAction
        (A ⧸ T.normalSubgroup) ℂˣ
    T.projectiveObstructionClass = 0 := by
  obtain ⟨q, hq⟩ := hcyclic.exists_generator
  obtain ⟨a, ha⟩ :=
    QuotientGroup.mk'_surjective T.normalSubgroup q
  have htop :
      Subgroup.zpowers
          (QuotientGroup.mk' T.normalSubgroup a) =
        ⊤ := by
    rw [ha]
    apply top_unique
    intro x _
    exact hq x
  have hinvariant :
      IrreducibleCharacter.IsInvariantUnder
        T.normalSubgroup T.character a := by
    intro x
    exact T.isInvariant a x
  obtain ⟨psi, hpsi⟩ :=
    IrreducibleCharacter.exists_extension_of_cyclic_quotient
      T.normalSubgroup T.character htop hinvariant
  exact
    IrreducibleCharacter.projectiveObstructionClass_eq_zero_of_isExtension
      psi hpsi

end CharacterTriple

end McKayConjecture
