/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.ProjectiveObstructionExtension
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveObstructionClass

/-!
# Automatic cases of the central-triple projective obstruction

For a central restriction, the two outer quotients are canonically
isomorphic.  This file records two useful situations in which their
intrinsic projective obstruction classes agree automatically:

* both distinguished normal characters extend to their ambient groups;
* equivalently, both intrinsic obstruction classes vanish; and
* in particular, either (hence both) outer quotient is cyclic.

These are genuine automatic cases of the factor-set half of the
Dade--Glauberman--Nagao comparison.  They do not assert triviality of the
independent residual scalar character.
-/

noncomputable section

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

/-- If both intrinsic extension obstructions vanish, arbitrary associated
lifts have matching quotient-factor classes along a central restriction. -/
theorem quotientFactorH2ClassAgreement_of_both_obstructions_eq_zero
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (hleft :
      letI :=
        trivialMulDistribMulAction
          (A ⧸ T.normalSubgroup) ℂˣ
      T.projectiveObstructionClass = 0)
    (hright :
      letI :=
        trivialMulDistribMulAction
          (B ⧸ U.normalSubgroup) ℂˣ
      U.projectiveObstructionClass = 0) :
    R.QuotientFactorH2ClassAgreement S g := by
  letI :=
    trivialMulDistribMulAction
      (B ⧸ U.normalSubgroup) ℂˣ
  have hSclass :
      S.quotientFactorSet.h2Class = 0 :=
    S.quotientFactorSet_h2Class_eq_projectiveObstructionClass.trans
      hright
  have hRclass :
      letI :=
        trivialMulDistribMulAction
          (A ⧸ T.normalSubgroup) ℂˣ
      R.quotientFactorSet.h2Class = 0 :=
    R.quotientFactorSet_h2Class_eq_projectiveObstructionClass.trans
      hleft
  have hRone :
      R.quotientFactorSet.Cohomologous
        (FactorSet.one :
          FactorSet (A ⧸ T.normalSubgroup) ℂˣ) :=
    FactorSet.cohomologous_of_h2Class_eq
      (hRclass.trans FactorSet.h2Class_one.symm)
  have hRalongRaw :=
    FactorSet.comap_cohomologous
      hRone g.quotientEquiv.toMonoidHom
  have hcomapOne :
      (FactorSet.one :
        FactorSet (A ⧸ T.normalSubgroup) ℂˣ).comap
          g.quotientEquiv.toMonoidHom =
        (FactorSet.one :
          FactorSet (B ⧸ U.normalSubgroup) ℂˣ) := by
    ext q r
    rfl
  have hRalong :
      (R.quotientFactorSetAlong g).Cohomologous
        (FactorSet.one :
          FactorSet (B ⧸ U.normalSubgroup) ℂˣ) := by
    rw [← hcomapOne]
    exact hRalongRaw
  have hRalongClass :
      (R.quotientFactorSetAlong g).h2Class = 0 :=
    (FactorSet.h2Class_eq_of_cohomologous hRalong).trans
      FactorSet.h2Class_one
  exact hSclass.trans hRalongClass.symm

/-- Honest extensions of both distinguished normal characters discharge
the quotient-factor H² obstruction. -/
theorem quotientFactorH2ClassAgreement_of_extensions
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (psi : IrreducibleCharacter A)
    (hpsi :
      IrreducibleCharacter.IsExtensionAlong
        T.normalSubgroup.subtype T.character psi)
    (xi : IrreducibleCharacter B)
    (hxi :
      IrreducibleCharacter.IsExtensionAlong
        U.normalSubgroup.subtype U.character xi) :
    R.QuotientFactorH2ClassAgreement S g :=
  R.quotientFactorH2ClassAgreement_of_both_obstructions_eq_zero
    S g
    (IrreducibleCharacter.projectiveObstructionClass_eq_zero_of_isExtension
      psi hpsi)
    (IrreducibleCharacter.projectiveObstructionClass_eq_zero_of_isExtension
      xi hxi)

/-- If the left outer quotient is cyclic, both obstruction classes vanish
because the central-restriction quotient equivalence makes the right outer
quotient cyclic as well. -/
theorem quotientFactorH2ClassAgreement_of_isCyclic_leftQuotient
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (hcyclic : IsCyclic (A ⧸ T.normalSubgroup)) :
    R.QuotientFactorH2ClassAgreement S g := by
  have hrightCyclic :
      IsCyclic (B ⧸ U.normalSubgroup) :=
    g.quotientEquiv.isCyclic.mpr hcyclic
  exact
    R.quotientFactorH2ClassAgreement_of_both_obstructions_eq_zero
      S g
      (T.projectiveObstructionClass_eq_zero_of_isCyclic_quotient
        hcyclic)
      (U.projectiveObstructionClass_eq_zero_of_isCyclic_quotient
        hrightCyclic)

/-- Symmetric form: cyclicity of the right outer quotient also makes the
factor obstruction automatic. -/
theorem quotientFactorH2ClassAgreement_of_isCyclic_rightQuotient
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (hcyclic : IsCyclic (B ⧸ U.normalSubgroup)) :
    R.QuotientFactorH2ClassAgreement S g := by
  have hleftCyclic :
      IsCyclic (A ⧸ T.normalSubgroup) :=
    g.quotientEquiv.isCyclic.mp hcyclic
  exact
    R.quotientFactorH2ClassAgreement_of_isCyclic_leftQuotient
      S g hleftCyclic

end AssociatedProjectiveRepresentation
end CharacterTriple
end McKayConjecture
