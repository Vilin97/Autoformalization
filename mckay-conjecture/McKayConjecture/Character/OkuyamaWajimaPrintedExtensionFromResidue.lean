/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.OkuyamaWajimaPrintedMultiplicityPPrimary
import McKayConjecture.CharacterTriple.AssociatedGeneralExistence
import McKayConjecture.InductiveMcKay.CentralTripleFactorMatchedCohomology

/-!
# An optional Okuyama--Wajima extension route from a residue class

The retained prime-to-`p` factor constructed in
`OkuyamaWajimaPrintedMultiplicityPPrimary` is a factor set on the acting
group `U`.  The extension problem, however, is controlled by the common
outer quotient

`U / C_K(Q) ≃ (UK) / K`.

This distinction matters: vanishing after inflation to `U` does not, in
general, imply vanishing on `U / C_K(Q)`.  Thus the external mismatch
calculation cannot honestly be identified with the character-triple
obstruction without one further descent statement.

The printed 1980 proof does not supply this stronger residue statement;
it proves extension-existence equivalence directly by induction.  The
construction here is therefore an optional sufficient-condition adapter,
not a reformulation of that induction.

This file makes that boundary exact and closes everything after it.

* The quotient-factor gauge construction is developed for
  `FactorMatchedRestrictionGroupData`.  The older API used
  `CentralRestrictionGroupData`, although centralizer containment plays no
  role in this construction.
* Equality of the two quotient `H²` classes gives an explicit
  quotient-cochain rescaling and hence the existing literal
  factor-matching input.
* The retained prime-to-`p` split kills the external mismatch class.
* A named external-to-quotient residue-transfer input is therefore the only
  remaining local hypothesis needed to obtain
  `InvariantOkuyamaWajimaPrintedExtensionTheoremInput`.

No injectivity of inflation in group cohomology is asserted.
-/

noncomputable section

namespace McKayConjecture

open CharacterTriple
open GroupTheory

namespace InductiveMcKay

variable {A B : Type}
variable [Group A] [Finite A] [Group B] [Finite B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {e : B →* A}

namespace FactorMatchedRestrictionGroupData

/-- The embedding maps the right normal subgroup into the left normal
subgroup.  This is the quotient-theoretic part of the intersection
hypothesis. -/
theorem rightNormal_le_comap_leftNormal
    (g : FactorMatchedRestrictionGroupData T U e) :
    U.normalSubgroup ≤ T.normalSubgroup.comap e := by
  intro b hb
  have hmap :
      e b ∈ U.normalSubgroup.map e :=
    ⟨b, hb, rfl⟩
  rw [← g.intersection_eq] at hmap
  exact hmap.1

/-- Membership in the left normal subgroup is reflected by the
embedding. -/
theorem mem_rightNormal_of_embedding_mem_leftNormal
    (g : FactorMatchedRestrictionGroupData T U e)
    {b : B} (hb : e b ∈ T.normalSubgroup) :
    b ∈ U.normalSubgroup := by
  have hinf :
      e b ∈ T.normalSubgroup ⊓ MonoidHom.range e :=
    ⟨hb, ⟨b, rfl⟩⟩
  rw [g.intersection_eq] at hinf
  obtain ⟨m, hm, hme⟩ := hinf
  have hmb : m = b :=
    g.embedding_injective hme
  exact hmb ▸ hm

/-- The homomorphism on outer quotients induced by the embedding. -/
def quotientHom
    (g : FactorMatchedRestrictionGroupData T U e) :
    B ⧸ U.normalSubgroup →*
      A ⧸ T.normalSubgroup :=
  QuotientGroup.map U.normalSubgroup T.normalSubgroup
    e g.rightNormal_le_comap_leftNormal

@[simp]
theorem quotientHom_mk
    (g : FactorMatchedRestrictionGroupData T U e)
    (b : B) :
    g.quotientHom
        (QuotientGroup.mk' U.normalSubgroup b) =
      QuotientGroup.mk' T.normalSubgroup (e b) :=
  rfl

/-- The intersection hypothesis makes the quotient map injective. -/
theorem quotientHom_injective
    (g : FactorMatchedRestrictionGroupData T U e) :
    Function.Injective g.quotientHom := by
  intro q r hqr
  induction q using QuotientGroup.induction_on with
  | H b =>
      induction r using QuotientGroup.induction_on with
      | H c =>
          apply
            (QuotientGroup.eq_iff_div_mem
              (N := U.normalSubgroup)).2
          apply
            g.mem_rightNormal_of_embedding_mem_leftNormal
          have hquot :
              (e b : A ⧸ T.normalSubgroup) =
                (e c : A ⧸ T.normalSubgroup) := by
            exact hqr
          have hmem :=
            (QuotientGroup.eq_iff_div_mem
              (N := T.normalSubgroup)).1 hquot
          simpa only [map_div] using hmem

/-- The normal-times-image decomposition makes the quotient map
surjective. -/
theorem quotientHom_surjective
    (g : FactorMatchedRestrictionGroupData T U e) :
    Function.Surjective g.quotientHom := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H a =>
      obtain ⟨x, b, hxb⟩ :=
        g.ambient_eq_product a
      refine
        ⟨QuotientGroup.mk' U.normalSubgroup b, ?_⟩
      change
        QuotientGroup.mk' T.normalSubgroup (e b) =
          QuotientGroup.mk' T.normalSubgroup a
      rw [← hxb, map_mul]
      have hx :
          QuotientGroup.mk' T.normalSubgroup (x : A) =
            1 :=
        (QuotientGroup.eq_one_iff (x : A)).2 x.property
      rw [hx, one_mul]

/-- The canonical equivalence of outer quotients supplied by the three
factor-matched group conditions. -/
def quotientEquiv
    (g : FactorMatchedRestrictionGroupData T U e) :
    (B ⧸ U.normalSubgroup) ≃*
      (A ⧸ T.normalSubgroup) :=
  MulEquiv.ofBijective g.quotientHom
    ⟨g.quotientHom_injective,
      g.quotientHom_surjective⟩

@[simp]
theorem quotientEquiv_mk
    (g : FactorMatchedRestrictionGroupData T U e)
    (b : B) :
    g.quotientEquiv
        (QuotientGroup.mk' U.normalSubgroup b) =
      QuotientGroup.mk' T.normalSubgroup (e b) :=
  rfl

end FactorMatchedRestrictionGroupData
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

/-- The left quotient factor transported to the right quotient using only
factor-matched group data. -/
def factorMatchedQuotientFactorSetAlong
    (R : AssociatedProjectiveRepresentation T V P)
    (g : FactorMatchedRestrictionGroupData T U e) :
    FactorSet (B ⧸ U.normalSubgroup) ℂˣ :=
  R.quotientFactorSet.comap
    g.quotientEquiv.toMonoidHom

@[simp]
theorem factorMatchedQuotientFactorSetAlong_mk
    (R : AssociatedProjectiveRepresentation T V P)
    (g : FactorMatchedRestrictionGroupData T U e)
    (b c : B) :
    R.factorMatchedQuotientFactorSetAlong g
        (QuotientGroup.mk' U.normalSubgroup b)
        (QuotientGroup.mk' U.normalSubgroup c) =
      P.factor (e b) (e c) := by
  change
    R.quotientFactorSet
        (g.quotientEquiv
          (QuotientGroup.mk' U.normalSubgroup b))
        (g.quotientEquiv
          (QuotientGroup.mk' U.normalSubgroup c)) =
      P.factor (e b) (e c)
  rw [g.quotientEquiv_mk, g.quotientEquiv_mk,
    R.quotientFactorSet_mk]

/-- The transported factor remains normalized. -/
theorem factorMatchedQuotientFactorSetAlong_isNormalized
    (R : AssociatedProjectiveRepresentation T V P)
    (g : FactorMatchedRestrictionGroupData T U e) :
    (R.factorMatchedQuotientFactorSetAlong g).IsNormalized :=
  FactorSet.comap_isNormalized
    R.quotientFactorSet
    g.quotientEquiv.toMonoidHom
    R.quotientFactorSet_isNormalized

/-- Explicit quotient-cochain agreement for factor-matched group data. -/
def FactorMatchedQuotientFactorCohomologyAgreement
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : FactorMatchedRestrictionGroupData T U e) : Prop :=
  S.quotientFactorSet.Cohomologous
    (R.factorMatchedQuotientFactorSetAlong g)

/-- The same agreement as equality in second group cohomology. -/
def FactorMatchedQuotientFactorH2ClassAgreement
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : FactorMatchedRestrictionGroupData T U e) : Prop :=
  letI :=
    trivialMulDistribMulAction
      (B ⧸ U.normalSubgroup) ℂˣ
  S.quotientFactorSet.h2Class =
    (R.factorMatchedQuotientFactorSetAlong g).h2Class

/-- The quotient-factor agreement is independent of both associated
projective lifts. -/
theorem factorMatchedQuotientFactorH2ClassAgreement_congr
    {V' W' : Type}
    [AddCommGroup V'] [Module ℂ V']
      [Module.Finite ℂ V'] [Nontrivial V']
    [AddCommGroup W'] [Module ℂ W']
      [Module.Finite ℂ W'] [Nontrivial W']
    {P' : ProjectiveRepresentation ℂ A V'}
    {Q' : ProjectiveRepresentation ℂ B W'}
    (R : AssociatedProjectiveRepresentation T V P)
    (R' : AssociatedProjectiveRepresentation T V' P')
    (S : AssociatedProjectiveRepresentation U W Q)
    (S' : AssociatedProjectiveRepresentation U W' Q')
    (g : FactorMatchedRestrictionGroupData T U e)
    (h : R.FactorMatchedQuotientFactorH2ClassAgreement S g) :
    R'.FactorMatchedQuotientFactorH2ClassAgreement S' g := by
  letI :=
    trivialMulDistribMulAction
      (B ⧸ U.normalSubgroup) ℂˣ
  have hright :
      S.quotientFactorSet.h2Class =
        S'.quotientFactorSet.h2Class :=
    FactorSet.h2Class_eq_of_cohomologous
      (S'.quotientFactorSet_cohomologous S)
  have hleftCohomologous :
      (R.factorMatchedQuotientFactorSetAlong g).Cohomologous
        (R'.factorMatchedQuotientFactorSetAlong g) := by
    exact
      FactorSet.comap_cohomologous
        (R'.quotientFactorSet_cohomologous R)
        g.quotientEquiv.toMonoidHom
  have hleft :
      (R.factorMatchedQuotientFactorSetAlong g).h2Class =
        (R'.factorMatchedQuotientFactorSetAlong g).h2Class :=
    FactorSet.h2Class_eq_of_cohomologous
      hleftCohomologous
  exact hright.symm.trans (h.trans hleft)

/-- The quotient mismatch factor representing the difference of the two
outer obstruction classes. -/
def factorMatchedQuotientMismatchFactorSet
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : FactorMatchedRestrictionGroupData T U e) :
    FactorSet (B ⧸ U.normalSubgroup) ℂˣ :=
  R.factorMatchedQuotientFactorSetAlong g *
    S.quotientFactorSet⁻¹

/-- Vanishing of the quotient mismatch is exactly quotient-factor class
agreement. -/
theorem factorMatchedQuotientMismatchFactorSet_h2Class_eq_zero_iff
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : FactorMatchedRestrictionGroupData T U e) :
    (letI :=
      trivialMulDistribMulAction
        (B ⧸ U.normalSubgroup) ℂˣ
    (R.factorMatchedQuotientMismatchFactorSet S g).h2Class = 0) ↔
      R.FactorMatchedQuotientFactorH2ClassAgreement S g := by
  letI :=
    trivialMulDistribMulAction
      (B ⧸ U.normalSubgroup) ℂˣ
  exact
    (FactorSet.h2Class_mul_inv_eq_zero_iff
      (R.factorMatchedQuotientFactorSetAlong g)
      S.quotientFactorSet).trans eq_comm

/-- Equality of quotient `H²` classes supplies an explicit quotient
cochain. -/
theorem factorMatchedQuotientFactorCohomologyAgreement_of_h2Class
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : FactorMatchedRestrictionGroupData T U e)
    (h : R.FactorMatchedQuotientFactorH2ClassAgreement S g) :
    R.FactorMatchedQuotientFactorCohomologyAgreement S g :=
  FactorSet.cohomologous_of_h2Class_eq h

/-- The chosen quotient cochain witnessing factor-class agreement. -/
def factorMatchedFactorMatchingQuotientScalar
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : FactorMatchedRestrictionGroupData T U e)
    (h : R.FactorMatchedQuotientFactorCohomologyAgreement S g) :
    (B ⧸ U.normalSubgroup) → ℂˣ :=
  Classical.choose h

/-- The selected cochain gauges the right quotient factor to the
transported left quotient factor. -/
theorem factorMatchedQuotientFactorSetAlong_eq_gauge
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : FactorMatchedRestrictionGroupData T U e)
    (h : R.FactorMatchedQuotientFactorCohomologyAgreement S g) :
    R.factorMatchedQuotientFactorSetAlong g =
      S.quotientFactorSet.gauge
        (R.factorMatchedFactorMatchingQuotientScalar S g h) :=
  Classical.choose_spec h

/-- Normalization forces the quotient gauge to be one at the identity. -/
theorem factorMatchedFactorMatchingQuotientScalar_one
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : FactorMatchedRestrictionGroupData T U e)
    (h : R.FactorMatchedQuotientFactorCohomologyAgreement S g) :
    R.factorMatchedFactorMatchingQuotientScalar S g h 1 = 1 := by
  have heq :=
    congrArg
      (fun alpha :
        FactorSet (B ⧸ U.normalSubgroup) ℂˣ ↦
          alpha 1 1)
      (R.factorMatchedQuotientFactorSetAlong_eq_gauge S g h)
  rw [R.factorMatchedQuotientFactorSetAlong_isNormalized g |>.1 1,
    FactorSet.gauge_apply,
    S.quotientFactorSet_isNormalized.1 1] at heq
  simpa using heq.symm

/-- Gauge the right associated lift by the quotient cochain. -/
def factorMatchedRightAssociatedFromQuotientCohomology
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : FactorMatchedRestrictionGroupData T U e)
    (h : R.FactorMatchedQuotientFactorCohomologyAgreement S g) :
    AssociatedProjectiveRepresentation U W
      (Q.rescale
        (quotientScalar
          (R.factorMatchedFactorMatchingQuotientScalar S g h))) :=
  S.rescaleByQuotientScalar
    (R.factorMatchedFactorMatchingQuotientScalar S g h)
    (R.factorMatchedFactorMatchingQuotientScalar_one S g h)

/-- The quotient gauge makes the ambient factors agree literally along
the embedding. -/
theorem factorMatchedRightAssociatedFromQuotientCohomology_factor_agreement
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : FactorMatchedRestrictionGroupData T U e)
    (h : R.FactorMatchedQuotientFactorCohomologyAgreement S g)
    (b c : B) :
    P.factor (e b) (e c) =
      (Q.rescale
        (quotientScalar
          (R.factorMatchedFactorMatchingQuotientScalar S g h))
        ).factor b c := by
  calc
    P.factor (e b) (e c) =
        R.factorMatchedQuotientFactorSetAlong g
          (QuotientGroup.mk' U.normalSubgroup b)
          (QuotientGroup.mk' U.normalSubgroup c) :=
      (R.factorMatchedQuotientFactorSetAlong_mk g b c).symm
    _ =
        S.quotientFactorSet.gauge
          (R.factorMatchedFactorMatchingQuotientScalar S g h)
          (QuotientGroup.mk' U.normalSubgroup b)
          (QuotientGroup.mk' U.normalSubgroup c) := by
      rw [R.factorMatchedQuotientFactorSetAlong_eq_gauge S g h]
    _ =
        (Q.rescale
          (quotientScalar
            (R.factorMatchedFactorMatchingQuotientScalar S g h))
          ).factor b c := by
      rw [FactorSet.gauge_apply,
        ProjectiveRepresentation.rescale_factor,
        S.quotientFactorSet_mk]
      rfl

end AssociatedProjectiveRepresentation
end CharacterTriple

namespace InductiveMcKay

open CharacterTriple

variable {A B : Type}
variable [Finite A] [Group A] [Finite B] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {e : B →* A}
variable {V W : Type}
variable [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W]
  [Module.Finite ℂ W] [Nontrivial W]
variable {P : ProjectiveRepresentation ℂ A V}
variable {Q : ProjectiveRepresentation ℂ B W}

/-- Quotient `H²` agreement produces the literal factor-matched
projective data, using only the three ordinary group conditions. -/
def completeFactorMatchedProjectiveComparisonDataOfFactorMatchedQuotientH2
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : FactorMatchedRestrictionGroupData T U e)
    (h : R.FactorMatchedQuotientFactorH2ClassAgreement S g) :
    CompleteFactorMatchedProjectiveComparisonData T U e := by
  let hc :=
    R.factorMatchedQuotientFactorCohomologyAgreement_of_h2Class
      S g h
  exact
    { leftSpace := V
      rightSpace := W
      leftProjective := P
      leftAssociated := R
      rightProjective :=
        Q.rescale
          (AssociatedProjectiveRepresentation.quotientScalar
            (R.factorMatchedFactorMatchingQuotientScalar S g hc))
      rightAssociated :=
        R.factorMatchedRightAssociatedFromQuotientCohomology S g hc
      factor_agreement :=
        R.factorMatchedRightAssociatedFromQuotientCohomology_factor_agreement
          S g hc }

end InductiveMcKay

/-! ## The Okuyama--Wajima quotient residue -/

variable {A : Type} [Group A] [Finite A]
variable {p : ℕ} [Fact p.Prime]
variable (K Q U : Subgroup A) [K.Normal]

/-- The intrinsic quotient-factor residue for the two canonical
Okuyama--Wajima triples.  It is stated using the canonical associated
projective lifts, but independence of associated lifts follows from the
usual quotient-factor uniqueness theorem. -/
def InvariantOkuyamaWajimaQuotientResidueAgreement
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (hCU : coprimeFixedPoints K Q ≤ U)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) : Prop :=
  let source :=
    invariantOkuyamaWajimaSourceTriple
      K Q U theta hinvariant
  let target :=
    invariantOkuyamaWajimaTargetTriple
      K Q U hU hCU d theta hinvariant
  let groupData :=
    invariantOkuyamaWajimaFactorMatchedGroupData
      K Q U hQ hK hU hCU d theta hinvariant
  (AssociatedGeneralExistence.associated source
    ).FactorMatchedQuotientFactorH2ClassAgreement
      (AssociatedGeneralExistence.associated target)
      groupData

/-- The quotient mismatch class itself, stated as a vanishing condition.
This is the precise residue which inflation to the external acting group
can fail to detect. -/
def InvariantOkuyamaWajimaQuotientResidueFactorIsSplit
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (hCU : coprimeFixedPoints K Q ≤ U)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) : Prop :=
  let source :=
    invariantOkuyamaWajimaSourceTriple
      K Q U theta hinvariant
  let target :=
    invariantOkuyamaWajimaTargetTriple
      K Q U hU hCU d theta hinvariant
  let groupData :=
    invariantOkuyamaWajimaFactorMatchedGroupData
      K Q U hQ hK hU hCU d theta hinvariant
  let R := AssociatedGeneralExistence.associated source
  let S := AssociatedGeneralExistence.associated target
  letI :=
    trivialMulDistribMulAction
      (U ⧸ target.normalSubgroup) ℂˣ
  (R.factorMatchedQuotientMismatchFactorSet S groupData).h2Class =
    0

/-- The split-residue and equality formulations are definitionally tied by
the factor-set `H²` group law. -/
theorem invariantOkuyamaWajimaQuotientResidueFactorIsSplit_iff_agreement
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (hCU : coprimeFixedPoints K Q ≤ U)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) :
    InvariantOkuyamaWajimaQuotientResidueFactorIsSplit
        K Q U hQ hK hU hCU d theta hinvariant ↔
      InvariantOkuyamaWajimaQuotientResidueAgreement
        K Q U hQ hK hU hCU d theta hinvariant := by
  exact
    AssociatedProjectiveRepresentation.factorMatchedQuotientMismatchFactorSet_h2Class_eq_zero_iff
      (AssociatedGeneralExistence.associated
        (invariantOkuyamaWajimaSourceTriple
          K Q U theta hinvariant))
      (AssociatedGeneralExistence.associated
        (invariantOkuyamaWajimaTargetTriple
          K Q U hU hCU d theta hinvariant))
      (invariantOkuyamaWajimaFactorMatchedGroupData
        K Q U hQ hK hU hCU d theta hinvariant)

/-- Quotient-residue agreement constructs the factor-matching input by an
explicit quotient-cochain gauge correction. -/
theorem invariantOkuyamaWajimaFactorMatchingInput_of_quotientResidueAgreement
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (hCU : coprimeFixedPoints K Q ≤ U)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hresidue :
      InvariantOkuyamaWajimaQuotientResidueAgreement
        K Q U hQ hK hU hCU d theta hinvariant) :
    invariantOkuyamaWajimaFactorMatchingInput
      K Q U hU hCU d theta hinvariant := by
  let source :=
    invariantOkuyamaWajimaSourceTriple
      K Q U theta hinvariant
  let target :=
    invariantOkuyamaWajimaTargetTriple
      K Q U hU hCU d theta hinvariant
  let groupData :=
    invariantOkuyamaWajimaFactorMatchedGroupData
      K Q U hQ hK hU hCU d theta hinvariant
  refine ⟨?_⟩
  exact
    InductiveMcKay.completeFactorMatchedProjectiveComparisonDataOfFactorMatchedQuotientH2
      (AssociatedGeneralExistence.associated source)
      (AssociatedGeneralExistence.associated target)
      groupData hresidue

/-- The split quotient mismatch is sufficient for factor matching. -/
theorem invariantOkuyamaWajimaFactorMatchingInput_of_quotientResidueFactorIsSplit
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (hCU : coprimeFixedPoints K Q ≤ U)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hsplit :
      InvariantOkuyamaWajimaQuotientResidueFactorIsSplit
        K Q U hQ hK hU hCU d theta hinvariant) :
    invariantOkuyamaWajimaFactorMatchingInput
      K Q U hU hCU d theta hinvariant :=
  invariantOkuyamaWajimaFactorMatchingInput_of_quotientResidueAgreement
    K Q U hQ hK hU hCU d theta hinvariant
    ((invariantOkuyamaWajimaQuotientResidueFactorIsSplit_iff_agreement
      K Q U hQ hK hU hCU d theta hinvariant).mp hsplit)

/-- The quotient residue is exactly sufficient for the extension
equivalence; literal factor equality is constructed rather than assumed. -/
theorem okuyamaWajimaExtensionConclusion_of_quotientResidueAgreement
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (hCU : coprimeFixedPoints K Q ≤ U)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hresidue :
      InvariantOkuyamaWajimaQuotientResidueAgreement
        K Q U hQ hK hU hCU d theta hinvariant) :
    okuyamaWajimaExtensionConclusion
      K Q U hCU d theta :=
  okuyamaWajimaExtensionConclusion_of_factorMatching
    K Q U hQ hK hU hCU d theta hinvariant
    (invariantOkuyamaWajimaFactorMatchingInput_of_quotientResidueAgreement
      K Q U hQ hK hU hCU d theta hinvariant hresidue)

/-- Equivalent split-factor form of the quotient-residue criterion. -/
theorem okuyamaWajimaExtensionConclusion_of_quotientResidueFactorIsSplit
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (hCU : coprimeFixedPoints K Q ≤ U)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hsplit :
      InvariantOkuyamaWajimaQuotientResidueFactorIsSplit
        K Q U hQ hK hU hCU d theta hinvariant) :
    okuyamaWajimaExtensionConclusion
      K Q U hCU d theta :=
  okuyamaWajimaExtensionConclusion_of_quotientResidueAgreement
    K Q U hQ hK hU hCU d theta hinvariant
    ((invariantOkuyamaWajimaQuotientResidueFactorIsSplit_iff_agreement
      K Q U hQ hK hU hCU d theta hinvariant).mp hsplit)

/-! ## From the retained factor to the precise descent boundary -/

/-- Splitting the retained prime-to-`p` coefficient factor kills the
canonical external multiplicity mismatch class. -/
theorem okuyamaWajimaPrintedProjectiveMultiplicityFactorSet_h2Class_eq_zero_of_primeToPFactor
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hsplit :
      InvariantOkuyamaWajimaPrintedMultiplicityPrimeToPFactorIsSplit
        K Q U hU d theta hinvariant) :
    letI := trivialMulDistribMulAction U ℂˣ
    (GlaubermanCorrespondence.ProjectiveMultiplicityFactorSet
      (okuyamaWajimaKernelConjugationAction K U)
      (okuyamaWajimaFixedPointConjugationAction K Q U hU)
      d theta
      (okuyamaWajimaKernelConjugationAction_invariant
        K Q U theta hinvariant)
      (okuyamaWajimaFixedPointConjugationAction_invariant
        K Q U hU d theta hinvariant)).h2Class =
      0 := by
  exact
    okuyamaWajimaPrintedProjectiveMultiplicityFactorSet_h2Class_eq_zero
      K Q U hU d theta hinvariant
      (invariantOkuyamaWajimaPrintedProjectiveMultiplicityPPrimary_of_primeToPFactor
        K Q U hU d theta hinvariant hsplit)

/-- The exact external-to-quotient descent statement left after the
retained coefficient factor has been split.

The premise is the vanishing external mismatch on `U`; the conclusion is
the quotient obstruction agreement on `U / C_K(Q)`.  This implication is
not formal group-cohomology bookkeeping: it rules out the kernel of
inflation and is therefore recorded as a mathematical input. -/
def InvariantOkuyamaWajimaExternalToQuotientResidueTransfer
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (hCU : coprimeFixedPoints K Q ≤ U)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) : Prop :=
  (letI := trivialMulDistribMulAction U ℂˣ
    ;
    (GlaubermanCorrespondence.ProjectiveMultiplicityFactorSet
      (okuyamaWajimaKernelConjugationAction K U)
      (okuyamaWajimaFixedPointConjugationAction K Q U hU)
      d theta
      (okuyamaWajimaKernelConjugationAction_invariant
        K Q U theta hinvariant)
      (okuyamaWajimaFixedPointConjugationAction_invariant
        K Q U hU d theta hinvariant)).h2Class =
      0) →
    InvariantOkuyamaWajimaQuotientResidueFactorIsSplit
      K Q U hQ hK hU hCU d theta hinvariant

/-- The `p`-primary multiplicity seam plus external-to-quotient transfer
already gives the extension conclusion. -/
theorem okuyamaWajimaExtensionConclusion_of_projectiveMultiplicityPPrimary_and_residueTransfer
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (hCU : coprimeFixedPoints K Q ≤ U)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hprimary :
      InvariantOkuyamaWajimaPrintedProjectiveMultiplicityPPrimary
        K Q U hU d theta hinvariant)
    (htransfer :
      InvariantOkuyamaWajimaExternalToQuotientResidueTransfer
        K Q U hQ hK hU hCU d theta hinvariant) :
    okuyamaWajimaExtensionConclusion
      K Q U hCU d theta :=
  okuyamaWajimaExtensionConclusion_of_quotientResidueFactorIsSplit
    K Q U hQ hK hU hCU d theta hinvariant
    (htransfer
      (okuyamaWajimaPrintedProjectiveMultiplicityFactorSet_h2Class_eq_zero
        K Q U hU d theta hinvariant hprimary))

/-- A split retained factor plus the exact external-to-quotient transfer
gives the Okuyama--Wajima extension conclusion. -/
theorem okuyamaWajimaExtensionConclusion_of_primeToPFactor_and_residueTransfer
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (hCU : coprimeFixedPoints K Q ≤ U)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hsplit :
      InvariantOkuyamaWajimaPrintedMultiplicityPrimeToPFactorIsSplit
        K Q U hU d theta hinvariant)
    (htransfer :
      InvariantOkuyamaWajimaExternalToQuotientResidueTransfer
        K Q U hQ hK hU hCU d theta hinvariant) :
    okuyamaWajimaExtensionConclusion
      K Q U hCU d theta :=
  okuyamaWajimaExtensionConclusion_of_projectiveMultiplicityPPrimary_and_residueTransfer
    K Q U hQ hK hU hCU d theta hinvariant
    (invariantOkuyamaWajimaPrintedProjectiveMultiplicityPPrimary_of_primeToPFactor
      K Q U hU d theta hinvariant hsplit)
    htransfer

/-! ## The printed local scopes -/

/-- Retained prime-to-`p` splitting on every printed local scope. -/
def InvariantOkuyamaWajimaPrintedPrimeToPFactorSplitInput
    (_hQ : IsPGroup p Q)
    (_hK : IsPPrimeGroup p K)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) : Prop :=
  ∀ (W : Subgroup A)
      (_hCW : coprimeFixedPoints K Q ≤ W)
      (scope :
        InvariantOkuyamaWajimaPrintedLocalScope
          (p := p) K Q W),
    InvariantOkuyamaWajimaPrintedMultiplicityPrimeToPFactorIsSplit
      K Q (Q ⊔ W) scope.sup_le_normalizer
      d theta hinvariant

/-- The remaining external-to-quotient transfer on every printed local
scope. -/
def InvariantOkuyamaWajimaPrintedExternalToQuotientResidueTransferInput
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) : Prop :=
  ∀ (W : Subgroup A)
      (hCW : coprimeFixedPoints K Q ≤ W)
      (scope :
        InvariantOkuyamaWajimaPrintedLocalScope
          (p := p) K Q W),
    InvariantOkuyamaWajimaExternalToQuotientResidueTransfer
      K Q (Q ⊔ W) hQ hK
      scope.sup_le_normalizer
      (hCW.trans le_sup_right)
      d theta hinvariant

/-- The retained prime-to-`p` split yields the full printed extension input
once the exact external-to-quotient residue transfer is supplied locally.
All literal factor matching is produced by quotient-cochain gauge
correction. -/
theorem invariantOkuyamaWajimaPrintedExtensionTheoremInput_of_primeToPFactor_and_residueTransfer
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hsplit :
      InvariantOkuyamaWajimaPrintedPrimeToPFactorSplitInput
        K Q hQ hK d theta hinvariant)
    (htransfer :
      InvariantOkuyamaWajimaPrintedExternalToQuotientResidueTransferInput
        K Q hQ hK d theta hinvariant) :
    InvariantOkuyamaWajimaPrintedExtensionTheoremInput
      K Q hQ hK d theta hinvariant := by
  intro W hCW scope
  exact
    okuyamaWajimaExtensionConclusion_of_primeToPFactor_and_residueTransfer
      K Q (Q ⊔ W) hQ hK
      scope.sup_le_normalizer
      (hCW.trans le_sup_right)
      d theta hinvariant
      (hsplit W hCW scope)
      (htransfer W hCW scope)

/-- A shorter direct interface: quotient-residue agreement on every local
scope already gives the printed extension input. -/
theorem invariantOkuyamaWajimaPrintedExtensionTheoremInput_of_quotientResidueAgreement
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hresidue :
      ∀ (W : Subgroup A)
          (hCW : coprimeFixedPoints K Q ≤ W)
          (scope :
            InvariantOkuyamaWajimaPrintedLocalScope
              (p := p) K Q W),
        InvariantOkuyamaWajimaQuotientResidueAgreement
          K Q (Q ⊔ W) hQ hK
          scope.sup_le_normalizer
          (hCW.trans le_sup_right)
          d theta hinvariant) :
    InvariantOkuyamaWajimaPrintedExtensionTheoremInput
      K Q hQ hK d theta hinvariant := by
  intro W hCW scope
  exact
    okuyamaWajimaExtensionConclusion_of_quotientResidueAgreement
      K Q (Q ⊔ W) hQ hK
      scope.sup_le_normalizer
      (hCW.trans le_sup_right)
      d theta hinvariant
      (hresidue W hCW scope)

end McKayConjecture
