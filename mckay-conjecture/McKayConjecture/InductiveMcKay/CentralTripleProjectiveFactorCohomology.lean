/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedRescale
import McKayConjecture.CharacterTriple.AssociatedQuotientFactorUniqueness
import McKayConjecture.CharacterTriple.FactorSetCentralExtensionNormalizer
import McKayConjecture.CharacterTriple.FactorSetCohomology
import McKayConjecture.CharacterTriple.FactorSetQuotient
import McKayConjecture.InductiveMcKay.CentralTripleRestrictionWitness

/-!
# Literal factor matching from quotient-factor cohomology

The factor set of an associated projective representation descends to the
outer quotient of its character triple.  The ordinary group data in a
central restriction identifies the two outer quotients.

This file proves the exact cohomological reduction: if the right quotient
factor set and the transported left quotient factor set are cohomologous,
then a normalized quotient cochain rescales the right projective lift so
that the two factors agree literally along the embedding.  Because the
cochain lives on the quotient, the rescaled lift remains associated with
the same right character triple.

Thus generic existence of associated lifts does not itself solve factor
matching.  The missing mathematical claim is equality of these two
quotient-factor cohomology classes.
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

/-- The embedding maps the right normal subgroup into the left normal
subgroup. -/
theorem rightNormal_le_comap_leftNormal
    (g : CentralRestrictionGroupData T U e) :
    U.normalSubgroup ≤ T.normalSubgroup.comap e := by
  intro b hb
  have hmap :
      e b ∈ U.normalSubgroup.map e :=
    ⟨b, hb, rfl⟩
  rw [← g.intersection_eq] at hmap
  exact hmap.1

/-- Membership in the left normal subgroup is reflected by the embedding. -/
theorem mem_rightNormal_of_embedding_mem_leftNormal
    (g : CentralRestrictionGroupData T U e)
    {b : B} (hb : e b ∈ T.normalSubgroup) :
    b ∈ U.normalSubgroup := by
  have hinf :
      e b ∈
        T.normalSubgroup ⊓ MonoidHom.range e :=
    ⟨hb, ⟨b, rfl⟩⟩
  rw [g.intersection_eq] at hinf
  obtain ⟨m, hm, hme⟩ := hinf
  have hmb : m = b :=
    g.embedding_injective hme
  exact hmb ▸ hm

/-- The quotient homomorphism determined by the embedding. -/
def quotientHom
    (g : CentralRestrictionGroupData T U e) :
    B ⧸ U.normalSubgroup →*
      A ⧸ T.normalSubgroup :=
  QuotientGroup.map U.normalSubgroup T.normalSubgroup
    e g.rightNormal_le_comap_leftNormal

@[simp]
theorem quotientHom_mk
    (g : CentralRestrictionGroupData T U e)
    (b : B) :
    g.quotientHom
        (QuotientGroup.mk' U.normalSubgroup b) =
      QuotientGroup.mk' T.normalSubgroup (e b) :=
  rfl

/-- The intersection condition makes the quotient homomorphism injective. -/
theorem quotientHom_injective
    (g : CentralRestrictionGroupData T U e) :
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

/-- The normal-times-image decomposition makes the quotient homomorphism
surjective. -/
theorem quotientHom_surjective
    (g : CentralRestrictionGroupData T U e) :
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

/-- The canonical outer-quotient equivalence supplied by the ordinary
restriction-group data. -/
def quotientEquiv
    (g : CentralRestrictionGroupData T U e) :
    (B ⧸ U.normalSubgroup) ≃*
      (A ⧸ T.normalSubgroup) :=
  MulEquiv.ofBijective g.quotientHom
    ⟨g.quotientHom_injective,
      g.quotientHom_surjective⟩

@[simp]
theorem quotientEquiv_mk
    (g : CentralRestrictionGroupData T U e)
    (b : B) :
    g.quotientEquiv
        (QuotientGroup.mk' U.normalSubgroup b) =
      QuotientGroup.mk' T.normalSubgroup (e b) :=
  rfl

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

/-- The left quotient factor, transported to the right outer quotient. -/
def quotientFactorSetAlong
    (R : AssociatedProjectiveRepresentation T V P)
    (g : CentralRestrictionGroupData T U e) :
    FactorSet (B ⧸ U.normalSubgroup) ℂˣ :=
  R.quotientFactorSet.comap
    g.quotientEquiv.toMonoidHom

@[simp]
theorem quotientFactorSetAlong_mk
    (R : AssociatedProjectiveRepresentation T V P)
    (g : CentralRestrictionGroupData T U e)
    (b c : B) :
    R.quotientFactorSetAlong g
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

/-- The transported left quotient factor remains normalized. -/
theorem quotientFactorSetAlong_isNormalized
    (R : AssociatedProjectiveRepresentation T V P)
    (g : CentralRestrictionGroupData T U e) :
    (R.quotientFactorSetAlong g).IsNormalized :=
  FactorSet.comap_isNormalized
    R.quotientFactorSet
    g.quotientEquiv.toMonoidHom
    R.quotientFactorSet_isNormalized

/-- The precise cohomological factor-matching condition for two associated
lifts along a central restriction. -/
def QuotientFactorCohomologyAgreement
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e) : Prop :=
  S.quotientFactorSet.Cohomologous
    (R.quotientFactorSetAlong g)

/-- The same comparison stated as literal equality in mathlib's second
group-cohomology group. -/
def QuotientFactorH2ClassAgreement
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e) : Prop :=
  letI :=
    trivialMulDistribMulAction
      (B ⧸ U.normalSubgroup) ℂˣ
  S.quotientFactorSet.h2Class =
    (R.quotientFactorSetAlong g).h2Class

/-- Equality of the quotient-factor `H²` classes supplies the explicit
gauge cochain required by the factor-matching construction. -/
theorem quotientFactorCohomologyAgreement_of_h2Class
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (h : R.QuotientFactorH2ClassAgreement S g) :
    R.QuotientFactorCohomologyAgreement S g := by
  exact FactorSet.cohomologous_of_h2Class_eq h

/-- The explicit and `H²` formulations of quotient factor matching are
equivalent. -/
theorem quotientFactorCohomologyAgreement_iff_h2Class
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e) :
    R.QuotientFactorCohomologyAgreement S g ↔
      R.QuotientFactorH2ClassAgreement S g :=
  FactorSet.cohomologous_iff_h2Class_eq

/-- Quotient-factor agreement is intrinsic to the two character triples:
it is unchanged when either associated projective lift is replaced by any
other associated lift of the same triple. -/
theorem quotientFactorH2ClassAgreement_congr
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
    (g : CentralRestrictionGroupData T U e)
    (h : R.QuotientFactorH2ClassAgreement S g) :
    R'.QuotientFactorH2ClassAgreement S' g := by
  letI :=
    trivialMulDistribMulAction
      (B ⧸ U.normalSubgroup) ℂˣ
  have hright :
      S.quotientFactorSet.h2Class =
        S'.quotientFactorSet.h2Class :=
    FactorSet.h2Class_eq_of_cohomologous
      (S'.quotientFactorSet_cohomologous S)
  have hleftCohomologous :
      (R.quotientFactorSetAlong g).Cohomologous
        (R'.quotientFactorSetAlong g) := by
    exact
      FactorSet.comap_cohomologous
        (R'.quotientFactorSet_cohomologous R)
        g.quotientEquiv.toMonoidHom
  have hleft :
      (R.quotientFactorSetAlong g).h2Class =
        (R'.quotientFactorSetAlong g).h2Class :=
    FactorSet.h2Class_eq_of_cohomologous
      hleftCohomologous
  exact hright.symm.trans (h.trans hleft)

/-- A quotient cochain witnessing factor-class agreement. -/
def factorMatchingQuotientScalar
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (h : R.QuotientFactorCohomologyAgreement S g) :
    (B ⧸ U.normalSubgroup) → ℂˣ :=
  Classical.choose h

/-- The selected quotient cochain gauges the right factor to the transported
left factor. -/
theorem quotientFactorSetAlong_eq_gauge
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (h : R.QuotientFactorCohomologyAgreement S g) :
    R.quotientFactorSetAlong g =
      S.quotientFactorSet.gauge
        (R.factorMatchingQuotientScalar S g h) :=
  Classical.choose_spec h

/-- Normalization of both quotient factor sets forces the selected gauge
cochain to take the value one at the identity. -/
theorem factorMatchingQuotientScalar_one
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (h : R.QuotientFactorCohomologyAgreement S g) :
    R.factorMatchingQuotientScalar S g h 1 = 1 := by
  have heq :=
    congrArg
      (fun alpha :
        FactorSet (B ⧸ U.normalSubgroup) ℂˣ ↦
          alpha 1 1)
      (R.quotientFactorSetAlong_eq_gauge S g h)
  rw [R.quotientFactorSetAlong_isNormalized g |>.1 1,
    FactorSet.gauge_apply,
    S.quotientFactorSet_isNormalized.1 1] at heq
  simpa using heq.symm

/-- The right associated lift after the quotient-cochain correction. -/
def factorMatchedRightAssociated
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (h : R.QuotientFactorCohomologyAgreement S g) :
    AssociatedProjectiveRepresentation U W
      (Q.rescale
        (quotientScalar
          (R.factorMatchingQuotientScalar S g h))) :=
  S.rescaleByQuotientScalar
    (R.factorMatchingQuotientScalar S g h)
    (R.factorMatchingQuotientScalar_one S g h)

/-- The association-preserving quotient rescaling makes the two factors
agree literally along the embedding. -/
theorem factorMatchedRightAssociated_factor_agreement
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (h : R.QuotientFactorCohomologyAgreement S g)
    (b c : B) :
    P.factor (e b) (e c) =
      (Q.rescale
        (quotientScalar
          (R.factorMatchingQuotientScalar S g h))
        ).factor b c := by
  calc
    P.factor (e b) (e c) =
        R.quotientFactorSetAlong g
          (QuotientGroup.mk' U.normalSubgroup b)
          (QuotientGroup.mk' U.normalSubgroup c) :=
      (R.quotientFactorSetAlong_mk g b c).symm
    _ =
        S.quotientFactorSet.gauge
          (R.factorMatchingQuotientScalar S g h)
          (QuotientGroup.mk' U.normalSubgroup b)
          (QuotientGroup.mk' U.normalSubgroup c) := by
      rw [R.quotientFactorSetAlong_eq_gauge S g h]
    _ =
        (Q.rescale
          (quotientScalar
            (R.factorMatchingQuotientScalar S g h))
          ).factor b c := by
      rw [FactorSet.gauge_apply,
        ProjectiveRepresentation.rescale_factor,
        S.quotientFactorSet_mk]
      rfl

end AssociatedProjectiveRepresentation
end CharacterTriple

end McKayConjecture
