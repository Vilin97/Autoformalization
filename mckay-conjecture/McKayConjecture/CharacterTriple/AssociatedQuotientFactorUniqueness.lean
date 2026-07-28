/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedUniqueness
import McKayConjecture.CharacterTriple.FactorSetCohomology
import McKayConjecture.CharacterTriple.FactorSetQuotient

/-!
# Intrinsic quotient factor class of a character triple

Two projective representations associated with the same character triple
have factor sets differing by a scalar gauge which is constant on normal
cosets.  Consequently that gauge descends to the outer quotient, where it
identifies the two quotient factor sets.

In particular, the class in `H²(A/N, ℂˣ)` represented by an associated
projective lift depends only on the character triple, not on the chosen
representation space or intertwining operators.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace AssociatedProjectiveRepresentation

variable {A : Type} [Finite A] [Group A]
variable {T : CharacterTriple A}
variable {V W : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]
variable {P : ProjectiveRepresentation ℂ A V}
variable {Q : ProjectiveRepresentation ℂ A W}

/-- The scalar comparing two associated lifts has the same value on any
two representatives of one outer quotient coset. -/
theorem gaugeScalar_eq_of_quotient_eq
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation T W Q)
    (E : Representation.Equiv
      (linearRepresentationOfAction R.restriction)
      (linearRepresentationOfAction S.restriction))
    {a b : A}
    (hab :
      QuotientGroup.mk' T.normalSubgroup a =
        QuotientGroup.mk' T.normalSubgroup b) :
    gaugeScalar R S E a =
      gaugeScalar R S E b := by
  obtain ⟨n, hn, han⟩ :=
    (QuotientGroup.mk'_eq_mk'
      (N := T.normalSubgroup)).mp hab
  let x : T.normalSubgroup := ⟨n, hn⟩
  calc
    gaugeScalar R S E a =
        gaugeScalar R S E (a * (x : A)) :=
      (gaugeScalar_mul_normal R S E a x).symm
    _ = gaugeScalar R S E b := by
      rw [han]

/-- The comparison gauge descended to the outer quotient. -/
def quotientGaugeScalar
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation T W Q) :
    (A ⧸ T.normalSubgroup) → ℂˣ :=
  let E := restrictionEquiv R S
  fun q ↦
    gaugeScalar R S E
      (ProjectiveRepresentation.quotientRepresentative
        T.normalSubgroup q)

/-- Evaluating the quotient gauge on a represented coset recovers the
ambient comparison scalar. -/
@[simp]
theorem quotientGaugeScalar_mk
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation T W Q)
    (a : A) :
    quotientGaugeScalar R S
        (QuotientGroup.mk' T.normalSubgroup a) =
      gaugeScalar R S (restrictionEquiv R S) a := by
  apply gaugeScalar_eq_of_quotient_eq R S (restrictionEquiv R S)
  exact
    ProjectiveRepresentation.mk_quotientRepresentative
      T.normalSubgroup
      (QuotientGroup.mk' T.normalSubgroup a)

/-- Quotient factor sets of two associated lifts of the same character
triple are related by the descended comparison gauge. -/
theorem quotientFactorSet_eq_gauge
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation T W Q) :
    R.quotientFactorSet =
      S.quotientFactorSet.gauge
        (quotientGaugeScalar R S) := by
  let E := restrictionEquiv R S
  let rep :=
    ProjectiveRepresentation.quotientRepresentative
      T.normalSubgroup
  apply FactorSet.ext
  intro q r
  change
    P.factor (rep q) (rep r) =
      gaugeScalar R S E (rep q) *
          gaugeScalar R S E (rep r) /
          gaugeScalar R S E (rep (q * r)) *
        Q.factor (rep q) (rep r)
  have hcoset :
      QuotientGroup.mk' T.normalSubgroup
          (rep q * rep r) =
        QuotientGroup.mk' T.normalSubgroup
          (rep (q * r)) := by
    rw [map_mul,
      ProjectiveRepresentation.mk_quotientRepresentative,
      ProjectiveRepresentation.mk_quotientRepresentative,
      ProjectiveRepresentation.mk_quotientRepresentative]
  have hgauge :
      gaugeScalar R S E (rep q * rep r) =
        gaugeScalar R S E (rep (q * r)) :=
    gaugeScalar_eq_of_quotient_eq R S E hcoset
  rw [← hgauge]
  simpa only [ProjectiveRepresentation.rescale_factor] using
    gauge_factor_eq R S E (rep q) (rep r)

/-- The quotient factor sets of any two associated lifts of the same
character triple are cohomologous. -/
theorem quotientFactorSet_cohomologous
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation T W Q) :
    S.quotientFactorSet.Cohomologous
      R.quotientFactorSet :=
  ⟨quotientGaugeScalar R S,
    quotientFactorSet_eq_gauge R S⟩

/-- The quotient factor class in second cohomology is independent of the
chosen associated projective lift. -/
theorem quotientFactorSet_h2Class_eq
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation T W Q) :
    letI :=
      trivialMulDistribMulAction
        (A ⧸ T.normalSubgroup) ℂˣ
    R.quotientFactorSet.h2Class =
      S.quotientFactorSet.h2Class := by
  exact
    FactorSet.h2Class_eq_of_cohomologous
      (FactorSet.cohomologous_symm
        (quotientFactorSet_cohomologous R S))

end AssociatedProjectiveRepresentation
end CharacterTriple
end McKayConjecture
