/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanActionStrong
import McKayConjecture.Character.GlaubermanActionTransitivity

/-!
# Transitivity of strong action-level Glauberman correspondences

Full multiplicity uniqueness removes any need to know separately that all
intermediate irreducible character degrees are prime to `p`.  In the
transitivity sum, every intermediate character other than the selected
`Q`-correspondent contributes a multiple of `p`; conversely, a sum prime to
`p` contains a term which both strong correspondences identify uniquely.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture

open CliffordCorrespondence

variable (P A : Type) [Group P] [Group A]
variable [MulDistribMulAction P A]
variable [Finite P] [Finite A]
variable (Q : Subgroup P) [Q.Normal]
variable {p : ℕ} [Fact p.Prime]

private noncomputable local instance :
    Fintype (IrreducibleCharacter
      (FixedPoints.subgroup Q A)) :=
  Fintype.ofFinite _

/-- The two-stage character equivalence underlying strong transitivity. -/
def strongIteratedGlaubermanCharacterEquiv
    (dQ : StrongActionGlaubermanCorrespondence Q A p)
    (dQuot :
      StrongActionGlaubermanCorrespondence
        (P ⧸ Q) (FixedPoints.subgroup Q A) p) :
    ActionInvariantPPrimeIrreducibleCharacter P A p ≃
      PPrimeIrreducibleCharacter
        (FixedPoints.subgroup P A) p :=
  iteratedGlaubermanCharacterEquiv
    P A Q dQ.toAction dQuot.toAction

/-- The two-stage selected character has restriction multiplicity prime
to `p`. -/
theorem strongIteratedGlaubermanCharacterEquiv_multiplicity_isPPrime
    (dQ : StrongActionGlaubermanCorrespondence Q A p)
    (dQuot :
      StrongActionGlaubermanCorrespondence
        (P ⧸ Q) (FixedPoints.subgroup Q A) p)
    (θ : ActionInvariantPPrimeIrreducibleCharacter P A p) :
    ¬p ∣
      restrictionMultiplicity
        (actionFixedPointsInclusion P A)
        (strongIteratedGlaubermanCharacterEquiv
          P A Q dQ dQuot θ).1
        θ.1.1 := by
  classical
  let θQ :=
    actionInvariantCharacterOfSubgroup P A Q θ
  let ηQ :=
    quotientInvariantCorrespondent
      P A Q dQ.toAction θ
  let ξ :=
    dQuot.characterEquiv ηQ
  change
    ¬p ∣
      restrictionMultiplicity
        (actionFixedPointsInclusion P A)
        (ξ.1.comap
          (GroupTheory.iteratedFixedPointsEquiv
            P A Q).symm)
        θ.1.1
  rw [restrictionMultiplicity_iteratedFixedPoints_sum P A Q]
  apply
    not_dvd_sum_mul_of_unique
      (Fact.out : p.Prime)
      Finset.univ
      (fun η ↦
        restrictionMultiplicity
          (actionFixedPointsInclusion
            (P ⧸ Q) (FixedPoints.subgroup Q A))
          ξ.1 η)
      (fun η ↦
        restrictionMultiplicity
          (actionFixedPointsInclusion Q A)
          η θ.1.1)
      (i := ηQ.1.1)
      (Finset.mem_univ _)
      (dQuot.multiplicity_isPPrime ηQ)
      (dQ.multiplicity_isPPrime θQ)
  intro η _ hη
  right
  apply dQ.multiplicity_dvd_of_ne θQ η
  intro heq
  apply hη
  calc
    η = (dQ.characterEquiv θQ).1 := heq
    _ = ηQ.1.1 := by rfl

/-- Full multiplicity uniqueness is preserved by the two-stage
construction. -/
theorem eq_strongIteratedGlaubermanCharacterEquiv_of_multiplicity_isPPrime
    (dQ : StrongActionGlaubermanCorrespondence Q A p)
    (dQuot :
      StrongActionGlaubermanCorrespondence
        (P ⧸ Q) (FixedPoints.subgroup Q A) p)
    (θ : ActionInvariantPPrimeIrreducibleCharacter P A p)
    (φ : IrreducibleCharacter
      (FixedPoints.subgroup P A))
    (hφ :
      ¬p ∣
        restrictionMultiplicity
          (actionFixedPointsInclusion P A)
          φ θ.1.1) :
    φ =
      (strongIteratedGlaubermanCharacterEquiv
        P A Q dQ dQuot θ).1 := by
  classical
  let e :=
    GroupTheory.iteratedFixedPointsEquiv P A Q
  let θQ :=
    actionInvariantCharacterOfSubgroup P A Q θ
  let ηQ :=
    quotientInvariantCorrespondent
      P A Q dQ.toAction θ
  let ξ :
      IrreducibleCharacter
        (FixedPoints.subgroup (P ⧸ Q)
          (FixedPoints.subgroup Q A)) :=
    φ.comap e
  have hcomposite :
      ¬p ∣
        restrictionMultiplicity
          ((actionFixedPointsInclusion Q A).comp
            (actionFixedPointsInclusion
              (P ⧸ Q) (FixedPoints.subgroup Q A)))
          ξ θ.1.1 := by
    rw [← restrictionMultiplicity_iteratedFixedPoints
      P A Q]
    have hback :
        ξ.comap e.symm = φ := by
      change (φ.comap e).comap e.symm = φ
      simp
    rw [hback]
    exact hφ
  have hsum :
      ¬p ∣
        ∑ η :
            IrreducibleCharacter
              (FixedPoints.subgroup Q A),
          restrictionMultiplicity
              (actionFixedPointsInclusion
                (P ⧸ Q) (FixedPoints.subgroup Q A))
              ξ η *
            restrictionMultiplicity
              (actionFixedPointsInclusion Q A)
              η θ.1.1 := by
    rw [← restrictionMultiplicity_comp]
    exact hcomposite
  obtain ⟨η, -, hfirst, hsecond⟩ :=
    exists_not_dvd_both_of_not_dvd_sum_mul
      (Fact.out : p.Prime)
      Finset.univ
      (fun η ↦
        restrictionMultiplicity
          (actionFixedPointsInclusion
            (P ⧸ Q) (FixedPoints.subgroup Q A))
          ξ η)
      (fun η ↦
        restrictionMultiplicity
          (actionFixedPointsInclusion Q A)
          η θ.1.1)
      hsum
  have hη :
      η = (dQ.characterEquiv θQ).1 :=
    dQ.eq_correspondent_of_multiplicity_isPPrime
      θQ η hsecond
  have hfirst' :
      ¬p ∣
        restrictionMultiplicity
          (actionFixedPointsInclusion
            (P ⧸ Q) (FixedPoints.subgroup Q A))
          ξ ηQ.1.1 := by
    have hηQ :
        ηQ.1.1 = (dQ.characterEquiv θQ).1 := by
      rfl
    rw [hηQ, ← hη]
    exact hfirst
  have hξ :
      ξ = (dQuot.characterEquiv ηQ).1 :=
    dQuot.eq_correspondent_of_multiplicity_isPPrime
      ηQ ξ hfirst'
  calc
    φ = ξ.comap e.symm := by
      change φ = (φ.comap e).comap e.symm
      simp
    _ =
        (dQuot.characterEquiv ηQ).1.comap e.symm :=
      congrArg
        (fun χ : IrreducibleCharacter
          (FixedPoints.subgroup (P ⧸ Q)
            (FixedPoints.subgroup Q A)) ↦
          χ.comap e.symm)
        hξ
    _ =
        (strongIteratedGlaubermanCharacterEquiv
          P A Q dQ dQuot θ).1 := by
      rfl

/-- Strong Glauberman correspondences are transitive along a normal
subgroup of the acting group. -/
def StrongActionGlaubermanCorrespondence.transitive
    (dQ : StrongActionGlaubermanCorrespondence Q A p)
    (dQuot :
      StrongActionGlaubermanCorrespondence
        (P ⧸ Q) (FixedPoints.subgroup Q A) p) :
    StrongActionGlaubermanCorrespondence P A p where
  characterEquiv :=
    strongIteratedGlaubermanCharacterEquiv
      P A Q dQ dQuot
  multiplicity_isPPrime :=
    strongIteratedGlaubermanCharacterEquiv_multiplicity_isPPrime
      P A Q dQ dQuot
  eq_correspondent_of_multiplicity_isPPrime :=
    eq_strongIteratedGlaubermanCharacterEquiv_of_multiplicity_isPPrime
      P A Q dQ dQuot

end McKayConjecture
