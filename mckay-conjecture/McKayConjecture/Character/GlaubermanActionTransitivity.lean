/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanActionEquivariance
import McKayConjecture.Character.PPrimeMultiplicitySum
import McKayConjecture.Character.RestrictionMultiplicityTransitivity
import McKayConjecture.GroupTheory.IteratedFixedPoints

/-!
# Transitivity of the action-level Glauberman correspondence

Let `Q ◁ P` act on `A`.  A Glauberman correspondence for the action of
`Q` and one for the induced action of `P / Q` compose to a correspondence
for `P`.  The proof uses the exact transitivity formula for restriction
multiplicities.  The hypothesis that every irreducible character of `A^Q`
has `p'`-degree is the form needed in the coprime-action application, where
`A` (and hence `A^Q`) is a `p'`-group.
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

/-- The two-stage character bijection, with the iterated fixed-point group
transported to `A^P` through its canonical group equivalence. -/
def iteratedGlaubermanCharacterEquiv
    (dQ : ActionGlaubermanCorrespondence Q A p)
    (dQuot :
      ActionGlaubermanCorrespondence
        (P ⧸ Q) (FixedPoints.subgroup Q A) p) :
    ActionInvariantPPrimeIrreducibleCharacter P A p ≃
      PPrimeIrreducibleCharacter
        (FixedPoints.subgroup P A) p :=
  (invariantCharacterEquivQuotientInvariantCorrespondent
      P A Q dQ).trans
    (dQuot.characterEquiv.trans
      (IrreducibleCharacter.pPrimeComapEquiv p
        (GroupTheory.iteratedFixedPointsEquiv
          P A Q).symm))

/-- The composite of the two fixed-point inclusions is the inclusion of
`A^P`, after applying the canonical equivalence from iterated fixed points. -/
theorem iteratedFixedPointsInclusion_commutes :
    (actionFixedPointsInclusion Q A).comp
        (actionFixedPointsInclusion
          (P ⧸ Q) (FixedPoints.subgroup Q A)) =
      (actionFixedPointsInclusion P A).comp
        (GroupTheory.iteratedFixedPointsEquiv
          P A Q).toMonoidHom := by
  ext x
  rfl

/-- Restriction multiplicity along `A^P ↪ A` agrees with restriction
through `A^Q` after transporting the iterated fixed-point group. -/
theorem restrictionMultiplicity_iteratedFixedPoints
    (ξ :
      IrreducibleCharacter
        (FixedPoints.subgroup (P ⧸ Q)
          (FixedPoints.subgroup Q A)))
    (θ : IrreducibleCharacter A) :
    restrictionMultiplicity
        (actionFixedPointsInclusion P A)
        (ξ.comap
          (GroupTheory.iteratedFixedPointsEquiv
            P A Q).symm)
        θ =
      restrictionMultiplicity
        ((actionFixedPointsInclusion Q A).comp
          (actionFixedPointsInclusion
            (P ⧸ Q) (FixedPoints.subgroup Q A)))
        ξ θ := by
  let e :=
    GroupTheory.iteratedFixedPointsEquiv P A Q
  have h :=
    restrictionMultiplicity_comap_equiv
      (MulEquiv.refl A) e
      (actionFixedPointsInclusion P A)
      ((actionFixedPointsInclusion Q A).comp
        (actionFixedPointsInclusion
          (P ⧸ Q) (FixedPoints.subgroup Q A)))
      (iteratedFixedPointsInclusion_commutes P A Q).symm
      (ξ.comap e.symm) θ
  simpa [e] using h.symm

/-- The multiplicity for restriction to `A^P` is the sum of products of
the two successive restriction multiplicities through `A^Q`. -/
theorem restrictionMultiplicity_iteratedFixedPoints_sum
    (ξ :
      IrreducibleCharacter
        (FixedPoints.subgroup (P ⧸ Q)
          (FixedPoints.subgroup Q A)))
    (θ : IrreducibleCharacter A) :
    restrictionMultiplicity
        (actionFixedPointsInclusion P A)
        (ξ.comap
          (GroupTheory.iteratedFixedPointsEquiv
            P A Q).symm)
        θ =
      ∑ η :
          IrreducibleCharacter
            (FixedPoints.subgroup Q A),
        restrictionMultiplicity
            (actionFixedPointsInclusion
              (P ⧸ Q) (FixedPoints.subgroup Q A))
            ξ η *
          restrictionMultiplicity
            (actionFixedPointsInclusion Q A)
            η θ := by
  rw [restrictionMultiplicity_iteratedFixedPoints P A Q]
  exact
    restrictionMultiplicity_comp
      (actionFixedPointsInclusion Q A)
      (actionFixedPointsInclusion
        (P ⧸ Q) (FixedPoints.subgroup Q A))
      ξ θ

/-- The composed character bijection has prime-to-`p` restriction
multiplicity. -/
theorem iteratedGlaubermanCharacterEquiv_multiplicity_isPPrime
    (dQ : ActionGlaubermanCorrespondence Q A p)
    (dQuot :
      ActionGlaubermanCorrespondence
        (P ⧸ Q) (FixedPoints.subgroup Q A) p)
    (hallPPrime :
      ∀ η :
        IrreducibleCharacter
          (FixedPoints.subgroup Q A),
        η.IsPPrimeDegree p)
    (θ : ActionInvariantPPrimeIrreducibleCharacter P A p) :
    ¬p ∣
      restrictionMultiplicity
        (actionFixedPointsInclusion P A)
        (iteratedGlaubermanCharacterEquiv
          P A Q dQ dQuot θ).1
        θ.1.1 := by
  classical
  let θQ :=
    actionInvariantCharacterOfSubgroup P A Q θ
  let ηQ :=
    quotientInvariantCorrespondent P A Q dQ θ
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
  by_contra hprime
  let η' :
      PPrimeIrreducibleCharacter
        (FixedPoints.subgroup Q A) p :=
    ⟨η, hallPPrime η⟩
  have heq :
      η' = dQ.characterEquiv θQ :=
    dQ.eq_correspondent_of_multiplicity_isPPrime
      θQ η' hprime
  apply hη
  simpa [η', ηQ] using congrArg Subtype.val heq

/-- Prime-to-`p` restriction multiplicity uniquely determines the output
of the composed character bijection. -/
theorem eq_iteratedGlaubermanCharacterEquiv_of_multiplicity_isPPrime
    (dQ : ActionGlaubermanCorrespondence Q A p)
    (dQuot :
      ActionGlaubermanCorrespondence
        (P ⧸ Q) (FixedPoints.subgroup Q A) p)
    (hallPPrime :
      ∀ η :
        IrreducibleCharacter
          (FixedPoints.subgroup Q A),
        η.IsPPrimeDegree p)
    (θ : ActionInvariantPPrimeIrreducibleCharacter P A p)
    (φ :
      PPrimeIrreducibleCharacter
        (FixedPoints.subgroup P A) p)
    (hφ :
      ¬p ∣
        restrictionMultiplicity
          (actionFixedPointsInclusion P A)
          φ.1 θ.1.1) :
    φ =
      iteratedGlaubermanCharacterEquiv
        P A Q dQ dQuot θ := by
  classical
  let e :=
    GroupTheory.iteratedFixedPointsEquiv P A Q
  let θQ :=
    actionInvariantCharacterOfSubgroup P A Q θ
  let ηQ :=
    quotientInvariantCorrespondent P A Q dQ θ
  let ξ :
      PPrimeIrreducibleCharacter
        (FixedPoints.subgroup (P ⧸ Q)
          (FixedPoints.subgroup Q A)) p :=
    IrreducibleCharacter.pPrimeComapEquiv p e φ
  have hcomposite :
      ¬p ∣
        restrictionMultiplicity
          ((actionFixedPointsInclusion Q A).comp
            (actionFixedPointsInclusion
              (P ⧸ Q) (FixedPoints.subgroup Q A)))
          ξ.1 θ.1.1 := by
    rw [← restrictionMultiplicity_iteratedFixedPoints
      P A Q]
    have hback :
        ξ.1.comap e.symm = φ.1 := by
      change (φ.1.comap e).comap e.symm = φ.1
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
              ξ.1 η *
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
          ξ.1 η)
      (fun η ↦
        restrictionMultiplicity
          (actionFixedPointsInclusion Q A)
          η θ.1.1)
      hsum
  let η' :
      PPrimeIrreducibleCharacter
        (FixedPoints.subgroup Q A) p :=
    ⟨η, hallPPrime η⟩
  have hη :
      η' = dQ.characterEquiv θQ :=
    dQ.eq_correspondent_of_multiplicity_isPPrime
      θQ η' hsecond
  have hηval :
      η = ηQ.1.1 := by
    simpa [η', ηQ] using
      congrArg Subtype.val hη
  have hfirst' :
      ¬p ∣
        restrictionMultiplicity
          (actionFixedPointsInclusion
            (P ⧸ Q) (FixedPoints.subgroup Q A))
          ξ.1 ηQ.1.1 := by
    rw [← hηval]
    exact hfirst
  have hξ :
      ξ = dQuot.characterEquiv ηQ :=
    dQuot.eq_correspondent_of_multiplicity_isPPrime
      ηQ ξ hfirst'
  calc
    φ =
        (IrreducibleCharacter.pPrimeComapEquiv
          p e).symm ξ := by
      simpa [ξ] using
        ((IrreducibleCharacter.pPrimeComapEquiv
          p e).symm_apply_apply φ).symm
    _ =
        (IrreducibleCharacter.pPrimeComapEquiv
          p e).symm
          (dQuot.characterEquiv ηQ) :=
      congrArg
        (IrreducibleCharacter.pPrimeComapEquiv
          p e).symm hξ
    _ =
        iteratedGlaubermanCharacterEquiv
          P A Q dQ dQuot θ := by
      rfl

/-- Transitivity of the action-level Glauberman correspondence. -/
def ActionGlaubermanCorrespondence.transitive
    (dQ : ActionGlaubermanCorrespondence Q A p)
    (dQuot :
      ActionGlaubermanCorrespondence
        (P ⧸ Q) (FixedPoints.subgroup Q A) p)
    (hallPPrime :
      ∀ η :
        IrreducibleCharacter
          (FixedPoints.subgroup Q A),
        η.IsPPrimeDegree p) :
    ActionGlaubermanCorrespondence P A p where
  characterEquiv :=
    iteratedGlaubermanCharacterEquiv
      P A Q dQ dQuot
  multiplicity_isPPrime :=
    iteratedGlaubermanCharacterEquiv_multiplicity_isPPrime
      P A Q dQ dQuot hallPPrime
  eq_correspondent_of_multiplicity_isPPrime :=
    eq_iteratedGlaubermanCharacterEquiv_of_multiplicity_isPPrime
      P A Q dQ dQuot hallPPrime

end McKayConjecture
