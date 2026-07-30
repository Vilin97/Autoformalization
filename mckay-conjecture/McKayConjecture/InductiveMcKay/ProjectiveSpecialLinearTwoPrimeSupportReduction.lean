/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.ProjectiveSpecialLinearTwoCardinality
import McKayConjecture.InductiveMcKay.UniversalCoverSimpleTargetPrimeSupport

/-!
# Exact prime-support branches for the simple PSL₂ family

For `PSL(2,q)`, a prime can occur only in one of the three standard
rank-one factors

`q`, `q - 1`, or `q + 1`.

This file turns that order calculation into an exact verification
interface.  First it removes parameters for which the prime does not divide
the simple target: the universal-cover Sylow subgroup is then central and
the canonical local datum applies.  It then splits the remaining
character-theoretic work into the defining-characteristic, split-torus,
and nonsplit-torus branches.

No local datum in any of the three relevant branches is asserted.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-! ### Removing unsupported primes -/

/-- Representative verification only at parameters whose simple target
order is divisible by `p`. -/
def ProjectiveSpecialLinearTwoPrimeSupportedRepresentativeVerification
    (p : ℕ) : Prop :=
  ∀ a : ProjectiveSpecialLinearTwoSimpleParameter,
    p ∣ Nat.card (projectiveSpecialLinearTwoRepresentative a) →
      ProjectiveSpecialLinearTwoRepresentativeVerification p a

/-- The unfiltered representative-family verification restricts to the
prime-supported parameters. -/
theorem
    ProjectiveSpecialLinearTwoRepresentativeFamilyVerification.toPrimeSupported
    {p : ℕ}
    (h : ProjectiveSpecialLinearTwoRepresentativeFamilyVerification p) :
    ProjectiveSpecialLinearTwoPrimeSupportedRepresentativeVerification p :=
  fun a _ ↦ h a

/-- A parameter outside the simple target's prime support is automatic.
This pointwise form is useful when another parameter split (for example,
the exceptional/generic cover split) has already been imposed. -/
theorem
    projectiveSpecialLinearTwoRepresentativeVerification_of_prime_not_dvd_card
    (p : ℕ) [Fact p.Prime]
    (a : ProjectiveSpecialLinearTwoSimpleParameter)
    (hp :
      ¬p ∣ Nat.card (projectiveSpecialLinearTwoRepresentative a)) :
    ProjectiveSpecialLinearTwoRepresentativeVerification p a := by
  obtain ⟨U, groupU, finiteU, ⟨E⟩⟩ :=
    finite_universalCentralExtension_exists_of_isSimpleGroup
      (projectiveSpecialLinearTwoRepresentative_isSimpleGroup a)
      (projectiveSpecialLinearTwoRepresentative_not_isMulCommutative a)
  letI : Group U := groupU
  letI : Finite U := finiteU
  let P : Sylow p U := default
  exact
    ⟨U, inferInstance, inferInstance, E, P,
      LocalInductiveMcKayData.nonempty_of_sylow_le_center
        P
        (CentralExtension.sylow_le_center_of_prime_not_dvd_card
          E.toCentralExtension P hp)⟩

/-- Prime-supported representative verification recovers the full
representative-family obligation.  At an unsupported parameter, choose a
finite universal central extension; its Sylow `p`-subgroup lies in the
center and therefore has the canonical local datum. -/
theorem
    ProjectiveSpecialLinearTwoPrimeSupportedRepresentativeVerification.toFull
    {p : ℕ} [Fact p.Prime]
    (h :
      ProjectiveSpecialLinearTwoPrimeSupportedRepresentativeVerification p) :
    ProjectiveSpecialLinearTwoRepresentativeFamilyVerification p := by
  intro a
  by_cases hp :
      p ∣ Nat.card (projectiveSpecialLinearTwoRepresentative a)
  · exact h a hp
  · exact
      projectiveSpecialLinearTwoRepresentativeVerification_of_prime_not_dvd_card
        p a hp

/-- Exact removal of all parameters at which `p` is absent from the simple
projective target. -/
theorem
    projectiveSpecialLinearTwoRepresentativeFamilyVerification_iff_primeSupported
    (p : ℕ) [Fact p.Prime] :
    ProjectiveSpecialLinearTwoRepresentativeFamilyVerification p ↔
      ProjectiveSpecialLinearTwoPrimeSupportedRepresentativeVerification p :=
  ⟨ProjectiveSpecialLinearTwoRepresentativeFamilyVerification.toPrimeSupported,
    ProjectiveSpecialLinearTwoPrimeSupportedRepresentativeVerification.toFull⟩

/-! ### The three rank-one support branches -/

/-- A prime divides the field-order factor `q = rⁿ` exactly when it is the
defining characteristic `r`.  This is the arithmetic adapter between the
factorized order formula and the usual defining-characteristic language. -/
theorem prime_dvd_projectiveSpecialLinearTwoFieldOrder_iff_characteristic
    (a : ProjectiveSpecialLinearTwoSimpleParameter)
    {p : ℕ}
    (hp : p.Prime) :
    p ∣ a.characteristic ^ a.degree ↔
      p = a.characteristic := by
  constructor
  · intro h
    exact
      (Nat.prime_dvd_prime_iff_eq hp a.characteristic_prime).1
        (hp.dvd_of_dvd_pow h)
  · intro h
    rw [h]
    exact dvd_pow_self a.characteristic a.degree_ne_zero

/-- Local verification in the defining-characteristic support branch
`p ∣ q`. -/
def ProjectiveSpecialLinearTwoDefiningCharacteristicVerification
    (p : ℕ) : Prop :=
  ∀ a : ProjectiveSpecialLinearTwoSimpleParameter,
    p ∣ a.characteristic ^ a.degree →
      ProjectiveSpecialLinearTwoRepresentativeVerification p a

/-- Local verification in the split-torus support branch `p ∣ q - 1`. -/
def ProjectiveSpecialLinearTwoSplitTorusVerification
    (p : ℕ) : Prop :=
  ∀ a : ProjectiveSpecialLinearTwoSimpleParameter,
    p ∣ a.characteristic ^ a.degree - 1 →
      ProjectiveSpecialLinearTwoRepresentativeVerification p a

/-- Local verification in the nonsplit-torus support branch
`p ∣ q + 1`. -/
def ProjectiveSpecialLinearTwoNonsplitTorusVerification
    (p : ℕ) : Prop :=
  ∀ a : ProjectiveSpecialLinearTwoSimpleParameter,
    p ∣ a.characteristic ^ a.degree + 1 →
      ProjectiveSpecialLinearTwoRepresentativeVerification p a

/-- Prime-supported representative verification is exactly the conjunction
of the defining-characteristic and the two torus branches.  The branches
are intentionally allowed to overlap (notably at `p = 2`); this is the
cleanest interface for later character-theoretic constructions. -/
theorem
    projectiveSpecialLinearTwoPrimeSupportedRepresentativeVerification_iff_branches
    (p : ℕ) [Fact p.Prime] :
    ProjectiveSpecialLinearTwoPrimeSupportedRepresentativeVerification p ↔
      ProjectiveSpecialLinearTwoDefiningCharacteristicVerification p ∧
        ProjectiveSpecialLinearTwoSplitTorusVerification p ∧
          ProjectiveSpecialLinearTwoNonsplitTorusVerification p := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro a hq
      exact
        h a
          ((prime_dvd_natCard_projectiveSpecialLinearTwoRepresentative_iff
            a (Fact.out : p.Prime)).2 (Or.inl hq))
    · intro a hqSub
      exact
        h a
          ((prime_dvd_natCard_projectiveSpecialLinearTwoRepresentative_iff
            a (Fact.out : p.Prime)).2 (Or.inr (Or.inl hqSub)))
    · intro a hqAdd
      exact
        h a
          ((prime_dvd_natCard_projectiveSpecialLinearTwoRepresentative_iff
            a (Fact.out : p.Prime)).2 (Or.inr (Or.inr hqAdd)))
  · rintro ⟨hDefining, hSplit, hNonsplit⟩ a hp
    rcases
        (prime_dvd_natCard_projectiveSpecialLinearTwoRepresentative_iff
          a (Fact.out : p.Prime)).1 hp with
      hq | hqSub | hqAdd
    · exact hDefining a hq
    · exact hSplit a hqSub
    · exact hNonsplit a hqAdd

/-- The complete representative-family obligation is exactly the three
rank-one prime-support branches.  This is the intended entry point for the
generic PSL₂ character calculation. -/
theorem
    projectiveSpecialLinearTwoRepresentativeFamilyVerification_iff_supportBranches
    (p : ℕ) [Fact p.Prime] :
    ProjectiveSpecialLinearTwoRepresentativeFamilyVerification p ↔
      ProjectiveSpecialLinearTwoDefiningCharacteristicVerification p ∧
        ProjectiveSpecialLinearTwoSplitTorusVerification p ∧
          ProjectiveSpecialLinearTwoNonsplitTorusVerification p :=
  (projectiveSpecialLinearTwoRepresentativeFamilyVerification_iff_primeSupported
      p).trans
    (projectiveSpecialLinearTwoPrimeSupportedRepresentativeVerification_iff_branches
      p)

/-! ### Direct abstract-family interface -/

/-- The abstract one-cover/one-Sylow verification for the isomorphism-closed
simple PSL₂ family is itself exactly the conjunction of the three
prime-support branches.  Thus later Lie-type work can enter the global
family API without an additional transport premise. -/
theorem
    projectiveSpecialLinearTwoSimpleGroupFamilyVerification_iff_supportBranches
    (p : ℕ) [Fact p.Prime] :
    OneUniversalCoverOneSylowFamilyVerification
        p projectiveSpecialLinearTwoSimpleGroupFamily ↔
      ProjectiveSpecialLinearTwoDefiningCharacteristicVerification p ∧
        ProjectiveSpecialLinearTwoSplitTorusVerification p ∧
          ProjectiveSpecialLinearTwoNonsplitTorusVerification p := by
  constructor
  · intro h
    apply
      (projectiveSpecialLinearTwoRepresentativeFamilyVerification_iff_supportBranches
        p).1
    intro a
    exact
      h (projectiveSpecialLinearTwoRepresentative a)
        (projectiveSpecialLinearTwoRepresentative_mem_family a)
        (projectiveSpecialLinearTwoRepresentative_isSimpleGroup a)
        (projectiveSpecialLinearTwoRepresentative_not_isMulCommutative a)
  · intro h
    exact
      ((projectiveSpecialLinearTwoRepresentativeFamilyVerification_iff_supportBranches
        p).2 h).toFamily

/-- The prime-supported family interface used by CFSG assembly has the same
exact three-branch description. -/
theorem
    projectiveSpecialLinearTwoPrimeSupportedFamilyVerification_iff_supportBranches
    (p : ℕ) [Fact p.Prime] :
    PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p projectiveSpecialLinearTwoSimpleGroupFamily ↔
      ProjectiveSpecialLinearTwoDefiningCharacteristicVerification p ∧
        ProjectiveSpecialLinearTwoSplitTorusVerification p ∧
          ProjectiveSpecialLinearTwoNonsplitTorusVerification p :=
  (OneUniversalCoverOneSylowFamilyVerification.iff_primeSupported
      (p := p)
      (family := projectiveSpecialLinearTwoSimpleGroupFamily)).symm.trans
    (projectiveSpecialLinearTwoSimpleGroupFamilyVerification_iff_supportBranches
      p)

/-- The same three branch proofs directly supply the prime-supported
classification-family interface used by the final McKay reduction. -/
theorem
    projectiveSpecialLinearTwoPrimeSupportedFamilyVerification_of_supportBranches
    (p : ℕ) [Fact p.Prime]
    (hDefining :
      ProjectiveSpecialLinearTwoDefiningCharacteristicVerification p)
    (hSplit :
      ProjectiveSpecialLinearTwoSplitTorusVerification p)
    (hNonsplit :
      ProjectiveSpecialLinearTwoNonsplitTorusVerification p) :
    PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
      p projectiveSpecialLinearTwoSimpleGroupFamily :=
  (projectiveSpecialLinearTwoPrimeSupportedFamilyVerification_iff_supportBranches
    p).2 ⟨hDefining, hSplit, hNonsplit⟩

end InductiveMcKay
end McKayConjecture
