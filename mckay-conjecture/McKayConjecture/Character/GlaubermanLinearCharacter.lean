/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanCorrespondence
import McKayConjecture.Character.LinearRestrictionMultiplicity

/-!
# The Glauberman constituent for invariant linear characters

For a `P`-invariant degree-one character of `K`, the Glauberman
constituent is elementary: it is ordinary restriction to `C_K(P)`.
That restriction is irreducible, has multiplicity one, and is the unique
constituent whose multiplicity is prime to `p`.

Thus the character-theoretic constituent theorem is already complete on
the linear stratum.  For an abelian coprime kernel, the remaining issue is
the group-theoretic fixed-dual statement that restriction bijects the
`P`-fixed linear characters of `K` with the linear characters of
`C_K(P)`.
-/

noncomputable section

namespace McKayConjecture

open CliffordCorrespondence

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (K P : Subgroup G) [K.Normal]

/-- Restriction to `C_K(P)` of a degree-one invariant character, packaged
as a prime-to-`p` irreducible character. -/
def linearGlaubermanCandidate
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (hθ : θ.1.1.degree = 1) :
    PPrimeIrreducibleCharacter
      (coprimeFixedPoints K P) p :=
  ⟨θ.1.1.linearRestriction
      (coprimeFixedPointsInclusion K P) hθ,
    by
      rw [IrreducibleCharacter.IsPPrimeDegree,
        IrreducibleCharacter.linearRestriction_degree]
      exact (Fact.out : p.Prime).not_dvd_one⟩

omit [Finite G] in
@[simp]
theorem linearGlaubermanCandidate_coe
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (hθ : θ.1.1.degree = 1) :
    (linearGlaubermanCandidate K P θ hθ).1 =
      θ.1.1.linearRestriction
        (coprimeFixedPointsInclusion K P) hθ :=
  rfl

/-- The linear Glauberman candidate occurs with multiplicity one. -/
theorem restrictionMultiplicity_linearGlaubermanCandidate_eq_one
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (hθ : θ.1.1.degree = 1) :
    restrictionMultiplicity
        (coprimeFixedPointsInclusion K P)
        (linearGlaubermanCandidate K P θ hθ).1
        θ.1.1 =
      1 := by
  exact
    restrictionMultiplicity_linearRestriction_eq_one
      (coprimeFixedPointsInclusion K P)
      θ.1.1 hθ

/-- Every other irreducible character has multiplicity zero in the
restriction of an invariant linear character. -/
theorem restrictionMultiplicity_eq_zero_of_ne_linearGlaubermanCandidate
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (hθ : θ.1.1.degree = 1)
    (φ :
      PPrimeIrreducibleCharacter
        (coprimeFixedPoints K P) p)
    (hne :
      φ ≠ linearGlaubermanCandidate K P θ hθ) :
    restrictionMultiplicity
        (coprimeFixedPointsInclusion K P)
        φ.1 θ.1.1 =
      0 := by
  refine
    restrictionMultiplicity_linearRestriction_eq_zero_of_ne
      (coprimeFixedPointsInclusion K P)
      θ.1.1 hθ φ.1 ?_
  intro heq
  apply hne
  apply Subtype.ext
  simpa only [linearGlaubermanCandidate_coe]
    using heq

/-- The linear Glauberman candidate has prime-to-`p` multiplicity. -/
theorem linearGlaubermanCandidate_multiplicity_isPPrime
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (hθ : θ.1.1.degree = 1) :
    ¬p ∣
      restrictionMultiplicity
        (coprimeFixedPointsInclusion K P)
        (linearGlaubermanCandidate K P θ hθ).1
        θ.1.1 := by
  rw [
    restrictionMultiplicity_linearGlaubermanCandidate_eq_one]
  exact (Fact.out : p.Prime).not_dvd_one

/-- Prime-to-`p` multiplicity uniquely characterizes the restriction of
an invariant linear character. -/
theorem eq_linearGlaubermanCandidate_of_multiplicity_isPPrime
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (hθ : θ.1.1.degree = 1)
    (φ :
      PPrimeIrreducibleCharacter
        (coprimeFixedPoints K P) p)
    (hφ :
      ¬p ∣
        restrictionMultiplicity
          (coprimeFixedPointsInclusion K P)
          φ.1 θ.1.1) :
    φ = linearGlaubermanCandidate K P θ hθ := by
  by_contra hne
  have hzero :=
    restrictionMultiplicity_eq_zero_of_ne_linearGlaubermanCandidate
      K P θ hθ φ hne
  exact hφ (hzero ▸ dvd_zero p)

/-- For a commutative kernel every irreducible source character is linear,
so ordinary restriction supplies its unique Glauberman constituent. -/
def commutativeKernelGlaubermanCandidate
    [IsMulCommutative K]
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    PPrimeIrreducibleCharacter
      (coprimeFixedPoints K P) p :=
  linearGlaubermanCandidate K P θ
    (IrreducibleCharacter.degree_eq_one_of_isMulCommutative
      θ.1.1)

@[simp]
theorem restrictionMultiplicity_commutativeKernelGlaubermanCandidate_eq_one
    [IsMulCommutative K]
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    restrictionMultiplicity
        (coprimeFixedPointsInclusion K P)
        (commutativeKernelGlaubermanCandidate
          K P θ).1 θ.1.1 =
      1 :=
  restrictionMultiplicity_linearGlaubermanCandidate_eq_one
    K P θ
      (IrreducibleCharacter.degree_eq_one_of_isMulCommutative
        θ.1.1)

/-- On a commutative kernel, prime-to-`p` restriction multiplicity
uniquely determines the candidate attached to every invariant source
character. -/
theorem eq_commutativeKernelGlaubermanCandidate_of_multiplicity_isPPrime
    [IsMulCommutative K]
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (φ :
      PPrimeIrreducibleCharacter
        (coprimeFixedPoints K P) p)
    (hφ :
      ¬p ∣
        restrictionMultiplicity
          (coprimeFixedPointsInclusion K P)
          φ.1 θ.1.1) :
    φ =
      commutativeKernelGlaubermanCandidate K P θ :=
  eq_linearGlaubermanCandidate_of_multiplicity_isPPrime
    K P θ
      (IrreducibleCharacter.degree_eq_one_of_isMulCommutative
        θ.1.1)
      φ hφ

end McKayConjecture
