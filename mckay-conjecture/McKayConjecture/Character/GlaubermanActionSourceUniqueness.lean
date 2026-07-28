/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanActionOrbitSum
import McKayConjecture.Character.GlaubermanActionStrong
import McKayConjecture.Character.RestrictionMultiplicityDegree

/-!
# Constructing a strong action correspondence from source uniqueness

For a finite `p`-group acting on a finite `p'`-group, the orbit-sum
argument supplies existence over every prime-to-`p` target character.
Consequently, to construct the strong Glauberman correspondence it is
enough to prove:

* every invariant prime-to-`p` source has a unique irreducible target
  occurring with prime-to-`p` multiplicity; and
* two sources cannot select the same target.

The first condition also forces the selected target to have
prime-to-`p` degree, by evaluating the restricted source character at
the identity.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture

open CliffordCorrespondence

variable (P A : Type) [Group P] [Group A]
variable [MulDistribMulAction P A]
variable [Finite P] [Finite A]
variable {p : ℕ} [Fact p.Prime]

/-- Full multiplicity relation between an invariant source character and
an arbitrary irreducible character of the fixed-point group. -/
def HasPPrimeRestrictionMultiplicityIrreducible
    (θ : ActionInvariantPPrimeIrreducibleCharacter P A p)
    (φ : IrreducibleCharacter (FixedPoints.subgroup P A)) : Prop :=
  ¬p ∣
    restrictionMultiplicity
      (actionFixedPointsInclusion P A) φ θ.1.1

/-- The unique target selected by full source-side multiplicity
uniqueness. -/
def sourceUniqueCorrespondent
    (hsource :
      ∀ θ : ActionInvariantPPrimeIrreducibleCharacter P A p,
        ∃! φ : IrreducibleCharacter (FixedPoints.subgroup P A),
          HasPPrimeRestrictionMultiplicityIrreducible P A θ φ)
    (θ : ActionInvariantPPrimeIrreducibleCharacter P A p) :
    IrreducibleCharacter (FixedPoints.subgroup P A) :=
  Classical.choose (hsource θ)

/-- The source-unique correspondent has prime-to-`p` restriction
multiplicity. -/
theorem sourceUniqueCorrespondent_multiplicity_isPPrime
    (hsource :
      ∀ θ : ActionInvariantPPrimeIrreducibleCharacter P A p,
        ∃! φ : IrreducibleCharacter (FixedPoints.subgroup P A),
          HasPPrimeRestrictionMultiplicityIrreducible P A θ φ)
    (θ : ActionInvariantPPrimeIrreducibleCharacter P A p) :
    HasPPrimeRestrictionMultiplicityIrreducible P A θ
      (sourceUniqueCorrespondent P A hsource θ) :=
  (Classical.choose_spec (hsource θ)).1

/-- Full source uniqueness forces the selected target character to have
prime-to-`p` degree. -/
theorem sourceUniqueCorrespondent_degree_isPPrime
    (hsource :
      ∀ θ : ActionInvariantPPrimeIrreducibleCharacter P A p,
        ∃! φ : IrreducibleCharacter (FixedPoints.subgroup P A),
          HasPPrimeRestrictionMultiplicityIrreducible P A θ φ)
    (θ : ActionInvariantPPrimeIrreducibleCharacter P A p) :
    ¬p ∣ (sourceUniqueCorrespondent P A hsource θ).degree := by
  classical
  let ψ := sourceUniqueCorrespondent P A hsource θ
  have hdegree :=
    degree_eq_sum_restrictionMultiplicity_mul_degree_nat
      (actionFixedPointsInclusion P A) θ.1.1
  intro hψdegree
  apply θ.1.2
  rw [hdegree]
  apply Finset.dvd_sum
  intro φ _hφ
  by_cases hφψ : φ = ψ
  · rw [hφψ]
    exact dvd_mul_of_dvd_right hψdegree _
  · have hmult :
        p ∣
          restrictionMultiplicity
            (actionFixedPointsInclusion P A) φ θ.1.1 := by
      by_contra hprime
      apply hφψ
      exact
        (hsource θ).unique hprime
          (sourceUniqueCorrespondent_multiplicity_isPPrime
            P A hsource θ)
    exact dvd_mul_of_dvd_left hmult _

/-- Full source-side uniqueness and target-side injectivity construct the
strong action Glauberman correspondence.  Surjectivity is supplied by
the weighted orbit-sum theorem. -/
def strongActionGlaubermanCorrespondenceOfSourceUniqueness
    (hP : IsPGroup p P)
    (hA : GroupTheory.IsPPrimeGroup p A)
    (hsource :
      ∀ θ : ActionInvariantPPrimeIrreducibleCharacter P A p,
        ∃! φ : IrreducibleCharacter (FixedPoints.subgroup P A),
          HasPPrimeRestrictionMultiplicityIrreducible P A θ φ)
    (hinjective :
      Function.Injective
        (sourceUniqueCorrespondent P A hsource)) :
    StrongActionGlaubermanCorrespondence P A p := by
  let f :
      ActionInvariantPPrimeIrreducibleCharacter P A p →
        PPrimeIrreducibleCharacter
          (FixedPoints.subgroup P A) p :=
    fun θ =>
      ⟨sourceUniqueCorrespondent P A hsource θ,
        sourceUniqueCorrespondent_degree_isPPrime
          P A hsource θ⟩
  have hf :
      ∀ θ,
        HasPPrimeRestrictionMultiplicityIrreducible
          P A θ (f θ).1 := by
    intro θ
    exact
      sourceUniqueCorrespondent_multiplicity_isPPrime
        P A hsource θ
  have hfinjective : Function.Injective f := by
    intro θ η heq
    apply hinjective
    exact congrArg Subtype.val heq
  have hfsurjective : Function.Surjective f := by
    intro φ
    obtain ⟨θ, hθ⟩ :=
      exists_actionInvariantPPrime_of_target
        P A hP hA φ
    refine ⟨θ, ?_⟩
    apply Subtype.ext
    exact
      (hsource θ).unique
        (sourceUniqueCorrespondent_multiplicity_isPPrime
          P A hsource θ)
        hθ
  let e := Equiv.ofBijective f
    ⟨hfinjective, hfsurjective⟩
  exact
    { characterEquiv := e
      multiplicity_isPPrime := hf
      eq_correspondent_of_multiplicity_isPPrime := by
        intro θ φ hφ
        exact
          (hsource θ).unique hφ
            (sourceUniqueCorrespondent_multiplicity_isPPrime
              P A hsource θ) }

end McKayConjecture
