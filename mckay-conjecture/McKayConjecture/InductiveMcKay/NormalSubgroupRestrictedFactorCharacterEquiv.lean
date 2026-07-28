/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FixedFiniteFactorCharacterEquiv
import McKayConjecture.InductiveMcKay.NormalSubgroupRestrictedFactorFibre

/-!
# Ordinary characters for the fixed restricted factor

This file applies the arbitrary fixed-factor character correspondence to the
literal restriction of the canonical finite normalization.  In particular,
the target is exactly the restricted extension already identified with the
lifted-Sylow normalizer; no second determinant normalization is introduced.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupRestrictedFactorFibre

open CharacterTriple
open CharacterTriple.AssociatedProjectiveRepresentation
open GroupTheory
open NormalSubgroupAssociatedFactorFibre
open NormalSubgroupFactorNormalizerFibre

variable {A : Type} [Finite A] [Group A]
variable {p : ℕ} [Fact p.Prime]

/-- The literal restriction of the canonical finite-normalization package,
viewed as arbitrary fixed finite-factor data. -/
abbrev RestrictedFixedFiniteFactorData
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    FixedFiniteFactorData
      (RestrictedTriple T S)
      T.character.realization :=
  FixedFiniteFactorData.normalizerRestriction
    (CanonicalAssociated T)
    (CanonicalAssociated T).finiteFactorNormalization S

/-- Ordinary prime-to-`p` characters over the restricted triple character
are canonically equivalent to the inverse-coefficient fibre in the literal
fixed restricted extension. -/
def restrictedFixedFiniteFactorPPrimeCharacterEquiv
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (hT : (RestrictedTriple T S).character.IsPPrimeDegree p) :
    PPrimeCharactersOver (RestrictedTriple T S) p ≃
      RestrictedPPrimeInverseCoefficientFibre T S :=
  (RestrictedFixedFiniteFactorData T S
    ).fixedFiniteFactorPPrimeCharacterEquiv Fact.out hT

end NormalSubgroupRestrictedFactorFibre
end InductiveMcKay
end McKayConjecture
