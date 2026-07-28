/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedFiniteFactorNormalizerRestriction

/-!
# Arbitrary fixed finite factors for an associated projective lift

The canonical determinant normalization is only one way to obtain the finite
factor used in the character-triple correspondence.  For restriction
arguments one must retain the already chosen factor literally.  This file
packages precisely the data used by the character correspondence:

* an associated projective representation,
* a roots-of-unity-valued normalized factor on the quotient, and
* exact agreement of that factor with the chosen projective operators.

The exponent is part of the package and need not be recomputed after
restricting the ambient triple.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace AssociatedProjectiveRepresentation

variable {A : Type} [Finite A] [Group A]
variable (T : CharacterTriple A)
variable (V : Type) [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]

/-- A fixed finite quotient factor together with the associated projective
lift whose factor it represents exactly. -/
structure FixedFiniteFactorData where
  /-- Exponent of the finite coefficient group. -/
  exponent : ℕ
  /-- The chosen associated projective lift. -/
  projective : ProjectiveRepresentation ℂ A V
  /-- Association with the original character triple. -/
  associated :
    AssociatedProjectiveRepresentation T V projective
  /-- The fixed roots-of-unity-valued factor on `A / T.normalSubgroup`. -/
  quotientFactorSet :
    FactorSet (A ⧸ T.normalSubgroup) (rootsOfUnity exponent ℂ)
  /-- The fixed quotient factor is normalized. -/
  quotientFactorSet_isNormalized :
    quotientFactorSet.IsNormalized
  /-- Pulling the quotient factor back to `A` gives the exact projective
  factor, after forgetting the finite coefficient group. -/
  quotientFactorSet_mk_coe :
    ∀ a b : A,
      ((quotientFactorSet
          (QuotientGroup.mk' T.normalSubgroup a)
          (QuotientGroup.mk' T.normalSubgroup b) :
        rootsOfUnity exponent ℂ) : ℂˣ) =
          projective.factor a b

namespace FixedFiniteFactorData

variable {T V}

/-- Name matching the canonical finite-factor API. -/
abbrev fixedFiniteFactorProjective
    (R : FixedFiniteFactorData T V) :=
  R.projective

/-- Name matching the canonical associated-lift API. -/
abbrev fixedFiniteFactorAssociated
    (R : FixedFiniteFactorData T V) :=
  R.associated

/-- The fixed quotient factor. -/
abbrev fixedFiniteQuotientFactorSet
    (R : FixedFiniteFactorData T V) :=
  R.quotientFactorSet

/-- Normalization of the fixed quotient factor. -/
abbrev fixedFiniteQuotientFactorSet_isNormalized
    (R : FixedFiniteFactorData T V) :
    R.fixedFiniteQuotientFactorSet.IsNormalized :=
  R.quotientFactorSet_isNormalized

/-- The concrete central extension defined by the fixed quotient factor. -/
abbrev FixedFiniteFactorCentralExtensionGroup
    (R : FixedFiniteFactorData T V) :=
  FactorSet.CentralExtensionGroup
    R.fixedFiniteQuotientFactorSet
    R.fixedFiniteQuotientFactorSet_isNormalized

@[simp]
theorem fixedFiniteQuotientFactorSet_mk_coe
    (R : FixedFiniteFactorData T V)
    (a b : A) :
    ((R.fixedFiniteQuotientFactorSet
        (QuotientGroup.mk' T.normalSubgroup a)
        (QuotientGroup.mk' T.normalSubgroup b) :
      rootsOfUnity R.exponent ℂ) : ℂˣ) =
        R.fixedFiniteFactorProjective.factor a b :=
  R.quotientFactorSet_mk_coe a b

/-- Package any arbitrary association-preserving finite normalization. -/
def ofNormalization
    {P : ProjectiveRepresentation ℂ A V}
    (R : AssociatedProjectiveRepresentation T V P)
    (F : AssociatedFiniteFactorNormalization R) :
    FixedFiniteFactorData T V where
  exponent := associatedFactorExponent T V
  projective := F.projective
  associated := F.associated
  quotientFactorSet := F.finiteQuotientFactorSet R
  quotientFactorSet_isNormalized :=
    F.finiteQuotientFactorSet_isNormalized R
  quotientFactorSet_mk_coe a b := by
    rw [F.finiteQuotientFactorSet_mk R a b]
    exact F.factorSet_coe a b

/-- The canonical finite normalization, regarded as fixed data. -/
abbrev canonical
    {P : ProjectiveRepresentation ℂ A V}
    (R : AssociatedProjectiveRepresentation T V P) :
    FixedFiniteFactorData T V :=
  ofNormalization R R.finiteFactorNormalization

/-- Restrict a fixed normalization literally to the full preimage of a
quotient Sylow normalizer.  The coefficient exponent remains the one chosen
before restriction. -/
def normalizerRestriction
    {P : ProjectiveRepresentation ℂ A V}
    (R : AssociatedProjectiveRepresentation T V P)
    (F : AssociatedFiniteFactorNormalization R)
    {p : ℕ} [Fact p.Prime]
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    FixedFiniteFactorData
      (quotientSylowNormalizerRestrictionTriple T S) V where
  exponent := associatedFactorExponent T V
  projective :=
    F.projective.comap
      (quotientSylowNormalizerPreimage T S).subtype
  associated := F.normalizerRestrictionAssociated R S
  quotientFactorSet :=
    F.normalizerRestrictionFiniteQuotientFactorSet R S
  quotientFactorSet_isNormalized :=
    F.normalizerRestrictionFiniteQuotientFactorSet_isNormalized R S
  quotientFactorSet_mk_coe x y :=
    F.normalizerRestrictionFiniteQuotientFactorSet_mk_coe
      R S x y

end FixedFiniteFactorData
end AssociatedProjectiveRepresentation
end CharacterTriple
end McKayConjecture
