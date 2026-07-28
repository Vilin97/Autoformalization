/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import
  McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45LiftedFactorCorrespondence
import
  McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45QuotientFactorCharacter

/-!
# The remaining quotient-to-ambient restriction claim in Proposition 4.5

Central-index induction on the quotient factor extension produces the
inverse coefficient scalar on the right Sylow-normalizer factor.  That is
not yet a character on the pulled-back factor extension over the full right
inertia group.

This file isolates the first genuinely missing representation-theoretic
statement: a coefficient character on that ambient target extension must
restrict along the canonical lifted normal subgroup to the
Okuyama--Wajima target normal character.  No centralizer trace equality is
included.  Thus this predicate is strictly weaker than
`LiftedFactorCorrespondence.ImageData` and is not a renaming of it.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple
open CharacterTriple.AssociatedProjectiveRepresentation

variable {A B : Type}
variable [Group A] [Finite A] [Group B] [Finite B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {e : B →* A}
variable {V : Type}
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}

namespace LiftedFactorCorrespondence

variable
  (R : AssociatedProjectiveRepresentation T V P)
  (F : R.AssociatedFiniteFactorNormalization)
  (g : CentralRestrictionGroupData T U e)

/-- The exact missing restriction assertion for a proposed target factor
character. -/
def HasTargetNormalRestriction
    (psi :
      IrreducibleCharacter
        (TargetFactorCentralExtensionGroup R F g)) : Prop :=
  IrreducibleCharacter.IsExtensionAlong
    (targetNormalLift R F g) U.character psi

/-- Existence of a coefficient character on the ambient target factor
extension with the required normal restriction.  This omits the
centralizer trace field of `ImageData`. -/
def TargetNormalExtensionClaim : Prop :=
  ∃ psi :
      IrreducibleCharacter
        (TargetFactorCentralExtensionGroup R F g),
    FactorSet.CentralExtensionGroup.HasCoefficientCharacter
        (targetFactorSet R F g)
        (targetFactorSet_isNormalized R F g)
        (coefficientHom R F g) psi ∧
      HasTargetNormalRestriction R F g psi

/-- A full lifted-DGN image implies the separated restriction claim. -/
theorem ImageData.targetNormalExtensionClaim
    (d : ImageData R F g) :
    TargetNormalExtensionClaim R F g :=
  ⟨d.targetCharacter, d.coefficientCharacter,
    d.extendsTargetNormalCharacter⟩

end LiftedFactorCorrespondence

namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open ComplementReduction
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The separated target-normal restriction claim for one concrete
Proposition-4.5 inertia pair.  Quotient-factor induction supplies the
coefficient-normalizer side; this is the remaining quotient-to-ambient
lifting assertion. -/
abbrev ProductAmbientGlaubermanTargetNormalExtensionClaim
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q) :=
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  LiftedFactorCorrespondence.TargetNormalExtensionClaim
    (productAmbientGlaubermanLeftAssociated
      S C hgenerate theta)
    (productAmbientGlaubermanLeftFiniteFactorNormalization
      S C hgenerate theta)
    (productAmbientGlaubermanInertiaRestrictionGroupData
      S C hcentral hgenerate g theta)

/-- The old full image-data hypothesis implies the newly isolated,
strictly weaker target-normal extension claim. -/
theorem productAmbientGlaubermanTargetNormalExtensionClaim_of_liftedDGNImage
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (d :
      ProductAmbientGlaubermanLiftedDGNImageData
        S C hcentral hgenerate g theta) :
    ProductAmbientGlaubermanTargetNormalExtensionClaim
      S C hcentral hgenerate g theta := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  exact
    d.targetNormalExtensionClaim
      (productAmbientGlaubermanLeftAssociated
        S C hgenerate theta)
      (productAmbientGlaubermanLeftFiniteFactorNormalization
        S C hgenerate theta)
      (productAmbientGlaubermanInertiaRestrictionGroupData
        S C hcentral hgenerate g theta)

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
