/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralTripleFactorMatchedCohomology
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionJoinCenterFibreReduction
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionProposition45IntrinsicObstructions

/-!
# Proposition 4.5 from the intrinsic projective obstruction

The intrinsic `H²` obstruction agreement on a matched
Glauberman--Okuyama--Wajima inertia pair canonically gauges the right
associated projective representation so that its factor set agrees
literally with the left factor set.  The factor-matched character-triple
correspondence then gives the required prime-to-`q` inertia-fibre
equivalence.

After adjoining the ambient center, those ordinary fibre equivalences
automatically preserve the central scalars used by the final Clifford
assembly.  Hence the projective obstruction agreement is the only
remaining input in the central-intersection reduction.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open CliffordCorrespondence
open ComplementReduction

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- Intrinsic projective obstruction agreement gives the actual
prime-to-`q` equivalence on one matched inertia fibre. -/
def productAmbientGlaubermanPPrimeInertiaFibreEquivOfProjectiveObstructionClassAgreement
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter
        (product S C) q)
    (h :
      ProductAmbientGlaubermanProjectiveObstructionClassAgreement
        S C hcentral hgenerate g theta) :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal S C hgenerate
    PPrimeIrreducibleCharactersOverInertia
        (product S C) theta.1 q ≃
      PPrimeIrreducibleCharactersOverInertia
        (internalProductNormalizer S C)
        (internalTheorem44CharacterEquiv
          S C
          (complementCharacterEquivOfGlauberman
            S C hcentral g) theta).1 q := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  let phi :=
    internalTheorem44CharacterEquiv
      S C
      (complementCharacterEquivOfGlauberman
        S C hcentral g) theta
  let leftAssociated :=
    productAmbientGlaubermanLeftAssociated
      S C hgenerate theta
  let rightAssociated :=
    productAmbientGlaubermanRightAssociated
      S C hcentral hgenerate g theta
  let groupData :=
    productAmbientGlaubermanInertiaRestrictionGroupData
      S C hcentral hgenerate g theta
  let factorAgreement :=
    productAmbientGlaubermanCanonicalFactorAgreement
      S C hcentral hgenerate g theta h
  let tripleEquiv :=
    pPrimeIrreducibleCharactersOverEquivOfQuotientCohomology
      (Fact.out : q.Prime)
      leftAssociated rightAssociated groupData factorAgreement
      theta.2 phi.2
  exact
    (pPrimeIrreducibleCharactersOverInertiaEquivTriple
      (product S C) theta.1 q).trans
      (tripleEquiv.trans
        (pPrimeIrreducibleCharactersOverInertiaEquivTriple
          (internalProductNormalizer S C) phi.1 q).symm)

/-- A family of intrinsic projective obstruction agreements supplies the
complete numerical ambient coherence for the canonical correspondence. -/
def productAmbientGlaubermanTheorem44CoherenceOfProjectiveObstructionClassAgreement
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (h :
      ∀ theta :
          PPrimeIrreducibleCharacter
            (product S C) q,
        ProductAmbientGlaubermanProjectiveObstructionClassAgreement
          S C hcentral hgenerate g theta) :
    ProductAmbientTheorem44Coherence
      S C hgenerate
      (complementCharacterEquivOfGlauberman
        S C hcentral g) :=
  productAmbientGlaubermanTheorem44CoherenceOfInertiaFibreEquiv
    S C hcentral hgenerate g
    (fun theta ↦
      productAmbientGlaubermanPPrimeInertiaFibreEquivOfProjectiveObstructionClassAgreement
        S C hcentral hgenerate g theta (h theta))

end Proposition45

open Proposition45

/-- The exact global Dade--Glauberman--Nagao input left by the
central-intersection reduction: equality of the two intrinsic projective
obstruction classes for every canonical matched inertia pair. -/
def ProductAmbientGlaubermanProjectiveObstructionClassAgreementHypothesis
    (q : ℕ) [Fact q.Prime] : Prop :=
  ∀ (X : Type) [Group X] [Finite X]
    (S : Sylow q X) (C : Subgroup X)
    (hCnormal : C.Normal)
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤),
      letI : C.Normal := hCnormal
      ∀ (g :
          ComplementReduction.ProductGlaubermanCorrespondence
            S C hcentral)
        (theta :
          PPrimeIrreducibleCharacter
            (product S C) q),
        Proposition45.ProductAmbientGlaubermanProjectiveObstructionClassAgreement
          S C hcentral hgenerate g theta

/-- Intrinsic projective obstruction agreement alone implies the complete
central-intersection reduction.  The formerly separate scalar obstruction
disappears after adjoining the ambient center. -/
theorem centralScalarCentralIntersectionReductionHypothesis_of_projectiveObstructionClassAgreement
    {q : ℕ} [Fact q.Prime]
    (h :
      ProductAmbientGlaubermanProjectiveObstructionClassAgreementHypothesis
        q) :
    CentralScalarCentralIntersectionReductionHypothesis q := by
  apply
    centralScalarCentralIntersectionReductionHypothesis_of_inertiaFibreEquiv
  intro X _ _ S C hCnormal hcentral hgenerate
  letI : C.Normal := hCnormal
  intro g theta
  refine ⟨?_⟩
  exact
    productAmbientGlaubermanPPrimeInertiaFibreEquivOfProjectiveObstructionClassAgreement
      S C hcentral hgenerate g theta
        (h X S C hCnormal hcentral hgenerate g theta)

end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
