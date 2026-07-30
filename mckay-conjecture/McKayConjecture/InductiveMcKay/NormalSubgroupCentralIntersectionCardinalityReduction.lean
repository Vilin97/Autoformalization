/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionJoinCenterFibreReduction
import McKayConjecture.Character.Finiteness

/-!
# Central-intersection reduction from inertia-fibre cardinalities

After adjoining the ambient center, the numerical Proposition 4.5 reduction
needs only ordinary equivalences between the matched prime-to-`p` inertia
fibres.  Since those fibres are finite, it is enough to prove that their
cardinalities agree.

This is the formalization boundary naturally supplied by the
automorphism-equivariant Okuyama--Wajima counting argument: no projective
factor-set comparison or Dade-algebra witness is needed at this numerical
boundary.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction

open CliffordCorrespondence
open ComplementReduction
open Proposition45

/-- The exact remaining numerical input after adjoining the ambient center,
stated as equality of the two finite inertia-fibre cardinalities. -/
def CentralScalarCentralIntersectionInertiaFibreCardinalityHypothesis
    (q : ℕ) [Fact q.Prime] : Prop :=
  ∀ (X : Type) [Group X] [Finite X]
    (S : Sylow q X) (C : Subgroup X)
    (hCnormal : C.Normal)
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤),
      letI : C.Normal := hCnormal
      ∀ g :
          ProductGlaubermanCorrespondence
            S C hcentral,
        letI : (product S C).Normal :=
          product_normal S C hgenerate
        letI :
            (internalProductNormalizer S C).Normal :=
          internalProductNormalizer_normal S C hgenerate
        ∀ theta :
            PPrimeIrreducibleCharacter
              (product S C) q,
          Nat.card
              (PPrimeIrreducibleCharactersOverInertia
                (product S C) theta.1 q) =
            Nat.card
              (PPrimeIrreducibleCharactersOverInertia
                (internalProductNormalizer S C)
                (internalTheorem44CharacterEquiv
                  S C
                  (complementCharacterEquivOfGlauberman
                    S C hcentral g) theta).1 q)

/-- Equal finite inertia-fibre cardinalities provide the equivalences
required by the join-center reduction. -/
theorem
    centralScalarCentralIntersectionInertiaFibreEquivHypothesis_of_cardinality
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionInertiaFibreCardinalityHypothesis
        q) :
    CentralScalarCentralIntersectionInertiaFibreEquivHypothesis q := by
  intro X _ _ S C hCnormal hcentral hgenerate
  letI : C.Normal := hCnormal
  intro g
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  intro theta
  letI :
      Finite
        (PPrimeIrreducibleCharactersOverInertia
          (product S C) theta.1 q) :=
    Finite.of_injective
      (fun χ => χ.1.1)
      (fun _ _ hχ => Subtype.ext (Subtype.ext hχ))
  letI :
      Finite
        (PPrimeIrreducibleCharactersOverInertia
          (internalProductNormalizer S C)
          (internalTheorem44CharacterEquiv
            S C
            (complementCharacterEquivOfGlauberman
              S C hcentral g) theta).1 q) :=
    Finite.of_injective
      (fun χ => χ.1.1)
      (fun _ _ hχ => Subtype.ext (Subtype.ext hχ))
  exact
    (Finite.card_eq.mp
      (h X S C hCnormal hcentral hgenerate g theta))

/-- Inertia-fibre cardinality equalities imply the complete
central-intersection reduction. -/
theorem
    centralScalarCentralIntersectionReductionHypothesis_of_cardinality
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionInertiaFibreCardinalityHypothesis
        q) :
    CentralScalarCentralIntersectionReductionHypothesis q :=
  centralScalarCentralIntersectionReductionHypothesis_of_inertiaFibreEquiv
    (centralScalarCentralIntersectionInertiaFibreEquivHypothesis_of_cardinality
      h)

/-- Inertia-fibre cardinality equalities supply the complete normal-subgroup
input to the central-scalar Rossi reduction. -/
theorem
    centralScalarNormalSubgroupReductionHypothesis_of_cardinality
    {q : ℕ} [Fact q.Prime]
    (h :
      CentralScalarCentralIntersectionInertiaFibreCardinalityHypothesis
        q) :
    CentralScalarNormalSubgroupReductionHypothesis q :=
  centralScalarNormalSubgroupReductionHypothesis_of_centralIntersection
    (centralScalarCentralIntersectionReductionHypothesis_of_cardinality h)

end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
