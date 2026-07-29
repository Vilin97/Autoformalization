/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ActionInvariantOver
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionCardinalityReduction

/-!
# Ordinary inertia-fibre counts and the prime-to-degree bridge

The fixed-character counting theorem used in the optimized
normal-subgroup reduction counts ordinary irreducible characters.  The
prime-to-`q` Clifford reduction used downstream counts a subtype selected
by degree.  This file keeps the two mathematical inputs separate:

* equality of the matched ordinary inertia-fibre cardinalities;
* the automatic prime-to-`q` degree theorem on each ordinary fibre.

Their conjunction gives exactly the prime-to-`q` cardinality hypothesis
consumed by the existing numerical reduction.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction

open CliffordCorrespondence
open ComplementReduction
open Proposition45

/-- The ordinary matched-inertia cardinality equality supplied by the
fixed-character counting theorem. -/
def CentralScalarCentralIntersectionOrdinaryInertiaFibreCardinalityHypothesis
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
              (IrreducibleCharactersOverInertia
                (product S C) theta.1) =
            Nat.card
              (IrreducibleCharactersOverInertia
                (internalProductNormalizer S C)
                (internalTheorem44CharacterEquiv
                  S C
                  (complementCharacterEquivOfGlauberman
                    S C hcentral g) theta).1)

/-- The automatic-degree input: every ordinary character in each matched
inertia fibre has prime-to-`q` degree. -/
def CentralScalarCentralIntersectionInertiaFibrePPrimeDegreeHypothesis
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
          (∀ χ :
              IrreducibleCharactersOverInertia
                (product S C) theta.1,
              χ.1.IsPPrimeDegree q) ∧
            (∀ χ :
              IrreducibleCharactersOverInertia
                (internalProductNormalizer S C)
                (internalTheorem44CharacterEquiv
                  S C
                  (complementCharacterEquivOfGlauberman
                    S C hcentral g) theta).1,
              χ.1.IsPPrimeDegree q)

/-- Ordinary matched-fibre counts and automatic prime-to-`q` degree give
the prime-to-`q` matched-fibre counts required by the numerical
normal-subgroup reduction. -/
theorem
    centralScalarCentralIntersectionInertiaFibreCardinalityHypothesis_of_ordinary
    {q : ℕ} [Fact q.Prime]
    (hcard :
      CentralScalarCentralIntersectionOrdinaryInertiaFibreCardinalityHypothesis
        q)
    (hdegree :
      CentralScalarCentralIntersectionInertiaFibrePPrimeDegreeHypothesis
        q) :
    CentralScalarCentralIntersectionInertiaFibreCardinalityHypothesis q := by
  intro X _ _ S C hCnormal hcentral hgenerate
  letI : C.Normal := hCnormal
  intro g
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal S C hgenerate
  intro theta
  obtain ⟨hsource, htarget⟩ :=
    hdegree X S C hCnormal hcentral hgenerate g theta
  calc
    Nat.card
        (PPrimeIrreducibleCharactersOverInertia
          (product S C) theta.1 q) =
      Nat.card
        (IrreducibleCharactersOverInertia
          (product S C) theta.1) :=
      natCard_pPrimeIrreducibleCharactersOverInertia_eq_of_forall_isPPrimeDegree
        (product S C) theta.1 q hsource
    _ =
      Nat.card
        (IrreducibleCharactersOverInertia
          (internalProductNormalizer S C)
          (internalTheorem44CharacterEquiv
            S C
            (complementCharacterEquivOfGlauberman
              S C hcentral g) theta).1) :=
      hcard X S C hCnormal hcentral hgenerate g theta
    _ =
      Nat.card
        (PPrimeIrreducibleCharactersOverInertia
          (internalProductNormalizer S C)
          (internalTheorem44CharacterEquiv
            S C
            (complementCharacterEquivOfGlauberman
              S C hcentral g) theta).1 q) :=
      (natCard_pPrimeIrreducibleCharactersOverInertia_eq_of_forall_isPPrimeDegree
        (internalProductNormalizer S C)
        (internalTheorem44CharacterEquiv
          S C
          (complementCharacterEquivOfGlauberman
            S C hcentral g) theta).1 q htarget).symm

end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
