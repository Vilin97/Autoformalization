/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.SetTheory.Cardinal.Finite
import McKayConjecture.GroupTheory.AlternatingSixGeneration
import McKayConjecture.GroupTheory.TwoGeneratorAutomorphismEvaluation

/-!
# Candidate generator images for automorphisms of `A₆`

The standard generators `a,b` of `A₆` satisfy

`a² = b⁴ = (ab)⁵ = (ab²)⁵ = 1`.

Consequently an automorphism determines a pair satisfying the same
relations, with nonidentity first coordinate.  Since `a,b` generate `A₆`,
the resulting evaluation map is injective.  The candidate type is written
as a sigma type so that its cardinality reduces to a nested finite sum.
-/

namespace McKayConjecture
namespace GroupTheory

open scoped BigOperators

/-- The relator conditions satisfied by the images of the standard
generators under an automorphism of `A₆`.  The condition on `x` is placed
first so the finite checker can reject non-involutions before inspecting
the second coordinate. -/
def AlternatingSixAutomorphismImagePairCondition
    (x y : AlternatingSix) :
    Prop :=
  x ^ 2 = 1 ∧
    x ≠ 1 ∧
      y ^ 4 = 1 ∧
        (x * y) ^ 5 = 1 ∧
          (x * y ^ 2) ^ 5 = 1

/-- The relator-pair condition is decidable by concrete permutation
calculation. -/
instance alternatingSixAutomorphismImagePairConditionDecidable
    (x y : AlternatingSix) :
    Decidable
      (AlternatingSixAutomorphismImagePairCondition x y) := by
  unfold AlternatingSixAutomorphismImagePairCondition
  infer_instance

/-- Candidate images of the two standard generators under an automorphism
of `A₆`. -/
abbrev AlternatingSixAutomorphismImagePair :=
  Σ x : AlternatingSix,
    {y : AlternatingSix //
      AlternatingSixAutomorphismImagePairCondition x y}

/-- For a fixed first image, the number of possible second images. -/
def alternatingSixAutomorphismSecondImageCard
    (x : AlternatingSix) :
    Nat :=
  (Finset.univ.filter
    fun y : AlternatingSix =>
      AlternatingSixAutomorphismImagePairCondition x y).card

/-- The part of the candidate count whose first image sends `0` to `i`. -/
def alternatingSixAutomorphismImagePairBlockCard
    (i : Fin 6) :
    Nat :=
  ∑ x : AlternatingSix,
    if i = x.1 0 then
      alternatingSixAutomorphismSecondImageCard x
    else
      0

/-- The sigma-type candidate cardinality is the nested finite sum used by
the checker. -/
theorem natCard_alternatingSixAutomorphismImagePair
    :
    Nat.card AlternatingSixAutomorphismImagePair =
      ∑ x : AlternatingSix,
        alternatingSixAutomorphismSecondImageCard x := by
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.card_subtype]
  rfl

/-- Evaluation of an automorphism on the standard generators, bundled with
the four presentation relations and the nonidentity condition. -/
def alternatingSixMulAutToImagePair
    (α : MulAut AlternatingSix) :
    AlternatingSixAutomorphismImagePair := by
  refine
    ⟨α alternatingSixPresentationA,
      ⟨α alternatingSixPresentationB, ?_⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [map_pow, map_one] using
      congrArg α alternatingSixPresentation_relations.1
  · intro himage
    have hsource :
        alternatingSixPresentationA = 1 := by
      apply α.injective
      simpa only [map_one] using himage
    exact (by decide : alternatingSixPresentationA ≠ 1) hsource
  · simpa only [map_pow, map_one] using
      congrArg α alternatingSixPresentation_relations.2.1
  · simpa only [map_mul, map_pow, map_one] using
      congrArg α alternatingSixPresentation_relations.2.2.1
  · simpa only [map_mul, map_pow, map_one] using
      congrArg α alternatingSixPresentation_relations.2.2.2

/-- Distinct automorphisms give distinct candidate image pairs. -/
theorem alternatingSixMulAutToImagePair_injective :
    Function.Injective
      alternatingSixMulAutToImagePair := by
  intro α β hpair
  apply
    twoGeneratorMulAutEvaluation_injective
      alternatingSixPresentationA
      alternatingSixPresentationB
      alternatingSixGeneratorSubgroup_eq_top
  exact congrArg
    (fun p : AlternatingSixAutomorphismImagePair =>
      (p.1, p.2.1))
    hpair

end GroupTheory
end McKayConjecture
