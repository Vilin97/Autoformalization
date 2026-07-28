/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FiniteTensorPermutationComparison

/-!
# Constructing paired tensor-permutation cocycles

For applications, the natural input is a pair of coordinate transport
families for which each two-step composite differs from the one-step
transport by one common scalar.  This file chooses those scalars once and
uses them as the factors of two tensor-permutation cocycles.

Thus exact equality of the two global factor sets is not an assumption.  It
is forced by the common local projective multiplication law.
-/

noncomputable section

universe u v w

namespace McKayConjecture
namespace CharacterTriple

variable {K : Type u} [Field K]
variable {A : Type v} [Group A]
variable {ι : Type w} [MulAction A ι]
variable {V W : Type*}
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

/-- Two coordinate transport systems with one common scalar discrepancy in
each multiplication law. -/
structure PairedFiniteTensorPermutationTransport where
  /-- Coordinate transports on the source spaces. -/
  sourceTransport :
    A → ι → V ≃ₗ[K] V
  /-- Coordinate transports on the target spaces. -/
  targetTransport :
    A → ι → W ≃ₗ[K] W
  /-- The two transport systems have a common local projective factor. -/
  common_mul :
    ∀ (a b : A) (i : ι),
      ∃ c : Kˣ,
        sourceTransport a i *
              sourceTransport b (a⁻¹ • i) =
            scalarLinearEquiv K V c *
              sourceTransport (a * b) i ∧
          targetTransport a i *
              targetTransport b (a⁻¹ • i) =
            scalarLinearEquiv K W c *
              targetTransport (a * b) i

namespace PairedFiniteTensorPermutationTransport

/-- The common factor selected from the local projective multiplication
law. -/
def factor
    (T : PairedFiniteTensorPermutationTransport
      (K := K) (A := A) (ι := ι) (V := V) (W := W))
    (a b : A) (i : ι) : Kˣ :=
  Classical.choose (T.common_mul a b i)

/-- Source tensor-permutation cocycle constructed using the selected common
factor. -/
def sourceCocycle
    (T : PairedFiniteTensorPermutationTransport
      (K := K) (A := A) (ι := ι) (V := V) (W := W)) :
    FiniteTensorPermutationCocycle
      (K := K) (A := A) (ι := ι) V where
  transport := T.sourceTransport
  factor := T.factor
  transport_mul a b i :=
    (Classical.choose_spec (T.common_mul a b i)).1

/-- Target tensor-permutation cocycle constructed using the same selected
factor. -/
def targetCocycle
    (T : PairedFiniteTensorPermutationTransport
      (K := K) (A := A) (ι := ι) (V := V) (W := W)) :
    FiniteTensorPermutationCocycle
      (K := K) (A := A) (ι := ι) W where
  transport := T.targetTransport
  factor := T.factor
  transport_mul a b i :=
    (Classical.choose_spec (T.common_mul a b i)).2

/-- The two constructed cocycles have literally equal coordinate factors. -/
theorem cocycleAgreement
    (T : PairedFiniteTensorPermutationTransport
      (K := K) (A := A) (ι := ι) (V := V) (W := W)) :
    FiniteTensorPermutationCocycleAgreement
      T.sourceCocycle T.targetCocycle where
  factor_eq _ _ _ := rfl

/-- A common scalar action of the two coordinate transport systems at one
group element. -/
def HasCommonCoordinateScalarAction
    (T : PairedFiniteTensorPermutationTransport
      (K := K) (A := A) (ι := ι) (V := V) (W := W))
    (a : A) : Prop :=
  ∃ c : ι → Kˣ,
    (∀ i : ι, a • i = i) ∧
      (∀ i : ι,
        T.sourceTransport a i =
          scalarLinearEquiv K V (c i)) ∧
      ∀ i : ι,
        T.targetTransport a i =
          scalarLinearEquiv K W (c i)

/-- Common scalar transport data gives the comparison structure used by the
assembled tensor-permutation operators. -/
def commonScalar
    (T : PairedFiniteTensorPermutationTransport
      (K := K) (A := A) (ι := ι) (V := V) (W := W))
    {a : A}
    (h : T.HasCommonCoordinateScalarAction a) :
    FiniteTensorPermutationCommonScalar
      T.sourceCocycle T.targetCocycle a := by
  let hc :
      Nonempty
        {c : ι → Kˣ //
          (∀ i : ι, a • i = i) ∧
            (∀ i : ι,
              T.sourceTransport a i =
                scalarLinearEquiv K V (c i)) ∧
            ∀ i : ι,
              T.targetTransport a i =
                scalarLinearEquiv K W (c i)} := by
    rcases h with ⟨c, hfixed, hsource, htarget⟩
    exact ⟨⟨c, hfixed, hsource, htarget⟩⟩
  let c := Classical.choice hc
  exact
    { scalar := c.1
      source := ⟨c.2.1, c.2.2.1⟩
      target := ⟨c.2.1, c.2.2.2⟩ }

end PairedFiniteTensorPermutationTransport

end CharacterTriple
end McKayConjecture
