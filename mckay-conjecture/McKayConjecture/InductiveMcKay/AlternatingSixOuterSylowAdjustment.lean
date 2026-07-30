/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurOuterClassActionAutomorphisms
import McKayConjecture.InductiveMcKay.SylowAutomorphismInnerAdjustment

/-!
# Sylow-stabilizing outer representatives for the universal cover of `A₆`

The two audited automorphisms of the canonical universal cover need not
preserve the arbitrarily fixed Sylow subgroups.  Sylow conjugacy supplies
inner corrections, giving representatives of the same two outer classes
inside each fixed Sylow automorphism stabilizer.

The final generation statements in this file deliberately retain one
explicit hypothesis: the two audited classes generate the outer
automorphism quotient.  Proving that hypothesis requires a classification
of all automorphisms of the sixfold cover; it is not implied merely by
constructing the two audited automorphisms.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixOuterAdjustmentFactPrimeTwo :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

local instance alternatingSixOuterAdjustmentFactPrimeThree :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

local instance alternatingSixOuterAdjustmentFactPrimeFive :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- The first audited outer representative, adjusted by an inner
automorphism to stabilize the fixed Sylow `p`-subgroup. -/
def alternatingSixUniversalCoverSylowAdjustedAlphaOne
    (p : ℕ) [Fact p.Prime] :
    SylowAutStabilizer
      (alternatingSixUniversalCoverSylow p) :=
  sylowAdjustedAutomorphism
    (alternatingSixUniversalCoverSylow p)
    alternatingSixUniversalCoverAlphaOneAutomorphism

/-- The second audited outer representative, adjusted by an inner
automorphism to stabilize the fixed Sylow `p`-subgroup. -/
def alternatingSixUniversalCoverSylowAdjustedAlphaTwo
    (p : ℕ) [Fact p.Prime] :
    SylowAutStabilizer
      (alternatingSixUniversalCoverSylow p) :=
  sylowAdjustedAutomorphism
    (alternatingSixUniversalCoverSylow p)
    alternatingSixUniversalCoverAlphaTwoAutomorphism

/-- The two adjusted outer representatives in the fixed Sylow
automorphism stabilizer. -/
def alternatingSixUniversalCoverSylowAdjustedOuterGenerators
    (p : ℕ) [Fact p.Prime] :
    Set
      (SylowAutStabilizer
        (alternatingSixUniversalCoverSylow p)) :=
  {alternatingSixUniversalCoverSylowAdjustedAlphaOne p,
    alternatingSixUniversalCoverSylowAdjustedAlphaTwo p}

/-- The images of the two audited automorphisms in the outer
automorphism quotient. -/
def alternatingSixUniversalCoverOuterQuotientGenerators :
    Set
      (OuterAutomorphismQuotient
        AlternatingSixUniversalCover) :=
  {QuotientGroup.mk'
      (InnerAutomorphismSubgroup
        AlternatingSixUniversalCover)
      alternatingSixUniversalCoverAlphaOneAutomorphism,
    QuotientGroup.mk'
      (InnerAutomorphismSubgroup
        AlternatingSixUniversalCover)
      alternatingSixUniversalCoverAlphaTwoAutomorphism}

/-- The exact remaining automorphism-classification input: the two
audited outer classes generate the full outer automorphism group of the
canonical universal cover. -/
def AlternatingSixUniversalCoverOuterQuotientGeneration :
    Prop :=
  Subgroup.closure
      alternatingSixUniversalCoverOuterQuotientGenerators =
    ⊤

/-- Inner correction leaves the first audited representative unchanged in
the outer quotient. -/
@[simp]
theorem alternatingSixUniversalCoverSylowAdjustedAlphaOne_outer
    (p : ℕ) [Fact p.Prime] :
    sylowAutStabilizerOuterHom
        (alternatingSixUniversalCoverSylow p)
        (alternatingSixUniversalCoverSylowAdjustedAlphaOne p) =
      QuotientGroup.mk'
        (InnerAutomorphismSubgroup
          AlternatingSixUniversalCover)
        alternatingSixUniversalCoverAlphaOneAutomorphism :=
  sylowAutStabilizerOuterHom_adjusted
    (alternatingSixUniversalCoverSylow p)
    alternatingSixUniversalCoverAlphaOneAutomorphism

/-- Inner correction leaves the second audited representative unchanged
in the outer quotient. -/
@[simp]
theorem alternatingSixUniversalCoverSylowAdjustedAlphaTwo_outer
    (p : ℕ) [Fact p.Prime] :
    sylowAutStabilizerOuterHom
        (alternatingSixUniversalCoverSylow p)
        (alternatingSixUniversalCoverSylowAdjustedAlphaTwo p) =
      QuotientGroup.mk'
        (InnerAutomorphismSubgroup
          AlternatingSixUniversalCover)
        alternatingSixUniversalCoverAlphaTwoAutomorphism :=
  sylowAutStabilizerOuterHom_adjusted
    (alternatingSixUniversalCoverSylow p)
    alternatingSixUniversalCoverAlphaTwoAutomorphism

/-- The adjusted generators have exactly the two audited images in the
outer quotient. -/
theorem alternatingSixUniversalCover_adjustedOuterGenerators_image
    (p : ℕ) [Fact p.Prime] :
    sylowAutStabilizerOuterHom
          (alternatingSixUniversalCoverSylow p) ''
        alternatingSixUniversalCoverSylowAdjustedOuterGenerators p =
      alternatingSixUniversalCoverOuterQuotientGenerators := by
  rw [alternatingSixUniversalCoverSylowAdjustedOuterGenerators,
    alternatingSixUniversalCoverOuterQuotientGenerators]
  ext q
  simp only [Set.mem_image, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases ha with rfl | rfl
    · exact Or.inl
        (alternatingSixUniversalCoverSylowAdjustedAlphaOne_outer p)
    · exact Or.inr
        (alternatingSixUniversalCoverSylowAdjustedAlphaTwo_outer p)
  · rintro (rfl | rfl)
    · exact
        ⟨alternatingSixUniversalCoverSylowAdjustedAlphaOne p,
          Or.inl rfl,
          alternatingSixUniversalCoverSylowAdjustedAlphaOne_outer p⟩
    · exact
        ⟨alternatingSixUniversalCoverSylowAdjustedAlphaTwo p,
          Or.inr rfl,
          alternatingSixUniversalCoverSylowAdjustedAlphaTwo_outer p⟩

/-- The global two-generator outer-quotient hypothesis implies that the
adjusted representatives generate the outer quotient at every fixed
Sylow subgroup. -/
theorem alternatingSixUniversalCover_adjusted_generatesSylowOuterQuotient
    (p : ℕ) [Fact p.Prime]
    (hgeneration :
      AlternatingSixUniversalCoverOuterQuotientGeneration) :
    GeneratesSylowOuterQuotient
      (alternatingSixUniversalCoverSylow p)
      (alternatingSixUniversalCoverSylowAdjustedOuterGenerators p) := by
  rw [GeneratesSylowOuterQuotient,
    alternatingSixUniversalCover_adjustedOuterGenerators_image]
  exact hgeneration

/-- Consequently the two adjusted representatives, together with inner
automorphisms from the exact normalizer, generate the full Sylow
automorphism stabilizer. -/
theorem
    alternatingSixUniversalCover_adjusted_generatesSylowAutStabilizerModuloInner
    (p : ℕ) [Fact p.Prime]
    (hgeneration :
      AlternatingSixUniversalCoverOuterQuotientGeneration) :
    GeneratesSylowAutStabilizerModuloInner
      (alternatingSixUniversalCoverSylow p)
      (alternatingSixUniversalCoverSylowAdjustedOuterGenerators p) :=
  generatesSylowAutStabilizerModuloInner_of_generatesOuter
    (alternatingSixUniversalCoverSylow p)
    (alternatingSixUniversalCoverSylowAdjustedOuterGenerators p)
    (alternatingSixUniversalCover_adjusted_generatesSylowOuterQuotient
      p hgeneration)

/-- Sylow-two specialization of the stabilizer-generation reduction. -/
theorem
    alternatingSixUniversalCoverTwo_adjusted_generatesSylowAutStabilizerModuloInner
    (hgeneration :
      AlternatingSixUniversalCoverOuterQuotientGeneration) :
    GeneratesSylowAutStabilizerModuloInner
      (alternatingSixUniversalCoverSylow 2)
      (alternatingSixUniversalCoverSylowAdjustedOuterGenerators 2) :=
  alternatingSixUniversalCover_adjusted_generatesSylowAutStabilizerModuloInner
    2 hgeneration

/-- Sylow-three specialization of the stabilizer-generation reduction. -/
theorem
    alternatingSixUniversalCoverThree_adjusted_generatesSylowAutStabilizerModuloInner
    (hgeneration :
      AlternatingSixUniversalCoverOuterQuotientGeneration) :
    GeneratesSylowAutStabilizerModuloInner
      (alternatingSixUniversalCoverSylow 3)
      (alternatingSixUniversalCoverSylowAdjustedOuterGenerators 3) :=
  alternatingSixUniversalCover_adjusted_generatesSylowAutStabilizerModuloInner
    3 hgeneration

/-- Sylow-five specialization of the stabilizer-generation reduction. -/
theorem
    alternatingSixUniversalCoverFive_adjusted_generatesSylowAutStabilizerModuloInner
    (hgeneration :
      AlternatingSixUniversalCoverOuterQuotientGeneration) :
    GeneratesSylowAutStabilizerModuloInner
      (alternatingSixUniversalCoverSylow 5)
      (alternatingSixUniversalCoverSylowAdjustedOuterGenerators 5) :=
  alternatingSixUniversalCover_adjusted_generatesSylowAutStabilizerModuloInner
    5 hgeneration

end InductiveMcKay
end McKayConjecture
