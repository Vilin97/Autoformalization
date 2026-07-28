/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralScalarNumericalCondition
import McKayConjecture.InductiveMcKay.MinimalCounterexampleStructure
import McKayConjecture.InductiveMcKay.QuasisimpleHypothesis

/-!
# Central-scalar numerical factorization of the Rossi reduction

This is the reduction interface used by the numerical McKay proof.
Compared with the full strengthened Conjecture A, it retains precisely the
central-value identity required by the projective factor-extension step.

The two normal-subgroup reductions and the final layer reduction must return
`CentralScalarLocalCorrespondence`.  Their underlying character bijections
therefore prove the numerical theorem, while their central cross identities
keep the central-index induction strong enough for the next invocation of
Rossi's Lemma 4.1.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory
open scoped IsMulCommutative

/-- The two normal-subgroup principles at exactly the central-scalar
numerical strength. -/
structure CentralScalarNormalSubgroupLocalReductionPrinciples
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) : Prop where
  /-- Proposition 4.2 when its intermediate is proper. -/
  of_normal_noncentral_sup_sylowNormalizer_ne_top :
    ∀ N : Subgroup G,
      N.Normal →
      ¬N ≤ Subgroup.center G →
      N ⊔ Subgroup.normalizer (P : Set G) ≠ ⊤ →
      Nonempty (CentralScalarLocalCorrespondence P)
  /-- Theorem 4.4 and Proposition 4.5 after the generation equality. -/
  of_normal_inf_sylow_le_center_not_le_center_of_sup_sylowNormalizer_eq_top :
    ∀ K : Subgroup G,
      K.Normal →
      K ⊓ (P : Subgroup G) ≤ Subgroup.center G →
      ¬K ≤ Subgroup.center G →
      K ⊔ Subgroup.normalizer (P : Set G) = ⊤ →
      Nonempty (CentralScalarLocalCorrespondence P)

namespace CentralScalarNormalSubgroupLocalReductionPrinciples

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {P : Sylow p G}

/-- Failure of the scalar numerical local condition, together with the two
normal-subgroup reductions, gives the standard numerical
minimal-counterexample structure. -/
theorem minimalCounterexampleStructure
    (r :
      CentralScalarNormalSubgroupLocalReductionPrinciples P)
    (hnoncommutative : ¬IsMulCommutative G)
    (hnoLocal :
      ¬Nonempty (CentralScalarLocalCorrespondence P)) :
    MinimalCounterexampleStructure P where
  normalizer_ne_top := by
    intro hnormalizer
    exact hnoLocal
      ⟨(LocalInductiveMcKayData.of_normalizer_eq_top
        P hnormalizer).toCentralScalarLocal⟩
  noncommutative := hnoncommutative
  normal_sup_sylowNormalizer_eq_top := by
    intro N hNnormal hNnoncentral
    by_contra hproper
    exact hnoLocal
      (r.of_normal_noncentral_sup_sylowNormalizer_ne_top
        N hNnormal hNnoncentral hproper)
  normal_le_center_of_inf_sylow_le_center := by
    intro K hKnormal hinf
    by_contra hKnoncentral
    have hgenerate :
        K ⊔ Subgroup.normalizer (P : Set G) = ⊤ := by
      by_contra hproper
      exact hnoLocal
        (r.of_normal_noncentral_sup_sylowNormalizer_ne_top
          K hKnormal hKnoncentral hproper)
    exact hnoLocal
      (r.of_normal_inf_sylow_le_center_not_le_center_of_sup_sylowNormalizer_eq_top
        K hKnormal hinf hKnoncentral hgenerate)

end CentralScalarNormalSubgroupLocalReductionPrinciples

/-- In each noncommutative central-index stage, scalar numerical data on
smaller groups constructs both normal-subgroup reduction principles. -/
def CentralScalarNormalSubgroupReductionHypothesis
    (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G]
    (P : Sylow p G),
    ¬IsMulCommutative G →
    (∀ (H : Type) [Group H] [Finite H],
      centralIndex H < centralIndex G →
        ∀ Q : Sylow p H,
          Nonempty (CentralScalarLocalCorrespondence Q)) →
    CentralScalarNormalSubgroupLocalReductionPrinciples P

/-- The final layer reduction at central-scalar numerical strength. -/
def CentralScalarLayerReductionHypothesis
    (p : ℕ) [Fact p.Prime] : Prop :=
  QuasisimpleInductiveMcKayHypothesis.{0} p →
    ∀ (G : Type) [Group G] [Finite G]
      (P : Sylow p G),
      MinimalCounterexampleStructure P →
        Nonempty (CentralScalarLocalCorrespondence P)

/-- The two scalar numerical Rossi inputs give the noncommutative
central-index step. -/
theorem noncommutativeCentralScalarCentralIndexStep_of_rossiHypotheses
    {p : ℕ} [Fact p.Prime]
    (normalReduction :
      CentralScalarNormalSubgroupReductionHypothesis p)
    (layerReduction :
      CentralScalarLayerReductionHypothesis p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p) :
    NoncommutativeCentralScalarCentralIndexInductionStep.{0} p := by
  intro G _ _ P hnoncommutative ih
  by_cases hnormalizer :
      Subgroup.normalizer (P : Set G) = ⊤
  · exact
      ⟨(LocalInductiveMcKayData.of_normalizer_eq_top
        P hnormalizer).toCentralScalarLocal⟩
  · by_cases hlocal :
        Nonempty (CentralScalarLocalCorrespondence P)
    · exact hlocal
    · exact
        layerReduction covers G P
          ((normalReduction G P hnoncommutative ih)
            |>.minimalCounterexampleStructure
              hnoncommutative hlocal)

/-- Scalar numerical Rossi reductions imply the scalar numerical
inductive-McKay condition for all finite groups. -/
theorem centralScalarNumericalInductiveMcKay_of_rossiHypotheses
    {p : ℕ} [Fact p.Prime]
    (normalReduction :
      CentralScalarNormalSubgroupReductionHypothesis p)
    (layerReduction :
      CentralScalarLayerReductionHypothesis p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p) :
    CentralScalarNumericalInductiveMcKay.{0} p :=
  centralScalarNumericalInductiveMcKay_of_noncommutativeCentralIndexStep
    (noncommutativeCentralScalarCentralIndexStep_of_rossiHypotheses
      normalReduction layerReduction covers)

/-- The public cardinal McKay statement obtained from the scalar numerical
Rossi reduction. -/
theorem statement_of_centralScalarRossiHypotheses
    {p : ℕ} [Fact p.Prime]
    (normalReduction :
      CentralScalarNormalSubgroupReductionHypothesis p)
    (layerReduction :
      CentralScalarLayerReductionHypothesis p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  (centralScalarNumericalInductiveMcKay_of_rossiHypotheses
    normalReduction layerReduction covers).statement G P

end InductiveMcKay
end McKayConjecture
