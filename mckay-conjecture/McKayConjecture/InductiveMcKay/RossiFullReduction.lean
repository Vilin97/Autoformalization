/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralIndexInduction
import McKayConjecture.InductiveMcKay.EquivariantMinimalCounterexampleStructure
import McKayConjecture.InductiveMcKay.QuasisimpleHypothesis

/-!
# Full factorization of the Rossi reduction

Rossi's induction is an induction on the strengthened inductive McKay
condition, not merely on the numerical cardinal equality.  This distinction
is essential in Lemma 4.1: the correspondence on a smaller projective
factor extension must preserve the prescribed central scalar character.
That preservation is supplied by the character-triple part of
`LocalInductiveMcKayData`.

This file records the sound full-strength factorization.  The two
normal-subgroup principles and the layer exit all produce complete local
inductive-McKay data.  Once those inputs have been constructed, ordinary
well-founded induction on the central index gives the full inductive McKay
condition, from which the public numerical statement follows.

The propositions below are interfaces, not axioms.  Later files must
construct their inhabitants.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory
open scoped IsMulCommutative

/-- Full-strength versions of the two normal-subgroup reductions in
Rossi's minimal-counterexample argument.

Unlike `NormalSubgroupLocalReductionPrinciples`, both fields return the
equivariant correspondence and all central character-triple witnesses.
This is the strength required to contradict failure of the inductive McKay
condition at the current central-index induction stage. -/
structure FullNormalSubgroupLocalReductionPrinciples
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) : Prop where
  /-- Proposition 4.2 for a normal noncentral subgroup whose local
  intermediate is proper. -/
  of_normal_noncentral_sup_sylowNormalizer_ne_top :
    ∀ N : Subgroup G,
      N.Normal →
      AutomorphismInvariant (SylowAutStabilizer P) N →
      ¬N ≤ Subgroup.center G →
      N ⊔ Subgroup.normalizer (P : Set G) ≠ ⊤ →
      Nonempty (LocalInductiveMcKayData P)
  /-- Theorem 4.4 and Proposition 4.5 after Corollary 4.3 has supplied
  the required generation equality. -/
  of_normal_inf_sylow_le_center_not_le_center_of_sup_sylowNormalizer_eq_top :
    ∀ K : Subgroup G,
      K.Normal →
      AutomorphismInvariant (SylowAutStabilizer P) K →
      K ⊓ (P : Subgroup G) ≤ Subgroup.center G →
      ¬K ≤ Subgroup.center G →
      K ⊔ Subgroup.normalizer (P : Set G) = ⊤ →
      Nonempty (LocalInductiveMcKayData P)

namespace FullNormalSubgroupLocalReductionPrinciples

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {P : Sylow p G}

/-- If complete local data does not exist, the two full-strength
normal-subgroup reductions force the structural conclusions used by the
layer argument. -/
theorem minimalCounterexampleStructure
    (r : FullNormalSubgroupLocalReductionPrinciples P)
    (hnoncommutative : ¬IsMulCommutative G)
    (hnoLocal : ¬Nonempty (LocalInductiveMcKayData P)) :
    EquivariantMinimalCounterexampleStructure P where
  normalizer_ne_top := by
    intro hnormalizer
    exact hnoLocal
      ⟨LocalInductiveMcKayData.of_normalizer_eq_top
        P hnormalizer⟩
  noncommutative := hnoncommutative
  invariantNormal_sup_sylowNormalizer_eq_top := by
    intro N hNnormal hNinvariant hNnoncentral
    by_contra hproper
    exact hnoLocal
      (r.of_normal_noncentral_sup_sylowNormalizer_ne_top
        N hNnormal hNinvariant hNnoncentral hproper)
  invariantNormal_le_center_of_inf_sylow_le_center := by
    intro K hKnormal hKinvariant hinf
    by_contra hKnoncentral
    have hgenerate :
        K ⊔ Subgroup.normalizer (P : Set G) = ⊤ := by
      by_contra hproper
      exact hnoLocal
        (r.of_normal_noncentral_sup_sylowNormalizer_ne_top
          K hKnormal hKinvariant hKnoncentral hproper)
    exact hnoLocal
      (r.of_normal_inf_sylow_le_center_not_le_center_of_sup_sylowNormalizer_eq_top
        K hKnormal hKinvariant hinf hKnoncentral hgenerate)

end FullNormalSubgroupLocalReductionPrinciples

/-- In every noncommutative central-index induction case, complete local
data on all smaller groups constructs the two full normal-subgroup
reduction principles. -/
def FullNormalSubgroupReductionHypothesis
    (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G]
    (P : Sylow p G),
    ¬IsMulCommutative G →
    (∀ (H : Type) [Group H] [Finite H],
      centralIndex H < centralIndex G →
        ∀ Q : Sylow p H,
          Nonempty (LocalInductiveMcKayData Q)) →
    FullNormalSubgroupLocalReductionPrinciples P

/-- The full-strength output of the layer part of the reduction. -/
def FullLayerReductionHypothesis
    (p : ℕ) [Fact p.Prime] : Prop :=
  QuasisimpleInductiveMcKayHypothesis.{0} p →
    ∀ (G : Type) [Group G] [Finite G]
      (P : Sylow p G),
      EquivariantMinimalCounterexampleStructure P →
        Nonempty (LocalInductiveMcKayData P)

/-- The two full-strength Rossi inputs give the noncommutative part of
central-index induction. -/
theorem noncommutativeCentralIndexStep_of_fullRossiHypotheses
    {p : ℕ} [Fact p.Prime]
    (normalReduction :
      FullNormalSubgroupReductionHypothesis p)
    (layerReduction :
      FullLayerReductionHypothesis p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p) :
    NoncommutativeCentralIndexInductionStep.{0} p := by
  intro G _ _ P hnoncommutative ih
  by_cases hnormalizer :
      Subgroup.normalizer (P : Set G) = ⊤
  · exact
      ⟨LocalInductiveMcKayData.of_normalizer_eq_top
        P hnormalizer⟩
  · by_cases hlocal :
        Nonempty (LocalInductiveMcKayData P)
    · exact hlocal
    · exact
        layerReduction covers G P
          ((normalReduction G P hnoncommutative ih)
            |>.minimalCounterexampleStructure
              hnoncommutative hlocal)

/-- Full Rossi normal-subgroup and layer reductions imply the inductive
McKay condition for all finite groups. -/
theorem inductiveMcKayCondition_of_fullRossiHypotheses
    {p : ℕ} [Fact p.Prime]
    (normalReduction :
      FullNormalSubgroupReductionHypothesis p)
    (layerReduction :
      FullLayerReductionHypothesis p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p) :
    InductiveMcKayCondition.{0} p :=
  inductiveMcKayCondition_of_noncommutativeCentralIndexStep
    (noncommutativeCentralIndexStep_of_fullRossiHypotheses
      normalReduction layerReduction covers)

/-- Cardinal McKay statement obtained only after the full reduction has
been completed. -/
theorem statement_of_fullRossiHypotheses
    {p : ℕ} [Fact p.Prime]
    (normalReduction :
      FullNormalSubgroupReductionHypothesis p)
    (layerReduction :
      FullLayerReductionHypothesis p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  (inductiveMcKayCondition_of_fullRossiHypotheses
    normalReduction layerReduction covers).statement G P

end InductiveMcKay
end McKayConjecture
