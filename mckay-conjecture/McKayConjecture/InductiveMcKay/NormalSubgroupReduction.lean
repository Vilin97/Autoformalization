/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.RossiNumericalReduction

/-!
# Elementary consequences of normal-subgroup local reductions

This file separates the elementary contradiction argument in Rossi's
normal-subgroup reduction from the genuine character-theoretic input.

For a fixed Sylow subgroup `P`, two explicit local-reduction principles are
assumed:

1. a normal noncentral subgroup `N` whose join with `N_G(P)` is proper
   produces a local correspondence at `P`;
2. after the first principle has forced
   `K ⊔ N_G(P) = G`, a normal subgroup `K` with
   `K ∩ P ≤ Z(G)` but `K ≰ Z(G)` produces a local correspondence at `P`.

If `G` is noncommutative and no local correspondence at `P` exists, these
principles force the two normal-subgroup conclusions in
`MinimalCounterexampleStructure`.  Properness of the Sylow normalizer is
also forced: if it were all of `G`, the elementary identity construction
`LocalCorrespondence.of_normalizer_eq_top` would give the forbidden local
correspondence.

No construction of either normal-subgroup local reduction is asserted here;
those are precisely the DGN/Rossi inputs retained as fields below.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory
open scoped IsMulCommutative

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {P : Sylow p G}

/-- The two explicit normal-subgroup local-reduction principles used in the
minimal-counterexample argument.

Both fields produce the same concrete conclusion,
`Nonempty (LocalCorrespondence P)`.  They contain all of the substantive
DGN/Rossi input; the passage from these fields to the structural
minimal-counterexample conclusions is elementary. -/
structure NormalSubgroupLocalReductionPrinciples
    (P : Sylow p G) : Prop where
  /-- A normal noncentral subgroup whose join with the chosen Sylow
  normalizer is proper produces a local correspondence. -/
  of_normal_noncentral_sup_sylowNormalizer_ne_top :
    ∀ N : Subgroup G,
      N.Normal →
      ¬N ≤ Subgroup.center G →
      N ⊔ Subgroup.normalizer (P : Set G) ≠ ⊤ →
      Nonempty (LocalCorrespondence P)
  /-- A normal subgroup with central Sylow intersection but which is itself
  noncentral produces a local correspondence once Corollary 4.3 has supplied
  the generation equality `G = K N_G(P)`.

  This equality is an essential input in Rossi's Proposition 4.5: it is used
  to make `L = KP` normal and to lift the Theorem-4.4 correspondence from
  `L` to `G`. -/
  of_normal_inf_sylow_le_center_not_le_center_of_sup_sylowNormalizer_eq_top :
    ∀ K : Subgroup G,
      K.Normal →
      K ⊓ (P : Subgroup G) ≤ Subgroup.center G →
      ¬K ≤ Subgroup.center G →
      K ⊔ Subgroup.normalizer (P : Set G) = ⊤ →
      Nonempty (LocalCorrespondence P)

namespace NormalSubgroupLocalReductionPrinciples

/-- If no local correspondence exists, the two explicit normal-subgroup
reduction principles force all structural fields of a Rossi minimal
counterexample.

In particular, no separate proper-normalizer hypothesis is required. -/
theorem minimalCounterexampleStructure
    (r : NormalSubgroupLocalReductionPrinciples P)
    (hnoncommutative : ¬IsMulCommutative G)
    (hnoLocal : ¬Nonempty (LocalCorrespondence P)) :
    MinimalCounterexampleStructure P where
  normalizer_ne_top := by
    intro hnormalizer
    exact hnoLocal
      ⟨LocalCorrespondence.of_normalizer_eq_top
        P hnormalizer⟩
  noncommutative := hnoncommutative
  normal_sup_sylowNormalizer_eq_top := by
    intro N hNnormal hNnoncentral
    by_contra hsup
    exact hnoLocal
      (r.of_normal_noncentral_sup_sylowNormalizer_ne_top
        N hNnormal hNnoncentral hsup)
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

end NormalSubgroupLocalReductionPrinciples

/-! ### Connection to central-index induction -/

/-- A central-index-induction formulation of the genuine normal-subgroup
input: in each noncommutative induction case, the smaller-central-index
local correspondences construct the two explicit normal-subgroup reduction
principles.

Unlike `NormalSubgroupReductionHypothesis`, this hypothesis does not assume
in advance that the Sylow normalizer is proper; that conclusion is derived
by `minimalCounterexampleStructure`. -/
def NormalSubgroupLocalReductionPrinciplesHypothesis
    (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G]
    (P : Sylow p G),
    ¬IsMulCommutative G →
    (∀ (H : Type) [Group H] [Finite H],
      centralIndex H < centralIndex G →
        ∀ Q : Sylow p H,
          Nonempty (LocalCorrespondence Q)) →
    NormalSubgroupLocalReductionPrinciples P

/-- The explicit two-principle central-index hypothesis implies the
normal-subgroup output interface used by the factorized Rossi numerical
reduction. -/
theorem normalSubgroupReductionHypothesis_of_localReductionPrinciples
    {p : ℕ} [Fact p.Prime]
    (h :
      NormalSubgroupLocalReductionPrinciplesHypothesis p) :
    NormalSubgroupReductionHypothesis p := by
  intro G _ _ P hnoncommutative _hnormalizer ih hnoLocal
  exact
    (h G P hnoncommutative ih).minimalCounterexampleStructure
      hnoncommutative hnoLocal

end InductiveMcKay
end McKayConjecture
