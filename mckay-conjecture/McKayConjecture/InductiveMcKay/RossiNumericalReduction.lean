/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralIndexInduction
import McKayConjecture.InductiveMcKay.MinimalCounterexampleStructure
import McKayConjecture.InductiveMcKay.QuasisimpleHypothesis

/-!
# Numerical factorization of the Rossi reduction

For the numerical McKay theorem, the central-index induction separates into
two logically distinct assertions.

* The normal-subgroup reduction shows that a noncommutative induction case
  with proper Sylow normalizer has `MinimalCounterexampleStructure`.
* The layer reduction uses the inductive McKay condition on quasisimple
  groups and that structure to construct a local character correspondence.

This file proves that those two assertions imply the numerical inductive
McKay condition, and hence the McKay theorem.  The definitions are
propositions, not axioms: later files must construct their inhabitants.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- The exact output required from the normal-subgroup part of Rossi's
minimal-counterexample argument. -/
def NormalSubgroupReductionHypothesis
    (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G]
    (P : Sylow p G),
    ¬IsMulCommutative G →
    Subgroup.normalizer (P : Set G) ≠ ⊤ →
    (∀ (H : Type) [Group H] [Finite H],
      centralIndex H < centralIndex G →
        ∀ Q : Sylow p H,
          Nonempty (LocalCorrespondence Q)) →
    ¬Nonempty (LocalCorrespondence P) →
    MinimalCounterexampleStructure P

/-- The exact numerical output required from the layer/Clifford part of
Rossi's reduction. -/
def LayerReductionHypothesis
    (p : ℕ) [Fact p.Prime] : Prop :=
  QuasisimpleInductiveMcKayHypothesis.{0} p →
    ∀ (G : Type) [Group G] [Finite G]
      (P : Sylow p G),
      MinimalCounterexampleStructure P →
        Nonempty (LocalCorrespondence P)

/-- The two halves of the Rossi reduction give a noncommutative
central-index induction step. -/
theorem noncommutativeNumericalCentralIndexStep_of_rossiHypotheses
    {p : ℕ} [Fact p.Prime]
    (normalReduction :
      NormalSubgroupReductionHypothesis p)
    (layerReduction :
      LayerReductionHypothesis p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p) :
    NoncommutativeNumericalCentralIndexInductionStep.{0} p := by
  intro G _ _ P hnoncomm ih
  by_cases hnormalizer :
      Subgroup.normalizer (P : Set G) = ⊤
  · exact
      ⟨LocalCorrespondence.of_normalizer_eq_top
        P hnormalizer⟩
  · by_cases hlocal :
        Nonempty (LocalCorrespondence P)
    · exact hlocal
    · exact
        layerReduction covers G P
          (normalReduction G P hnoncomm
            hnormalizer ih hlocal)

/-- Numerical Rossi normal-subgroup and layer reductions imply the numerical
inductive McKay condition for all finite groups. -/
theorem numericalInductiveMcKay_of_rossiHypotheses
    {p : ℕ} [Fact p.Prime]
    (normalReduction :
      NormalSubgroupReductionHypothesis p)
    (layerReduction :
      LayerReductionHypothesis p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p) :
    NumericalInductiveMcKay.{0} p :=
  numericalInductiveMcKay_of_noncommutativeCentralIndexStep
    (noncommutativeNumericalCentralIndexStep_of_rossiHypotheses
      normalReduction layerReduction covers)

/-- Cardinal form of the preceding factorized Rossi reduction. -/
theorem statement_of_rossiHypotheses
    {p : ℕ} [Fact p.Prime]
    (normalReduction :
      NormalSubgroupReductionHypothesis p)
    (layerReduction :
      LayerReductionHypothesis p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  (numericalInductiveMcKay_of_rossiHypotheses
    normalReduction layerReduction covers).statement G P

end InductiveMcKay
end McKayConjecture
