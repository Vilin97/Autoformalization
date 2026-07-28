/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.LayerTensorPermutationCanonicalRealization
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralScalarReduction
import McKayConjecture.InductiveMcKay.UniversalCoverQuasisimpleDescent

/-!
# Final central-scalar reduction interface

After the fixed-factor inertia transport and the tensor-permutation layer
assembly, the final interface isolates the two remaining mathematical
inputs:

* the central-intersection (Theorem 4.4/Proposition 4.5) reduction;
* the inductive McKay condition for finite quasisimple groups.

The canonical layer realization is supplied internally by source covariance
and projective Schur uniqueness.  The theorems in this file compose the two
remaining inputs with the proved central-index induction and cardinality
interfaces.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-- The three remaining constructive inputs imply the central-scalar
numerical inductive-McKay condition for every finite group in `Type`. -/
theorem centralScalarNumericalInductiveMcKay_of_centralIntersection_tensorPermutation_quasisimple
    {p : ℕ} [Fact p.Prime]
    (centralIntersection :
      CentralScalarCentralIntersectionReductionHypothesis p)
    (layerAssembly :
      CanonicalMinimalLayerTensorPermutationAssemblyHypothesis p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p) :
    CentralScalarNumericalInductiveMcKay.{0} p :=
  centralScalarNumericalInductiveMcKay_of_rossiHypotheses
    (centralScalarNormalSubgroupReductionHypothesis_of_centralIntersection
      centralIntersection)
    (centralScalarLayerReductionHypothesis_of_tensorPermutationAssembly
      layerAssembly)
    covers

/-- Public McKay cardinal equality obtained from the three remaining
constructive inputs. -/
theorem statement_of_centralIntersection_tensorPermutation_quasisimple
    {p : ℕ} [Fact p.Prime]
    (centralIntersection :
      CentralScalarCentralIntersectionReductionHypothesis p)
    (layerAssembly :
      CanonicalMinimalLayerTensorPermutationAssemblyHypothesis p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  (centralScalarNumericalInductiveMcKay_of_centralIntersection_tensorPermutation_quasisimple
    centralIntersection layerAssembly covers).statement G P

/-- Universal-cover form of the final tensor-permutation reduction. -/
theorem centralScalarNumericalInductiveMcKay_of_centralIntersection_tensorPermutation_universalCover
    {p : ℕ} [Fact p.Prime]
    (centralIntersection :
      CentralScalarCentralIntersectionReductionHypothesis p)
    (layerAssembly :
      CanonicalMinimalLayerTensorPermutationAssemblyHypothesis p)
    (covers :
      UniversalCoverInductiveMcKayHypothesis.{0} p) :
    CentralScalarNumericalInductiveMcKay.{0} p :=
  centralScalarNumericalInductiveMcKay_of_centralIntersection_tensorPermutation_quasisimple
    centralIntersection layerAssembly
    covers.toQuasisimple

/-- Public McKay statement in the universal-cover formulation of the
tensor-permutation reduction. -/
theorem statement_of_centralIntersection_tensorPermutation_universalCover
    {p : ℕ} [Fact p.Prime]
    (centralIntersection :
      CentralScalarCentralIntersectionReductionHypothesis p)
    (layerAssembly :
      CanonicalMinimalLayerTensorPermutationAssemblyHypothesis p)
    (covers :
      UniversalCoverInductiveMcKayHypothesis.{0} p)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  (centralScalarNumericalInductiveMcKay_of_centralIntersection_tensorPermutation_universalCover
    centralIntersection layerAssembly covers).statement G P

/-- The same final reduction with the canonical finite coordinates,
permutation actions, cocycles, factor agreement, and central fixed-coordinate
claims discharged.  Its layer input is only the remaining transport and
global-intertwiner realization package. -/
theorem centralScalarNumericalInductiveMcKay_of_centralIntersection_canonicalRealization_quasisimple
    {p : ℕ} [Fact p.Prime]
    (centralIntersection :
      CentralScalarCentralIntersectionReductionHypothesis p)
    (layerRealization :
      CanonicalMinimalLayerTensorPermutationRealizationHypothesis p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p) :
    CentralScalarNumericalInductiveMcKay.{0} p :=
  centralScalarNumericalInductiveMcKay_of_centralIntersection_tensorPermutation_quasisimple
    centralIntersection
    (canonicalMinimalLayerTensorPermutationAssemblyHypothesis_of_realization
      layerRealization)
    covers

/-- Public McKay cardinal equality from the central-intersection input, the
canonical tensor-permutation realization package, and the quasisimple local
correspondences. -/
theorem statement_of_centralIntersection_canonicalRealization_quasisimple
    {p : ℕ} [Fact p.Prime]
    (centralIntersection :
      CentralScalarCentralIntersectionReductionHypothesis p)
    (layerRealization :
      CanonicalMinimalLayerTensorPermutationRealizationHypothesis p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  (centralScalarNumericalInductiveMcKay_of_centralIntersection_canonicalRealization_quasisimple
    centralIntersection layerRealization covers).statement G P

/-- Universal-cover form of the final canonical-realization reduction. -/
theorem centralScalarNumericalInductiveMcKay_of_canonicalRealization_universalCover
    {p : ℕ} [Fact p.Prime]
    (centralIntersection :
      CentralScalarCentralIntersectionReductionHypothesis p)
    (layerRealization :
      CanonicalMinimalLayerTensorPermutationRealizationHypothesis p)
    (covers :
      UniversalCoverInductiveMcKayHypothesis.{0} p) :
    CentralScalarNumericalInductiveMcKay.{0} p :=
  centralScalarNumericalInductiveMcKay_of_centralIntersection_canonicalRealization_quasisimple
    centralIntersection layerRealization
    covers.toQuasisimple

/-- Public McKay statement in the universal-cover formulation of the
canonical-realization reduction. -/
theorem statement_of_centralIntersection_canonicalRealization_universalCover
    {p : ℕ} [Fact p.Prime]
    (centralIntersection :
      CentralScalarCentralIntersectionReductionHypothesis p)
    (layerRealization :
      CanonicalMinimalLayerTensorPermutationRealizationHypothesis p)
    (covers :
      UniversalCoverInductiveMcKayHypothesis.{0} p)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  (centralScalarNumericalInductiveMcKay_of_canonicalRealization_universalCover
    centralIntersection layerRealization covers).statement G P

/-- With canonical layer realization discharged, the central-intersection
and quasisimple inputs imply the numerical inductive-McKay condition. -/
theorem centralScalarNumericalInductiveMcKay_of_centralIntersection_quasisimple
    {p : ℕ} [Fact p.Prime]
    (centralIntersection :
      CentralScalarCentralIntersectionReductionHypothesis p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p) :
    CentralScalarNumericalInductiveMcKay.{0} p :=
  centralScalarNumericalInductiveMcKay_of_centralIntersection_canonicalRealization_quasisimple
    centralIntersection
    canonicalMinimalLayerTensorPermutationRealizationHypothesis
    covers

/-- Public McKay equality after the canonical layer realization has been
discharged. -/
theorem statement_of_centralIntersection_quasisimple
    {p : ℕ} [Fact p.Prime]
    (centralIntersection :
      CentralScalarCentralIntersectionReductionHypothesis p)
    (covers :
      QuasisimpleInductiveMcKayHypothesis.{0} p)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  (centralScalarNumericalInductiveMcKay_of_centralIntersection_quasisimple
    centralIntersection covers).statement G P

/-- Universal-cover form with canonical layer realization discharged. -/
theorem centralScalarNumericalInductiveMcKay_of_centralIntersection_universalCover
    {p : ℕ} [Fact p.Prime]
    (centralIntersection :
      CentralScalarCentralIntersectionReductionHypothesis p)
    (covers :
      UniversalCoverInductiveMcKayHypothesis.{0} p) :
    CentralScalarNumericalInductiveMcKay.{0} p :=
  centralScalarNumericalInductiveMcKay_of_centralIntersection_quasisimple
    centralIntersection covers.toQuasisimple

/-- Public McKay equality in the universal-cover formulation, with the
layer realization no longer an external hypothesis. -/
theorem statement_of_centralIntersection_universalCover
    {p : ℕ} [Fact p.Prime]
    (centralIntersection :
      CentralScalarCentralIntersectionReductionHypothesis p)
    (covers :
      UniversalCoverInductiveMcKayHypothesis.{0} p)
    (G : Type) [Group G] [Finite G]
    (P : Sylow p G) :
    Statement G p P :=
  (centralScalarNumericalInductiveMcKay_of_centralIntersection_universalCover
    centralIntersection covers).statement G P

end InductiveMcKay
end McKayConjecture
