/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupIntermediateCentralScalarAssembly
import McKayConjecture.InductiveMcKay.NormalSubgroupRestrictedFactorInertiaFibre
import McKayConjecture.InductiveMcKay.RossiCentralScalarReduction

/-!
# Central-scalar normal-subgroup reduction

The scalar-local central-index induction hypothesis now constructs Rossi's
Proposition 4.2 correspondence directly.  The fixed restricted factor is
converted to the ordinary target inertia fibre, Sylow fusion assembles the
fibre equivalences, and lying-over on the common join-center subgroup gives
the required central-scalar identity.

Consequently, the only remaining normal-subgroup input in the central-scalar
Rossi reduction is the central-intersection case (Theorem 4.4 followed by
Proposition 4.5).  This file isolates that input and proves that it supplies
the formerly bundled pair of normal-subgroup principles.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- The unresolved central-intersection half of the central-scalar
normal-subgroup reduction.

Unlike `CentralScalarNormalSubgroupReductionHypothesis`, this proposition
does not retain Proposition 4.2 as an assumption: that half is constructed
from the scalar-local central-index induction hypothesis below. -/
def CentralScalarCentralIntersectionReductionHypothesis
    (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G]
    (P : Sylow p G) (K : Subgroup G),
    K.Normal →
    K ⊓ (P : Subgroup G) ≤ Subgroup.center G →
    ¬K ≤ Subgroup.center G →
    K ⊔ Subgroup.normalizer (P : Set G) = ⊤ →
    Nonempty (CentralScalarLocalCorrespondence P)

/-- Scalar-local central-index induction discharges Proposition 4.2, so the
central-intersection hypothesis alone supplies the complete normal-subgroup
input to the central-scalar Rossi reduction. -/
theorem centralScalarNormalSubgroupReductionHypothesis_of_centralIntersection
    {p : ℕ} [Fact p.Prime]
    (centralIntersection :
      CentralScalarCentralIntersectionReductionHypothesis p) :
    CentralScalarNormalSubgroupReductionHypothesis p := by
  intro G _ _ P _hnoncommutative ih
  refine
    { of_normal_noncentral_sup_sylowNormalizer_ne_top := ?_
      of_normal_inf_sylow_le_center_not_le_center_of_sup_sylowNormalizer_eq_top :=
        ?_ }
  · intro N hNnormal hNnoncentral hproper
    letI : N.Normal := hNnormal
    exact
      ⟨NormalSubgroupIntermediateOrbitAssembly.InertiaFibreData.toCentralScalarLocalCorrespondence
        P N
        (NormalSubgroupRestrictedFactorInertiaFibre.inertiaFibreDataOfCentralScalarLocalIH
          P N ih hNnoncentral)
        hproper⟩
  · intro K hKnormal hcentral hKnoncentral hgenerate
    exact
      centralIntersection G P K hKnormal
        hcentral hKnoncentral hgenerate

end InductiveMcKay
end McKayConjecture
