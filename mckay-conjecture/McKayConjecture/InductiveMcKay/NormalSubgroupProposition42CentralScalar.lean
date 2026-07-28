/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralScalarReduction

/-!
# Proposition 4.2 at central-scalar numerical strength

The fixed-factor inertia descent and canonical Clifford-orbit assembly
construct Rossi's Proposition-4.2 correspondence from central-scalar local
data on groups of smaller central index.  When the normalizer intermediate
is proper, its central-value identity packages the result as the first
normal-subgroup principle used by the central-scalar Rossi reduction.

This file also exposes the narrow constructor for the two-principle
interface.  Its only remaining argument is the independent Theorem-4.4 /
Proposition-4.5 branch.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupProposition42CentralScalar

open GroupTheory
open NormalSubgroupIntermediateOrbitAssembly
open NormalSubgroupRestrictedFactorInertiaFibre

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (P : Sylow p G)

/-- Smaller-central-index central-scalar local data construct the first
normal-subgroup principle of the Rossi reduction. -/
theorem localCorrespondence_of_centralScalarLocalIH
    (ih :
      ∀ (Y : Type) [Group Y] [Finite Y],
        centralIndex Y < centralIndex G →
          ∀ Q : Sylow p Y,
            Nonempty (CentralScalarLocalCorrespondence Q))
    (N : Subgroup G)
    (hNnormal : N.Normal)
    (hNnoncentral : ¬N ≤ Subgroup.center G)
    (hproper :
      N ⊔ Subgroup.normalizer (P : Set G) ≠ ⊤) :
    Nonempty (CentralScalarLocalCorrespondence P) := by
  letI : N.Normal := hNnormal
  exact
    ⟨(inertiaFibreDataOfCentralScalarLocalIH
        P N ih hNnoncentral).toCentralScalarLocalCorrespondence
      P N hproper⟩

/-- The exact constructor consumed by the central-scalar Rossi reduction:
Proposition 4.2 is now automatic, while the independent central-intersection
branch remains explicit. -/
theorem localReductionPrinciplesOfCentralScalarLocalIH
    (ih :
      ∀ (Y : Type) [Group Y] [Finite Y],
        centralIndex Y < centralIndex G →
          ∀ Q : Sylow p Y,
            Nonempty (CentralScalarLocalCorrespondence Q))
    (second :
      ∀ K : Subgroup G,
        K.Normal →
        K ⊓ (P : Subgroup G) ≤ Subgroup.center G →
        ¬K ≤ Subgroup.center G →
        K ⊔ Subgroup.normalizer (P : Set G) = ⊤ →
        Nonempty (CentralScalarLocalCorrespondence P)) :
    CentralScalarNormalSubgroupLocalReductionPrinciples P where
  of_normal_noncentral_sup_sylowNormalizer_ne_top :=
    localCorrespondence_of_centralScalarLocalIH P ih
  of_normal_inf_sylow_le_center_not_le_center_of_sup_sylowNormalizer_eq_top :=
    second

end NormalSubgroupProposition42CentralScalar
end InductiveMcKay
end McKayConjecture
