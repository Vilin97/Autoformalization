/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupRestrictedFactorInertiaFibre
import McKayConjecture.InductiveMcKay.NormalSubgroupProposition42CentralScalar
import McKayConjecture.InductiveMcKay.SolvableNormalSubgroupFactorFibre

/-!
# Proposition 4.2 inside solvable-group induction

Every inertia subgroup and every canonical factor extension arising from a
solvable ambient group is solvable.  Thus the already proved fixed-factor
descent and orbit assembly construct Rossi's Proposition 4.2 using only
smaller solvable groups.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupRestrictedFactorInertiaFibre

open CharacterTriple
open CliffordCorrespondence
open GroupTheory
open NormalSubgroupAssociatedFactorFibre
open NormalSubgroupInertiaFactorDescent
open NormalSubgroupIntermediateInertia
open NormalSubgroupIntermediateOrbitAssembly
open NormalSubgroupRestrictedFactorFibre

variable {G : Type} [Group G] [Finite G] [Group.IsSolvable G]
variable {p : ℕ} [Fact p.Prime]
variable (P : Sylow p G)
variable (N : Subgroup G) [N.Normal]

/-- In a solvable ambient group, smaller-solvable central-scalar data
supplies all ordinary inertia-fibre equivalences used by Proposition 4.2. -/
def inertiaFibreDataOfSolvableCentralScalarLocalIH
    (ih :
      ∀ (Y : Type) [Group Y] [Finite Y] [Group.IsSolvable Y],
        centralIndex Y < centralIndex G →
          ∀ Q : Sylow p Y,
            Nonempty (CentralScalarLocalCorrespondence Q))
    (hNnoncentral : ¬N ≤ Subgroup.center G) :
    InertiaFibreData P N where
  fibreEquiv θ hP :=
    (CharacterTriple.pPrimeIrreducibleCharactersOverInertiaEquivTriple
      (joinCenter N) θ.1 p).trans
      ((restrictedPPrimeCharacterEquivOfSolvableCentralScalarLocalIH
        ih
        (inertiaTriple N θ.1)
        (inertiaTriple_character_isPPrimeDegree N θ)
        (centralIndex_inertiaFactorExtension_lt
          N hNnoncentral θ.1)
        (inertiaQuotientSylow N P θ.1 hP)).trans
        ((fixedRestrictedFactorInertiaDescent
          P N).fibreEquiv θ hP))

end NormalSubgroupRestrictedFactorInertiaFibre

namespace NormalSubgroupProposition42CentralScalar

open GroupTheory
open NormalSubgroupIntermediateOrbitAssembly
open NormalSubgroupRestrictedFactorInertiaFibre

variable {G : Type} [Group G] [Finite G] [Group.IsSolvable G]
variable {p : ℕ} [Fact p.Prime]
variable (P : Sylow p G)

/-- The Proposition-4.2 local correspondence in a solvable ambient group,
using only scalar-local induction data on smaller solvable groups. -/
theorem localCorrespondence_of_solvableCentralScalarLocalIH
    (ih :
      ∀ (Y : Type) [Group Y] [Finite Y] [Group.IsSolvable Y],
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
    ⟨(inertiaFibreDataOfSolvableCentralScalarLocalIH
        P N ih hNnoncentral).toCentralScalarLocalCorrespondence
      P N hproper⟩

/-- Solvable Proposition 4.2 plus an explicit central-intersection branch
give the two normal-subgroup principles. -/
theorem localReductionPrinciplesOfSolvableCentralScalarLocalIH
    (ih :
      ∀ (Y : Type) [Group Y] [Finite Y] [Group.IsSolvable Y],
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
    localCorrespondence_of_solvableCentralScalarLocalIH P ih
  of_normal_inf_sylow_le_center_not_le_center_of_sup_sylowNormalizer_eq_top :=
    second

end NormalSubgroupProposition42CentralScalar
end InductiveMcKay
end McKayConjecture
