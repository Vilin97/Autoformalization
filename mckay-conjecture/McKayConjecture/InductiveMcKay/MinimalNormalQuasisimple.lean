/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.MinimalNormalQuasisimple
import McKayConjecture.InductiveMcKay.QuasisimpleHypothesis

/-!
# Inductive-McKay data on the factors of a minimal normal subgroup

The factors of a finite nonabelian minimal normal subgroup are nonabelian
simple, hence quasisimple.  A quasisimple inductive-McKay hypothesis
therefore supplies full local data on every factor and, after forgetting
structure, a family of numerical local correspondences.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory
open GroupTheory.MinimalNormalFactors

variable {G : Type u} [Group G] [Finite G]
variable {N : Subgroup G} [N.Normal]
variable {p : ℕ}

namespace QuasisimpleInductiveMcKayHypothesis

/-- Full local inductive-McKay data supplied on one simple factor of a
nonabelian minimal-normal decomposition. -/
def factorLocalData
    (h : QuasisimpleInductiveMcKayHypothesis.{u} p)
    (D : NonabelianMinimalNormalDecomposition N)
    (i : D.ι) (P : Sylow p (D.factor i)) :
    LocalInductiveMcKayData P :=
  Classical.choice
    (h (D.factor i) (D.factor_isQuasisimple i) P)

/-- The numerical local correspondence underlying the full datum on a
simple factor. -/
def factorLocalCorrespondence
    (h : QuasisimpleInductiveMcKayHypothesis.{u} p)
    (D : NonabelianMinimalNormalDecomposition N)
    (i : D.ι) (P : Sylow p (D.factor i)) :
    LocalCorrespondence P :=
  (h.factorLocalData D i P).toLocal

/-- Simultaneously choose numerical local correspondences for a family of
Sylow subgroups of all the simple factors. -/
def factorLocalCorrespondenceFamily
    (h : QuasisimpleInductiveMcKayHypothesis.{u} p)
    (D : NonabelianMinimalNormalDecomposition N)
    (P : ∀ i, Sylow p (D.factor i)) :
    ∀ i, LocalCorrespondence (P i) :=
  fun i ↦ h.factorLocalCorrespondence D i (P i)

end QuasisimpleInductiveMcKayHypothesis

end InductiveMcKay
end McKayConjecture
