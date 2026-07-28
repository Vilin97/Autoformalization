/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.ComponentSubnormal
import McKayConjecture.GroupTheory.GeneralizedFitting
import McKayConjecture.GroupTheory.MinimalNormalAbelian
import McKayConjecture.GroupTheory.MinimalNormalFactors
import McKayConjecture.GroupTheory.SimpleQuasisimple

/-!
# Minimal normal subgroups lie in the generalized Fitting subgroup

The proof follows the elementary minimal-normal dichotomy.  An abelian
minimal normal subgroup is an elementary abelian `p`-group and therefore
lies in `O_p(G) ≤ F(G)`.  A nonabelian minimal normal subgroup is generated
by its simple factors; each factor is quasisimple and subnormal in the
ambient group, hence is a component and lies in `E(G)`.
-/

noncomputable section

universe u

namespace McKayConjecture.GroupTheory

open scoped IsMulCommutative
open MinimalNormalFactors

variable {G : Type u} [Group G]

namespace IsMinimalNormal

/-- An abelian finite minimal normal subgroup lies in the Fitting
subgroup. -/
theorem le_fittingSubgroup_of_isMulCommutative
    [Finite G] {N : Subgroup G}
    (hN : IsMinimalNormal N)
    (hcomm : IsMulCommutative N) :
    N ≤ fittingSubgroup G := by
  letI : IsMulCommutative N := hcomm
  obtain ⟨p, hp, hpow⟩ :=
    hN.exists_prime_pow_eq_one
  letI : Fact p.Prime := ⟨hp⟩
  have hpgroup : IsPGroup p N := by
    intro x
    exact ⟨1, by simpa using hpow x⟩
  exact (le_pCore hpgroup hN.normal).trans
    (pCore_le_fittingSubgroup hp)

/-- Every simple factor in a nonabelian minimal-normal decomposition is a
component of the ambient group. -/
theorem decomposition_factor_isComponent
    [Finite G] {N : Subgroup G} [N.Normal]
    (hN : IsMinimalNormal N)
    (D : NonabelianMinimalNormalDecomposition N)
    (i : D.ι) :
    IsComponent ((D.factor i).map N.subtype) := by
  have hfactorComponentN :
      IsComponent (D.factor i) := by
    refine ⟨(D.factor_minimalNormal i).normal.isSubnormal, ?_⟩
    exact isQuasisimple_of_isSimpleGroup
      (D.factor_simple i) (D.factor_nonabelian i)
  exact hfactorComponentN.map_subtype hN.normal.isSubnormal

/-- A nonabelian finite minimal normal subgroup lies in the layer. -/
theorem le_layer_of_not_isMulCommutative
    [Finite G] {N : Subgroup G}
    (hN : IsMinimalNormal N)
    (hnoncomm : ¬IsMulCommutative N) :
    N ≤ layer G := by
  letI : N.Normal := hN.normal
  let D : NonabelianMinimalNormalDecomposition N :=
    nonabelianMinimalNormalDecomposition hN hnoncomm
  have hfactors :
      ∀ i : D.ι,
        (D.factor i).map N.subtype ≤ layer G := by
    intro i
    exact (hN.decomposition_factor_isComponent D i).le_layer
  have htopMap :
      (⊤ : Subgroup N).map N.subtype ≤ layer G := by
    rw [← D.iSup_eq_top, Subgroup.map_iSup]
    exact iSup_le hfactors
  intro n hn
  exact htopMap ⟨⟨n, hn⟩, Subgroup.mem_top _, rfl⟩

/-- Every finite minimal normal subgroup lies in the generalized Fitting
subgroup. -/
theorem le_generalizedFittingSubgroup
    [Finite G] {N : Subgroup G}
    (hN : IsMinimalNormal N) :
    N ≤ generalizedFittingSubgroup G := by
  by_cases hcomm : IsMulCommutative N
  · exact (hN.le_fittingSubgroup_of_isMulCommutative hcomm).trans
      fittingSubgroup_le_generalizedFitting
  · exact (hN.le_layer_of_not_isMulCommutative hcomm).trans
      layer_le_generalizedFitting

/-- A nontrivial finite group has nontrivial generalized Fitting
subgroup. -/
theorem generalizedFittingSubgroup_ne_bot
    [Finite G] [Nontrivial G] :
    generalizedFittingSubgroup G ≠ ⊥ := by
  obtain ⟨N, hN⟩ := exists_minimalNormal (G := G)
  intro hbot
  exact hN.ne_bot
    (eq_bot_iff.mpr
      (hN.le_generalizedFittingSubgroup.trans_eq hbot))

end IsMinimalNormal
end McKayConjecture.GroupTheory
