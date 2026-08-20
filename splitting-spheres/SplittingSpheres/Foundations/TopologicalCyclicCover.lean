/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.CyclicCharacter
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Existence
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.RecoveredSubgroup
public import TauCeti.Topology.Homotopy.Monodromy.Basic

/-!
# Topological cyclic covers classified by the two-handle character

Given a based space whose fundamental group has been identified with the free group on the left
and right handle generators, this file constructs the connected cover classified by the kernel of
the cyclic character.  It also proves the exact number of sheets and the subgroup inclusions that
produce factor maps when one degree divides another.
-/

@[expose] public section

open scoped Multiplicative

noncomputable section

namespace SplittingSpheres

universe uX

variable {X : Type uX} [TopologicalSpace X] (x₀ : X)

/-- The subgroup of the fundamental group classifying the degree-`m` cyclic cover. -/
def cyclicCoverSubgroup
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2)) (m : ℕ) :
    Subgroup (FundamentalGroup X x₀) :=
  (cyclicCharacter m).ker.comap π.toMonoidHom

instance cyclicCoverSubgroup_normal
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2)) (m : ℕ) :
    (cyclicCoverSubgroup x₀ π m).Normal :=
  (MonoidHom.normal_ker (cyclicCharacter m)).comap π.toMonoidHom

/-- The classifying subgroups nest in the direction required for a cover of degree `m` to factor
through one of degree `k`. -/
theorem cyclicCoverSubgroup_mono_dvd
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2)) {k m : ℕ} (h : k ∣ m) :
    cyclicCoverSubgroup x₀ π m ≤ cyclicCoverSubgroup x₀ π k :=
  Subgroup.comap_mono (cyclicCharacter_ker_mono h)

/-- The classifying subgroup has index `m`. -/
theorem cyclicCoverSubgroup_index
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2)) (m : ℕ) [NeZero m] :
    (cyclicCoverSubgroup x₀ π m).index = m := by
  rw [cyclicCoverSubgroup,
    Subgroup.index_comap_of_surjective (H := (cyclicCharacter m).ker) π.surjective,
    cyclicCharacter_ker_index]

/-- The connected topological cyclic cover supplied by the universal-cover classification. -/
def topologicalCyclicCover [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [TauCeti.SemilocallySimplyConnectedSpace X]
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2)) (m : ℕ) :
    TauCeti.ConnectedCoveringSpace (TopCat.of X) :=
  TauCeti.UniversalCover.subgroupCover x₀ (cyclicCoverSubgroup x₀ π m)

/-- The raw subgroup-quotient projection defining the cyclic cover has exactly `m` points in the
fibre over the chosen basepoint. -/
theorem card_fiber_topologicalCyclicCover
    [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [TauCeti.SemilocallySimplyConnectedSpace X]
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2)) (m : ℕ) [NeZero m] :
    Nat.card
        (TauCeti.UniversalCover.subgroupQuotientProj x₀ (cyclicCoverSubgroup x₀ π m) ⁻¹'
          {x₀}) = m := by
  let H := cyclicCoverSubgroup x₀ π m
  let hp := TauCeti.UniversalCover.isCoveringMap_subgroupQuotientProj x₀ H
  let e : TauCeti.UniversalCover.subgroupQuotientProj x₀ H ⁻¹' {x₀} :=
    ⟨TauCeti.UniversalCover.SubgroupQuotient.basepoint x₀ H,
      TauCeti.UniversalCover.subgroupQuotientProj_basepoint x₀ H⟩
  have hcard := TauCeti.IsCoveringMap.card_fiber_eq_index hp e
  have hrange :
      (FundamentalGroup.mapOfEq
        ⟨TauCeti.UniversalCover.subgroupQuotientProj x₀ H, hp.continuous⟩ e.2).range = H := by
    simpa only [e] using
      TauCeti.UniversalCover.range_mapOfEq_subgroupQuotientProj x₀ H
  rw [hrange] at hcard
  exact hcard.trans (cyclicCoverSubgroup_index x₀ π m)

end SplittingSpheres
