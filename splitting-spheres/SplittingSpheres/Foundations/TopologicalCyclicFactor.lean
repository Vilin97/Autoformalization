/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.TopologicalCyclicCover
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Pointed

/-!
# Factor maps in the tower of topological cyclic covers

When `k ∣ m`, the subgroup classifying the `m`-fold cyclic cover lies in the subgroup classifying
the `k`-fold cover.  The pointed covering-space lifting criterion therefore gives a unique map
from the `m`-cover to the `k`-cover over the base.  This file constructs that canonical factor map
and proves its identity and composition laws.
-/

@[expose] public section

noncomputable section

namespace SplittingSpheres

universe uX uE uB

open _root_.FundamentalGroup
open Topology Filter Set Function

/-- A local homeomorphism with locally path-connected codomain has locally path-connected
domain.  This is the local-property transfer needed for total spaces of covering maps. -/
theorem locallyPathConnectedSpace_of_isLocalHomeomorph
    {E : Type uE} {B : Type uB} [TopologicalSpace E] [TopologicalSpace B]
    [LocallyPathConnectedSpace B] {p : E → B} (hp : IsLocalHomeomorph p) :
    LocallyPathConnectedSpace E := by
  constructor
  intro e
  rw [Filter.hasBasis_self]
  intro U hU
  obtain ⟨W, hWU, hWopen, heW⟩ := mem_nhds_iff.mp hU
  let φ := hp.localInverseAt e
  have hpe_source : p e ∈ φ.source := hp.apply_self_mem_localInverseAt_source
  have hsource : IsOpen (φ.source ∩ φ ⁻¹' W) :=
    φ.continuousOn_toFun.isOpen_inter_preimage φ.open_source hWopen
  have hpe : p e ∈ φ.source ∩ φ ⁻¹' W := by
    refine ⟨hpe_source, ?_⟩
    simpa only [Set.mem_preimage, φ, hp.localInverseAt_apply_self] using heW
  obtain ⟨V, ⟨hVopen, hpeV, hVpath⟩, hVsub⟩ :=
    (isOpen_isPathConnected_basis (p e)).mem_iff.mp (hsource.mem_nhds hpe)
  refine ⟨φ '' V, ?_, hVpath.image' (φ.continuousOn_toFun.mono fun _ hv ↦ (hVsub hv).1), ?_⟩
  · exact (φ.isOpen_image_of_subset_source hVopen
      (hVsub.trans Set.inter_subset_left)).mem_nhds ⟨p e, hpeV, by simp [φ]⟩
  · rintro z ⟨y, hyV, rfl⟩
    exact hWU (hVsub hyV).2

variable {X : Type uX} [TopologicalSpace X] (x₀ : X)
  [LocallyPathConnectedSpace X] [PathConnectedSpace X]
  [TauCeti.SemilocallySimplyConnectedSpace X]

/-- The raw total space of the cyclic cover classified by `cyclicCoverSubgroup`. -/
abbrev CyclicCoverTotal
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2)) (m : ℕ) :=
  TauCeti.UniversalCover.SubgroupQuotient x₀ (cyclicCoverSubgroup x₀ π m)

/-- Projection from the raw cyclic-cover total space to the base. -/
abbrev cyclicCoverProj
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2)) (m : ℕ) :
    CyclicCoverTotal x₀ π m → X :=
  TauCeti.UniversalCover.subgroupQuotientProj x₀ (cyclicCoverSubgroup x₀ π m)

/-- Distinguished point of the raw cyclic cover over `x₀`. -/
abbrev cyclicCoverBasepoint
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2)) (m : ℕ) :
    CyclicCoverTotal x₀ π m :=
  TauCeti.UniversalCover.SubgroupQuotient.basepoint x₀ (cyclicCoverSubgroup x₀ π m)

/-- The pointed factor map from the `m`-cover to the `k`-cover exists uniquely when `k ∣ m`. -/
theorem existsUnique_cyclicCoverFactor
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2))
    {k m : ℕ} (h : k ∣ m) :
    ∃! F : C(CyclicCoverTotal x₀ π m, CyclicCoverTotal x₀ π k),
      F (cyclicCoverBasepoint x₀ π m) = cyclicCoverBasepoint x₀ π k ∧
      cyclicCoverProj x₀ π k ∘ F = cyclicCoverProj x₀ π m := by
  let _ : LocallyPathConnectedSpace (CyclicCoverTotal x₀ π m) :=
    locallyPathConnectedSpace_of_isLocalHomeomorph
      (TauCeti.UniversalCover.isCoveringMap_subgroupQuotientProj x₀
        (cyclicCoverSubgroup x₀ π m)).isLocalHomeomorph
  apply TauCeti.IsCoveringMap.existsUnique_continuousMap_comp_eq_of_range_le
    (TauCeti.UniversalCover.continuous_subgroupQuotientProj x₀
      (cyclicCoverSubgroup x₀ π m))
    (TauCeti.UniversalCover.isCoveringMap_subgroupQuotientProj x₀
      (cyclicCoverSubgroup x₀ π k))
    (TauCeti.UniversalCover.subgroupQuotientProj_basepoint x₀
      (cyclicCoverSubgroup x₀ π m))
    (TauCeti.UniversalCover.subgroupQuotientProj_basepoint x₀
      (cyclicCoverSubgroup x₀ π k))
  rw [TauCeti.UniversalCover.range_mapOfEq_subgroupQuotientProj,
    TauCeti.UniversalCover.range_mapOfEq_subgroupQuotientProj]
  exact cyclicCoverSubgroup_mono_dvd x₀ π h

/-- The canonical pointed factor map in the divisibility tower of cyclic covers. -/
def cyclicCoverFactor
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2))
    {k m : ℕ} (h : k ∣ m) :
    C(CyclicCoverTotal x₀ π m, CyclicCoverTotal x₀ π k) :=
  Classical.choose (existsUnique_cyclicCoverFactor x₀ π h)

@[simp]
theorem cyclicCoverFactor_basepoint
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2))
    {k m : ℕ} (h : k ∣ m) :
    cyclicCoverFactor x₀ π h (cyclicCoverBasepoint x₀ π m) =
      cyclicCoverBasepoint x₀ π k :=
  (Classical.choose_spec (existsUnique_cyclicCoverFactor x₀ π h)).1.1

/-- The factor map commutes with projection to the common base. -/
theorem cyclicCoverProj_comp_factor
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2))
    {k m : ℕ} (h : k ∣ m) :
    cyclicCoverProj x₀ π k ∘ cyclicCoverFactor x₀ π h = cyclicCoverProj x₀ π m :=
  (Classical.choose_spec (existsUnique_cyclicCoverFactor x₀ π h)).1.2

/-- A continuous map over the base carrying distinguished point to distinguished point is the
canonical cyclic-cover factor. -/
theorem eq_cyclicCoverFactor
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2))
    {k m : ℕ} (h : k ∣ m)
    (F : C(CyclicCoverTotal x₀ π m, CyclicCoverTotal x₀ π k))
    (hbase : F (cyclicCoverBasepoint x₀ π m) = cyclicCoverBasepoint x₀ π k)
    (hproj : cyclicCoverProj x₀ π k ∘ F = cyclicCoverProj x₀ π m) :
    F = cyclicCoverFactor x₀ π h :=
  (Classical.choose_spec (existsUnique_cyclicCoverFactor x₀ π h)).2 F ⟨hbase, hproj⟩

/-- The canonical factor associated to reflexive divisibility is the identity. -/
@[simp]
theorem cyclicCoverFactor_refl
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2)) (m : ℕ) :
    cyclicCoverFactor x₀ π (dvd_refl m) = ContinuousMap.id _ := by
  symm
  apply eq_cyclicCoverFactor x₀ π (dvd_refl m)
  · rfl
  · rfl

/-- Divisibility factor maps compose canonically. -/
theorem cyclicCoverFactor_comp
    (π : FundamentalGroup X x₀ ≃* FreeGroup (Fin 2))
    {k m d : ℕ} (hkm : k ∣ m) (hmd : m ∣ d) :
    (cyclicCoverFactor x₀ π hkm).comp (cyclicCoverFactor x₀ π hmd) =
      cyclicCoverFactor x₀ π (dvd_trans hkm hmd) := by
  apply eq_cyclicCoverFactor x₀ π (dvd_trans hkm hmd)
  · change cyclicCoverFactor x₀ π hkm
        (cyclicCoverFactor x₀ π hmd (cyclicCoverBasepoint x₀ π d)) =
      cyclicCoverBasepoint x₀ π k
    rw [cyclicCoverFactor_basepoint x₀ π hmd,
      cyclicCoverFactor_basepoint x₀ π hkm]
  · funext z
    have hmdProj := congrFun (cyclicCoverProj_comp_factor x₀ π hmd) z
    have hkmProj := congrFun (cyclicCoverProj_comp_factor x₀ π hkm)
      (cyclicCoverFactor x₀ π hmd z)
    exact hkmProj.trans hmdProj

end SplittingSpheres
