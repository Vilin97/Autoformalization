/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.OpenDiffeomorphExtension

/-!
# Extending smooth families of open-submanifold maps

A jointly smooth family of self-maps of an open submanifold extends jointly smoothly to the
ambient manifold when every member is uniformly the identity off a fixed closed subset of the
open domain.
-/

@[expose] public section

noncomputable section

open Function Set Topology
open TopologicalSpace
open scoped ContDiff Manifold

namespace SplittingSpheres

universe uE uH uM uEP uHP uP

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H]
  {IM : ModelWithCorners ℝ E H}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {EP : Type uEP} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type uHP} [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP}
  {P : Type uP} [TopologicalSpace P] [ChartedSpace HP P]

/-- A jointly smooth family on an open submanifold extends jointly smoothly by the ambient
identity when its members are uniformly fixed off a closed subset of the open domain. -/
theorem contMDiff_extendOpenMapFamilyByIdentity
    (U : Opens M) (K : Set M) (f : P × U → U)
    (hf : ContMDiff (IP.prod IM) IM ∞ f)
    (hKclosed : IsClosed K) (hKU : K ⊆ U)
    (hfix : ∀ p : P × U, p.2.1 ∉ K → f p = p.2) :
    ContMDiff (IP.prod IM) IM ∞
      (fun p : P × M ↦
        extendOpenMapByIdentity U (fun z ↦ f (p.1, z)) p.2) := by
  intro p
  by_cases hpU : p.2 ∈ U
  · let V : Opens (P × M) :=
      ⟨Set.univ ×ˢ (U : Set M), isOpen_univ.prod U.2⟩
    have hpV : p ∈ V := ⟨Set.mem_univ _, hpU⟩
    let pV : V := ⟨p, hpV⟩
    apply (contMDiffAt_subtype_iff
      (U := V) (f := fun q : P × M ↦
        extendOpenMapByIdentity U (fun z ↦ f (q.1, z)) q.2)
      (x := pV)).mp
    have hval : ContMDiff (IP.prod IM) (IP.prod IM) ∞
        (Subtype.val : V → P × M) := contMDiff_subtype_val
    have hfst : ContMDiff (IP.prod IM) IP ∞ (fun q : V ↦ q.1.1) :=
      contMDiff_fst.comp hval
    have hsnd : ContMDiff (IP.prod IM) IM ∞ (fun q : V ↦ q.1.2) :=
      contMDiff_snd.comp hval
    have hsndU : ContMDiff (IP.prod IM) IM ∞
        (fun q : V ↦ (⟨q.1.2, q.2.2⟩ : U)) := by
      apply (ContMDiff.subtypeVal_comp_iff U _).mp
      exact hsnd
    have hin : ContMDiff (IP.prod IM) (IP.prod IM) ∞
        (fun q : V ↦ (q.1.1, (⟨q.1.2, q.2.2⟩ : U))) :=
      hfst.prodMk hsndU
    have hopen : ContMDiff (IP.prod IM) IM ∞
        (fun q : V ↦ (f (q.1.1, ⟨q.1.2, q.2.2⟩) : M)) :=
      contMDiff_subtype_val.comp (hf.comp hin)
    apply (hopen pV).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun q ↦ by
      exact extendOpenMapByIdentity_coe U
        (fun z ↦ f (q.1.1, z)) ⟨q.1.2, q.2.2⟩
  · have hpK : p.2 ∉ K := fun hp ↦ hpU (hKU hp)
    apply contMDiffAt_snd.congr_of_eventuallyEq
    filter_upwards [continuousAt_snd.eventually
      (hKclosed.isOpen_compl.mem_nhds hpK)] with q hq
    exact extendOpenMapByIdentity_eq_self_of_not_mem U K
      (fun z ↦ f (q.1, z)) (fun z hz ↦ hfix (q.1, z) hz) hq

end SplittingSpheres
