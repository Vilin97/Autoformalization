/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.CentralExtensionDerived
import McKayConjecture.GroupTheory.ComponentSubnormal
import McKayConjecture.GroupTheory.FittingProduct
import McKayConjecture.GroupTheory.MinimalNormalFactors

/-!
# The Fitting centralizer in a component-free finite group

If a finite group has no components, its Fitting subgroup contains its own
centralizer.  The proof passes to the centralizer modulo its intersection
with the Fitting subgroup and chooses a minimal normal subgroup there.
An abelian minimal normal subgroup lifts to a normal nilpotent subgroup.  A
nonabelian minimal normal subgroup has a simple factor whose full preimage
has quasisimple derived subgroup, producing a component.
-/

noncomputable section

open scoped IsMulCommutative

universe u

namespace McKayConjecture.GroupTheory

open MinimalNormalFactors

variable {G : Type u} [Group G] [Finite G]

/-- In a finite group with trivial layer, the Fitting subgroup contains
its ambient centralizer. -/
theorem centralizer_fittingSubgroup_le_of_layer_eq_bot
    (hlayer : layer G = ⊥) :
    Subgroup.centralizer (fittingSubgroup G : Set G) ≤
      fittingSubgroup G := by
  by_contra hnle
  let F : Subgroup G := fittingSubgroup G
  let C : Subgroup G :=
    Subgroup.centralizer (F : Set G)
  let Z : Subgroup G := F ⊓ C
  letI : F.Normal := inferInstance
  letI : C.Normal := inferInstance
  letI : Z.Normal := inferInstance
  have hCnotleF : ¬C ≤ F := by
    exact hnle
  have hCnotleZ : ¬C ≤ Z := by
    intro hCZ
    exact hCnotleF (hCZ.trans inf_le_left)
  let q : G →* G ⧸ Z := QuotientGroup.mk' Z
  let Cbar : Subgroup (G ⧸ Z) := C.map q
  have hCbarNormal : Cbar.Normal :=
    Subgroup.Normal.map inferInstance q
      (QuotientGroup.mk'_surjective Z)
  have hCbarNe : Cbar ≠ ⊥ := by
    intro hbot
    apply hCnotleZ
    have hle :
        C ≤ q.ker :=
      (Subgroup.map_eq_bot_iff (H := C)).mp hbot
    rwa [QuotientGroup.ker_mk'] at hle
  obtain ⟨Mbar, hMbar, hMbarC⟩ :=
    exists_minimalNormal_le hCbarNormal hCbarNe
  letI : Mbar.Normal := hMbar.normal
  let X : Subgroup G := Mbar.comap q
  have hXnormal : X.Normal :=
    Subgroup.Normal.comap hMbar.normal q
  letI : X.Normal := hXnormal
  have hZX : Z ≤ X := by
    intro z hz
    change q z ∈ Mbar
    have hzq : q z = 1 :=
      (QuotientGroup.eq_one_iff z).mpr hz
    rw [hzq]
    exact Mbar.one_mem
  have hXleC : X ≤ C := by
    have hle :
        Mbar.comap q ≤ (C.map q).comap q :=
      Subgroup.comap_mono hMbarC
    have hkerC : q.ker ≤ C := by
      rw [QuotientGroup.ker_mk']
      exact inf_le_right
    change Mbar.comap q ≤ C
    rwa [Subgroup.comap_map_eq_self
      (f := q) (H := C) hkerC] at hle
  have hXmap : X.map q = Mbar := by
    exact Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective Z) Mbar
  let f : X →* Mbar :=
    (q.domRestrict X).codRestrict Mbar
      (fun x => x.property)
  have hfSurjective : Function.Surjective f := by
    intro m
    obtain ⟨g, hg⟩ :=
      QuotientGroup.mk'_surjective Z (m : G ⧸ Z)
    have hgX : g ∈ X := by
      change q g ∈ Mbar
      rw [hg]
      exact m.property
    refine ⟨⟨g, hgX⟩, ?_⟩
    apply Subtype.ext
    exact hg
  have hfKerCenter : f.ker ≤ Subgroup.center X := by
    intro k hk
    have hkZ : (k : G) ∈ Z := by
      rw [← QuotientGroup.ker_mk' Z]
      change q (k : G) = 1
      exact congrArg Subtype.val hk
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    have hxC : (x : G) ∈ C :=
      hXleC x.property
    exact (hxC (k : G) hkZ.1).symm
  by_cases hMcomm : IsMulCommutative Mbar
  · letI : IsMulCommutative Mbar := hMcomm
    letI : CommGroup Mbar := inferInstance
    have hXnilpotent : Group.IsNilpotent X :=
      Subgroup.isNilpotent_of_ker_le_center f hfKerCenter
    have hXleF : X ≤ F :=
      normal_isNilpotent_le_fittingSubgroup
        X hXnormal hXnilpotent
    have hXZ : X = Z :=
      le_antisymm (le_inf hXleF hXleC) hZX
    have hMbarBot : Mbar = ⊥ := by
      rw [← hXmap, hXZ]
      exact
        (Subgroup.map_eq_bot_iff (H := Z)).mpr
          (by
            rw [QuotientGroup.ker_mk'])
    exact hMbar.ne_bot hMbarBot
  · let D :
        NonabelianMinimalNormalDecomposition Mbar :=
      nonabelianMinimalNormalDecomposition
        hMbar hMcomm
    let i : D.ι := Classical.choice D.nonempty
    let S : Subgroup Mbar := D.factor i
    let P : Subgroup X := S.comap f
    have hPnormal : P.Normal :=
      Subgroup.Normal.comap
        (D.factor_minimalNormal i).normal f
    letI : P.Normal := hPnormal
    let fP : P →* S :=
      (f.domRestrict P).codRestrict S
        (fun x => x.property)
    have hfPSurjective :
        Function.Surjective fP := by
      intro s
      obtain ⟨x, hx⟩ := hfSurjective (s : Mbar)
      have hxP : x ∈ P := by
        change f x ∈ S
        rw [hx]
        exact s.property
      refine ⟨⟨x, hxP⟩, ?_⟩
      apply Subtype.ext
      exact hx
    have hfPKerCenter :
        fP.ker ≤ Subgroup.center P := by
      intro k hk
      have hkXcenter :
          (k : X) ∈ Subgroup.center X := by
        apply hfKerCenter
        change f (k : X) = 1
        exact congrArg Subtype.val hk
      rw [Subgroup.mem_center_iff]
      intro x
      apply Subtype.ext
      exact
        Subgroup.mem_center_iff.mp hkXcenter
          (x : X)
    let E : CentralExtension P S :=
      { projection := fP
        surjective := hfPSurjective
        ker_le_center := hfPKerCenter }
    have hKquasisimple :
        IsQuasisimple (_root_.commutator P) :=
      E.commutator_isQuasisimple
        (D.factor_simple i)
        (D.factor_nonabelian i)
    have hKcomponentP :
        IsComponent (_root_.commutator P) :=
      ⟨(inferInstance :
          (_root_.commutator P).Normal).isSubnormal,
        hKquasisimple⟩
    have hKcomponentX :
        IsComponent
          ((_root_.commutator P).map P.subtype) :=
      hKcomponentP.map_subtype hPnormal.isSubnormal
    have hKcomponentG :
        IsComponent
          (((_root_.commutator P).map P.subtype).map
            X.subtype) :=
      hKcomponentX.map_subtype hXnormal.isSubnormal
    apply hKcomponentG.ne_bot
    exact eq_bot_iff.mpr
      (hKcomponentG.le_layer.trans_eq hlayer)

end McKayConjecture.GroupTheory
