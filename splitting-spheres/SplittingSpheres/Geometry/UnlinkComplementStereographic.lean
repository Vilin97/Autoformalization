/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.UnlinkComplement

/-!
# Global stereographic coordinates on the standard-unlink complement

Any point of the standard unlink can serve as the pole of a stereographic chart containing its
entire complement.  This file chooses the explicit point on component zero and restricts that
chart to `StandardUnlinkComplement`.  Its image is an open subset of Euclidean four-space, and
the restricted chart is packaged as a genuine smooth diffeomorphism.
-/

@[expose] public section

open Function Set Topology TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace SplittingSpheres

local instance standardUnlinkStereographicFinrankFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (4 + 1))) = 4 + 1) :=
  ⟨by simp⟩

/-- The chosen stereographic pole, lying on component zero of the standard unlink. -/
def standardUnlinkStereographicPole : Sphere 4 :=
  standardUnlinkPoint 0

theorem standardUnlinkStereographicPole_mem_carrier :
    standardUnlinkStereographicPole ∈ standardUnlinkCarrier := by
  exact Or.inl (standardUnlinkPoint_mem_component 0)

/-- Every point of the strict unlink complement lies in the stereographic chart with the chosen
pole. -/
theorem standardUnlinkComplement_subset_stereographicSource :
    (standardUnlinkComplementOpens : Set (Sphere 4)) ⊆
      (stereographic' 4 standardUnlinkStereographicPole).source := by
  intro x hx
  rw [stereographic'_source]
  intro hxpole
  exact hx (hxpole ▸ standardUnlinkStereographicPole_mem_carrier)

/-- The strict standard-unlink complement is nonempty. -/
theorem standardUnlinkComplement_nonempty :
    Nonempty StandardUnlinkComplement := by
  let x : Sphere 3 := ⟨Classical.choose
      (NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin 4))
        (x := 0) (r := 1) |>.2 (by norm_num)),
    Classical.choose_spec
      (NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin 4))
        (x := 0) (r := 1) |>.2 (by norm_num))⟩
  refine ⟨⟨equatorSphereMap x, ?_⟩⟩
  exact Set.disjoint_left.1 disjoint_coordinateEquator_standardUnlinkCarrier
    (range_equatorSphereMap ▸ mem_range_self x)

/-- Stereographic projection restricted to the strict standard-unlink complement. -/
def standardUnlinkComplementStereographicPartialHomeomorph :
    OpenPartialHomeomorph StandardUnlinkComplement
      (EuclideanSpace ℝ (Fin 4)) :=
  (stereographic' 4 standardUnlinkStereographicPole).subtypeRestr
    standardUnlinkComplement_nonempty

@[simp]
theorem standardUnlinkComplementStereographicPartialHomeomorph_source :
    standardUnlinkComplementStereographicPartialHomeomorph.source = Set.univ := by
  rw [standardUnlinkComplementStereographicPartialHomeomorph,
    OpenPartialHomeomorph.subtypeRestr_source]
  ext x
  simp only [mem_preimage, mem_univ, iff_true]
  exact standardUnlinkComplement_subset_stereographicSource x.2

/-- The open Euclidean image of the strict standard-unlink complement under stereographic
projection. -/
def standardUnlinkComplementStereographicImage :
    Opens (EuclideanSpace ℝ (Fin 4)) :=
  ⟨standardUnlinkComplementStereographicPartialHomeomorph.target,
    standardUnlinkComplementStereographicPartialHomeomorph.open_target⟩

@[simp]
theorem standardUnlinkComplementStereographicPartialHomeomorph_target :
    standardUnlinkComplementStereographicPartialHomeomorph.target =
      standardUnlinkComplementStereographicImage :=
  rfl

theorem standardUnlinkComplementStereographicPartialHomeomorph_mem_maximalAtlas :
    standardUnlinkComplementStereographicPartialHomeomorph ∈
      IsManifold.maximalAtlas
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
        StandardUnlinkComplement := by
  apply StructureGroupoid.subtypeRestr_mem_maximalAtlas
  exact ⟨standardUnlinkStereographicPole, rfl⟩

/-- Global smooth stereographic coordinates identify the strict standard-unlink complement with
an open subset of Euclidean four-space. -/
def standardUnlinkComplementStereographicDiffeomorph :
    StandardUnlinkComplement
      ≃ₘ^∞⟮modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)),
        modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))⟯
      standardUnlinkComplementStereographicImage := by
  let f : StandardUnlinkComplement →
      standardUnlinkComplementStereographicImage := fun x ↦
    ⟨standardUnlinkComplementStereographicPartialHomeomorph x,
      standardUnlinkComplementStereographicPartialHomeomorph.map_source
        (standardUnlinkComplementStereographicPartialHomeomorph_source.symm ▸
          Set.mem_univ x)⟩
  let g : standardUnlinkComplementStereographicImage →
      StandardUnlinkComplement := fun y ↦
    standardUnlinkComplementStereographicPartialHomeomorph.symm y.1
  let e : StandardUnlinkComplement ≃
      standardUnlinkComplementStereographicImage :=
    { toFun := f
      invFun := g
      left_inv := fun x ↦
        standardUnlinkComplementStereographicPartialHomeomorph.left_inv
          (standardUnlinkComplementStereographicPartialHomeomorph_source.symm ▸
            Set.mem_univ x)
      right_inv := fun y ↦
        Subtype.ext
          (standardUnlinkComplementStereographicPartialHomeomorph.right_inv y.2) }
  have hf : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞ f := by
    rw [← ContMDiff.subtypeVal_comp_iff standardUnlinkComplementStereographicImage]
    change ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      standardUnlinkComplementStereographicPartialHomeomorph
    apply contMDiffOn_univ.mp
    rw [← standardUnlinkComplementStereographicPartialHomeomorph_source]
    exact contMDiffOn_of_mem_maximalAtlas
      standardUnlinkComplementStereographicPartialHomeomorph_mem_maximalAtlas
  have hg : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞ g := by
    intro y
    change ContMDiffAt
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ∞
      (fun z : standardUnlinkComplementStereographicImage ↦
        standardUnlinkComplementStereographicPartialHomeomorph.symm z.1) y
    rw [contMDiffAt_subtype_iff]
    exact (contMDiffOn_symm_of_mem_maximalAtlas
      standardUnlinkComplementStereographicPartialHomeomorph_mem_maximalAtlas).contMDiffAt
        (standardUnlinkComplementStereographicPartialHomeomorph.open_target.mem_nhds y.2)
  exact ⟨e, hf, hg⟩

@[simp]
theorem standardUnlinkComplementStereographicDiffeomorph_apply_coe
    (x : StandardUnlinkComplement) :
    (standardUnlinkComplementStereographicDiffeomorph x :
        EuclideanSpace ℝ (Fin 4)) =
      stereographic' 4 standardUnlinkStereographicPole x.1 :=
  rfl

@[simp]
theorem standardUnlinkComplementStereographicDiffeomorph_symm_apply_coe
    (y : standardUnlinkComplementStereographicImage) :
    ((standardUnlinkComplementStereographicDiffeomorph.symm y :
        StandardUnlinkComplement) : Sphere 4) =
      (stereographic' 4 standardUnlinkStereographicPole).symm y.1 := by
  exact (stereographic' 4 standardUnlinkStereographicPole).subtypeRestr_symm_apply
    standardUnlinkComplement_nonempty y.2

@[simp]
theorem standardUnlinkComplementStereographicDiffeomorph_apply_symm_coe
    (y : standardUnlinkComplementStereographicImage) :
    stereographic' 4 standardUnlinkStereographicPole
        ((standardUnlinkComplementStereographicDiffeomorph.symm y :
          StandardUnlinkComplement) : Sphere 4) = y.1 := by
  rw [← standardUnlinkComplementStereographicDiffeomorph_apply_coe]
  exact congrArg Subtype.val
    (standardUnlinkComplementStereographicDiffeomorph.apply_symm_apply y)

/-- The coordinate range is exactly the displayed Euclidean open subset. -/
theorem range_standardUnlinkComplementStereographicDiffeomorph_coe :
    range (fun x : StandardUnlinkComplement ↦
      (standardUnlinkComplementStereographicDiffeomorph x :
        EuclideanSpace ℝ (Fin 4))) =
      standardUnlinkComplementStereographicImage := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact (standardUnlinkComplementStereographicDiffeomorph x).2
  · intro hy
    let z : standardUnlinkComplementStereographicImage := ⟨y, hy⟩
    refine ⟨standardUnlinkComplementStereographicDiffeomorph.symm z, ?_⟩
    exact congrArg Subtype.val
      (standardUnlinkComplementStereographicDiffeomorph.apply_symm_apply z)

end SplittingSpheres
