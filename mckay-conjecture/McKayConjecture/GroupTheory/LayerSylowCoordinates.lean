/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.LayerCenter
import McKayConjecture.GroupTheory.LayerCentralProduct
import McKayConjecture.GroupTheory.QuasisimpleSylow
import McKayConjecture.GroupTheory.SylowPi

/-!
# Sylow coordinates in the layer

Multiplication of the components maps their external direct product
surjectively onto the layer.  A Sylow subgroup of the layer therefore
lifts to a Sylow subgroup of the component product.  Every Sylow subgroup
of a finite dependent product is the coordinatewise product of its images
under the evaluation homomorphisms, so the lift can be described by a
family of component Sylow subgroups.

If the layer Sylow subgroup is not contained in `Z(E(G))`, at least one
coordinate Sylow subgroup is not contained in the center of its component.
That component is quasisimple, hence the coordinate Sylow subgroup has a
proper normalizer.

Internal centrality in `E(G)` and ambient centrality in `G` are different:
`Z(E(G))` need not map into `Z(G)` without an additional hypothesis.  The
ambient variants below therefore explicitly assume this containment; the
reduction hypothesis `F(G) ≤ Z(G)` is a sufficient condition.

The layer package is stated for `G : Type` (universe zero), matching the
universe in which it is consumed by the finite-group reduction.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace GroupTheory

/-- Evaluation from a dependent product of groups is surjective. -/
theorem piEvalMonoidHom_surjective
    {ι : Type u} {A : ι → Type v}
    [∀ i, Group (A i)] (i : ι) :
    Function.Surjective (Pi.evalMonoidHom A i) := by
  classical
  intro x
  refine
    ⟨Pi.mulSingle (M := A) i x, ?_⟩
  simp

namespace Sylow

variable {ι : Type u} {A : ι → Type v}
variable [∀ i, Group (A i)]
variable [Finite ι] [∀ i, Finite (A i)]
variable {p : ℕ} [Fact p.Prime]

/-- The image of a Sylow subgroup of a finite dependent product in one
coordinate. -/
def eval (S : Sylow p (∀ i, A i)) (i : ι) :
    Sylow p (A i) :=
  S.mapSurjective (piEvalMonoidHom_surjective i)

@[simp, norm_cast]
theorem coe_eval
    (S : Sylow p (∀ i, A i)) (i : ι) :
    (eval S i : Subgroup (A i)) =
      (S : Subgroup (∀ i, A i)).map
        (Pi.evalMonoidHom A i) :=
  rfl

/-- Every Sylow subgroup of a finite dependent product is exactly the
coordinatewise product of its evaluation images. -/
theorem pi_eval_eq
    (S : Sylow p (∀ i, A i)) :
    pi (fun i => eval S i) = S := by
  apply Sylow.ext
  exact
    S.is_maximal'
      (pi (fun i => eval S i)).isPGroup' (by
        intro x hx
        rw [coe_pi, Subgroup.mem_pi]
        intro i _
        change
          x i ∈
            (S : Subgroup (∀ i, A i)).map
              (Pi.evalMonoidHom A i)
        exact ⟨x, hx, rfl⟩)

end Sylow

section Layer

variable (G : Type) [Group G] [Finite G]
variable (p : ℕ) [Fact p.Prime]
variable (Q : Sylow p (layer G))

/-- Coordinate data for a lift of a Sylow subgroup of the layer to the
external product of the components. -/
structure LayerSylowCoordinateData where
  /-- A Sylow subgroup of the external product lifting `Q`. -/
  source : Sylow p (∀ K : ComponentIndex G, K.1)
  /-- Its Sylow image in every component coordinate. -/
  coordinate : ∀ K : ComponentIndex G, Sylow p K.1
  /-- The source Sylow subgroup is exactly the coordinatewise product. -/
  source_eq_pi :
    source = Sylow.pi coordinate
  /-- Component multiplication maps the source exactly onto `Q`. -/
  map_eq :
    source.mapSurjective
        (layerProductHom_surjective G) =
      Q

/-- Choose coordinate Sylow data above a Sylow subgroup of the layer. -/
def layerSylowCoordinateData :
    LayerSylowCoordinateData G p Q := by
  classical
  let S : Sylow p
      (∀ K : ComponentIndex G, K.1) :=
    Classical.choose
      ((Sylow.mapSurjective_surjective
        (layerProductHom_surjective G) p) Q)
  have hS :
      S.mapSurjective
          (layerProductHom_surjective G) =
        Q :=
    Classical.choose_spec
      ((Sylow.mapSurjective_surjective
        (layerProductHom_surjective G) p) Q)
  let P : ∀ K : ComponentIndex G, Sylow p K.1 :=
    fun K => Sylow.eval S K
  exact
    { source := S
      coordinate := P
      source_eq_pi := by
        exact (Sylow.pi_eval_eq S).symm
      map_eq := hS }

namespace LayerSylowCoordinateData

variable {G p Q}

/-- At subgroup level, component multiplication maps the chosen source
exactly onto the prescribed layer Sylow subgroup. -/
theorem map_source_eq
    (D : LayerSylowCoordinateData G p Q) :
    (D.source :
        Subgroup (∀ K : ComponentIndex G, K.1)).map
        (layerProductHom G) =
      (Q : Subgroup (layer G)) := by
  have h :=
    congrArg
      (fun R : Sylow p (layer G) =>
        (R : Subgroup (layer G)))
      D.map_eq
  simpa using h

/-- The coordinatewise product itself maps onto the prescribed layer
Sylow subgroup. -/
theorem map_pi_eq
    (D : LayerSylowCoordinateData G p Q) :
    ((Sylow.pi D.coordinate :
        Sylow p (∀ K : ComponentIndex G, K.1)) :
        Subgroup (∀ K : ComponentIndex G, K.1)).map
          (layerProductHom G) =
      (Q : Subgroup (layer G)) := by
  rw [← D.source_eq_pi]
  exact D.map_source_eq

/-- If all coordinate Sylow subgroups are central in their components,
then the chosen source is central in the external component product. -/
theorem source_le_center_of_coordinate_le_center
    (D : LayerSylowCoordinateData G p Q)
    (hcoordinate :
      ∀ K,
        (D.coordinate K : Subgroup K.1) ≤
          Subgroup.center K.1) :
    (D.source :
        Subgroup (∀ K : ComponentIndex G, K.1)) ≤
      Subgroup.center
        (∀ K : ComponentIndex G, K.1) := by
  rw [D.source_eq_pi, Sylow.coe_pi,
    Subgroup.center_pi]
  intro x hx
  rw [Subgroup.mem_pi] at hx ⊢
  intro K _
  exact hcoordinate K
    (hx K (Set.mem_univ K))

/-- If all coordinate Sylow subgroups are central, then the layer Sylow
subgroup is central in the layer. -/
theorem le_center_layer_of_coordinate_le_center
    (D : LayerSylowCoordinateData G p Q)
    (hcoordinate :
      ∀ K,
        (D.coordinate K : Subgroup K.1) ≤
          Subgroup.center K.1) :
    (Q : Subgroup (layer G)) ≤
      Subgroup.center (layer G) := by
  rw [← D.map_source_eq]
  exact
    (Subgroup.map_mono
      (D.source_le_center_of_coordinate_le_center
        hcoordinate)).trans
      (map_center_le_center_of_surjective
        (layerProductHom_surjective G))

/-- A layer Sylow subgroup not contained in `Z(E(G))` has a noncentral
coordinate Sylow subgroup. -/
theorem exists_coordinate_not_le_center
    (D : LayerSylowCoordinateData G p Q)
    (hQnoncentral :
      ¬(Q : Subgroup (layer G)) ≤
        Subgroup.center (layer G)) :
    ∃ K : ComponentIndex G,
      ¬(D.coordinate K : Subgroup K.1) ≤
        Subgroup.center K.1 := by
  classical
  by_contra hnone
  apply hQnoncentral
  apply D.le_center_layer_of_coordinate_le_center
  intro K
  by_contra hK
  exact hnone ⟨K, hK⟩

/-- A noncentral Sylow subgroup of the layer has a component coordinate
which is noncentral and whose normalizer in that component is proper. -/
theorem exists_coordinate_normalizer_lt_top
    (D : LayerSylowCoordinateData G p Q)
    (hQnoncentral :
      ¬(Q : Subgroup (layer G)) ≤
        Subgroup.center (layer G)) :
    ∃ K : ComponentIndex G,
      (¬(D.coordinate K : Subgroup K.1) ≤
          Subgroup.center K.1) ∧
      Subgroup.normalizer
          (D.coordinate K : Set K.1) <
        ⊤ := by
  obtain ⟨K, hK⟩ :=
    D.exists_coordinate_not_le_center
      hQnoncentral
  refine ⟨K, hK, ?_⟩
  exact
    IsQuasisimple.normalizer_sylow_lt_top_of_not_le_center
      K.2.isQuasisimple (D.coordinate K) hK

/-- Exact hypothesis under which failure of ambient centrality implies
failure of centrality inside the layer. -/
theorem not_le_center_layer_of_map_not_le_center
    (_D : LayerSylowCoordinateData G p Q)
    (hcenterImage :
      (Subgroup.center (layer G)).map
          (layer G).subtype ≤
        Subgroup.center G)
    (hQambient :
      ¬(Q : Subgroup (layer G)).map
          (layer G).subtype ≤
        Subgroup.center G) :
    ¬(Q : Subgroup (layer G)) ≤
      Subgroup.center (layer G) := by
  intro hQ
  apply hQambient
  exact (Subgroup.map_mono hQ).trans
    hcenterImage

/-- Under an explicit ambient-center hypothesis, ambient noncentrality
also produces a coordinate with a proper normalizer. -/
theorem exists_coordinate_normalizer_lt_top_of_map_not_le_center
    (D : LayerSylowCoordinateData G p Q)
    (hcenterImage :
      (Subgroup.center (layer G)).map
          (layer G).subtype ≤
        Subgroup.center G)
    (hQambient :
      ¬(Q : Subgroup (layer G)).map
          (layer G).subtype ≤
        Subgroup.center G) :
    ∃ K : ComponentIndex G,
      (¬(D.coordinate K : Subgroup K.1) ≤
          Subgroup.center K.1) ∧
      Subgroup.normalizer
          (D.coordinate K : Set K.1) <
        ⊤ :=
  D.exists_coordinate_normalizer_lt_top
    (D.not_le_center_layer_of_map_not_le_center
      hcenterImage hQambient)

/-- The reduction hypothesis `F(G) ≤ Z(G)` supplies the ambient-center
containment needed by the preceding theorem. -/
theorem exists_coordinate_normalizer_lt_top_of_fitting_le_center
    (D : LayerSylowCoordinateData G p Q)
    (hF : fittingSubgroup G ≤ Subgroup.center G)
    (hQambient :
      ¬(Q : Subgroup (layer G)).map
          (layer G).subtype ≤
        Subgroup.center G) :
    ∃ K : ComponentIndex G,
      (¬(D.coordinate K : Subgroup K.1) ≤
          Subgroup.center K.1) ∧
      Subgroup.normalizer
          (D.coordinate K : Set K.1) <
        ⊤ :=
  D.exists_coordinate_normalizer_lt_top_of_map_not_le_center
    (map_center_layer_le_fittingSubgroup.trans hF)
    hQambient

end LayerSylowCoordinateData

end Layer

end GroupTheory
end McKayConjecture
