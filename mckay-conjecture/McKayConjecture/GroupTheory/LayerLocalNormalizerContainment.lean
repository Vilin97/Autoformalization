/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.LayerLocalSubgroupIdentification
import McKayConjecture.GroupTheory.LayerSylowNormalizerAction

/-!
# Layer Sylow normalizers lie in coordinate-local subgroups

Let a Sylow subgroup `Q` of the layer be represented by coordinate
Sylow subgroups of the components.  If a subgroup chosen in every
component contains the normalizer of the corresponding coordinate
Sylow subgroup, then the internal normalizer of `Q` lies in the image
of the coordinatewise product of those chosen subgroups.

The key point is that component multiplication has central kernel.
Consequently a Sylow subgroup above `Q` is unique.  If an element of
the component product maps to an element normalizing `Q`, conjugating
the source Sylow subgroup by that element gives another lift of `Q`,
so uniqueness forces the source to be normalized.  The normalizer of
a coordinatewise product is coordinatewise, which gives the result.

No additional hypothesis that the chosen coordinate subgroups contain
the component centers is needed for this containment.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace GroupTheory

namespace Sylow

variable {X : Type u} {Y : Type v}
variable [Group X] [Group Y] [Finite X]
variable {p : ℕ} [Fact p.Prime]

/-- Mapping a conjugate Sylow subgroup through a surjective homomorphism
gives the conjugate of its image. -/
theorem mapSurjective_smul
    {f : X →* Y} (hf : Function.Surjective f)
    (x : X) (P : Sylow p X) :
    (x • P).mapSurjective hf =
      f x • P.mapSurjective hf := by
  apply Sylow.ext
  change
    ((P : Subgroup X).map
        (MulAut.conj x).toMonoidHom).map f =
      ((P : Subgroup X).map f).map
        (MulAut.conj (f x)).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext z
  simp [mul_assoc]

/-- If a surjective homomorphism has central kernel, every lift of an
element normalizing the image of a Sylow subgroup normalizes that Sylow
subgroup. -/
theorem mem_normalizer_of_mapSurjective_mem_normalizer_of_ker_le_center
    {f : X →* Y} (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center X)
    (P : Sylow p X) (x : X)
    (hx :
      f x ∈ Subgroup.normalizer
        (P.mapSurjective hf : Set Y)) :
    x ∈ Subgroup.normalizer (P : Set X) := by
  rw [← Sylow.smul_eq_iff_mem_normalizer]
  apply
    mapSurjective_injective_of_ker_le_center
      hf hker
  rw [mapSurjective_smul]
  exact Sylow.smul_eq_iff_mem_normalizer.mpr hx

end Sylow

section Layer

variable (G : Type) [Group G] [Finite G]
variable (p : ℕ) [Fact p.Prime]
variable (Q : Sylow p (layer G))

namespace LayerSylowCoordinateData

variable {G p Q}

/-- A lift in the external component product of an element normalizing
the layer Sylow subgroup normalizes the chosen source Sylow subgroup. -/
theorem mem_source_normalizer_of_image_mem_normalizer
    (D : LayerSylowCoordinateData G p Q)
    (x : ∀ K : ComponentIndex G, K.1)
    (hx :
      layerProductHom G x ∈
        Subgroup.normalizer (Q : Set (layer G))) :
    x ∈ Subgroup.normalizer (D.source : Set
      (∀ K : ComponentIndex G, K.1)) := by
  apply
    Sylow.mem_normalizer_of_mapSurjective_mem_normalizer_of_ker_le_center
      (layerProductHom_surjective G)
      (layerProductHom_ker_le_center G)
      D.source x
  simpa only [D.map_eq] using hx

/-- If each chosen component subgroup contains the corresponding
coordinate Sylow normalizer, then every lift of a layer-normalizer
element lies in their coordinatewise product. -/
theorem mem_piLocalSubgroup_of_image_mem_normalizer
    (D : LayerSylowCoordinateData G p Q)
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (hM :
      ∀ K,
        Subgroup.normalizer
            (D.coordinate K : Set K.1) ≤
          M K)
    (x : ∀ K : ComponentIndex G, K.1)
    (hx :
      layerProductHom G x ∈
        Subgroup.normalizer (Q : Set (layer G))) :
    x ∈ piLocalSubgroup M := by
  have hxSource :
      x ∈ Subgroup.normalizer (D.source : Set
        (∀ K : ComponentIndex G, K.1)) :=
    D.mem_source_normalizer_of_image_mem_normalizer x hx
  have hxPi :
      x ∈ Subgroup.normalizer
        ((Sylow.pi D.coordinate :
          Sylow p (∀ K : ComponentIndex G, K.1)) :
            Set (∀ K : ComponentIndex G, K.1)) := by
    simpa only [← D.source_eq_pi] using hxSource
  change
    x ∈ Subgroup.normalizer
      (Subgroup.pi Set.univ
        (fun K =>
          (D.coordinate K : Subgroup K.1)) :
        Set (∀ K : ComponentIndex G, K.1)) at hxPi
  rw [Subgroup.normalizer_pi] at hxPi
  rw [mem_piLocalSubgroup]
  intro K
  apply hM K
  exact
    (Subgroup.mem_pi Set.univ).mp hxPi
      K (Set.mem_univ K)

/-- Coordinatewise containment of the component Sylow normalizers
implies containment of the internal layer Sylow normalizer in the
assembled layer-local subgroup. -/
theorem normalizer_le_layerLocalSubgroup
    (D : LayerSylowCoordinateData G p Q)
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (hM :
      ∀ K,
        Subgroup.normalizer
            (D.coordinate K : Set K.1) ≤
          M K) :
    Subgroup.normalizer (Q : Set (layer G)) ≤
      layerLocalSubgroup G M := by
  intro q hq
  obtain ⟨x, hx⟩ :=
    layerProductHom_surjective G q
  refine ⟨x, ?_, hx⟩
  apply
    D.mem_piLocalSubgroup_of_image_mem_normalizer
      M hM x
  simpa only [hx] using hq

/-- The same containment expressed using the component-generated
subgroup pulled back to the layer. -/
theorem normalizer_le_componentLocalSubgroupInLayer
    (D : LayerSylowCoordinateData G p Q)
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (hM :
      ∀ K,
        Subgroup.normalizer
            (D.coordinate K : Set K.1) ≤
          M K) :
    Subgroup.normalizer (Q : Set (layer G)) ≤
      componentLocalSubgroupInLayer G M := by
  rw [← layerLocalSubgroup_eq_componentLocalSubgroupInLayer]
  exact D.normalizer_le_layerLocalSubgroup M hM

end LayerSylowCoordinateData

end Layer

end GroupTheory
end McKayConjecture
