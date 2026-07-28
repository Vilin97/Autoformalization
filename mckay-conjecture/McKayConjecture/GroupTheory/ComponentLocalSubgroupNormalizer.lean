/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.ComponentLocalInvariant

/-!
# Partial conjugation invariance of component-local subgroups

For the final layer argument, a component-local family need not be invariant
under every element of the ambient group.  It is enough that it be equivariant
under the ambient normalizer of the chosen layer Sylow subgroup.  This file
records that exact, subgroup-relative condition and proves that the generated
component-local subgroup is normalized by the acting subgroup.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

variable (G : Type u) [Group G]

namespace ComponentLocalFamily

/-- A component-local family is conjugation-equivariant under a specified
subgroup of the ambient group. -/
def IsConjugationEquivariantUnder
    (A : Subgroup G)
    (M : ∀ K : ComponentIndex G, Subgroup K.1) : Prop :=
  ∀ (g : A) (K : ComponentIndex G),
    componentConjugateSubgroup G g.1 K (M K) =
      M (g.1 • K)

/-- Global equivariance implies equivariance under every ambient subgroup. -/
theorem IsConjugationEquivariant.under
    {M : ∀ K : ComponentIndex G, Subgroup K.1}
    (hM : IsConjugationEquivariant G M)
    (A : Subgroup G) :
    IsConjugationEquivariantUnder G A M :=
  fun g K ↦ hM g.1 K

end ComponentLocalFamily

/-- One element satisfying the coordinate transport laws conjugates the
generated component-local subgroup to itself. -/
theorem map_componentLocalSubgroup_conj_of_coordinate
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (g : G)
    (hg : ∀ K : ComponentIndex G,
      componentConjugateSubgroup G g K (M K) =
        M (g • K)) :
    (componentLocalSubgroup G M).map
        (MulAut.conj g).toMonoidHom =
      componentLocalSubgroup G M := by
  rw [componentLocalSubgroup, Subgroup.map_iSup]
  have hcoordinate :
      ∀ K : ComponentIndex G,
        ((M K).map K.1.subtype).map
            (MulAut.conj g).toMonoidHom =
          (M (g • K)).map (g • K).1.subtype := by
    intro K
    calc
      ((M K).map K.1.subtype).map
            (MulAut.conj g).toMonoidHom =
          (M K).map
            ((MulAut.conj g).toMonoidHom.comp
              K.1.subtype) := by
        rw [Subgroup.map_map]
      _ =
          (M K).map
            ((g • K).1.subtype.comp
              (componentConjugationEquiv G g K).toMonoidHom) := by
        rw [component_subtype_comp_componentConjugationEquiv]
      _ =
          (componentConjugateSubgroup G g K (M K)).map
            (g • K).1.subtype := by
        rw [componentConjugateSubgroup, Subgroup.map_map]
      _ =
          (M (g • K)).map (g • K).1.subtype := by
        rw [hg K]
  simp_rw [hcoordinate]
  apply le_antisymm
  · apply iSup_le
    intro K
    exact le_iSup
      (fun L : ComponentIndex G =>
        (M L).map L.1.subtype) (g • K)
  · apply iSup_le
    intro K
    have hle :=
      le_iSup
        (fun L : ComponentIndex G =>
          (M (g • L)).map (g • L).1.subtype)
        (g⁻¹ • K)
    have hindex : g • (g⁻¹ • K) = K :=
      smul_inv_smul g K
    rw [hindex] at hle
    exact hle

/-- Relative conjugation-equivariance is exactly enough for the acting
subgroup to normalize the generated component-local subgroup. -/
theorem le_normalizer_componentLocalSubgroup
    (A : Subgroup G)
    (M : ∀ K : ComponentIndex G, Subgroup K.1)
    (hM :
      ComponentLocalFamily.IsConjugationEquivariantUnder
        G A M) :
    A ≤ Subgroup.normalizer
      (componentLocalSubgroup G M) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact map_componentLocalSubgroup_conj_of_coordinate
    G M g (fun K ↦ hM ⟨g, hg⟩ K)

end GroupTheory
end McKayConjecture
