/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Index
import McKayConjecture.GroupTheory.GeneralizedFittingAction

/-!
# Stabilizers and automorphisms of a component

For the conjugation action on the components of `G`, the stabilizer of a
component `K` is its subgroup normalizer `N_G(K)`.  Conjugation by the
normalizer acts on `K`; its kernel is the copy of `C_G(K)` inside
`N_G(K)`.  Thus `N_G(K) / C_G(K)` embeds faithfully in `Aut(K)`.
-/

noncomputable section

universe u

namespace McKayConjecture.GroupTheory

variable (G : Type u) [Group G]

/-- The stabilizer of a component under ambient conjugation is exactly
its subgroup normalizer. -/
theorem component_stabilizer_eq_normalizer
    (K : ComponentIndex G) :
    MulAction.stabilizer G K =
      Subgroup.normalizer (K.1 : Set G) := by
  ext g
  rw [MulAction.mem_stabilizer_iff,
    Subgroup.mem_normalizer_iff_map_conj_eq]
  constructor
  · intro hg
    have hval :=
      congrArg (fun C : ComponentIndex G => C.1) hg
    change
      K.1.map (MulAut.conj g).toMonoidHom = K.1 at hval
    exact hval
  · intro hg
    apply Subtype.ext
    change
      K.1.map (MulAut.conj g).toMonoidHom = K.1
    exact hg

/-- The centralizer of a component, viewed as a subgroup of its
normalizer.  This is the internal form of
`C_G(K) ∩ N_G(K)`. -/
abbrev componentCentralizerInNormalizer
    (K : ComponentIndex G) :
    Subgroup (Subgroup.normalizer (K.1 : Set G)) :=
  (Subgroup.centralizer (K.1 : Set G)).subgroupOf
    (Subgroup.normalizer (K.1 : Set G))

/-- Conjugation by the normalizer of a component, acting on that
component. -/
abbrev componentNormalizerAction
    (K : ComponentIndex G) :
    Subgroup.normalizer (K.1 : Set G) →* MulAut K.1 :=
  K.1.normalizerMonoidHom

/-- The normalizer action is ambient conjugation on the underlying
elements of the component. -/
@[simp]
theorem componentNormalizerAction_apply_coe
    (K : ComponentIndex G)
    (n : Subgroup.normalizer (K.1 : Set G))
    (k : K.1) :
    ((componentNormalizerAction G K n) k : G) =
      (n : G) * (k : G) * (n : G)⁻¹ :=
  rfl

/-- The kernel of the normalizer action on a component is its ambient
centralizer, intersected with the normalizer. -/
theorem componentNormalizerAction_ker
    (K : ComponentIndex G) :
    (componentNormalizerAction G K).ker =
      componentCentralizerInNormalizer G K :=
  K.1.normalizerMonoidHom_ker

/-- Mapping the centralizer inside the normalizer back to `G` recovers
the ambient centralizer of the component. -/
theorem map_componentCentralizerInNormalizer
    (K : ComponentIndex G) :
    (componentCentralizerInNormalizer G K).map
        (Subgroup.normalizer (K.1 : Set G)).subtype =
      Subgroup.centralizer (K.1 : Set G) :=
  Subgroup.map_subgroupOf_eq_of_le
    (Subgroup.centralizer_le_normalizer (K.1 : Set G))

/-- The automorphism subgroup induced on a component by its normalizer. -/
abbrev ComponentNormalizerConjugationImage
    (K : ComponentIndex G) :=
  (componentNormalizerAction G K).range

/-- First isomorphism theorem for the action of `N_G(K)` on `K`. -/
def quotientComponentCentralizerEquivConjugationImage
    (K : ComponentIndex G) :
    (Subgroup.normalizer (K.1 : Set G) ⧸
        componentCentralizerInNormalizer G K) ≃*
      ComponentNormalizerConjugationImage G K :=
  (QuotientGroup.quotientMulEquivOfEq
      (componentNormalizerAction_ker G K).symm).trans
    (QuotientGroup.quotientKerEquivRange
      (componentNormalizerAction G K))

/-- The faithful homomorphism
`N_G(K) / C_G(K) → Aut(K)` induced by conjugation. -/
def quotientComponentCentralizerToAut
    (K : ComponentIndex G) :
    (Subgroup.normalizer (K.1 : Set G) ⧸
        componentCentralizerInNormalizer G K) →*
      MulAut K.1 :=
  (ComponentNormalizerConjugationImage G K).subtype.comp
    (quotientComponentCentralizerEquivConjugationImage G K).toMonoidHom

/-- Conjugation embeds `N_G(K) / C_G(K)` faithfully in `Aut(K)`. -/
theorem quotientComponentCentralizerToAut_injective
    (K : ComponentIndex G) :
    Function.Injective
      (quotientComponentCentralizerToAut G K) :=
  (ComponentNormalizerConjugationImage G K).subtype_injective.comp
    (quotientComponentCentralizerEquivConjugationImage G K).injective

/-- The size of the conjugacy orbit of a component is the index of its
normalizer. -/
theorem component_orbit_ncard_eq_normalizer_index
    (K : ComponentIndex G) :
    (MulAction.orbit G K).ncard =
      (Subgroup.normalizer (K.1 : Set G)).index := by
  rw [← component_stabilizer_eq_normalizer G K]
  exact (MulAction.index_stabilizer G K).symm

/-- For a finite group, the orbit size times the normalizer order is the
group order. -/
theorem component_orbit_ncard_mul_normalizer_card
    [Finite G] (K : ComponentIndex G) :
    (MulAction.orbit G K).ncard *
        Nat.card (Subgroup.normalizer (K.1 : Set G)) =
      Nat.card G := by
  rw [component_orbit_ncard_eq_normalizer_index G K]
  exact (Subgroup.normalizer (K.1 : Set G)).index_mul_card

end McKayConjecture.GroupTheory
