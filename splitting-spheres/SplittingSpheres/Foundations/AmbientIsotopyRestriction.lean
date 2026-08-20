/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Sets.Opens
public import TauCeti.Topology.Homotopy.Isotopy.Basic

/-!
# Restricting an ambient isotopy to an invariant subtype

An ambient isotopy restricts to a subtype when every time slice preserves membership in the
subtype in both directions.  This file packages that restriction and proves that fixing the
complement pointwise is a sufficient, symmetric invariance hypothesis.  The construction is
purely topological and applies to arbitrary subsets; an `Opens` convenience definition records the
case used for compactly supported vector fields.
-/

@[expose] public section


open Function Set
open unitInterval
open scoped Topology unitInterval

noncomputable section

namespace TauCeti

namespace AmbientIsotopy

variable {Y : Type*} [TopologicalSpace Y]

/-- If an ambient isotopy fixes the complement of `U` pointwise, every time slice preserves
membership in `U` in both directions. -/
theorem mem_iff_of_fixed_complement (Phi : AmbientIsotopy Y) (U : Set Y)
    (hfixed : ∀ t : I, ∀ y, y ∉ U → Phi.toContinuousMap (t, y) = y) (t : I) (y : Y) :
    Phi.toContinuousMap (t, y) ∈ U ↔ y ∈ U := by
  constructor
  · intro himage
    by_contra hy
    exact hy (by simpa [hfixed t y hy] using himage)
  · intro hy
    by_contra himage
    have heq : y = Phi.toContinuousMap (t, y) :=
      (Phi.isHomeomorph_apply t).injective (by
        rw [hfixed t (Phi.toContinuousMap (t, y)) himage])
    exact himage (heq ▸ hy)

/-- Invariance of `U` under every time slice also makes the inverse total map preserve `U` in its
spatial coordinate. -/
theorem totalHomeomorph_symm_snd_mem_of_mem_iff
    (Phi : AmbientIsotopy Y) (U : Set Y)
    (hinvariant : ∀ t : I, ∀ y, Phi.toContinuousMap (t, y) ∈ U ↔ y ∈ U)
    (p : I × Y) (hp : p.2 ∈ U) : (Phi.totalHomeomorph.symm p).2 ∈ U := by
  let q := Phi.totalHomeomorph.symm p
  have happ : Phi.totalHomeomorph q = p := Phi.totalHomeomorph.apply_symm_apply p
  have hsnd : Phi.toContinuousMap (q.1, q.2) = p.2 := by
    rw [totalHomeomorph_apply] at happ
    exact congrArg Prod.snd happ
  apply (hinvariant q.1 q.2).mp
  rw [hsnd]
  exact hp

/-- Restrict an ambient isotopy to a subtype whose membership is preserved in both directions by
every time slice.  The inverse is the restriction of the inverse total homeomorphism, so no
surjectivity of a merely forward-invariant subset is assumed. -/
def restrictSet (Phi : AmbientIsotopy Y) (U : Set Y)
    (hinvariant : ∀ t : I, ∀ y, Phi.toContinuousMap (t, y) ∈ U ↔ y ∈ U) :
    AmbientIsotopy U := by
  let forward : I × U → U := fun p ↦
    ⟨Phi.toContinuousMap (p.1, (p.2 : Y)), (hinvariant p.1 p.2).mpr p.2.property⟩
  have hforward : Continuous forward := by
    apply Continuous.subtype_mk
    fun_prop
  let inverse : I × U → I × U := fun p ↦
    let q := Phi.totalHomeomorph.symm (p.1, (p.2 : Y))
    (q.1, ⟨q.2, totalHomeomorph_symm_snd_mem_of_mem_iff Phi U hinvariant
      (p.1, (p.2 : Y)) p.2.property⟩)
  have hinverse : Continuous inverse := by
    let ambientInverse : I × U → I × Y := fun p ↦
      Phi.totalHomeomorph.symm (p.1, (p.2 : Y))
    have hambientInverse : Continuous ambientInverse := by
      exact Phi.totalHomeomorph.symm.continuous.comp (by fun_prop)
    dsimp only [inverse]
    exact (continuous_fst.comp hambientInverse).prodMk <|
      Continuous.subtype_mk (continuous_snd.comp hambientInverse) _
  refine
    { toContinuousMap := ⟨forward, hforward⟩
      isHomeomorph_total' := ?_
      map_zero_left' := ?_ }
  · rw [isHomeomorph_iff_exists_inverse]
    refine ⟨continuous_fst.prodMk hforward, inverse, ?_, ?_, hinverse⟩
    · intro p
      dsimp only [inverse, forward]
      have htotal : Phi.totalHomeomorph (p.1, (p.2 : Y)) =
          (p.1, Phi.toContinuousMap (p.1, (p.2 : Y))) :=
        Phi.totalHomeomorph_apply (p.1, (p.2 : Y))
      apply Prod.ext
      · change
          (Phi.totalHomeomorph.symm
            (p.1, Phi.toContinuousMap (p.1, (p.2 : Y)))).1 = p.1
        rw [← htotal, Phi.totalHomeomorph.symm_apply_apply]
      · apply Subtype.ext
        change
          (Phi.totalHomeomorph.symm
            (p.1, Phi.toContinuousMap (p.1, (p.2 : Y)))).2 = (p.2 : Y)
        rw [← htotal, Phi.totalHomeomorph.symm_apply_apply]
    · intro p
      dsimp only [inverse, forward]
      have happ := Phi.totalHomeomorph.apply_symm_apply (p.1, (p.2 : Y))
      rw [Phi.totalHomeomorph_apply] at happ
      apply Prod.ext
      · exact Phi.totalHomeomorph_symm_fst (p.1, (p.2 : Y))
      · apply Subtype.ext
        exact congrArg Prod.snd happ
  · intro y
    apply Subtype.ext
    exact Phi.map_zero_left y

@[simp]
theorem restrictSet_apply (Phi : AmbientIsotopy Y) (U : Set Y)
    (hinvariant : ∀ t : I, ∀ y, Phi.toContinuousMap (t, y) ∈ U ↔ y ∈ U)
    (p : I × U) :
    (restrictSet Phi U hinvariant).toContinuousMap p =
      ⟨Phi.toContinuousMap (p.1, (p.2 : Y)), (hinvariant p.1 p.2).mpr p.2.property⟩ := by
  apply Subtype.ext
  rfl

@[simp]
theorem coe_restrictSet_apply (Phi : AmbientIsotopy Y) (U : Set Y)
    (hinvariant : ∀ t : I, ∀ y, Phi.toContinuousMap (t, y) ∈ U ↔ y ∈ U)
    (p : I × U) :
    ((restrictSet Phi U hinvariant).toContinuousMap p : Y) =
      Phi.toContinuousMap (p.1, (p.2 : Y)) := by
  rw [restrictSet_apply]

/-- Restrict an ambient isotopy to a subtype when it fixes the complement pointwise. -/
def restrictSetOfFixedComplement (Phi : AmbientIsotopy Y) (U : Set Y)
    (hfixed : ∀ t : I, ∀ y, y ∉ U → Phi.toContinuousMap (t, y) = y) :
    AmbientIsotopy U :=
  restrictSet Phi U (mem_iff_of_fixed_complement Phi U hfixed)

@[simp]
theorem restrictSetOfFixedComplement_apply (Phi : AmbientIsotopy Y) (U : Set Y)
    (hfixed : ∀ t : I, ∀ y, y ∉ U → Phi.toContinuousMap (t, y) = y) (p : I × U) :
    (restrictSetOfFixedComplement Phi U hfixed).toContinuousMap p =
      ⟨Phi.toContinuousMap (p.1, (p.2 : Y)),
        (mem_iff_of_fixed_complement Phi U hfixed p.1 p.2).mpr p.2.property⟩ := by
  apply Subtype.ext
  rfl

@[simp]
theorem coe_restrictSetOfFixedComplement_apply (Phi : AmbientIsotopy Y) (U : Set Y)
    (hfixed : ∀ t : I, ∀ y, y ∉ U → Phi.toContinuousMap (t, y) = y) (p : I × U) :
    ((restrictSetOfFixedComplement Phi U hfixed).toContinuousMap p : Y) =
      Phi.toContinuousMap (p.1, (p.2 : Y)) := by
  rw [restrictSetOfFixedComplement_apply]

/-- Open-set convenience form of `restrictSetOfFixedComplement`. -/
def restrictOpensOfFixedComplement (Phi : AmbientIsotopy Y) (U : TopologicalSpace.Opens Y)
    (hfixed : ∀ t : I, ∀ y, y ∉ U → Phi.toContinuousMap (t, y) = y) :
    AmbientIsotopy U :=
  restrictSetOfFixedComplement Phi (U : Set Y) hfixed

@[simp]
theorem restrictOpensOfFixedComplement_apply (Phi : AmbientIsotopy Y)
    (U : TopologicalSpace.Opens Y)
    (hfixed : ∀ t : I, ∀ y, y ∉ U → Phi.toContinuousMap (t, y) = y) (p : I × U) :
    (restrictOpensOfFixedComplement Phi U hfixed).toContinuousMap p =
      ⟨Phi.toContinuousMap (p.1, (p.2 : Y)),
        (mem_iff_of_fixed_complement Phi (U : Set Y) hfixed p.1 p.2).mpr p.2.property⟩ := by
  rfl


@[simp]
theorem coe_restrictOpensOfFixedComplement_apply (Phi : AmbientIsotopy Y)
    (U : TopologicalSpace.Opens Y)
    (hfixed : ∀ t : I, ∀ y, y ∉ U → Phi.toContinuousMap (t, y) = y) (p : I × U) :
    ((restrictOpensOfFixedComplement Phi U hfixed).toContinuousMap p : Y) =
      Phi.toContinuousMap (p.1, (p.2 : Y)) := by
  rw [restrictOpensOfFixedComplement_apply]

end AmbientIsotopy

end TauCeti
