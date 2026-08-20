/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import SplittingSpheres.Statement

/-!
# Transporting separation by homeomorphisms

The definition of a splitting sphere uses relative connected components of its complement.
This file records that the underlying separation predicate is invariant under an ambient
homeomorphism.  In particular, the lemma does not depend on a choice of parametrization or on
smooth structure.
-/

@[expose] public section

open Set

namespace SplittingSpheres

/-- An ambient homeomorphism carries a separating triple of subsets to a separating triple. -/
theorem Separates.image_homeomorph {S A B : Set (Sphere 4)}
    (e : Sphere 4 ≃ₜ Sphere 4) (h : Separates S A B) :
    Separates (e '' S) (e '' A) (e '' B) := by
  rcases h with ⟨hdisjoint, a, ha, b, hb, hA, hB, hab⟩
  have haS : a ∈ Sᶜ := by
    rw [mem_compl_iff]
    intro ha'
    exact Set.disjoint_left.1 hdisjoint ha' (Or.inl ha)
  have hbS : b ∈ Sᶜ := by
    rw [mem_compl_iff]
    intro hb'
    exact Set.disjoint_left.1 hdisjoint hb' (Or.inr hb)
  have hcomponentA :
      e '' connectedComponentIn Sᶜ a = connectedComponentIn (e '' S)ᶜ (e a) := by
    rw [e.image_connectedComponentIn haS, e.image_compl]
  have hcomponentB :
      e '' connectedComponentIn Sᶜ b = connectedComponentIn (e '' S)ᶜ (e b) := by
    rw [e.image_connectedComponentIn hbS, e.image_compl]
  refine ⟨?_, e a, mem_image_of_mem e ha, e b, mem_image_of_mem e hb, ?_, ?_, ?_⟩
  · rw [← image_union]
    exact disjoint_image_of_injective e.injective hdisjoint
  · rw [← hcomponentA]
    exact image_mono hA
  · rw [← hcomponentB]
    exact image_mono hB
  · intro hEq
    apply hab
    apply e.injective.image_injective
    rw [hcomponentA, hcomponentB]
    exact hEq

/-- Separation is invariant under an ambient homeomorphism. -/
theorem separates_image_homeomorph_iff (e : Sphere 4 ≃ₜ Sphere 4)
    (S A B : Set (Sphere 4)) :
    Separates (e '' S) (e '' A) (e '' B) ↔ Separates S A B := by
  refine ⟨?_, Separates.image_homeomorph e⟩
  intro h
  have h' := Separates.image_homeomorph e.symm h
  rw [e.image_symm, e.preimage_image S, e.preimage_image A, e.preimage_image B] at h'
  exact h'

/-- If an ambient homeomorphism preserves the two labelled subsets, it carries every separator
of those subsets to another separator. -/
theorem Separates.image_homeomorph_of_fixed {S A B : Set (Sphere 4)}
    (e : Sphere 4 ≃ₜ Sphere 4) (hA : e '' A = A) (hB : e '' B = B)
    (h : Separates S A B) : Separates (e '' S) A B := by
  have h' := h.image_homeomorph e
  rw [hA, hB] at h'
  exact h'

/-- Separation of two labelled subsets is invariant under a homeomorphism preserving each one
setwise. -/
theorem separates_image_homeomorph_iff_of_fixed (e : Sphere 4 ≃ₜ Sphere 4)
    (S A B : Set (Sphere 4)) (hA : e '' A = A) (hB : e '' B = B) :
    Separates (e '' S) A B ↔ Separates S A B := by
  have hAinv : e.symm '' A = A := by
    calc
      e.symm '' A = e.symm '' (e '' A) := congrArg (e.symm '' ·) hA.symm
      _ = A := by rw [e.image_symm, e.preimage_image]
  have hBinv : e.symm '' B = B := by
    calc
      e.symm '' B = e.symm '' (e '' B) := congrArg (e.symm '' ·) hB.symm
      _ = B := by rw [e.image_symm, e.preimage_image]
  refine ⟨?_, fun h ↦ h.image_homeomorph_of_fixed e hA hB⟩
  intro h
  have h' := h.image_homeomorph_of_fixed e.symm hAinv hBinv
  rw [e.image_symm, e.preimage_image] at h'
  exact h'

/-- Preserving both labelled standard components preserves their union. -/
theorem image_standardUnlinkCarrier_of_components_fixed (e : Sphere 4 ≃ₜ Sphere 4)
    (h₀ : e '' standardUnlinkComponent 0 = standardUnlinkComponent 0)
    (h₁ : e '' standardUnlinkComponent 1 = standardUnlinkComponent 1) :
    e '' standardUnlinkCarrier = standardUnlinkCarrier := by
  rw [standardUnlinkCarrier, image_union, h₀, h₁]

end SplittingSpheres
