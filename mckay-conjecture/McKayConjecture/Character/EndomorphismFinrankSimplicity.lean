/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.RepresentationTheory.FinGroupCharZero

/-!
# Simplicity from a one-dimensional endomorphism space

For a complex representation of a finite group, Maschke semisimplicity makes
the converse to Schur's lemma available: an object whose endomorphism space is
one-dimensional is simple.  This file isolates that criterion from its
character-theoretic applications.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace McKayConjecture
namespace FDRep

/-- A finite-group complex representation with a one-dimensional
endomorphism space is simple. -/
theorem simple_of_end_finrank_eq_one
    {G : Type u} [Finite G] [Group G]
    (V : FDRep ℂ G)
    (h : Module.finrank ℂ (V ⟶ V) = 1) :
    Simple V := by
  letI : NeZero (Nat.card G : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  letI repInjective (X : Rep ℂ G) :
      CategoryTheory.Injective X := by
    rw [← Rep.equivalenceModuleMonoidAlgebra.map_injective_iff,
      ← Module.injective_iff_injective_object]
    exact Module.injective_of_isSemisimpleRing _ _
  letI fdRepInjective (X : FDRep ℂ G) :
      CategoryTheory.Injective X :=
    (forget₂ (FDRep ℂ G) (Rep ℂ G)).injective_of_map_injective
      inferInstance
  refine
    { mono_isIso_iff_nonzero := fun {W} f _ ↦
        ⟨fun hf habs ↦ ?_, fun hf ↦ ?_⟩ }
  · rw [habs, isIsoZero_iff_source_target_isZero] at hf
    obtain ⟨g, hg⟩ : ∃ g : V ⟶ V, g ≠ 0 :=
      (Module.finrank_pos_iff_exists_ne_zero).mp (by
        rw [h]
        norm_num)
    exact hg (hf.2.eq_zero_of_src g)
  · suffices Epi f by
      exact isIso_of_mono_of_epi f
    suffices Epi (Abelian.image.ι f) by
      rw [← Abelian.image.fac f]
      exact epi_comp _ _
    rw [← Abelian.image.fac f] at hf
    set i := Abelian.image.ι f
    set phi := CategoryTheory.Injective.factorThru (𝟙 _) i
    have hphi_i : phi ≫ i ≠ 0 := by
      intro habs
      have hi_phi : 𝟙 _ = i ≫ phi :=
        (CategoryTheory.Injective.comp_factorThru (𝟙 _) i).symm
      apply_fun (· ≫ i) at hi_phi
      simp_all
    obtain ⟨c, hc⟩ : ∃ c : ℂ, c • _ = 𝟙 V :=
      (finrank_eq_one_iff_of_nonzero' _ hphi_i).mp h (𝟙 V)
    refine Preadditive.epi_of_cancel_zero _ (fun g hg ↦ ?_)
    apply_fun (· ≫ g) at hc
    simpa [hg] using hc.symm

end FDRep
end McKayConjecture
