/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Geometry.UnlinkCyclicCover

/-!
# Properness of the punctured-complex power map

For nonzero degree, the polynomial `z ↦ z ^ m` is proper on the complex plane.  Restricting a
proper map over the open target `ℂ \ {0}` remains proper, and the nonzero-degree hypothesis
identifies the restricted source with `ℂ \ {0}` itself.  This yields the properness input needed
to prove compactness of power-map pullbacks over compact bases.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SplittingSpheres

/-- For nonzero degree, the power map on the punctured complex plane is proper. -/
theorem isProperMap_nonzeroComplexPow (m : ℕ) [NeZero m] :
    IsProperMap (nonzeroComplexPow m) := by
  have hdegree : 0 < Polynomial.degree ((Polynomial.X : Polynomial ℂ) ^ m) := by
    rw [Polynomial.degree_X_pow]
    exact_mod_cast NeZero.pos m
  have hproper : IsProperMap (fun z : ℂ ↦ z ^ m) := by
    simpa only [Polynomial.eval_X_pow] using
      Polynomial.isProperMap_eval ((Polynomial.X : Polynomial ℂ) ^ m) hdegree
  have hpreimage :
      (fun z : ℂ ↦ z ^ m) ⁻¹' ({0}ᶜ : Set ℂ) = {z : ℂ | z ≠ 0} := by
    ext z
    simp [NeZero.ne m]
  let e : {z : ℂ // z ≠ 0} ≃ₜ
      (fun z : ℂ ↦ z ^ m) ⁻¹' ({0}ᶜ : Set ℂ) :=
    Homeomorph.setCongr hpreimage.symm
  let d : ({0}ᶜ : Set ℂ) ≃ₜ {z : ℂ // z ≠ 0} :=
    Homeomorph.setCongr (by
      ext z
      change (z ≠ 0) ↔ (z ≠ 0)
      rfl)
  have hrestricted := hproper.restrictPreimage ({0}ᶜ : Set ℂ)
  have hcomposed : IsProperMap
      (d ∘ Set.restrictPreimage ({0}ᶜ : Set ℂ) (fun z : ℂ ↦ z ^ m) ∘ e) :=
    d.isProperMap.comp (hrestricted.comp e.isProperMap)
  convert hcomposed using 1
  ext z
  rfl

end SplittingSpheres
