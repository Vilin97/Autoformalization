/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Topology.Homotopy.Isotopy.Basic

/-!
# Transporting ambient isotopies through homeomorphisms

An ambient isotopy of `Y` pulls back through a homeomorphism `e : X ≃ₜ Y` by conjugating every
time slice with `e`.  The level-preserving total map is the corresponding conjugate of the old
total homeomorphism.  This file records the construction and its exact evaluation laws.
-/

@[expose] public section

open scoped unitInterval

namespace TauCeti.AmbientIsotopy

universe uX uY

variable {X : Type uX} {Y : Type uY}
variable [TopologicalSpace X] [TopologicalSpace Y]

/-- Pull an ambient isotopy of `Y` back through a homeomorphism `e : X ≃ₜ Y`.

At time `t`, this is the conjugate `e⁻¹ ∘ Phiₜ ∘ e`. -/
def pullbackHomeomorph (Phi : AmbientIsotopy Y) (e : X ≃ₜ Y) : AmbientIsotopy X where
  toContinuousMap :=
    ⟨fun p ↦ e.symm (Phi.toContinuousMap (p.1, e p.2)), by fun_prop⟩
  isHomeomorph_total' := by
    let eTotal : (unitInterval × X) ≃ₜ unitInterval × Y :=
      (Homeomorph.refl unitInterval).prodCongr e
    have hfun :
        (fun p : unitInterval × X ↦
          (p.1, e.symm (Phi.toContinuousMap (p.1, e p.2)))) =
          eTotal.symm ∘ Phi.totalMap ∘ eTotal := by
      funext p
      simp [eTotal, Function.comp_apply, Prod.map]
    rw [hfun]
    exact eTotal.symm.isHomeomorph.comp
      (Phi.isHomeomorph_total.comp eTotal.isHomeomorph)
  map_zero_left' := by
    intro x
    simp

@[simp]
theorem pullbackHomeomorph_apply (Phi : AmbientIsotopy Y) (e : X ≃ₜ Y)
    (p : unitInterval × X) :
    (Phi.pullbackHomeomorph e).toContinuousMap p =
      e.symm (Phi.toContinuousMap (p.1, e p.2)) :=
  rfl

/-- Conjugating the transported time slice back by `e` recovers the original time slice. -/
theorem apply_pullbackHomeomorph (Phi : AmbientIsotopy Y) (e : X ≃ₜ Y)
    (t : unitInterval) (x : X) :
    e ((Phi.pullbackHomeomorph e).toContinuousMap (t, x)) =
      Phi.toContinuousMap (t, e x) := by
  simp

@[simp]
theorem final_pullbackHomeomorph (Phi : AmbientIsotopy Y) (e : X ≃ₜ Y) (x : X) :
    (Phi.pullbackHomeomorph e).final x = e.symm (Phi.final (e x)) :=
  by
    rw [final_apply, pullbackHomeomorph_apply, final_apply]

/-- The time-slice homeomorphism is exactly the conjugate of the original time slice. -/
theorem homeomorph_pullbackHomeomorph (Phi : AmbientIsotopy Y) (e : X ≃ₜ Y)
    (t : unitInterval) :
    (Phi.pullbackHomeomorph e).homeomorph t =
      e.trans ((Phi.homeomorph t).trans e.symm) := by
  ext x
  rw [homeomorph_apply, pullbackHomeomorph_apply,
    Homeomorph.trans_apply, Homeomorph.trans_apply, homeomorph_apply]

end TauCeti.AmbientIsotopy
