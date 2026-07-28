/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.CentralExtensionUniversalityCriterion
import McKayConjecture.GroupTheory.UniversalCentralExtensionTargetEquiv

/-!
# Central closedness is invariant under group equivalence

This small transport lemma lets a finite presentation prove central
closedness for a concrete matrix group.  The proof transports an arbitrary
central extension across the inverse target equivalence and then transports
the resulting section back.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

/-- A multiplicative equivalence transports central closedness from its
source to its target. -/
theorem IsCentrallyClosed.of_mulEquiv
    {U V : Type u} [Group U] [Group V]
    (hU : IsCentrallyClosed U)
    (e : U ≃* V) :
    IsCentrallyClosed V := by
  intro W _ F
  let F' : CentralExtension W U :=
    F.targetEquiv e.symm
  obtain ⟨σ, hσ⟩ := hU W F'
  refine
    ⟨σ.comp e.symm.toMonoidHom, ?_⟩
  ext v
  apply e.symm.injective
  have hv :=
    DFunLike.congr_fun hσ (e.symm v)
  simpa [F'] using hv

/-- Central closedness is equivalent across a multiplicative
equivalence. -/
theorem isCentrallyClosed_iff_of_mulEquiv
    {U V : Type u} [Group U] [Group V]
    (e : U ≃* V) :
    IsCentrallyClosed U ↔ IsCentrallyClosed V :=
  ⟨fun h ↦ h.of_mulEquiv e,
    fun h ↦ h.of_mulEquiv e.symm⟩

end GroupTheory
end McKayConjecture
