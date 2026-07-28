/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.InvariantExtensionIntertwinerComparison

/-!
# Transporting conjugation actions through scalar operator comparisons

If two pairs of operators are intertwined up to nonzero scalars, their
induced conjugation actions on a linear Hom-space are intertwined by the
quotient of those scalars.  This elementary calculation is separated from
the character-theoretic construction of the scalars.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple

variable
  {VSource VTarget WSource WTarget : Type}
  [AddCommGroup VSource] [Module ℂ VSource]
  [AddCommGroup VTarget] [Module ℂ VTarget]
  [AddCommGroup WSource] [Module ℂ WSource]
  [AddCommGroup WTarget] [Module ℂ WTarget]

/-- Inverting an operator comparison inverts its scalar. -/
theorem scalar_operator_comparison_symm
    (E : VTarget ≃ₗ[ℂ] WTarget)
    (T : VTarget ≃ₗ[ℂ] VTarget)
    (P : WTarget ≃ₗ[ℂ] WTarget)
    (c : ℂˣ)
    (h :
      ∀ v : VTarget,
        E (T v) = (c : ℂ) • P (E v))
    (w : WTarget) :
    T.symm (E.symm w) =
      ((c⁻¹ : ℂˣ) : ℂ) • E.symm (P.symm w) := by
  apply E.injective
  have hw :=
    h (T.symm (E.symm w))
  have hw' :
      w =
        (c : ℂ) •
          P (E (T.symm (E.symm w))) := by
    simpa using hw
  have hscaled :=
    congrArg
      (fun z : WTarget ↦
        ((c⁻¹ : ℂˣ) : ℂ) • P.symm z)
      hw'
  simpa only [map_smul, LinearEquiv.symm_apply_apply,
    LinearEquiv.apply_symm_apply,
    Units.val_inv_eq_inv_val, inv_smul_smul₀ c.ne_zero]
    using hscaled.symm

/-- Scalar comparisons on source and target operators combine as their
quotient under the induced conjugation action on a Hom-space. -/
theorem scalar_conjugation_transport
    (ESource : VSource ≃ₗ[ℂ] WSource)
    (ETarget : VTarget ≃ₗ[ℂ] WTarget)
    (TSource : VSource ≃ₗ[ℂ] VSource)
    (TTarget : VTarget ≃ₗ[ℂ] VTarget)
    (PSource : WSource ≃ₗ[ℂ] WSource)
    (PTarget : WTarget ≃ₗ[ℂ] WTarget)
    (cSource cTarget : ℂˣ)
    (hSource :
      ∀ v : VSource,
        ESource (TSource v) =
          (cSource : ℂ) • PSource (ESource v))
    (hTarget :
      ∀ v : VTarget,
        ETarget (TTarget v) =
          (cTarget : ℂ) • PTarget (ETarget v))
    (f : VTarget →ₗ[ℂ] VSource)
    (w : WTarget) :
    ESource
        (TSource
          (f (TTarget.symm (ETarget.symm w)))) =
      ((cSource * cTarget⁻¹ : ℂˣ) : ℂ) •
        PSource
          (ESource
            (f (ETarget.symm (PTarget.symm w)))) := by
  rw [scalar_operator_comparison_symm
    ETarget TTarget PTarget cTarget hTarget]
  rw [map_smul, hSource, map_smul]
  simp only [map_smul]
  simp only [Units.val_inv_eq_inv_val, Units.val_mul, smul_smul]

end CharacterTriple
end McKayConjecture
