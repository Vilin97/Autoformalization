/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Uniqueness of implementers of endomorphism conjugation

Two invertible linear operators inducing the same conjugation
automorphism of a full endomorphism algebra differ by a nonzero scalar.
This is the uniqueness half of the Skolem--Noether argument used when
lifting actions on a split central simple algebra.
-/

noncomputable section

namespace Representation

variable {k V : Type}
variable [Field k]
variable [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V] [Nontrivial V]

/-- Scalar units in the full endomorphism algebra. -/
def endomorphismScalarUnit :
    kˣ →* (Module.End k V)ˣ :=
  Units.map
    (algebraMap k (Module.End k V)).toMonoidHom

omit [FiniteDimensional k V] [Nontrivial V] in
@[simp]
theorem coe_endomorphismScalarUnit
    (z : kˣ) :
    (endomorphismScalarUnit (V := V) z :
      Module.End k V) =
      algebraMap k (Module.End k V) (z : k) :=
  rfl

omit [FiniteDimensional k V] in
/-- Scalar units act faithfully on a nonzero vector space. -/
theorem endomorphismScalarUnit_injective :
    Function.Injective
      (endomorphismScalarUnit (k := k) (V := V)) := by
  intro z w h
  apply Units.ext
  apply FaithfulSMul.algebraMap_injective k (Module.End k V)
  exact congrArg Units.val h

omit [FiniteDimensional k V] [Nontrivial V] in
/-- Scalar units commute with every invertible endomorphism. -/
theorem endomorphismScalarUnit_commute
    (z : kˣ) (u : (Module.End k V)ˣ) :
    endomorphismScalarUnit (V := V) z * u =
      u * endomorphismScalarUnit (V := V) z := by
  apply Units.ext
  exact Algebra.commutes (z : k) (u : Module.End k V)

omit [FiniteDimensional k V] in
/-- If two units of a full endomorphism algebra induce the same
conjugation on every endomorphism, then their ratio is a scalar unit. -/
theorem exists_eq_mul_endomorphismScalarUnit_of_conjugation_eq
    (u v : (Module.End k V)ˣ)
    (hconj :
      ∀ f : Module.End k V,
        (u : Module.End k V) * f *
              (↑(u⁻¹) : Module.End k V) =
          (v : Module.End k V) * f *
              (↑(v⁻¹) : Module.End k V)) :
    ∃ z : kˣ,
      u = v * endomorphismScalarUnit (V := V) z := by
  let w : (Module.End k V)ˣ := v⁻¹ * u
  have hcomm :
      ∀ f : Module.End k V,
        (w : Module.End k V) * f =
          f * (w : Module.End k V) := by
    intro f
    have hu :
        (↑(u⁻¹) : Module.End k V) *
            (u : Module.End k V) =
          1 := by
      rw [← Units.val_mul, inv_mul_cancel]
      rfl
    have hv :
        (↑(v⁻¹) : Module.End k V) *
            (v : Module.End k V) =
          1 := by
      rw [← Units.val_mul, inv_mul_cancel]
      rfl
    have hvleft (x : Module.End k V) :
        (↑(v⁻¹) : Module.End k V) *
            ((v : Module.End k V) * x) =
          x := by
      rw [← mul_assoc, hv, one_mul]
    have h :=
      congrArg
        (fun x : Module.End k V =>
          (↑(v⁻¹) : Module.End k V) * x *
            (u : Module.End k V))
        (hconj f)
    simpa only [w, Units.val_mul, mul_assoc, hu,
      hvleft, mul_one] using h
  have hwcenter :
      (w : Module.End k V) ∈
        Set.center (Module.End k V) :=
    Semigroup.mem_center_iff.mpr
      (fun f ↦ (hcomm f).symm)
  obtain ⟨a, _, ha⟩ :=
    (Module.End.mem_center_iff.mp hwcenter)
  have ha0 : a ≠ 0 := by
    intro hazero
    subst a
    apply Units.ne_zero w
    rw [ha]
    ext x
    simp
  let z : kˣ := Units.mk0 a ha0
  have hw : w = endomorphismScalarUnit (V := V) z := by
    apply Units.ext
    rw [ha]
    ext x
    change a • x = a • x
    rfl
  refine ⟨z, ?_⟩
  calc
    u = v * w := by
      simp [w]
    _ = v * endomorphismScalarUnit (V := V) z := by
      rw [hw]

section GroupLift

variable {P : Type} [Group P]

omit [FiniteDimensional k V] in
/-- Two group lifts inducing the same action on a full endomorphism
algebra differ by a unique linear character. -/
theorem exists_unique_scalarCharacter_of_conjugation_eq
    (σ τ : P →* (Module.End k V)ˣ)
    (hconj :
      ∀ (g : P) (f : Module.End k V),
        (σ g : Module.End k V) * f *
              (↑((σ g)⁻¹) : Module.End k V) =
          (τ g : Module.End k V) * f *
              (↑((τ g)⁻¹) : Module.End k V)) :
    ∃! χ : P →* kˣ,
      ∀ g,
        σ g =
          τ g * endomorphismScalarUnit (V := V) (χ g) := by
  choose z hz using fun g =>
    exists_eq_mul_endomorphismScalarUnit_of_conjugation_eq
      (σ g) (τ g) (hconj g)
  have hone : z 1 = 1 := by
    apply endomorphismScalarUnit_injective (k := k) (V := V)
    have h :=
      congrArg (fun x => (τ 1)⁻¹ * x) (hz 1)
    simpa using h.symm
  have hmul : ∀ g h, z (g * h) = z g * z h := by
    intro g h
    apply endomorphismScalarUnit_injective (k := k) (V := V)
    apply mul_left_cancel (a := τ (g * h))
    calc
      τ (g * h) *
          endomorphismScalarUnit (V := V) (z (g * h)) =
        σ (g * h) := (hz (g * h)).symm
      _ = σ g * σ h := map_mul σ g h
      _ =
          (τ g * endomorphismScalarUnit (V := V) (z g)) *
            (τ h * endomorphismScalarUnit (V := V) (z h)) := by
        rw [hz g, hz h]
      _ =
          (τ g * τ h) *
            (endomorphismScalarUnit (V := V) (z g) *
              endomorphismScalarUnit (V := V) (z h)) := by
        calc
          (τ g * endomorphismScalarUnit (V := V) (z g)) *
                (τ h * endomorphismScalarUnit (V := V) (z h)) =
              τ g *
                (endomorphismScalarUnit (V := V) (z g) * τ h) *
                endomorphismScalarUnit (V := V) (z h) := by
            simp only [mul_assoc]
          _ =
              τ g *
                (τ h * endomorphismScalarUnit (V := V) (z g)) *
                endomorphismScalarUnit (V := V) (z h) := by
            rw [
              endomorphismScalarUnit_commute
                (V := V) (z g) (τ h)]
          _ =
              (τ g * τ h) *
                (endomorphismScalarUnit (V := V) (z g) *
                  endomorphismScalarUnit (V := V) (z h)) := by
            simp only [mul_assoc]
      _ =
          τ (g * h) *
            endomorphismScalarUnit (V := V) (z g * z h) := by
        rw [map_mul τ, map_mul]
  let χ : P →* kˣ :=
    { toFun := z
      map_one' := hone
      map_mul' := hmul }
  refine ⟨χ, hz, ?_⟩
  intro ψ hψ
  apply MonoidHom.ext
  intro g
  apply endomorphismScalarUnit_injective (k := k) (V := V)
  apply mul_left_cancel (a := τ g)
  change
    τ g * endomorphismScalarUnit (V := V) (ψ g) =
      τ g * endomorphismScalarUnit (V := V) (z g)
  exact (hψ g).symm.trans (hz g)

end GroupLift

end Representation
