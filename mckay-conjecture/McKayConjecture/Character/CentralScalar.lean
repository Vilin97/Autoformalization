/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Category.ModuleCat.Simple
import McKayConjecture.Character.QuotientDescent

/-!
# Scalars of irreducible characters on central elements

Schur's lemma makes every central group element act by a scalar in an
irreducible complex representation.  This file exposes that scalar and gives
an exact value criterion for representation-level triviality on a central
subgroup.

The criterion is particularly useful for central products: on a central
kernel, triviality can be checked from character values and degrees, so it is
independent of the chosen realization.
-/

noncomputable section

open CategoryTheory

universe u

namespace McKayConjecture
namespace IrreducibleCharacter

variable {G : Type u} [Group G]

/-- A central group element acts as an endomorphism of an irreducible
representation object. -/
def centralElementEndomorphism
    (χ : IrreducibleCharacter G)
    (z : G) (hz : z ∈ Subgroup.center G) :
    χ.realization ⟶ χ.realization :=
  ⟨InducedCategory.homMk
      (ModuleCat.ofHom (χ.realization.ρ z)),
    fun g => by
      apply FGModuleCat.hom_ext
      ext v
      change
        χ.realization.ρ z (χ.realization.ρ g v) =
          χ.realization.ρ g (χ.realization.ρ z v)
      rw [← Module.End.mul_apply, ← Module.End.mul_apply,
        ← map_mul, ← map_mul]
      exact congrArg (fun h : G => χ.realization.ρ h v)
        ((Subgroup.mem_center_iff.mp hz) g).symm⟩

@[simp]
theorem centralElementEndomorphism_apply
    (χ : IrreducibleCharacter G)
    (z : G) (hz : z ∈ Subgroup.center G)
    (v : χ.realization) :
    χ.centralElementEndomorphism z hz v =
      χ.realization.ρ z v :=
  rfl

/-- Schur's lemma in the form needed for ordinary characters: a central
element acts by one complex scalar. -/
theorem exists_realization_scalar_of_mem_center
    (χ : IrreducibleCharacter G)
    (z : G) (hz : z ∈ Subgroup.center G) :
    ∃ c : ℂ,
      χ.realization.ρ z =
        c • (LinearMap.id : Module.End ℂ χ.realization) := by
  let f := χ.centralElementEndomorphism z hz
  obtain ⟨c, hc⟩ :=
    endomorphism_simple_eq_smul_id ℂ f
  refine ⟨c, ?_⟩
  apply LinearMap.ext
  intro v
  have hv := ConcreteCategory.congr_hom hc v
  change c • v = χ.realization.ρ z v at hv
  simpa using hv.symm

/-- The value of an irreducible character at a central element is its degree
times the scalar by which that element acts. -/
theorem values_eq_scalar_mul_degree
    (χ : IrreducibleCharacter G)
    (z : G) (c : ℂ)
    (hc :
      χ.realization.ρ z =
        c • (LinearMap.id : Module.End ℂ χ.realization)) :
    χ.values z = c * (χ.degree : ℂ) := by
  calc
    χ.values z =
        χ.realization.character z :=
      (congrFun χ.realization_character z).symm
    _ =
        LinearMap.trace ℂ χ.realization
          (χ.realization.ρ z) :=
      rfl
    _ =
        LinearMap.trace ℂ χ.realization
          (c • (LinearMap.id :
            Module.End ℂ χ.realization)) := by
      rw [hc]
    _ = c *
        LinearMap.trace ℂ χ.realization
          (LinearMap.id :
            Module.End ℂ χ.realization) := by
      rw [map_smul]
      rfl
    _ = c * (χ.degree : ℂ) := by
      rw [LinearMap.trace_id, χ.realization_finrank]

/-- On a central subgroup, representation-level triviality is equivalent to
the elementary character-value identity `χ(z) = χ(1)`. -/
theorem trivialOn_iff_values_eq_degree
    [Finite G]
    (χ : IrreducibleCharacter G)
    (Z : Subgroup G)
    (hZ : Z ≤ Subgroup.center G) :
    χ.TrivialOn Z ↔
      ∀ z : Z, χ.values z = (χ.degree : ℂ) := by
  constructor
  · intro htriv z
    calc
      χ.values z =
          χ.realization.character (z : G) :=
        (congrFun χ.realization_character z).symm
      _ =
          LinearMap.trace ℂ χ.realization
            (χ.realization.ρ (z : G)) :=
        rfl
      _ =
          LinearMap.trace ℂ χ.realization
            (LinearMap.id :
              Module.End ℂ χ.realization) := by
        rw [htriv z]
      _ = (χ.degree : ℂ) := by
        rw [LinearMap.trace_id, χ.realization_finrank]
  · intro hvalues z
    obtain ⟨c, hc⟩ :=
      χ.exists_realization_scalar_of_mem_center
        (z : G) (hZ z.2)
    have hscalarDegree :
        c * (χ.degree : ℂ) =
          1 * (χ.degree : ℂ) := by
      rw [← χ.values_eq_scalar_mul_degree (z : G) c hc,
        hvalues z, one_mul]
    have hc_one : c = 1 :=
      mul_right_cancel₀
        (Nat.cast_ne_zero.mpr χ.degree_ne_zero)
        hscalarDegree
    rw [hc, hc_one, one_smul]

end IrreducibleCharacter
end McKayConjecture
