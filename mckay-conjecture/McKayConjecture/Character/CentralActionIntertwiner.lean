/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralScalar
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Intertwiners for central actions

Let `χ` and `ψ` be irreducible characters of possibly different groups,
and let `a` and `b` be central elements.  Schur's lemma says that the two
chosen realization operators are scalar.  A nonzero linear map intertwining
those two operators forces the scalars to agree, even when the realization
spaces have different dimensions.  Consequently the normalized character
values at `a` and `b` agree.

This is a deliberately elementwise interface.  It records representation
coherence upstream of the resulting character-value identity without
requiring a character-triple witness or a common ambient group.
-/

noncomputable section

namespace McKayConjecture
namespace IrreducibleCharacter

universe u v

variable {A : Type u} {B : Type v}
variable [Group A] [Group B]

/-- A nonzero linear map intertwining the actions of two specified group
elements on chosen irreducible realizations. -/
structure CentralActionIntertwiner
    (χ : IrreducibleCharacter A)
    (ψ : IrreducibleCharacter B)
    (a : A) (b : B) where
  /-- The comparison map between the two realization spaces. -/
  toLinearMap :
    χ.realization →ₗ[ℂ] ψ.realization
  /-- The comparison map is nonzero. -/
  ne_zero : toLinearMap ≠ 0
  /-- The comparison map intertwines the two selected operators. -/
  intertwines :
    toLinearMap.comp (χ.realization.ρ a) =
      (ψ.realization.ρ b).comp toLinearMap

namespace CentralActionIntertwiner

variable {χ : IrreducibleCharacter A}
variable {ψ : IrreducibleCharacter B}
variable {a : A} {b : B}

/-- A central-action intertwiner forces equality of normalized central
character values. -/
theorem central_cross
    (I : CentralActionIntertwiner χ ψ a b)
    (ha : a ∈ Subgroup.center A)
    (hb : b ∈ Subgroup.center B) :
    χ.values a * (ψ.degree : ℂ) =
      ψ.values b * (χ.degree : ℂ) := by
  obtain ⟨c, hc⟩ :=
    χ.exists_realization_scalar_of_mem_center a ha
  obtain ⟨d, hd⟩ :=
    ψ.exists_realization_scalar_of_mem_center b hb
  obtain ⟨x, hx⟩ :
      ∃ x : χ.realization, I.toLinearMap x ≠ 0 := by
    by_contra h
    simp only [not_exists, not_ne_iff] at h
    apply I.ne_zero
    ext x
    exact h x
  have hintertwines :
      I.toLinearMap (χ.realization.ρ a x) =
        ψ.realization.ρ b (I.toLinearMap x) :=
    LinearMap.congr_fun I.intertwines x
  have hscalar : c = d := by
    apply smul_left_injective ℂ hx
    calc
      c • I.toLinearMap x =
          I.toLinearMap (c • x) :=
        (I.toLinearMap.map_smul c x).symm
      _ = I.toLinearMap (χ.realization.ρ a x) := by
        rw [hc, LinearMap.smul_apply, LinearMap.id_apply]
      _ = ψ.realization.ρ b (I.toLinearMap x) :=
        hintertwines
      _ = d • I.toLinearMap x := by
        rw [hd, LinearMap.smul_apply, LinearMap.id_apply]
  rw [χ.values_eq_scalar_mul_degree a c hc,
    ψ.values_eq_scalar_mul_degree b d hd,
    hscalar]
  ring

/-- Conversely, equality of normalized central character values constructs
a nonzero intertwiner between the two central actions.  The realization
spaces need not have the same dimension: once Schur's lemma identifies both
operators with the same scalar, any nonzero rank-one linear map works. -/
def of_central_cross
    (ha : a ∈ Subgroup.center A)
    (hb : b ∈ Subgroup.center B)
    (hcross :
      χ.values a * (ψ.degree : ℂ) =
        ψ.values b * (χ.degree : ℂ)) :
    CentralActionIntertwiner χ ψ a b := by
  let c : ℂ :=
    Classical.choose
      (χ.exists_realization_scalar_of_mem_center a ha)
  have hc :
      χ.realization.ρ a =
        c • LinearMap.id :=
    Classical.choose_spec
      (χ.exists_realization_scalar_of_mem_center a ha)
  let d : ℂ :=
    Classical.choose
      (ψ.exists_realization_scalar_of_mem_center b hb)
  have hd :
      ψ.realization.ρ b =
        d • LinearMap.id :=
    Classical.choose_spec
      (ψ.exists_realization_scalar_of_mem_center b hb)
  have hχdegree : (χ.degree : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr χ.degree_ne_zero
  have hψdegree : (ψ.degree : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr ψ.degree_ne_zero
  have hscalar : c = d := by
    rw [χ.values_eq_scalar_mul_degree a c hc,
      ψ.values_eq_scalar_mul_degree b d hd] at hcross
    apply mul_left_cancel₀ (mul_ne_zero hχdegree hψdegree)
    calc
      (χ.degree : ℂ) * (ψ.degree : ℂ) * c =
          c * (χ.degree : ℂ) * (ψ.degree : ℂ) := by ring
      _ = d * (ψ.degree : ℂ) * (χ.degree : ℂ) := hcross
      _ = (χ.degree : ℂ) * (ψ.degree : ℂ) * d := by ring
  have hexistsx :
      ∃ x : χ.realization, x ≠ 0 :=
    Module.finrank_pos_iff_exists_ne_zero.mp (by
      rw [χ.realization_finrank]
      exact χ.degree_pos)
  let x : χ.realization :=
    Classical.choose hexistsx
  have hx : x ≠ 0 :=
    Classical.choose_spec hexistsx
  have hexistsy :
      ∃ y : ψ.realization, y ≠ 0 :=
    Module.finrank_pos_iff_exists_ne_zero.mp (by
      rw [ψ.realization_finrank]
      exact ψ.degree_pos)
  let y : ψ.realization :=
    Classical.choose hexistsy
  have hy : y ≠ 0 :=
    Classical.choose_spec hexistsy
  let f : Module.Dual ℂ χ.realization :=
    Classical.choose
      (Module.Projective.exists_dual_ne_zero ℂ hx)
  have hfx : f x ≠ 0 :=
    Classical.choose_spec
      (Module.Projective.exists_dual_ne_zero ℂ hx)
  let T : χ.realization →ₗ[ℂ] ψ.realization :=
    f.smulRight y
  refine
    { toLinearMap := T
      ne_zero := ?_
      intertwines := ?_ }
  · intro hT
    have hTx := LinearMap.congr_fun hT x
    simp only [T, LinearMap.smulRight_apply, LinearMap.zero_apply] at hTx
    apply hfx
    exact
      smul_left_injective ℂ hy
        (by simpa only [zero_smul] using hTx)
  · ext v
    rw [hc, hd, hscalar]
    simp only [LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_smul]

/-- For central elements, the existence of a central-action intertwiner is
equivalent to equality of normalized central character values. -/
theorem nonempty_iff_central_cross
    (ha : a ∈ Subgroup.center A)
    (hb : b ∈ Subgroup.center B) :
    Nonempty (CentralActionIntertwiner χ ψ a b) ↔
      χ.values a * (ψ.degree : ℂ) =
        ψ.values b * (χ.degree : ℂ) := by
  constructor
  · rintro ⟨I⟩
    exact I.central_cross ha hb
  · exact fun h ↦ ⟨of_central_cross ha hb h⟩

end CentralActionIntertwiner
end IrreducibleCharacter
end McKayConjecture
