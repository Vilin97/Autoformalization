/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RepresentationTheory.Character
import Mathlib.Tactic
import McKayConjecture.GroupTheory.QuaternionGroupHom

/-!
# Two-dimensional representations of dicyclic groups

Let `r` be a nonzero scalar satisfying `r ^ (2 * n) = 1`.  The standard
two-dimensional representation of `QuaternionGroup n` sends its generators
to

`A = diag(r, r⁻¹)` and `X = [[0, r^n], [1, 0]]`.

The dicyclic relations are verified as matrix identities and fed to the
generic `QuaternionGroup.lift` constructor.
-/

noncomputable section

open Matrix

namespace McKayConjecture
namespace QuaternionGroupRepresentation

variable {n : ℕ}

/-- Matrix of the cyclic dicyclic generator. -/
def cyclicMatrix (r : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![r, 0; 0, r⁻¹]

/-- Matrix of the order-four dicyclic generator. -/
def reflectionMatrix (n : ℕ) (r : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, r ^ n; 1, 0]

/-- The cyclic generator as an invertible matrix. -/
def cyclicGL (r : ℂ) (hr : r ≠ 0) :
    Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (cyclicMatrix r) (by
      simp [cyclicMatrix, Matrix.det_fin_two_of, hr])

/-- The order-four generator as an invertible matrix. -/
def reflectionGL (n : ℕ) (r : ℂ) (hr : r ≠ 0) :
    Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (reflectionMatrix n r) (by
      simp [reflectionMatrix, Matrix.det_fin_two_of,
        pow_ne_zero _ hr])

@[simp]
theorem coe_cyclicGL (r : ℂ) (hr : r ≠ 0) :
    (cyclicGL r hr :
      Matrix (Fin 2) (Fin 2) ℂ) =
      cyclicMatrix r :=
  rfl

@[simp]
theorem coe_reflectionGL (n : ℕ) (r : ℂ) (hr : r ≠ 0) :
    (reflectionGL n r hr :
      Matrix (Fin 2) (Fin 2) ℂ) =
      reflectionMatrix n r :=
  rfl

/-- Powers of the diagonal cyclic matrix are computed entrywise. -/
theorem cyclicMatrix_pow (r : ℂ) (m : ℕ) :
    cyclicMatrix r ^ m =
      !![r ^ m, 0; 0, (r⁻¹) ^ m] := by
  rw [show cyclicMatrix r =
      Matrix.diagonal ![r, r⁻¹] by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cyclicMatrix]]
  rw [Matrix.diagonal_pow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The cyclic matrix has the required order-dividing relation. -/
theorem cyclicGL_pow_two_mul
    (r : ℂ) (hr : r ≠ 0)
    (hroot : r ^ (2 * n) = 1) :
    cyclicGL r hr ^ (2 * n) = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  simp only [coe_cyclicGL, cyclicMatrix_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hroot, inv_pow]

/-- Squaring the reflection matrix gives the scalar `r^n`. -/
theorem reflectionGL_sq
    (r : ℂ) (hr : r ≠ 0) :
    ∀ (hroot : r ^ (2 * n) = 1),
    reflectionGL n r hr * reflectionGL n r hr =
      QuaternionGroup.zmodPower
        (cyclicGL r hr)
        (cyclicGL_pow_two_mul r hr hroot)
        n := by
  intro hroot
  rw [QuaternionGroup.zmodPower_natCast]
  have hself :
      (r ^ n)⁻¹ = r ^ n := by
    apply inv_eq_of_mul_eq_one_right
    calc
      r ^ n * r ^ n = r ^ (n + n) := (pow_add r n n).symm
      _ = r ^ (2 * n) := by rw [two_mul]
      _ = 1 := hroot
  apply Units.ext
  rw [Units.val_mul, Units.val_pow_eq_pow_val]
  simp only [coe_reflectionGL, coe_cyclicGL,
    cyclicMatrix_pow]
  simp [reflectionMatrix, Matrix.mul_fin_two,
    hself, inv_pow]

/-- The two generator matrices satisfy the basic dicyclic conjugation
relation before taking arbitrary powers of the cyclic generator. -/
theorem cyclicGL_mul_reflectionGL
    (r : ℂ) (hr : r ≠ 0) :
    cyclicGL r hr * reflectionGL n r hr =
      reflectionGL n r hr * (cyclicGL r hr)⁻¹ := by
  have htriple :
      cyclicGL r hr * reflectionGL n r hr *
          cyclicGL r hr =
        reflectionGL n r hr := by
    apply Units.ext
    simp only [Units.val_mul, coe_cyclicGL,
      coe_reflectionGL]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cyclicMatrix, reflectionMatrix,
        Matrix.mul_apply, hr, mul_comm] <;>
      field_simp
  calc
    cyclicGL r hr * reflectionGL n r hr =
        (cyclicGL r hr * reflectionGL n r hr *
          cyclicGL r hr) * (cyclicGL r hr)⁻¹ := by
          group
    _ =
        reflectionGL n r hr * (cyclicGL r hr)⁻¹ := by
          rw [htriple]

/-- The standard two-dimensional homomorphism of a dicyclic group into
invertible matrices. -/
def standardGLHom
    (r : ℂ) (hr : r ≠ 0)
    (hroot : r ^ (2 * n) = 1) :
    QuaternionGroup n →*
      Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  QuaternionGroup.lift
    (cyclicGL r hr)
    (reflectionGL n r hr)
    (cyclicGL_pow_two_mul r hr hroot)
    (reflectionGL_sq r hr hroot)
    (QuaternionGroup.zmodPower_mul_eq_mul_zmodPower_neg
      (cyclicGL r hr)
      (reflectionGL n r hr)
      (cyclicGL_pow_two_mul r hr hroot)
      (cyclicGL_mul_reflectionGL r hr))

/-- The standard two-dimensional complex representation of a dicyclic
group. -/
def standardRepresentation
    (r : ℂ) (hr : r ≠ 0)
    (hroot : r ^ (2 * n) = 1) :
    Representation ℂ (QuaternionGroup n) (Fin 2 → ℂ) :=
  (Units.coeHom
      ((Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))).comp
    ((Matrix.GeneralLinearGroup.toLin :
        Matrix.GeneralLinearGroup (Fin 2) ℂ ≃*
          LinearMap.GeneralLinearGroup ℂ (Fin 2 → ℂ))
      |>.toMonoidHom.comp
        (standardGLHom r hr hroot))

@[simp]
theorem standardGLHom_apply_a
    (r : ℂ) (hr : r ≠ 0)
    (hroot : r ^ (2 * n) = 1)
    (i : ZMod (2 * n)) :
    standardGLHom r hr hroot (QuaternionGroup.a i) =
      QuaternionGroup.zmodPower
        (cyclicGL r hr)
        (cyclicGL_pow_two_mul r hr hroot)
        i :=
  rfl

@[simp]
theorem standardGLHom_apply_xa
    (r : ℂ) (hr : r ≠ 0)
    (hroot : r ^ (2 * n) = 1)
    (i : ZMod (2 * n)) :
    standardGLHom r hr hroot (QuaternionGroup.xa i) =
      reflectionGL n r hr *
        QuaternionGroup.zmodPower
          (cyclicGL r hr)
          (cyclicGL_pow_two_mul r hr hroot)
          i :=
  rfl

@[simp]
theorem standardRepresentation_apply
    (r : ℂ) (hr : r ≠ 0)
    (hroot : r ^ (2 * n) = 1)
    (g : QuaternionGroup n) :
    standardRepresentation r hr hroot g =
      Matrix.toLin'
        (standardGLHom r hr hroot g :
          Matrix (Fin 2) (Fin 2) ℂ) :=
  rfl

/-- First standard basis vector of the two-dimensional model. -/
def firstVector : Fin 2 → ℂ :=
  ![1, 0]

/-- Second standard basis vector of the two-dimensional model. -/
def secondVector : Fin 2 → ℂ :=
  ![0, 1]

theorem standardRepresentation_apply_cyclicGenerator
    (r : ℂ) (hr : r ≠ 0)
    (hroot : r ^ (2 * n) = 1)
    (v : Fin 2 → ℂ) :
    standardRepresentation r hr hroot
        (QuaternionGroup.a (1 : ZMod (2 * n))) v =
      ![r * v 0, r⁻¹ * v 1] := by
  rw [standardRepresentation_apply,
    standardGLHom_apply_a]
  rw [show (1 : ZMod (2 * n)) =
      ((1 : ℕ) : ZMod (2 * n)) by norm_num]
  rw [QuaternionGroup.zmodPower_natCast]
  funext i
  fin_cases i <;>
    simp [Matrix.toLin'_apply, cyclicMatrix,
      Matrix.mulVec, dotProduct]

theorem standardRepresentation_apply_reflectionGenerator
    (r : ℂ) (hr : r ≠ 0)
    (hroot : r ^ (2 * n) = 1)
    (v : Fin 2 → ℂ) :
    standardRepresentation r hr hroot
        (QuaternionGroup.xa (0 : ZMod (2 * n))) v =
      ![r ^ n * v 1, v 0] := by
  funext i
  fin_cases i <;>
    simp [standardRepresentation, standardGLHom,
      Matrix.toLin'_apply, reflectionMatrix,
      Matrix.mulVec, dotProduct]

theorem vector_eq_coord_smul
    (v : Fin 2 → ℂ) :
    v = v 0 • firstVector + v 1 • secondVector := by
  funext i
  fin_cases i <;> simp [firstVector, secondVector]

/-- The standard dicyclic representation is irreducible as soon as the
two eigenvalues of the cyclic generator are distinct. -/
theorem standardRepresentation_isIrreducible
    (r : ℂ) (hr : r ≠ 0)
    (hroot : r ^ (2 * n) = 1)
    (heigen : r ≠ r⁻¹) :
    Representation.IsIrreducible
      (standardRepresentation r hr hroot) := by
  letI :
      Nontrivial
        (Subrepresentation
          (standardRepresentation r hr hroot)) :=
    ⟨⟨⊥, ⊤, fun h =>
      bot_ne_top
        (congrArg Subrepresentation.toSubmodule h)⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  have hSub : S.toSubmodule ≠ ⊥ := by
    intro h
    apply hS
    apply Subrepresentation.ext
    exact h
  obtain ⟨v, hv, hvne⟩ :=
    S.toSubmodule.ne_bot_iff.mp hSub
  have hcoord : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hvne
    funext i
    fin_cases i <;> simp [h.1, h.2]
  have hcyclic :
      standardRepresentation r hr hroot
          (QuaternionGroup.a
            (1 : ZMod (2 * n))) v ∈ S :=
    S.apply_mem_toSubmodule _ hv
  have hfirstSecond :
      firstVector ∈ S.toSubmodule ∧
        secondVector ∈ S.toSubmodule := by
    rcases hcoord with hx | hy
    · have hcomb :
          standardRepresentation r hr hroot
                (QuaternionGroup.a
                  (1 : ZMod (2 * n))) v -
              r⁻¹ • v ∈ S :=
        S.toSubmodule.sub_mem hcyclic
          (S.toSubmodule.smul_mem _ hv)
      have hcalc :
          standardRepresentation r hr hroot
                (QuaternionGroup.a
                  (1 : ZMod (2 * n))) v -
              r⁻¹ • v =
            ((r - r⁻¹) * v 0) • firstVector := by
        rw [standardRepresentation_apply_cyclicGenerator]
        funext i
        fin_cases i <;>
          simp [firstVector] <;> ring
      rw [hcalc] at hcomb
      have hc : (r - r⁻¹) * v 0 ≠ 0 :=
        mul_ne_zero (sub_ne_zero.mpr heigen) hx
      have hfirst : firstVector ∈ S.toSubmodule := by
        have hs :=
          S.toSubmodule.smul_mem
            (((r - r⁻¹) * v 0)⁻¹) hcomb
        simpa only [smul_smul,
          inv_mul_cancel₀ hc, one_smul] using hs
      have hreflection :=
        S.apply_mem_toSubmodule
          (QuaternionGroup.xa
            (0 : ZMod (2 * n))) hfirst
      have hsecond : secondVector ∈ S.toSubmodule := by
        rw [standardRepresentation_apply_reflectionGenerator]
          at hreflection
        simpa [firstVector, secondVector] using hreflection
      exact ⟨hfirst, hsecond⟩
    · have hcomb :
          standardRepresentation r hr hroot
                (QuaternionGroup.a
                  (1 : ZMod (2 * n))) v -
              r • v ∈ S :=
        S.toSubmodule.sub_mem hcyclic
          (S.toSubmodule.smul_mem _ hv)
      have hcalc :
          standardRepresentation r hr hroot
                (QuaternionGroup.a
                  (1 : ZMod (2 * n))) v -
              r • v =
            ((r⁻¹ - r) * v 1) • secondVector := by
        rw [standardRepresentation_apply_cyclicGenerator]
        funext i
        fin_cases i <;>
          simp [secondVector] <;> ring
      rw [hcalc] at hcomb
      have hc : (r⁻¹ - r) * v 1 ≠ 0 :=
        mul_ne_zero (sub_ne_zero.mpr heigen.symm) hy
      have hsecond : secondVector ∈ S.toSubmodule := by
        have hs :=
          S.toSubmodule.smul_mem
            (((r⁻¹ - r) * v 1)⁻¹) hcomb
        simpa only [smul_smul,
          inv_mul_cancel₀ hc, one_smul] using hs
      have hreflection :=
        S.apply_mem_toSubmodule
          (QuaternionGroup.xa
            (0 : ZMod (2 * n))) hsecond
      rw [standardRepresentation_apply_reflectionGenerator]
        at hreflection
      have hpow : r ^ n ≠ 0 := pow_ne_zero _ hr
      have hfirstScaled :
          (r ^ n) • firstVector ∈ S.toSubmodule := by
        simpa [firstVector, secondVector] using hreflection
      have hfirst : firstVector ∈ S.toSubmodule := by
        have hs :=
          S.toSubmodule.smul_mem (r ^ n)⁻¹ hfirstScaled
        simpa only [smul_smul,
          inv_mul_cancel₀ hpow, one_smul] using hs
      exact ⟨hfirst, hsecond⟩
  apply top_unique
  intro w _
  rw [vector_eq_coord_smul w]
  exact
    S.toSubmodule.add_mem
      (S.toSubmodule.smul_mem _ hfirstSecond.1)
      (S.toSubmodule.smul_mem _ hfirstSecond.2)

/-- Character value on a cyclic normal form, using a natural-number
representative of its residue-class exponent. -/
theorem standardCharacter_apply_a_natCast
    (r : ℂ) (hr : r ≠ 0)
    (hroot : r ^ (2 * n) = 1)
    (k : ℕ) :
    (standardRepresentation r hr hroot).character
        (QuaternionGroup.a (k : ZMod (2 * n))) =
      r ^ k + (r⁻¹) ^ k := by
  simp [Representation.character, Matrix.trace_fin_two,
    cyclicMatrix_pow]

/-- Character value on a reflection normal form, using a natural-number
representative of its residue-class exponent. -/
theorem standardCharacter_apply_xa_natCast
    (r : ℂ) (hr : r ≠ 0)
    (hroot : r ^ (2 * n) = 1)
    (k : ℕ) :
    (standardRepresentation r hr hroot).character
        (QuaternionGroup.xa (k : ZMod (2 * n))) = 0 := by
  simp [Representation.character, Matrix.trace_fin_two,
    cyclicMatrix_pow, reflectionMatrix, Matrix.mul_apply]

/-- Every element in the reflection coset has character value zero in the
standard two-dimensional representation. -/
theorem standardCharacter_apply_xa
    (r : ℂ) (hr : r ≠ 0)
    (hroot : r ^ (2 * n) = 1)
    (hn : n ≠ 0)
    (i : ZMod (2 * n)) :
    (standardRepresentation r hr hroot).character
        (QuaternionGroup.xa i) = 0 := by
  letI : NeZero (2 * n) := ⟨by omega⟩
  rw [← ZMod.natCast_zmod_val i]
  exact
    standardCharacter_apply_xa_natCast
      r hr hroot i.val

end QuaternionGroupRepresentation
end McKayConjecture
