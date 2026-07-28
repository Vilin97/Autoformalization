/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Analysis.Complex.IsIntegral
import McKayConjecture.Character.FiniteOrderTrace
import McKayConjecture.Character.Realization

/-!
# Integrality of traces of finite-order complex operators

Every characteristic root of a finite-order complex operator is a root
of unity, hence an algebraic integer.  Summing the characteristic roots
shows that the trace is an algebraic integer.  In particular, every
ordinary character value of a finite group is an algebraic integer.
-/

noncomputable section

open Matrix Module Polynomial

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A characteristic root of a finite-order complex matrix is an
algebraic integer. -/
theorem isIntegral_of_mem_roots_charpoly_of_isOfFinOrder
    (A : Matrix n n ℂ) (hA : IsOfFinOrder A) {z : ℂ}
    (hz : z ∈ A.charpoly.roots) :
    IsIntegral ℤ z := by
  have hroot : A.charpoly.IsRoot z :=
    (mem_roots A.charpoly_monic.ne_zero).mp hz
  have heigen :
      Module.End.HasEigenvalue (Matrix.toLin' A) z := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly,
      Matrix.charpoly_toLin']
    exact hroot
  have hfinite : IsOfFinOrder (Matrix.toLinAlgEquiv' A) :=
    MonoidHom.isOfFinOrder
      ((Matrix.toLinAlgEquiv' :
        Matrix n n ℂ ≃ₐ[ℂ] ((n → ℂ) →ₗ[ℂ] (n → ℂ))).toMonoidHom) hA
  obtain ⟨m, hmpos, hm⟩ := hfinite.exists_pow_eq_one
  obtain ⟨v, hv⟩ := heigen.exists_hasEigenvector
  have hzpow : z ^ m = 1 := by
    obtain ⟨i, hvi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hv.2 (funext hall)
    apply smul_left_injective ℂ hvi
    have htoLin :
        Matrix.toLinAlgEquiv' A = Matrix.toLin' A := rfl
    have hvector :
        z ^ m • v = (1 : ℂ) • v := by
      calc
        z ^ m • v = ((Matrix.toLin' A) ^ m) v :=
          (hv.pow_apply m).symm
        _ = v := by rw [← htoLin, hm]; rfl
        _ = 1 • v := (one_smul ℂ v).symm
    simpa only [Pi.smul_apply] using congrFun hvector i
  exact IsIntegral.of_pow hmpos (hzpow ▸ isIntegral_one)

/-- The trace of a finite-order complex matrix is an algebraic integer. -/
theorem isIntegral_trace_of_isOfFinOrder
    (A : Matrix n n ℂ) (hA : IsOfFinOrder A) :
    IsIntegral ℤ A.trace := by
  rw [Matrix.trace_eq_sum_roots_charpoly]
  exact IsIntegral.multiset_sum fun z hz ↦
    isIntegral_of_mem_roots_charpoly_of_isOfFinOrder A hA hz

end Matrix

namespace LinearMap

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V]

/-- The trace of a finite-order complex endomorphism is an algebraic
integer. -/
theorem isIntegral_trace_of_isOfFinOrder
    (f : Module.End ℂ V) (hfinite : IsOfFinOrder f) :
    IsIntegral ℤ (LinearMap.trace ℂ V f) := by
  let b := Module.Free.chooseBasis ℂ V
  let A := LinearMap.toMatrix b b f
  have hA : IsOfFinOrder A :=
    MonoidHom.isOfFinOrder
      ((LinearMap.toMatrixAlgEquiv b).toMonoidHom) hfinite
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  exact Matrix.isIntegral_trace_of_isOfFinOrder A hA

end LinearMap

namespace Representation

universe u v

variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Every value of a finite-dimensional complex representation of a
finite group is an algebraic integer. -/
theorem isIntegral_character
    (ρ : Representation ℂ G V) (g : G) :
    IsIntegral ℤ (ρ.character g) :=
  LinearMap.isIntegral_trace_of_isOfFinOrder
    (ρ g) (ρ.isOfFinOrder (isOfFinOrder_of_finite g))

end Representation

namespace FDRep

universe u

variable {G : Type u} [Group G] [Finite G]

/-- Every ordinary `FDRep` character value is an algebraic integer. -/
theorem isIntegral_character (V : FDRep ℂ G) (g : G) :
    IsIntegral ℤ (V.character g) :=
  Representation.isIntegral_character V.ρ g

end FDRep

namespace McKayConjecture.IrreducibleCharacter

universe u

variable {G : Type u} [Group G] [Finite G]

/-- Every irreducible-character value of a finite group is an algebraic
integer. -/
theorem isIntegral_value (χ : IrreducibleCharacter G) (g : G) :
    IsIntegral ℤ (χ.values g) := by
  simpa only [χ.realization_character] using
    FDRep.isIntegral_character χ.realization g

end McKayConjecture.IrreducibleCharacter
