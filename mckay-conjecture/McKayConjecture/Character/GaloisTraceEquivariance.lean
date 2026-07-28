/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.FieldTheory.PrimitiveElement
import McKayConjecture.Character.ClassFunctionPairing
import McKayConjecture.Character.FiniteOrderTraceIntegrality

/-!
# Galois equivariance of finite-order traces and class-function pairings

Entrywise application of an automorphism of `ℂ` commutes with matrix
trace and preserves finite order.  The same automorphism commutes with
the normalized class-function pairing when it is applied to both
arguments.

We also isolate the elementary fixed-embedding criterion for
rationality: an algebraic complex number is rational if every
`ℚ`-embedding of the field it generates sends the generator to the
original number.  This is the field-theoretic endpoint used after a
Galois-orbit or Artin-induction argument.
-/

noncomputable section

open IntermediateField Matrix Module
open scoped BigOperators

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Entrywise application of a complex field automorphism commutes
with matrix trace. -/
theorem trace_map_ringEquiv
    (σ : ℂ ≃+* ℂ) (A : Matrix n n ℂ) :
    (A.map σ).trace = σ A.trace :=
  (AddMonoidHom.map_trace σ.toAddMonoidHom A).symm

/-- Entrywise application of a complex field automorphism preserves
finite order of a square matrix. -/
theorem isOfFinOrder_map_ringEquiv
    (σ : ℂ ≃+* ℂ) (A : Matrix n n ℂ)
    (hA : IsOfFinOrder A) :
    IsOfFinOrder (A.map σ) := by
  convert
    MonoidHom.isOfFinOrder
      σ.toRingHom.mapMatrix.toMonoidHom hA using 1
  ext i j
  rfl

end Matrix

namespace LinearMap

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A matrix model for the Galois conjugate of an endomorphism.  It is
basis-dependent as an operator, but its trace is not. -/
def galoisConjugateMatrix
    (σ : ℂ ≃+* ℂ) (b : Basis ι ℂ V)
    (f : Module.End ℂ V) :
    Matrix ι ι ℂ :=
  (LinearMap.toMatrix b b f).map σ

/-- The trace of the Galois-conjugate matrix is the Galois conjugate
of the original trace. -/
theorem trace_galoisConjugateMatrix
    (σ : ℂ ≃+* ℂ) (b : Basis ι ℂ V)
    (f : Module.End ℂ V) :
    (galoisConjugateMatrix σ b f).trace =
      σ (LinearMap.trace ℂ V f) := by
  rw [galoisConjugateMatrix,
    Matrix.trace_map_ringEquiv,
    LinearMap.trace_eq_matrix_trace ℂ b]

/-- A finite-order endomorphism has a finite-order Galois-conjugate
matrix in every basis. -/
theorem galoisConjugateMatrix_isOfFinOrder
    (σ : ℂ ≃+* ℂ) (b : Basis ι ℂ V)
    (f : Module.End ℂ V) (hf : IsOfFinOrder f) :
    IsOfFinOrder (galoisConjugateMatrix σ b f) := by
  apply Matrix.isOfFinOrder_map_ringEquiv
  exact
    MonoidHom.isOfFinOrder
      (LinearMap.toMatrixAlgEquiv b).toMonoidHom hf

/-- Every Galois conjugate of the trace of a finite-order complex
endomorphism is again an algebraic integer. -/
theorem isIntegral_map_trace_of_isOfFinOrder
    (σ : ℂ ≃+* ℂ) (f : Module.End ℂ V)
    (hf : IsOfFinOrder f) :
    IsIntegral ℤ (σ (LinearMap.trace ℂ V f)) := by
  let b := Module.Free.chooseBasis ℂ V
  rw [← trace_galoisConjugateMatrix σ b f]
  exact
    Matrix.isIntegral_trace_of_isOfFinOrder
      (galoisConjugateMatrix σ b f)
      (galoisConjugateMatrix_isOfFinOrder σ b f hf)

end LinearMap

namespace McKayConjecture
namespace ClassFunction

variable {G : Type*} [Group G]

/-- Apply a complex field automorphism pointwise to a class function. -/
def ringConjugate
    (σ : ℂ ≃+* ℂ) (f : ClassFunction G) :
    ClassFunction G :=
  ⟨fun g ↦ σ (f g), fun g h ↦ by
    exact congrArg σ (f.property g h)⟩

@[simp]
theorem ringConjugate_apply
    (σ : ℂ ≃+* ℂ) (f : ClassFunction G) (g : G) :
    ringConjugate σ f g = σ (f g) :=
  rfl

/-- Simultaneous Galois conjugation of both arguments commutes with
the normalized class-function pairing. -/
theorem ringConjugate_normalizedPairing
    [Finite G] (σ : ℂ ≃+* ℂ)
    (f k : ClassFunction G) :
    normalizedPairing (ringConjugate σ f) (ringConjugate σ k) =
      σ (normalizedPairing f k) := by
  letI : Fintype G := Fintype.ofFinite G
  change
    (Nat.card G : ℂ)⁻¹ *
        ∑ g : G, σ (f g) * σ (k g⁻¹) =
      σ ((Nat.card G : ℂ)⁻¹ *
        ∑ g : G, f g * k g⁻¹)
  simp only [map_mul, map_sum, map_inv₀, map_natCast]

/-- An integer algebraic complex number is algebraic over `ℚ`, hence
integral over `ℚ`. -/
theorem isIntegral_rat_of_isIntegral_int
    {z : ℂ} (hz : IsIntegral ℤ z) :
    IsIntegral ℚ z :=
  (hz.isAlgebraic.extendScalars Int.cast_injective).isIntegral

/-- An algebraic complex number fixed at the generator by every
`ℚ`-embedding of its generated field into `ℂ` is rational. -/
theorem exists_rat_eq_of_forall_adjoin_algHom_gen_eq
    {z : ℂ} (hz : IsIntegral ℚ z)
    (hfix :
      ∀ σ : ((ℚ⟮z⟯) →ₐ[ℚ] ℂ),
        σ (AdjoinSimple.gen ℚ z) = z) :
    ∃ q : ℚ, z = (q : ℂ) := by
  letI : FiniteDimensional ℚ (ℚ⟮z⟯) :=
    IntermediateField.adjoin.finiteDimensional hz
  have hsubsingleton :
      Subsingleton ((ℚ⟮z⟯) →ₐ[ℚ] ℂ) := by
    constructor
    intro σ τ
    apply IntermediateField.adjoin_algHom_ext ℚ
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact (hfix σ).trans (hfix τ).symm
  letI : Subsingleton ((ℚ⟮z⟯) →ₐ[ℚ] ℂ) :=
    hsubsingleton
  have hcard_le :
      Fintype.card ((ℚ⟮z⟯) →ₐ[ℚ] ℂ) ≤ 1 :=
    Fintype.card_le_one_iff_subsingleton.mpr inferInstance
  have hcard_pos :
      0 < Fintype.card ((ℚ⟮z⟯) →ₐ[ℚ] ℂ) :=
    Fintype.card_pos_iff.mpr
      ⟨(ℚ⟮z⟯).val⟩
  have hcard :
      Fintype.card ((ℚ⟮z⟯) →ₐ[ℚ] ℂ) = 1 :=
    Nat.le_antisymm hcard_le hcard_pos
  have hfinrank :
      Module.finrank ℚ (ℚ⟮z⟯) = 1 := by
    rw [← AlgHom.card ℚ (ℚ⟮z⟯) ℂ]
    exact hcard
  have hzbot :
      z ∈ (⊥ : IntermediateField ℚ ℂ) :=
    IntermediateField.finrank_adjoin_simple_eq_one_iff.mp
      hfinrank
  obtain ⟨q, hq⟩ :=
    IntermediateField.mem_bot.mp hzbot
  exact ⟨q, hq.symm⟩

end ClassFunction
end McKayConjecture
