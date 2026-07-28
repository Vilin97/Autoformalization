/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Central.TensorProduct
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Simplicity descends from a tensor product over a field

If `B ⊗[k] C` is simple and both factors are nonzero algebras over a
field, then each factor is simple.  For a proper two-sided ideal `I`
of `B`, tensor the quotient map `B → B/I` with the identity of `C`.
The codomain is nonzero, so simplicity makes this tensor map
injective.  Every `x ∈ I` maps `x ⊗ 1` to zero; injectivity of both
the tensor map and the left-factor inclusion forces `x = 0`.
-/

noncomputable section

open scoped TensorProduct

namespace Representation

variable (k B C : Type)
variable [Field k]
variable [Ring B] [Algebra k B] [Nontrivial B]
variable [Ring C] [Algebra k C] [Nontrivial C]

/-- A nonzero left factor of a simple tensor-product algebra over a
field is simple. -/
theorem isSimpleRing_left_of_tensorProduct
    [IsSimpleRing (B ⊗[k] C)] :
    IsSimpleRing B := by
  apply IsSimpleRing.of_eq_bot_or_eq_top
  intro I
  by_cases htop : I = ⊤
  · exact Or.inr htop
  · left
    apply SetLike.ext
    intro x
    constructor
    · intro hx
      let J : Ideal B :=
        TwoSidedIdeal.asIdeal I
      have hJ : J ≠ ⊤ := by
        intro h
        apply htop
        apply SetLike.ext
        intro y
        have hy : y ∈ J := by
          rw [h]
          trivial
        simpa [J] using hy
      let Q :=
        B ⧸ J
      letI : Nontrivial Q :=
        Ideal.Quotient.nontrivial_iff.mpr hJ
      let q : B →ₐ[k] Q :=
        Ideal.Quotient.mkₐ k J
      let f : B ⊗[k] C →ₐ[k] Q ⊗[k] C :=
        Algebra.TensorProduct.map q (AlgHom.id k C)
      letI : Nontrivial (Q ⊗[k] C) :=
        Function.Injective.nontrivial
          (Algebra.TensorProduct.includeLeft_injective
            (R := k) (S := k) (A := Q) (B := C)
            (FaithfulSMul.algebraMap_injective k C))
      have hf : Function.Injective f :=
        RingHom.injective f.toRingHom
      have hmap :
          f (x ⊗ₜ[k] (1 : C)) = 0 := by
        change
          (Ideal.Quotient.mk J x) ⊗ₜ[k] (1 : C) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
        simp
      have htensor :
          x ⊗ₜ[k] (1 : C) = 0 := by
        apply hf
        simpa using hmap
      have hinclude :
          Function.Injective
            (Algebra.TensorProduct.includeLeft :
              B →ₐ[k] B ⊗[k] C) :=
        Algebra.TensorProduct.includeLeft_injective
          (FaithfulSMul.algebraMap_injective k C)
      have hx0 : x = 0 := by
        apply hinclude
        simpa using htensor
      simp [hx0]
    · intro hx
      change x = 0 at hx
      rw [hx]
      exact I.zero_mem

/-- A nonzero right factor of a simple tensor-product algebra over a
field is simple. -/
theorem isSimpleRing_right_of_tensorProduct
    [IsSimpleRing (B ⊗[k] C)] :
    IsSimpleRing C := by
  letI : IsSimpleRing (C ⊗[k] B) :=
    IsSimpleRing.of_ringEquiv
      (Algebra.TensorProduct.comm k B C).toRingEquiv
      (inferInstance : IsSimpleRing (B ⊗[k] C))
  exact isSimpleRing_left_of_tensorProduct k C B

end Representation
