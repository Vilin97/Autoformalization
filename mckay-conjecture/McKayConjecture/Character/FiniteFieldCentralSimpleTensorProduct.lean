/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.EndomorphismCentralSimple
import McKayConjecture.Character.EndomorphismTensorProduct
import McKayConjecture.Character.FiniteFieldCentralSimpleSplitting
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Tensor products of central simple algebras over finite fields

Over a finite field, two finite-dimensional central simple algebras
split as full endomorphism algebras.  The tensor product is therefore
again a full endomorphism algebra, using the canonical equivalence
`End(V) ⊗ End(W) ≃ End(V ⊗ W)`.
-/

noncomputable section

open scoped TensorProduct

namespace Representation

universe u

variable (k A D : Type u)
variable [Field k] [Finite k]
variable [Ring A] [Algebra k A]
variable [Ring D] [Algebra k D]

/-- A simultaneous splitting of the tensor product of two
finite-dimensional central simple algebras over a finite field. -/
theorem exists_algEquiv_tensorProduct_endomorphism_of_finiteField
    [Algebra.IsCentral k A] [IsSimpleRing A]
    [FiniteDimensional k A]
    [Algebra.IsCentral k D] [IsSimpleRing D]
    [FiniteDimensional k D] :
    ∃ (n m : ℕ) (_ : NeZero n) (_ : NeZero m),
      Nonempty
        ((A ⊗[k] D) ≃ₐ[k]
          Module.End k
            ((Fin n → k) ⊗[k] (Fin m → k))) := by
  obtain ⟨n, hn, ⟨eA⟩⟩ :=
    exists_algEquiv_endomorphism_of_finiteField k A
  obtain ⟨m, hm, ⟨eD⟩⟩ :=
    exists_algEquiv_endomorphism_of_finiteField k D
  exact
    ⟨n, m, hn, hm,
      ⟨(Algebra.TensorProduct.congr eA eD).trans
        endomorphismTensorProductAlgEquiv⟩⟩

/-- Tensor products of finite-dimensional central simple algebras
over a finite field are central. -/
theorem tensorProduct_isCentral_of_finiteField
    [Algebra.IsCentral k A] [IsSimpleRing A]
    [FiniteDimensional k A]
    [Algebra.IsCentral k D] [IsSimpleRing D]
    [FiniteDimensional k D] :
    Algebra.IsCentral k (A ⊗[k] D) := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ :=
    exists_algEquiv_tensorProduct_endomorphism_of_finiteField
      k A D
  letI : NeZero n := hn
  letI : NeZero m := hm
  exact
    Algebra.IsCentral.of_algEquiv k
      (Module.End k
        ((Fin n → k) ⊗[k] (Fin m → k)))
      (A ⊗[k] D) e.symm

/-- Tensor products of finite-dimensional central simple algebras
over a finite field are simple. -/
theorem tensorProduct_isSimpleRing_of_finiteField
    [Algebra.IsCentral k A] [IsSimpleRing A]
    [FiniteDimensional k A]
    [Algebra.IsCentral k D] [IsSimpleRing D]
    [FiniteDimensional k D] :
    IsSimpleRing (A ⊗[k] D) := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ :=
    exists_algEquiv_tensorProduct_endomorphism_of_finiteField
      k A D
  letI : NeZero n := hn
  letI : NeZero m := hm
  letI : Nonempty (Fin n) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  letI : Nonempty (Fin m) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩⟩
  letI :
      Nontrivial
        ((Fin n → k) ⊗[k] (Fin m → k)) :=
    Module.nontrivial_of_finrank_pos (R := k) <| by
      rw [Module.finrank_tensorProduct]
      exact Nat.mul_pos Module.finrank_pos Module.finrank_pos
  have hend :
      IsSimpleRing
        (Module.End k
          ((Fin n → k) ⊗[k] (Fin m → k))) :=
    endomorphism_isSimpleRing
  exact
    IsSimpleRing.of_ringEquiv e.symm.toRingEquiv hend

end Representation
