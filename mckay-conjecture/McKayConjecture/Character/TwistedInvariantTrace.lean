/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.RepresentationTheory.Character

/-!
# Twisted traces on invariant subspaces

For a finite group representation, averaging is the projection onto the
invariant subspace.  If an endomorphism preserves that subspace, the
trace of its composite with the averaging projection is the trace of
its restriction to the invariant subspace.
-/

noncomputable section

open scoped BigOperators

namespace LinearMap

variable {R M : Type*} [Field R]
  [AddCommGroup M] [Module R M] [FiniteDimensional R M]

/-- Composing an endomorphism with a projection computes the trace of
the endomorphism restricted to the projected subspace. -/
theorem trace_comp_isProj_eq_trace_restrict
    {p : Submodule R M} {e T : Module.End R M}
    (he : IsProj p e)
    (hT : ∀ x ∈ p, T x ∈ p) :
    trace R M (T ∘ₗ e) =
      trace R p (T.restrict hT) := by
  rw [← he.subtype_comp_codRestrict]
  rw [← comp_assoc]
  rw [trace_comp_comm']
  congr 1
  ext x
  change e (T x) = T x
  exact he.map_id (T x) (hT x x.property)

/-- Restricting a finite-order endomorphism to an invariant subspace
again gives a finite-order endomorphism. -/
theorem isOfFinOrder_restrict
    {p : Submodule R M} (T : Module.End R M)
    (hT : ∀ x ∈ p, T x ∈ p)
    (hfinite : IsOfFinOrder T) :
    IsOfFinOrder (T.restrict hT) := by
  obtain ⟨n, hnpos, hn⟩ := hfinite.exists_pow_eq_one
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨n, hnpos, ?_⟩
  rw [Module.End.pow_restrict]
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (T ^ n) x = x
  rw [hn]
  rfl

/-- An exact power relation is preserved when an endomorphism is
restricted to an invariant subspace. -/
theorem pow_restrict_eq_one
    {p : Submodule R M} (T : Module.End R M)
    (hT : ∀ x ∈ p, T x ∈ p)
    {n : ℕ} (hpow : T ^ n = 1) :
    (T.restrict hT) ^ n = 1 := by
  rw [Module.End.pow_restrict]
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (T ^ n) x = x
  rw [hpow]
  rfl

variable {V W : Type*}
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- Postcomposition by an endomorphism, as a monoid homomorphism on
linear-hom spaces. -/
def postcompositionMonoidHom :
    Module.End ℂ W →*
      Module.End ℂ (V →ₗ[ℂ] W) where
  toFun A := A.compRight ℂ
  map_one' := by
    apply LinearMap.ext
    intro f
    ext x
    rfl
  map_mul' A B := by
    apply LinearMap.ext
    intro f
    ext x
    rfl

@[simp]
theorem postcompositionMonoidHom_apply
    (A : Module.End ℂ W) (f : V →ₗ[ℂ] W) :
    postcompositionMonoidHom (V := V) (W := W) A f =
      A ∘ₗ f :=
  rfl

/-- Finite order is preserved by postcomposition on a linear-hom
space. -/
theorem isOfFinOrder_postcomposition
    (A : Module.End ℂ W) (hA : IsOfFinOrder A) :
    IsOfFinOrder
      (postcompositionMonoidHom (V := V) (W := W) A) :=
  MonoidHom.isOfFinOrder
    (postcompositionMonoidHom (V := V) (W := W)) hA

/-- An exact power relation is preserved by postcomposition on a
linear-hom space. -/
theorem postcompositionMonoidHom_pow_eq_one
    (A : Module.End ℂ W) {n : ℕ} (hpow : A ^ n = 1) :
    (postcompositionMonoidHom (V := V) (W := W) A) ^ n =
      1 := by
  rw [← map_pow, hpow, map_one]

/-- Naturality of `dualTensorHom` for simultaneous pre- and
postcomposition. -/
theorem dualTensorHom_comp_tensorMap
    (A : Module.End ℂ W) (B : Module.End ℂ V) :
    dualTensorHom ℂ V W ∘ₗ
        TensorProduct.map B.dualMap A =
      (A.compRight ℂ ∘ₗ B.lcomp ℂ W) ∘ₗ
        dualTensorHom ℂ V W := by
  rw [← LinearMap.lTensor_comp_rTensor]
  rw [← comp_assoc]
  rw [dualTensorHom_comp_lTensor]
  rw [comp_assoc]
  rw [dualTensorHom_comp_rTensor_dualMap]
  rw [← comp_assoc]

/-- Under `dualTensorHomEquiv`, a tensor product of endomorphisms
becomes simultaneous pre- and postcomposition. -/
theorem dualTensorHomEquiv_conj_tensorMap
    (A : Module.End ℂ W) (B : Module.End ℂ V) :
    (dualTensorHomEquiv ℂ V W).conj
        (TensorProduct.map B.dualMap A) =
        A.compRight ℂ ∘ₗ B.lcomp ℂ W := by
  rw [LinearEquiv.conj_apply]
  change
    dualTensorHom ℂ V W ∘ₗ
          TensorProduct.map B.dualMap A ∘ₗ
          (dualTensorHomEquiv ℂ V W).symm.toLinearMap =
      A.compRight ℂ ∘ₗ B.lcomp ℂ W
  rw [← comp_assoc, dualTensorHom_comp_tensorMap]
  apply LinearMap.ext
  intro f
  change
    (A.compRight ℂ ∘ₗ B.lcomp ℂ W)
        ((dualTensorHomEquiv ℂ V W)
          ((dualTensorHomEquiv ℂ V W).symm f)) =
      (A.compRight ℂ ∘ₗ B.lcomp ℂ W) f
  rw [(dualTensorHomEquiv ℂ V W).apply_symm_apply]

/-- The trace on a linear-hom space of simultaneous pre- and
postcomposition is the product of the two traces. -/
theorem trace_compRight_comp_lcomp
    (A : Module.End ℂ W) (B : Module.End ℂ V) :
    trace ℂ (V →ₗ[ℂ] W)
        (A.compRight ℂ ∘ₗ B.lcomp ℂ W) =
      trace ℂ W A * trace ℂ V B := by
  calc
    trace ℂ (V →ₗ[ℂ] W)
        (A.compRight ℂ ∘ₗ B.lcomp ℂ W) =
        trace ℂ (V →ₗ[ℂ] W)
          ((dualTensorHomEquiv ℂ V W).conj
            (TensorProduct.map B.dualMap A)) := by
              rw [dualTensorHomEquiv_conj_tensorMap]
    _ = trace ℂ
          (TensorProduct ℂ (Module.Dual ℂ V) W)
          (TensorProduct.map B.dualMap A) :=
      trace_conj'
        (R := ℂ)
        (M := TensorProduct ℂ (Module.Dual ℂ V) W)
        (N := V →ₗ[ℂ] W)
        (TensorProduct.map B.dualMap A)
        (dualTensorHomEquiv ℂ V W)
    _ = trace ℂ W A * trace ℂ V B := by
      rw [trace_tensorProduct', LinearMap.dualMap_def,
        trace_transpose']
      ring

end LinearMap

namespace Representation

variable {R G M : Type*} [Field R] [CharZero R]
  [Group G] [Fintype G]
  [AddCommGroup M] [Module R M] [FiniteDimensional R M]

/-- A group-equivariant endomorphism preserves the invariant
subspace. -/
theorem endomorphism_mapsTo_invariants
    (ρ : Representation R G M) (T : Module.End R M)
    (hcomm : ∀ g : G, T ∘ₗ ρ g = ρ g ∘ₗ T) :
    ∀ x ∈ ρ.invariants, T x ∈ ρ.invariants := by
  intro x hx g
  have h := LinearMap.congr_fun (hcomm g) x
  simpa [hx g] using h.symm

/-- The average of the twisted traces is the trace of the twisting
endomorphism on the invariant subspace. -/
theorem card_inv_mul_sum_trace_comp_eq_trace_restrict_invariants
    (ρ : Representation R G M) (T : Module.End R M)
    (hcomm : ∀ g : G, T ∘ₗ ρ g = ρ g ∘ₗ T) :
    (Nat.card G : R)⁻¹ *
        ∑ g : G, LinearMap.trace R M (T ∘ₗ ρ g) =
      LinearMap.trace R ρ.invariants
        (T.restrict
          (endomorphism_mapsTo_invariants ρ T hcomm)) := by
  letI : Invertible (Fintype.card G : R) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr Fintype.card_pos.ne')
  rw [← LinearMap.trace_comp_isProj_eq_trace_restrict
    (isProj_averageMap ρ)
    (endomorphism_mapsTo_invariants ρ T hcomm)]
  simp [averageMap, GroupAlgebra.average,
    Representation.asAlgebraHom_def, _root_.map_sum]
  let L : Module.End R M →ₗ[R] R :=
    (LinearMap.trace R M).comp
      (LinearMap.llcomp R M M M T)
  change
    (Fintype.card G : R)⁻¹ * ∑ g : G, L (ρ g) =
      L ((Fintype.card G : R)⁻¹ • ∑ g : G, ρ g)
  rw [map_smul, map_sum]
  simp [smul_eq_mul]

section Complex

variable {H V W : Type*} [Group H] [Fintype H]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- Postcomposition by an endomorphism commuting with the target
representation commutes with the induced action on a linear-hom
representation. -/
theorem postcomposition_commutes_linHom
    (ρV : Representation ℂ H V)
    (ρW : Representation ℂ H W)
    (U : Module.End ℂ W)
    (hU : ∀ g : H, U ∘ₗ ρW g = ρW g ∘ₗ U) :
    ∀ g : H,
      LinearMap.postcompositionMonoidHom
          (V := V) (W := W) U ∘ₗ
          linHom ρV ρW g =
        linHom ρV ρW g ∘ₗ
          LinearMap.postcompositionMonoidHom
            (V := V) (W := W) U := by
  intro g
  apply LinearMap.ext
  intro f
  ext x
  have h :=
    LinearMap.congr_fun (hU g)
      (f (ρV g⁻¹ x))
  exact h

/-- The endomorphism induced by a commuting operator on the
intertwiner space, realized as the invariant subspace of a linear-hom
representation. -/
def twistedIntertwinerEndomorphism
    (ρV : Representation ℂ H V)
    (ρW : Representation ℂ H W)
    (U : Module.End ℂ W)
    (hU : ∀ g : H, U ∘ₗ ρW g = ρW g ∘ₗ U) :
    Module.End ℂ ((linHom ρV ρW).invariants) :=
  let T :=
    LinearMap.postcompositionMonoidHom
      (V := V) (W := W) U
  T.restrict
    (endomorphism_mapsTo_invariants
      (linHom ρV ρW) T
      (postcomposition_commutes_linHom ρV ρW U hU))

/-- A finite-order commuting operator induces a finite-order operator
on the intertwiner space. -/
theorem twistedIntertwinerEndomorphism_isOfFinOrder
    (ρV : Representation ℂ H V)
    (ρW : Representation ℂ H W)
    (U : Module.End ℂ W)
    (hU : ∀ g : H, U ∘ₗ ρW g = ρW g ∘ₗ U)
    (hfinite : IsOfFinOrder U) :
    IsOfFinOrder
      (twistedIntertwinerEndomorphism ρV ρW U hU) := by
  unfold twistedIntertwinerEndomorphism
  apply LinearMap.isOfFinOrder_restrict
  exact
    LinearMap.isOfFinOrder_postcomposition
      (V := V) (W := W) U hfinite

/-- An exact power relation for the commuting target operator is inherited
by its action on the intertwiner space. -/
theorem twistedIntertwinerEndomorphism_pow_eq_one
    (ρV : Representation ℂ H V)
    (ρW : Representation ℂ H W)
    (U : Module.End ℂ W)
    (hU : ∀ g : H, U ∘ₗ ρW g = ρW g ∘ₗ U)
    {n : ℕ} (hpow : U ^ n = 1) :
    (twistedIntertwinerEndomorphism ρV ρW U hU) ^ n =
      1 := by
  unfold twistedIntertwinerEndomorphism
  apply LinearMap.pow_restrict_eq_one
  exact
    LinearMap.postcompositionMonoidHom_pow_eq_one
      (V := V) (W := W) U hpow

/-- A twisted character pairing is the trace of the twisting operator
on the corresponding intertwiner space. -/
theorem twistedCharacterPairing_eq_trace
    (ρV : Representation ℂ H V)
    (ρW : Representation ℂ H W)
    (U : Module.End ℂ W)
    (hU : ∀ g : H, U ∘ₗ ρW g = ρW g ∘ₗ U) :
    (Nat.card H : ℂ)⁻¹ *
        ∑ g : H,
          LinearMap.trace ℂ W (U ∘ₗ ρW g) *
            ρV.character g⁻¹ =
      LinearMap.trace ℂ ((linHom ρV ρW).invariants)
        (twistedIntertwinerEndomorphism ρV ρW U hU) := by
  let T :=
    LinearMap.postcompositionMonoidHom
      (V := V) (W := W) U
  have hcomm :
      ∀ g : H,
        T ∘ₗ linHom ρV ρW g =
          linHom ρV ρW g ∘ₗ T :=
    postcomposition_commutes_linHom ρV ρW U hU
  have havg :=
    card_inv_mul_sum_trace_comp_eq_trace_restrict_invariants
      (linHom ρV ρW) T hcomm
  have htrace (g : H) :
      LinearMap.trace ℂ (V →ₗ[ℂ] W)
          (T ∘ₗ linHom ρV ρW g) =
        LinearMap.trace ℂ W (U ∘ₗ ρW g) *
          ρV.character g⁻¹ := by
    have hop :
        T ∘ₗ linHom ρV ρW g =
          (U ∘ₗ ρW g).compRight ℂ ∘ₗ
            (ρV g⁻¹).lcomp ℂ W := by
      apply LinearMap.ext
      intro f
      ext x
      rfl
    rw [hop, LinearMap.trace_compRight_comp_lcomp]
    rfl
  simp_rw [htrace] at havg
  simpa [twistedIntertwinerEndomorphism, T] using havg

end Complex

end Representation
