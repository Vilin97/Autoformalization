/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Finite-dimensional indecomposable representations

This file packages the direct-sum definition of indecomposability for
representations and proves its standard Fitting-theoretic consequence:
every equivariant endomorphism of a finite-dimensional indecomposable
representation is either a unit or nilpotent.  Consequently its
endomorphism ring is local.

These results provide the local-endomorphism-ring input to the
Krull--Schmidt argument used for finite permutation modules.
-/

noncomputable section

namespace Representation

variable {k G V : Type*}
variable [Field k] [Monoid G]
variable [AddCommGroup V] [Module k V]

/-- A representation is directly indecomposable if its underlying
module is nonzero and it has no decomposition into two nonzero
subrepresentations. -/
def IsDirectSumIndecomposable (ρ : Representation k G V) : Prop :=
  Nontrivial V ∧
    ∀ U W : Subrepresentation ρ,
      IsCompl U.toSubmodule W.toSubmodule → U = ⊥ ∨ W = ⊥

namespace IntertwiningMap

variable {ρ : Representation k G V}

/- Mathlib equips self-intertwining maps with a semiring structure and
all intertwining-map spaces with an additive-group structure, but it
does not currently bundle those compatible structures as a `Ring`. -/
instance instRingSelf : Ring (IntertwiningMap ρ ρ) :=
  { (inferInstance : Semiring (IntertwiningMap ρ ρ)) with
    __ := (inferInstance : AddCommGroup (IntertwiningMap ρ ρ)) }

@[simp]
theorem toLinearMap_pow (f : IntertwiningMap ρ ρ) (n : ℕ) :
    (f ^ n).toLinearMap = f.toLinearMap ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ, coe_mul, ih]

/-- An equivariant endomorphism is a unit precisely when its
underlying function is bijective. -/
theorem isUnit_iff_bijective (f : IntertwiningMap ρ ρ) :
    IsUnit f ↔ Function.Bijective f := by
  constructor
  · rintro ⟨u, rfl⟩
    refine Function.bijective_iff_has_inverse.mpr
      ⟨((↑u⁻¹ : IntertwiningMap ρ ρ) : V → V), ?_, ?_⟩
    · intro v
      simp only [← mul_apply, Units.inv_mul, coe_one, id_eq]
    · intro v
      simp only [← mul_apply, Units.mul_inv, coe_one, id_eq]
  · intro hf
    let e : ρ.Equiv ρ := f.ofBijective hf
    refine ⟨⟨f, e.symm.toIntertwiningMap, ?_, ?_⟩, rfl⟩
    · apply IntertwiningMap.ext
      ext v
      change f (e.symm v) = v
      exact e.apply_symm_apply v
    · apply IntertwiningMap.ext
      ext v
      change e.symm (f v) = v
      exact e.symm_apply_apply v

/-- Fitting decomposition, expressed using the invariant kernel and
range subrepresentations of an equivariant endomorphism.  The exponent
can be chosen positive. -/
theorem exists_pos_isCompl_ker_range_pow
    [FiniteDimensional k V]
    (f : IntertwiningMap ρ ρ) :
    ∃ n : ℕ, 0 < n ∧
      IsCompl (f ^ n).ker.toSubmodule (f ^ n).range.toSubmodule := by
  have hfit :=
    f.toLinearMap.eventually_isCompl_ker_pow_range_pow
  rw [Filter.eventually_atTop] at hfit
  obtain ⟨N, hN⟩ := hfit
  refine ⟨N + 1, Nat.zero_lt_succ N, ?_⟩
  simpa only [ker_toSubmodule, range_toSubmodule, toLinearMap_pow] using
    hN (N + 1) (Nat.le_succ N)

/-- Every equivariant endomorphism of a finite-dimensional directly
indecomposable representation is either invertible or nilpotent. -/
theorem isUnit_or_isNilpotent_of_isDirectSumIndecomposable
    [FiniteDimensional k V]
    (hρ : ρ.IsDirectSumIndecomposable)
    (f : IntertwiningMap ρ ρ) :
    IsUnit f ∨ IsNilpotent f := by
  obtain ⟨n, hn_pos, hcompl⟩ :=
    f.exists_pos_isCompl_ker_range_pow
  rcases hρ.2 (f ^ n).ker (f ^ n).range hcompl with hker | hrange
  · left
    have hker_linear :
        LinearMap.ker (f ^ n).toLinearMap = ⊥ := by
      exact congrArg Subrepresentation.toSubmodule hker
    have hpow_bijective :
        Function.Bijective (f ^ n) := by
      exact (Module.End.isUnit_iff (f ^ n).toLinearMap).mp
        ((LinearMap.isUnit_iff_ker_eq_bot (f ^ n).toLinearMap).mpr
          hker_linear)
    have hpow_unit : IsUnit (f ^ n) :=
      ((f ^ n).isUnit_iff_bijective).mpr hpow_bijective
    exact (isUnit_pow_iff hn_pos.ne').mp hpow_unit
  · right
    refine ⟨n, ?_⟩
    apply IntertwiningMap.ext
    have hrange_linear :
        LinearMap.range (f ^ n).toLinearMap = ⊥ := by
      exact congrArg Subrepresentation.toSubmodule hrange
    exact LinearMap.range_eq_bot.mp hrange_linear

end IntertwiningMap

/-- The endomorphism ring of a finite-dimensional directly
indecomposable representation is local. -/
theorem isLocalRing_endomorphisms_of_isDirectSumIndecomposable
    {ρ : Representation k G V}
    [FiniteDimensional k V]
    (hρ : ρ.IsDirectSumIndecomposable) :
    IsLocalRing (IntertwiningMap ρ ρ) := by
  letI : Nontrivial V := hρ.1
  letI : Nontrivial (IntertwiningMap ρ ρ) :=
    ⟨⟨0, 1, by
      intro h
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      apply hv
      have happ := DFunLike.congr_fun h v
      simpa using happ.symm⟩⟩
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro f
  rcases f.isUnit_or_isNilpotent_of_isDirectSumIndecomposable hρ with
    hf | hf
  · exact Or.inl hf
  · exact Or.inr hf.isUnit_one_sub

end Representation
