/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import McKayConjecture.Character.CyclicExtensionIntertwiner
import McKayConjecture.Character.CliffordRestriction
import McKayConjecture.Character.Construction
import McKayConjecture.Character.Determination
import McKayConjecture.Character.Extension
import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.RepresentationTheory.Rep.Iso

/-!
# Construction of extensions across cyclic quotients

This is the second half of the representation-level cyclic quotient extension
theorem, ported from Yawara Ishida's
`OddOrder.GroupTheory.RepresentationTheory.CyclicExtension`.

For a normalized conjugation unit `P` and a generator `gH` of `K/H`, the
extension is defined by

`ρ̃(g^i h) = P^i ρ(h)`.

The normalization theorem in `CyclicExtensionIntertwiner.lean` proves that
this is independent of the chosen exponent.  This file proves
multiplicativity, literal restriction to the original representation, and
irreducibility.  It then packages the complex specialization as an
`IrreducibleCharacter.IsExtensionAlong`.

## Main results

* `cyclicExtension` is the explicit extended representation.
* `exists_extension_of_nonempty_equiv_conjRep` is
  Bender--Glauberman Proposition 2.2(b).
* `IrreducibleCharacter.exists_extension_of_cyclic_quotient` packages the
  complex invariant-character specialization.

## References

* Bender--Glauberman, *Local Analysis for the Odd Order Theorem*,
  Proposition 2.2(b).
-/

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra

namespace McKayConjecture.RepresentationTheory

variable {K : Type*} [Group K] {H : Subgroup K} [hH : H.Normal]
variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

section Extension

variable {ρ : Representation F H V} {g : K}
  {P : (Module.End F V)ˣ}

/-- Move `ρ(h)` past `P^j` from the left. -/
theorem conjugation_unit_comm_zpow
    (hP : ∀ h : H, P * ρ.asGroupHom h =
      ρ.asGroupHom
        (ClassFunction.conjByMulEquiv (K := K) (H := H) g h) * P)
    (j : ℤ) (h : H) :
    ρ.asGroupHom h * P ^ j =
      P ^ j * ρ.asGroupHom
        (ClassFunction.conjByMulEquiv
          (K := K) (H := H) (g ^ j)⁻¹ h) := by
  have hiter := conjugation_unit_zpow_comm hP j
    (ClassFunction.conjByMulEquiv
      (K := K) (H := H) (g ^ j)⁻¹ h)
  rw [ClassFunction.conjByMulEquiv_mul, mul_inv_cancel,
    ClassFunction.conjByMulEquiv_one] at hiter
  exact hiter.symm

omit hH in
/-- The expression `P^i ρ(g⁻ⁱk)` does not depend on the valid exponent
`i`. -/
theorem cyclicExtension_zpow_mul_eq
    (hPt : ∀ (t : ℤ) (ht : g ^ t ∈ H),
      P ^ t = ρ.asGroupHom ⟨g ^ t, ht⟩)
    {k : K} {i j : ℤ}
    (hi : (g ^ i)⁻¹ * k ∈ H) (hj : (g ^ j)⁻¹ * k ∈ H) :
    P ^ i * ρ.asGroupHom ⟨(g ^ i)⁻¹ * k, hi⟩ =
      P ^ j * ρ.asGroupHom ⟨(g ^ j)⁻¹ * k, hj⟩ := by
  have hij : g ^ (i - j) ∈ H := by
    have heq :
        ((g ^ j)⁻¹ * k) * ((g ^ i)⁻¹ * k)⁻¹ =
          g ^ (i - j) := by
      group
    exact heq ▸ mul_mem hj (inv_mem hi)
  have hsplit :
      (⟨g ^ (i - j), hij⟩ : H) *
          ⟨(g ^ i)⁻¹ * k, hi⟩ =
        ⟨(g ^ j)⁻¹ * k, hj⟩ :=
    Subtype.ext (by
      change g ^ (i - j) * ((g ^ i)⁻¹ * k) =
        (g ^ j)⁻¹ * k
      group)
  have hpow : P ^ i = P ^ j * P ^ (i - j) := by
    rw [← zpow_add]
    congr 1
    omega
  calc
    P ^ i * ρ.asGroupHom ⟨(g ^ i)⁻¹ * k, hi⟩ =
        P ^ j *
          (P ^ (i - j) *
            ρ.asGroupHom ⟨(g ^ i)⁻¹ * k, hi⟩) := by
          rw [hpow, mul_assoc]
    _ = P ^ j *
        (ρ.asGroupHom ⟨g ^ (i - j), hij⟩ *
          ρ.asGroupHom ⟨(g ^ i)⁻¹ * k, hi⟩) := by
            rw [hPt (i - j) hij]
    _ = P ^ j * ρ.asGroupHom
        ⟨(g ^ j)⁻¹ * k, hj⟩ := by
          rw [← map_mul, hsplit]

variable (ρ g P) in
/-- The unit-valued extension function, before proving multiplicativity. -/
def cyclicExtensionUnit
    (hgen : ∀ k : K, ∃ i : ℤ, (g ^ i)⁻¹ * k ∈ H)
    (k : K) : (Module.End F V)ˣ :=
  P ^ (hgen k).choose *
    ρ.asGroupHom
      ⟨(g ^ (hgen k).choose)⁻¹ * k, (hgen k).choose_spec⟩

omit hH in
/-- Evaluate `cyclicExtensionUnit` using any valid exponent. -/
theorem cyclicExtensionUnit_eq
    (hPt : ∀ (t : ℤ) (ht : g ^ t ∈ H),
      P ^ t = ρ.asGroupHom ⟨g ^ t, ht⟩)
    (hgen : ∀ k : K, ∃ i : ℤ, (g ^ i)⁻¹ * k ∈ H)
    {k : K} (i : ℤ) (hi : (g ^ i)⁻¹ * k ∈ H) :
    cyclicExtensionUnit ρ g P hgen k =
      P ^ i * ρ.asGroupHom ⟨(g ^ i)⁻¹ * k, hi⟩ :=
  cyclicExtension_zpow_mul_eq hPt (hgen k).choose_spec hi

/-- The unit-valued extension function is multiplicative. -/
theorem cyclicExtensionUnit_mul
    (hP : ∀ h : H, P * ρ.asGroupHom h =
      ρ.asGroupHom
        (ClassFunction.conjByMulEquiv (K := K) (H := H) g h) * P)
    (hPt : ∀ (t : ℤ) (ht : g ^ t ∈ H),
      P ^ t = ρ.asGroupHom ⟨g ^ t, ht⟩)
    (hgen : ∀ k : K, ∃ i : ℤ, (g ^ i)⁻¹ * k ∈ H)
    (k₁ k₂ : K) :
    cyclicExtensionUnit ρ g P hgen (k₁ * k₂) =
      cyclicExtensionUnit ρ g P hgen k₁ *
        cyclicExtensionUnit ρ g P hgen k₂ := by
  obtain ⟨i₁, hi₁⟩ := hgen k₁
  obtain ⟨i₂, hi₂⟩ := hgen k₂
  have hmem : (g ^ (i₁ + i₂))⁻¹ * (k₁ * k₂) ∈ H := by
    have hconj :
        (g ^ i₂)⁻¹ * ((g ^ i₁)⁻¹ * k₁) *
            ((g ^ i₂)⁻¹)⁻¹ ∈ H :=
      hH.conj_mem _ hi₁ (g ^ i₂)⁻¹
    have hmul := mul_mem hconj hi₂
    have heq :
        ((g ^ i₂)⁻¹ * ((g ^ i₁)⁻¹ * k₁) *
            ((g ^ i₂)⁻¹)⁻¹) *
            ((g ^ i₂)⁻¹ * k₂) =
          (g ^ (i₁ + i₂))⁻¹ * (k₁ * k₂) := by
      group
    exact heq ▸ hmul
  rw [cyclicExtensionUnit_eq hPt hgen (i₁ + i₂) hmem,
    cyclicExtensionUnit_eq hPt hgen i₁ hi₁,
    cyclicExtensionUnit_eq hPt hgen i₂ hi₂]
  have hcomm := conjugation_unit_comm_zpow hP i₂
    (⟨(g ^ i₁)⁻¹ * k₁, hi₁⟩ : H)
  have hfuse :
      ClassFunction.conjByMulEquiv
          (K := K) (H := H) (g ^ i₂)⁻¹
          (⟨(g ^ i₁)⁻¹ * k₁, hi₁⟩ : H) *
          (⟨(g ^ i₂)⁻¹ * k₂, hi₂⟩ : H) =
        ⟨(g ^ (i₁ + i₂))⁻¹ * (k₁ * k₂), hmem⟩ :=
    Subtype.ext (by
      simp only [Subgroup.coe_mul,
        ClassFunction.conjByMulEquiv_apply]
      group)
  calc
    P ^ (i₁ + i₂) *
          ρ.asGroupHom
            ⟨(g ^ (i₁ + i₂))⁻¹ * (k₁ * k₂), hmem⟩ =
        P ^ i₁ * P ^ i₂ *
          ρ.asGroupHom
            (ClassFunction.conjByMulEquiv
                (K := K) (H := H) (g ^ i₂)⁻¹
                (⟨(g ^ i₁)⁻¹ * k₁, hi₁⟩ : H) *
              (⟨(g ^ i₂)⁻¹ * k₂, hi₂⟩ : H)) := by
          rw [hfuse, ← zpow_add]
    _ = P ^ i₁ *
          (ρ.asGroupHom
              (⟨(g ^ i₁)⁻¹ * k₁, hi₁⟩ : H) * P ^ i₂) *
          ρ.asGroupHom
            (⟨(g ^ i₂)⁻¹ * k₂, hi₂⟩ : H) := by
          rw [hcomm, map_mul]
          group
    _ = P ^ i₁ *
          ρ.asGroupHom ⟨(g ^ i₁)⁻¹ * k₁, hi₁⟩ *
          (P ^ i₂ *
            ρ.asGroupHom ⟨(g ^ i₂)⁻¹ * k₂, hi₂⟩) := by
          group

variable (ρ g P) in
/-- The representation extending `ρ` from `H` to `K`. -/
def cyclicExtension
    (hP : ∀ h : H, P * ρ.asGroupHom h =
      ρ.asGroupHom
        (ClassFunction.conjByMulEquiv (K := K) (H := H) g h) * P)
    (hPt : ∀ (t : ℤ) (ht : g ^ t ∈ H),
      P ^ t = ρ.asGroupHom ⟨g ^ t, ht⟩)
    (hgen : ∀ k : K, ∃ i : ℤ, (g ^ i)⁻¹ * k ∈ H) :
    Representation F K V :=
  (Units.coeHom (Module.End F V)).comp
    { toFun := cyclicExtensionUnit ρ g P hgen
      map_one' := by
        have h0 : (g ^ (0 : ℤ))⁻¹ * (1 : K) ∈ H := by simp
        rw [cyclicExtensionUnit_eq hPt hgen 0 h0]
        have hone :
            (⟨(g ^ (0 : ℤ))⁻¹ * (1 : K), h0⟩ : H) = 1 :=
          Subtype.ext (by simp)
        rw [hone, map_one, zpow_zero, one_mul]
      map_mul' := cyclicExtensionUnit_mul hP hPt hgen }

/-- The cyclic extension restricts to `ρ` on the nose. -/
theorem cyclicExtension_comp_subtype
    (hP : ∀ h : H, P * ρ.asGroupHom h =
      ρ.asGroupHom
        (ClassFunction.conjByMulEquiv (K := K) (H := H) g h) * P)
    (hPt : ∀ (t : ℤ) (ht : g ^ t ∈ H),
      P ^ t = ρ.asGroupHom ⟨g ^ t, ht⟩)
    (hgen : ∀ k : K, ∃ i : ℤ, (g ^ i)⁻¹ * k ∈ H) :
    (cyclicExtension ρ g P hP hPt hgen).comp H.subtype = ρ := by
  refine MonoidHom.ext fun h => ?_
  have h0 : (g ^ (0 : ℤ))⁻¹ * (h : K) ∈ H := by simp
  calc
    (cyclicExtension ρ g P hP hPt hgen).comp H.subtype h =
        ↑(cyclicExtensionUnit ρ g P hgen (h : K)) := rfl
    _ = ↑(P ^ (0 : ℤ) *
        ρ.asGroupHom
          ⟨(g ^ (0 : ℤ))⁻¹ * (h : K), h0⟩) := by
            rw [cyclicExtensionUnit_eq hPt hgen 0 h0]
    _ = ρ h := by
      have hcast :
          (⟨(g ^ (0 : ℤ))⁻¹ * (h : K), h0⟩ : H) = h :=
        Subtype.ext (by simp)
      rw [hcast, zpow_zero, one_mul,
        Representation.asGroupHom_apply]

/-- The cyclic extension of an irreducible representation remains
irreducible. -/
theorem isIrreducible_cyclicExtension
    [Representation.IsIrreducible ρ]
    (hP : ∀ h : H, P * ρ.asGroupHom h =
      ρ.asGroupHom
        (ClassFunction.conjByMulEquiv (K := K) (H := H) g h) * P)
    (hPt : ∀ (t : ℤ) (ht : g ^ t ∈ H),
      P ^ t = ρ.asGroupHom ⟨g ^ t, ht⟩)
    (hgen : ∀ k : K, ∃ i : ℤ, (g ^ i)⁻¹ * k ∈ H) :
    Representation.IsIrreducible
      (cyclicExtension ρ g P hP hPt hgen) :=
  Representation.isIrreducible_of_isIrreducible_comp
    (f := H.subtype) _
    ((cyclicExtension_comp_subtype hP hPt hgen).symm ▸
      ‹Representation.IsIrreducible ρ›)

end Extension

/-! ### Cyclic generation of the quotient -/

/-- If `gH` generates `K/H`, every element of `K` is in a coset `g^iH`. -/
theorem forall_exists_zpow_inv_mul_mem {g : K}
    (htop : Subgroup.zpowers (QuotientGroup.mk' H g) = ⊤) :
    ∀ k : K, ∃ i : ℤ, (g ^ i)⁻¹ * k ∈ H := by
  intro k
  have hk : QuotientGroup.mk' H k ∈
      Subgroup.zpowers (QuotientGroup.mk' H g) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hk
  refine ⟨i, ?_⟩
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply H,
    map_mul, map_inv, map_zpow, hi, inv_mul_cancel]

/-! ### Bender--Glauberman Proposition 2.2(b) -/

/-- An invariant irreducible representation extends across a cyclic
quotient, with literal equality on restriction. -/
theorem exists_extension_of_nonempty_equiv_conjRep
    [Finite K] [IsAlgClosed F] [FiniteDimensional F V]
    (ρ : Representation F H V) [Representation.IsIrreducible ρ]
    {g : K}
    (hgen : ∀ k : K, ∃ i : ℤ, (g ^ i)⁻¹ * k ∈ H)
    (hequiv : Nonempty (ρ.Equiv (conjRep ρ g))) :
    ∃ σ : Representation F K V,
      σ.comp H.subtype = ρ ∧
        Representation.IsIrreducible σ := by
  obtain ⟨P, hP, hPt⟩ :=
    exists_normalized_conjugation_unit_of_nonempty_equiv ρ g hequiv
  exact
    ⟨cyclicExtension ρ g P hP hPt hgen,
      cyclicExtension_comp_subtype hP hPt hgen,
      isIrreducible_cyclicExtension hP hPt hgen⟩

/-- Idiomatic quotient-generation form of the representation extension
theorem. -/
theorem exists_extension_of_cyclic_quotient
    [Finite K] [IsAlgClosed F] [FiniteDimensional F V]
    (ρ : Representation F H V) [Representation.IsIrreducible ρ]
    {g : K}
    (htop : Subgroup.zpowers (QuotientGroup.mk' H g) = ⊤)
    (hequiv : Nonempty (ρ.Equiv (conjRep ρ g))) :
    ∃ σ : Representation F K V,
      σ.comp H.subtype = ρ ∧
        Representation.IsIrreducible σ :=
  exists_extension_of_nonempty_equiv_conjRep ρ
    (forall_exists_zpow_inv_mul_mem htop) hequiv

end McKayConjecture.RepresentationTheory

namespace McKayConjecture

/-! ### Packaging as an irreducible complex character -/

namespace RepresentationTheory

universe u

variable {G : Type u} [Group G]

/-- An irreducible finite-dimensional representation gives a categorically
simple `FDRep`. -/
theorem simple_fdRep_of_isIrreducible
    {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ] :
    Simple (FDRep.of ρ) := by
  let R : Rep ℂ G :=
    (forget₂ (FDRep ℂ G) (Rep ℂ G)).obj (FDRep.of ρ)
  letI : IsSimpleModule ℂ[G] ρ.asModule := inferInstance
  letI : Simple (ModuleCat.of ℂ[G] ρ.asModule) := inferInstance
  letI : Simple
      ((Rep.equivalenceModuleMonoidAlgebra (k := ℂ) (G := G)).functor.obj R) := by
    change Simple (ModuleCat.of ℂ[G] ρ.asModule)
    infer_instance
  letI : Simple R :=
    Functor.simple_of_simple_obj
      (Rep.equivalenceModuleMonoidAlgebra (k := ℂ) (G := G)).functor R
  exact Functor.simple_of_simple_obj
    (forget₂ (FDRep ℂ G) (Rep ℂ G)) (FDRep.of ρ)

end RepresentationTheory

namespace IrreducibleCharacter

universe u

variable {K : Type u} [Finite K] [Group K]
variable (H : Subgroup K) [H.Normal]

/-- Invariance of a character under the conjugation automorphism induced by
`g`. -/
def IsInvariantUnder (χ : IrreducibleCharacter H) (g : K) : Prop :=
  ∀ h : H,
    χ.values
      (RepresentationTheory.ClassFunction.conjByMulEquiv
        (K := K) (H := H) g h) =
      χ.values h

/-- Character invariance supplies the representation equivalence used by
the cyclic extension theorem. -/
theorem realization_nonempty_equiv_conjRep
    (χ : IrreducibleCharacter H) (g : K)
    (hχ : IsInvariantUnder H χ g) :
    Nonempty
      (Representation.Equiv χ.realization.ρ
        (RepresentationTheory.conjRep χ.realization.ρ g)) := by
  let W : FDRep ℂ H :=
    FDRep.of (RepresentationTheory.conjRep χ.realization.ρ g)
  let E : FDRep ℂ H ≌ FDRep ℂ H :=
    Action.resEquiv (FGModuleCat ℂ)
      (RepresentationTheory.ClassFunction.conjByMulEquiv
        (K := K) (H := H) g)
  letI : Simple W := by
    change Simple (E.functor.obj χ.realization)
    exact CategoryTheory.simple_obj E.functor χ.realization
  have hchar : χ.realization.character = W.character := by
    funext h
    change χ.realization.character h =
      χ.realization.character
        (RepresentationTheory.ClassFunction.conjByMulEquiv
          (K := K) (H := H) g h)
    calc
      χ.realization.character h = χ.values h :=
        congrFun χ.realization_character h
      _ = χ.values
          (RepresentationTheory.ClassFunction.conjByMulEquiv
            (K := K) (H := H) g h) := (hχ h).symm
      _ = χ.realization.character
          (RepresentationTheory.ClassFunction.conjByMulEquiv
            (K := K) (H := H) g h) :=
        (congrFun χ.realization_character _).symm
  obtain ⟨i⟩ :=
    FDRep.nonempty_iso_of_character_eq χ.realization W hchar
  let e := FDRep.isoToLinearEquiv i
  change χ.realization ≃ₗ[ℂ] χ.realization at e
  refine ⟨Representation.Equiv.mk e (fun h => ?_)⟩
  have hconj := FDRep.Iso.conj_ρ i h
  change
    (RepresentationTheory.conjRep χ.realization.ρ g) h =
      e.conj (χ.realization.ρ h) at hconj
  ext v
  have hv := LinearMap.congr_fun hconj (e v)
  simpa [LinearEquiv.conj_apply] using hv.symm

/-- An invariant irreducible complex character extends across a cyclic
quotient. -/
theorem exists_extension_of_cyclic_quotient
    (χ : IrreducibleCharacter H) {g : K}
    (htop : Subgroup.zpowers (QuotientGroup.mk' H g) = ⊤)
    (hχ : IsInvariantUnder H χ g) :
    ∃ ψ : IrreducibleCharacter K,
      IsExtensionAlong H.subtype χ ψ := by
  letI : Representation.IsIrreducible χ.realization.ρ :=
    CliffordRestriction.isIrreducible_of_simple χ.realization
  obtain ⟨σ, hσ, hσirr⟩ :=
    RepresentationTheory.exists_extension_of_cyclic_quotient
      χ.realization.ρ htop
      (realization_nonempty_equiv_conjRep H χ g hχ)
  letI : Representation.IsIrreducible σ := hσirr
  letI : Simple (FDRep.of σ) :=
    RepresentationTheory.simple_fdRep_of_isIrreducible σ
  let ψ : IrreducibleCharacter K :=
    IrreducibleCharacter.ofSimple (FDRep.of σ)
  refine ⟨ψ, fun h => ?_⟩
  change LinearMap.trace ℂ _ (σ (H.subtype h)) = χ.values h
  rw [show σ (H.subtype h) = χ.realization.ρ h by
    exact DFunLike.congr_fun hσ h]
  exact congrFun χ.realization_character h

end IrreducibleCharacter

end McKayConjecture
