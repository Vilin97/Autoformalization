/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.CentralSylowDecomposition

/-!
# Sylow normalizers above a normal `p′`-kernel

Let `K ◁ G` have order prime to `p`, and suppose `G = KP` for a Sylow
`p`-subgroup `P`.  Then

`N_G(P) = C_K(P) P`.

The key elementary observation is `N_K(P) = C_K(P)`: for
`k ∈ K ∩ N_G(P)` and `x ∈ P`, their commutator belongs both to `K` and
to `P`, hence is trivial by coprimality.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
/-- A normal `p′`-subgroup element that normalizes a `p`-subgroup
centralizes it. -/
theorem inf_normalizer_le_centralizer_of_normal_isPPrime
    (P K : Subgroup G)
    [K.Normal]
    (hP : IsPGroup p P)
    (hK : IsPPrimeGroup p K) :
    K ⊓ Subgroup.normalizer (P : Set G) ≤
      Subgroup.centralizer (P : Set G) := by
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hconjP :
      k * x * k⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp hk.2 x).mp hx
  have hcommP :
      k * x * k⁻¹ * x⁻¹ ∈ P :=
    mul_mem hconjP (inv_mem hx)
  have hconjK :
      x * k⁻¹ * x⁻¹ ∈ K :=
    (inferInstance : K.Normal).conj_mem
      k⁻¹ (inv_mem hk.1) x
  have hcommK :
      k * x * k⁻¹ * x⁻¹ ∈ K := by
    have hconjK' :
        x * (k⁻¹ * x⁻¹) ∈ K := by
      simpa only [mul_assoc] using hconjK
    simpa only [mul_assoc] using
      (K.mul_mem hk.1 hconjK')
  have hcommOne :
      k * x * k⁻¹ * x⁻¹ = 1 :=
    Subgroup.disjoint_def.mp
      (IsPGroup.disjoint_of_isPPrimeGroup hP hK)
      hcommP hcommK
  have hkx : k * x = x * k := by
    apply mul_inv_eq_one.mp
    simpa only [mul_inv_rev, mul_assoc] using hcommOne
  exact hkx.symm

/-- For a normal `p′`-kernel generated together with a Sylow subgroup,
the Sylow normalizer is `C_K(P)P`. -/
theorem normalizer_eq_inf_centralizer_sup
    (P : Sylow p G)
    (K : Subgroup G) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hgenerate : K ⊔ (P : Subgroup G) = ⊤) :
    Subgroup.normalizer (P : Set G) =
      (K ⊓ Subgroup.centralizer (P : Set G)) ⊔
        (P : Subgroup G) := by
  apply le_antisymm
  · intro g hg
    have hgKP : g ∈ K ⊔ (P : Subgroup G) := by
      rw [hgenerate]
      exact Subgroup.mem_top g
    obtain ⟨k, hkK, x, hxP, hkx⟩ :=
      Subgroup.mem_sup_of_normal_left.mp hgKP
    have hxN :
        x ∈ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer hxP
    have hkEq : k = g * x⁻¹ := by
      rw [← hkx]
      group
    have hkN :
        k ∈ Subgroup.normalizer (P : Set G) := by
      rw [hkEq]
      exact mul_mem hg (inv_mem hxN)
    have hkC :
        k ∈ Subgroup.centralizer (P : Set G) :=
      inf_normalizer_le_centralizer_of_normal_isPPrime
        (p := p) (P : Subgroup G) K P.isPGroup' hK
        ⟨hkK, hkN⟩
    rw [← hkx]
    exact
      ((K ⊓ Subgroup.centralizer (P : Set G)) ⊔
          (P : Subgroup G)).mul_mem
        ((show
          K ⊓ Subgroup.centralizer (P : Set G) ≤
            (K ⊓ Subgroup.centralizer (P : Set G)) ⊔
              (P : Subgroup G) from le_sup_left)
          ⟨hkK, hkC⟩)
        ((show
          (P : Subgroup G) ≤
            (K ⊓ Subgroup.centralizer (P : Set G)) ⊔
              (P : Subgroup G) from le_sup_right)
          hxP)
  · exact sup_le
      (inf_le_right.trans
        (Subgroup.centralizer_le_normalizer
          (P : Set G)))
      Subgroup.le_normalizer

/-- The fixed-point part `C_K(P)`, viewed inside the Sylow normalizer. -/
abbrev internalPPrimeKernelFixedPoints
    (P : Sylow p G)
    (K : Subgroup G) :
    Subgroup (Subgroup.normalizer (P : Set G)) :=
  (K ⊓ Subgroup.centralizer (P : Set G)).subgroupOf
    (Subgroup.normalizer (P : Set G))

/-- The Sylow subgroup, viewed inside its own normalizer. -/
abbrev internalNormalizerSylow
    (P : Sylow p G) :
    Subgroup (Subgroup.normalizer (P : Set G)) :=
  (P : Subgroup G).subgroupOf
    (Subgroup.normalizer (P : Set G))

/-- Internally to the Sylow normalizer, `C_K(P)` and `P` generate the
whole group. -/
theorem internalFixedPoints_sup_internalSylow_eq_top
    (P : Sylow p G)
    (K : Subgroup G) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hgenerate : K ⊔ (P : Subgroup G) = ⊤) :
    internalPPrimeKernelFixedPoints P K ⊔
        internalNormalizerSylow P =
      ⊤ := by
  rw [← Subgroup.subgroupOf_sup
    (show
      K ⊓ Subgroup.centralizer (P : Set G) ≤
        Subgroup.normalizer (P : Set G) from
      inf_le_right.trans
        (Subgroup.centralizer_le_normalizer
          (P : Set G)))
    (show
      (P : Subgroup G) ≤
        Subgroup.normalizer (P : Set G) from
      Subgroup.le_normalizer)]
  rw [← normalizer_eq_inf_centralizer_sup
    P K hK hgenerate]
  exact Subgroup.subgroupOf_self _

omit [Fact p.Prime] in
/-- The two internal factors `C_K(P)` and `P` are disjoint. -/
theorem internalFixedPoints_disjoint_internalSylow
    (P : Sylow p G)
    (K : Subgroup G)
    (hK : IsPPrimeGroup p K) :
    Disjoint
      (internalPPrimeKernelFixedPoints P K)
      (internalNormalizerSylow P) := by
  apply Subgroup.disjoint_def.mpr
  intro x hxC hxP
  apply Subtype.ext
  exact
    Subgroup.disjoint_def.mp
      (IsPGroup.disjoint_of_isPPrimeGroup
        P.isPGroup' hK)
      hxP hxC.1

omit [Finite G] [Fact p.Prime] in
/-- The two internal factors commute. -/
theorem internalFixedPoints_le_centralizer_internalSylow
    (P : Sylow p G)
    (K : Subgroup G) :
    internalPPrimeKernelFixedPoints P K ≤
      Subgroup.centralizer
        (internalNormalizerSylow P :
          Set (Subgroup.normalizer (P : Set G))) := by
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  apply Subtype.ext
  exact hk.2 (x : G) hx

/-- Internally to `N_G(P)`, `C_K(P)` and `P` are complementary. -/
theorem internalFixedPoints_isComplement'_internalSylow
    (P : Sylow p G)
    (K : Subgroup G) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hgenerate : K ⊔ (P : Subgroup G) = ⊤) :
    (internalPPrimeKernelFixedPoints P K).IsComplement'
      (internalNormalizerSylow P) := by
  letI : (internalNormalizerSylow P).Normal :=
    Subgroup.normal_in_normalizer
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    (internalFixedPoints_disjoint_internalSylow P K hK)
  rw [← Subgroup.mul_normal
    (internalPPrimeKernelFixedPoints P K)
    (internalNormalizerSylow P)]
  rw [internalFixedPoints_sup_internalSylow_eq_top
    P K hK hgenerate]
  rfl

/-- Direct-product description of the Sylow normalizer above a normal
`p′`-kernel. -/
def pPrimeKernelFixedPointsProductEquiv
    (P : Sylow p G)
    (K : Subgroup G) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hgenerate : K ⊔ (P : Subgroup G) = ⊤) :
    internalPPrimeKernelFixedPoints P K ×
        internalNormalizerSylow P ≃*
      Subgroup.normalizer (P : Set G) :=
  complementaryCommutingProductMulEquiv
    (internalPPrimeKernelFixedPoints P K)
    (internalNormalizerSylow P)
    (internalFixedPoints_isComplement'_internalSylow
      P K hK hgenerate)
    (internalFixedPoints_le_centralizer_internalSylow
      P K)

@[simp]
theorem pPrimeKernelFixedPointsProductEquiv_apply
    (P : Sylow p G)
    (K : Subgroup G) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hgenerate : K ⊔ (P : Subgroup G) = ⊤)
    (x :
      internalPPrimeKernelFixedPoints P K ×
        internalNormalizerSylow P) :
    pPrimeKernelFixedPointsProductEquiv
        P K hK hgenerate x =
      (x.1 :
        Subgroup.normalizer (P : Set G)) *
        (x.2 :
          Subgroup.normalizer (P : Set G)) :=
  rfl

end GroupTheory
end McKayConjecture
