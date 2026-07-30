/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.PPrimeKernelSylowNormalizer
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The quotient equivalence in the Okuyama--Wajima argument

Let `K` be a normal `p′`-subgroup of a finite group `A`, let `S` be a
`p`-subgroup, and put `D = K ∩ C_A(S)`.  If
`D ≤ U ≤ N_A(S)`, then

* `K ∩ U = D`;
* the two copies of that intersection inside `U` agree; and
* Noether's second isomorphism theorem gives
  `U / D ≃ (U ⊔ K) / K`.

The final equivalence sends the coset of `u : U` to the coset of the same
ambient element in `U ⊔ K`.  This character-free leaf isolates the exact
group-theoretic transport used by the ordinary Okuyama--Wajima comparison.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

variable {A : Type u} [Group A] [Finite A]
variable {p : ℕ}
variable (K S : Subgroup A) [K.Normal]

omit [Finite A] in
/-- Every element normalizing `S` also normalizes the fixed-point subgroup
`K ∩ C_A(S)` of `S` in a normal subgroup `K`. -/
theorem normalizer_le_normalizer_inf_centralizer :
    Subgroup.normalizer (S : Set A) ≤
      Subgroup.normalizer
        ((K ⊓ Subgroup.centralizer (S : Set A) :
          Subgroup A) : Set A) := by
  rw [Subgroup.le_normalizer_iff]
  intro g hg x hx
  refine ⟨(inferInstance : K.Normal).conj_mem x hx.1 g, ?_⟩
  change g * x * g⁻¹ ∈
    Subgroup.centralizer (S : Set A)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : g⁻¹ * y * g ∈ S :=
    (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * y * g)).mpr (by
      simpa [mul_assoc] using hy)
  have hcomm :
      (g⁻¹ * y * g) * x =
        x * (g⁻¹ * y * g) :=
    Subgroup.mem_centralizer_iff.mp hx.2
      (g⁻¹ * y * g) hy'
  have hconj :=
    congrArg (fun z : A => g * z * g⁻¹) hcomm
  simpa [mul_assoc] using hconj

/-- Between `K ∩ C_A(S)` and `N_A(S)`, intersection with a normal
`p′`-kernel is exactly the fixed-point subgroup. -/
theorem pPrimeKernel_inf_eq_fixedPoints
    (hS : IsPGroup p S)
    (hK : IsPPrimeGroup p K)
    (U : Subgroup A)
    (hU : U ≤ Subgroup.normalizer (S : Set A))
    (hfixedU :
      K ⊓ Subgroup.centralizer (S : Set A) ≤ U) :
    K ⊓ U =
      K ⊓ Subgroup.centralizer (S : Set A) := by
  apply le_antisymm
  · exact le_inf inf_le_left
      ((inf_le_inf_left K hU).trans
        (inf_normalizer_le_centralizer_of_normal_isPPrime
          (p := p) S K hS hK))
  · exact le_inf inf_le_left hfixedU

/-- The copies inside `U` of `K` and of the fixed-point subgroup agree. -/
theorem pPrimeKernel_subgroupOf_eq_fixedPoints_subgroupOf
    (hS : IsPGroup p S)
    (hK : IsPPrimeGroup p K)
    (U : Subgroup A)
    (hU : U ≤ Subgroup.normalizer (S : Set A))
    (hfixedU :
      K ⊓ Subgroup.centralizer (S : Set A) ≤ U) :
    K.subgroupOf U =
      (K ⊓ Subgroup.centralizer (S : Set A)).subgroupOf U := by
  ext x
  change
    (x : A) ∈ K ↔
      (x : A) ∈
        K ⊓ Subgroup.centralizer (S : Set A)
  rw [← pPrimeKernel_inf_eq_fixedPoints
    K S hS hK U hU hfixedU]
  simp only [Subgroup.mem_inf, x.2, and_true]

/-- The second-isomorphism equivalence
`U / C_K(S) ≃ (U ⊔ K) / K` in the Okuyama--Wajima setup. -/
def okuyamaWajimaQuotientEquiv
    (hS : IsPGroup p S)
    (hK : IsPPrimeGroup p K)
    (U : Subgroup A)
    (hU : U ≤ Subgroup.normalizer (S : Set A))
    (hfixedU :
      K ⊓ Subgroup.centralizer (S : Set A) ≤ U) :
    letI :
        ((K ⊓ Subgroup.centralizer (S : Set A)).subgroupOf U).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer
        (hU.trans
          (normalizer_le_normalizer_inf_centralizer K S))
    U ⧸
        (K ⊓ Subgroup.centralizer (S : Set A)).subgroupOf U ≃*
      (U ⊔ K : Subgroup A) ⧸
        K.subgroupOf (U ⊔ K) := by
  letI :
      ((K ⊓ Subgroup.centralizer (S : Set A)).subgroupOf U).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (hU.trans
        (normalizer_le_normalizer_inf_centralizer K S))
  let hEq :
      (K ⊓ Subgroup.centralizer (S : Set A)).subgroupOf U =
        K.subgroupOf U :=
    (pPrimeKernel_subgroupOf_eq_fixedPoints_subgroupOf
      K S hS hK U hU hfixedU).symm
  exact
    (QuotientGroup.quotientMulEquivOfEq hEq).trans
      (QuotientGroup.quotientInfEquivProdNormalQuotient U K)

/-- The Okuyama--Wajima quotient equivalence maps the coset of `u : U`
to the coset of the same ambient element in `U ⊔ K`. -/
@[simp]
theorem okuyamaWajimaQuotientEquiv_mk
    (hS : IsPGroup p S)
    (hK : IsPPrimeGroup p K)
    (U : Subgroup A)
    (hU : U ≤ Subgroup.normalizer (S : Set A))
    (hfixedU :
      K ⊓ Subgroup.centralizer (S : Set A) ≤ U)
    (x : U) :
    letI :
        ((K ⊓ Subgroup.centralizer (S : Set A)).subgroupOf U).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer
        (hU.trans
          (normalizer_le_normalizer_inf_centralizer K S))
    okuyamaWajimaQuotientEquiv
        K S hS hK U hU hfixedU
        (QuotientGroup.mk'
          ((K ⊓ Subgroup.centralizer (S : Set A)).subgroupOf U) x) =
      QuotientGroup.mk' (K.subgroupOf (U ⊔ K))
        (Subgroup.inclusion le_sup_left x) := by
  letI :
      ((K ⊓ Subgroup.centralizer (S : Set A)).subgroupOf U).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (hU.trans
        (normalizer_le_normalizer_inf_centralizer K S))
  rfl

/-- In the reverse direction, the coset of an element coming from `U`
maps back to its original coset. -/
@[simp]
theorem okuyamaWajimaQuotientEquiv_symm_mk
    (hS : IsPGroup p S)
    (hK : IsPPrimeGroup p K)
    (U : Subgroup A)
    (hU : U ≤ Subgroup.normalizer (S : Set A))
    (hfixedU :
      K ⊓ Subgroup.centralizer (S : Set A) ≤ U)
    (x : U) :
    letI :
        ((K ⊓ Subgroup.centralizer (S : Set A)).subgroupOf U).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer
        (hU.trans
          (normalizer_le_normalizer_inf_centralizer K S))
    (okuyamaWajimaQuotientEquiv
        K S hS hK U hU hfixedU).symm
        (QuotientGroup.mk' (K.subgroupOf (U ⊔ K))
          (Subgroup.inclusion le_sup_left x)) =
      QuotientGroup.mk'
        ((K ⊓ Subgroup.centralizer (S : Set A)).subgroupOf U) x := by
  letI :
      ((K ⊓ Subgroup.centralizer (S : Set A)).subgroupOf U).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (hU.trans
        (normalizer_le_normalizer_inf_centralizer K S))
  rw [← okuyamaWajimaQuotientEquiv_mk
    K S hS hK U hU hfixedU]
  exact MulEquiv.symm_apply_apply _ _

end GroupTheory
end McKayConjecture
