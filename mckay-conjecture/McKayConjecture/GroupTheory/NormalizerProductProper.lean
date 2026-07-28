/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Group.Subgroup.Pointwise
import McKayConjecture.GroupTheory.CentralIndexSubgroup

/-!
# Properness of a subgroup times a normalizing subgroup

The final Rossi reduction replaces a normal subgroup `K` by a proper
subgroup `M < K` and adjoins an ambient normalizer `L`.  If `L`
normalizes `M` and `K ∩ L ≤ M`, then

`K ∩ (M ⊔ L) = M`.

In particular `M ⊔ L` is proper.  This is the exact elementary
group-theoretic calculation behind the decrease in the final induction.
-/

noncomputable section

open scoped Pointwise

universe u

namespace McKayConjecture
namespace GroupTheory

variable {G : Type u} [Group G]

/-- A Dedekind-style intersection calculation under an explicit
normalizer hypothesis. -/
theorem inf_sup_eq_of_le_normalizer_of_inf_le
    (K M L : Subgroup G)
    (hMK : M ≤ K)
    (hLM : L ≤ Subgroup.normalizer M)
    (hKL : K ⊓ L ≤ M) :
    K ⊓ (M ⊔ L) = M := by
  apply le_antisymm
  · intro x hx
    have hxprod :
        x ∈ (M : Set G) * (L : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left
        M L hLM]
      exact hx.2
    obtain ⟨m, hm, l, hl, hml⟩ := hxprod
    have hlK : l ∈ K := by
      have hmK : m ∈ K := hMK hm
      have hcalc : l = m⁻¹ * x := by
        rw [← hml]
        simp
      rw [hcalc]
      exact K.mul_mem (K.inv_mem hmK) hx.1
    have hlM : l ∈ M :=
      hKL ⟨hlK, hl⟩
    rw [← hml]
    exact M.mul_mem hm hlM
  · exact le_inf hMK le_sup_left

/-- Under the same hypotheses, adjoining the normalizing subgroup to a
proper subgroup of `K` cannot produce the whole ambient group. -/
theorem sup_lt_top_of_lt_of_le_normalizer_of_inf_le
    (K M L : Subgroup G)
    (hMK : M < K)
    (hLM : L ≤ Subgroup.normalizer M)
    (hKL : K ⊓ L ≤ M) :
    M ⊔ L < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  have hintersection :=
    inf_sup_eq_of_le_normalizer_of_inf_le
      K M L hMK.le hLM hKL
  have hKM : K = M := by
    calc
      K = K ⊓ (⊤ : Subgroup G) := (inf_top_eq K).symm
      _ = K ⊓ (M ⊔ L) := by rw [htop]
      _ = M := hintersection
  exact hMK.ne hKM.symm

/-- If the ambient center also lies in `M ⊔ L`, then the intermediate
group has strictly smaller central index than `G`. -/
theorem centralIndex_sup_lt_of_lt_of_le_normalizer_of_inf_le
    [Finite G]
    (K M L : Subgroup G)
    (hMK : M < K)
    (hLM : L ≤ Subgroup.normalizer M)
    (hKL : K ⊓ L ≤ M)
    (hZ : Subgroup.center G ≤ M ⊔ L) :
    centralIndex ↥(M ⊔ L) < centralIndex G :=
  centralIndex_lt_of_center_le_of_lt_top
    (M ⊔ L) hZ
    (sup_lt_top_of_lt_of_le_normalizer_of_inf_le
      K M L hMK hLM hKL)

end GroupTheory
end McKayConjecture
