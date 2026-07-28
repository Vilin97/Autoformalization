/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverUniversal
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverRepresentations

/-!
# Exact order of the explicit sixfold cover

The double- and triple-cover permutation representations detect the
`2`- and `3`-parts of `k₀`.  The rewrite-lattice calculation already
shows `k₀⁶ = 1`, so `k₀` has exact order six.  Since it lies in the
projection kernel and that kernel has order at most six, all cardinality
bounds are exact.
-/

noncomputable section

open scoped IsMulCommutative

namespace McKayConjecture
namespace GroupTheory

/-- The first central relator value has exponent dividing six. -/
theorem alternatingSixSchurPresentedK0_pow_six :
    alternatingSixSchurPresentedK 0 ^ 6 = 1 := by
  have hadditive :=
    alternatingSixSchurCentralKAdditive_reduce.2.2.2
  have hmultiplicative :=
    congrArg Additive.toMul hadditive
  have hambient :=
    congrArg Subtype.val hmultiplicative
  simpa [alternatingSixSchurCentralKAdditive,
    alternatingSixSchurCentralK] using hambient

/-- The double- and triple-cover actions together detect exact order six. -/
theorem orderOf_alternatingSixSchurPresentedK0 :
    orderOf (alternatingSixSchurPresentedK 0) = 6 := by
  have htwo :=
    orderOf_map_dvd
      alternatingSixDoubleCoverRepresentation
      (alternatingSixSchurPresentedK 0)
  rw [alternatingSixDoubleCoverRepresentation_k0_order]
    at htwo
  have hthree :=
    orderOf_map_dvd
      alternatingSixTripleCoverRepresentation
      (alternatingSixSchurPresentedK 0)
  rw [alternatingSixTripleCoverRepresentation_k0_order]
    at hthree
  have hsix :
      6 ∣ orderOf
        (alternatingSixSchurPresentedK 0) :=
    (show Nat.Coprime 2 3 by norm_num).mul_dvd_of_dvd_of_dvd
      htwo hthree
  exact Nat.dvd_antisymm
    (orderOf_dvd_of_pow_eq_one
      alternatingSixSchurPresentedK0_pow_six)
    hsix

/-- `k₀`, regarded as an element of the projection kernel. -/
def alternatingSixSchurPresentedK0InKernel :
    alternatingSixSchurProjection.ker :=
  ⟨alternatingSixSchurPresentedK 0, by
    rw [MonoidHom.mem_ker,
      alternatingSixSchurProjection_k]⟩

/-- The kernel element represented by `k₀` still has exact order six. -/
theorem orderOf_alternatingSixSchurPresentedK0InKernel :
    orderOf alternatingSixSchurPresentedK0InKernel = 6 := by
  have hinjectiveOrder :=
    orderOf_injective
      alternatingSixSchurProjection.ker.subtype
      Subtype.coe_injective
      alternatingSixSchurPresentedK0InKernel
  change
    orderOf (alternatingSixSchurPresentedK 0) =
      orderOf alternatingSixSchurPresentedK0InKernel
    at hinjectiveOrder
  rw [orderOf_alternatingSixSchurPresentedK0]
    at hinjectiveOrder
  exact hinjectiveOrder.symm

/-- The projection kernel of the explicit cover has exact order six. -/
theorem natCard_alternatingSixSchurProjection_ker :
    Nat.card alternatingSixSchurProjection.ker = 6 := by
  apply le_antisymm
  · exact natCard_alternatingSixSchurProjection_ker_le
  · apply Nat.le_of_dvd Nat.card_pos
    have hdvd :=
      orderOf_dvd_natCard
        alternatingSixSchurPresentedK0InKernel
    rw [orderOf_alternatingSixSchurPresentedK0InKernel]
      at hdvd
    exact hdvd

/-- The explicit Schur-cover presentation has exact order `2160`. -/
theorem natCard_alternatingSixSchurPresentedGroup :
    Nat.card AlternatingSixSchurPresentedGroup = 2160 := by
  have hrange :
      alternatingSixSchurProjection.range = ⊤ :=
    MonoidHom.range_eq_top.mpr
      alternatingSixSchurProjection_surjective
  calc
    Nat.card AlternatingSixSchurPresentedGroup =
        Nat.card alternatingSixSchurProjection.ker *
          alternatingSixSchurProjection.ker.index :=
      alternatingSixSchurProjection.ker.card_mul_index.symm
    _ =
        Nat.card alternatingSixSchurProjection.ker *
          Nat.card alternatingSixSchurProjection.range := by
      rw [Subgroup.index_ker]
    _ = 6 * 360 := by
      rw [natCard_alternatingSixSchurProjection_ker,
        hrange, Subgroup.card_top,
        natCard_alternatingSix]
    _ = 2160 := by norm_num

/-- The center of the explicit universal cover has exact order six. -/
theorem natCard_center_alternatingSixSchurPresentedGroup :
    Nat.card
        (Subgroup.center
          AlternatingSixSchurPresentedGroup) = 6 := by
  rw [←
    alternatingSixSchurCentralExtension.ker_eq_center
      (inferInstance : IsSimpleGroup AlternatingSix)
      alternatingSix_not_isMulCommutative]
  exact natCard_alternatingSixSchurProjection_ker

end GroupTheory
end McKayConjecture
