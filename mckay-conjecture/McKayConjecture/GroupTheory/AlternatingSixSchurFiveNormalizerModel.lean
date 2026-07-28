/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverExact

/-!
# Five-local generators in the presented sixfold cover of `A₆`

Write `c = k₀`, `p = (a b²)c`, and `x = ac`.  The checked
presentation gives `p⁵ = 1`, `x² = c³`, and `x p x⁻¹ = p⁻¹`.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- The distinguished central generator of the presented sixfold cover. -/
abbrev alternatingSixSchurFiveCentral :
    AlternatingSixSchurPresentedGroup :=
  alternatingSixSchurPresentedK 0

/-- A corrected order-five lift of the chosen target element. -/
def alternatingSixSchurFiveElement :
    AlternatingSixSchurPresentedGroup :=
  (alternatingSixSchurPresentedA *
      alternatingSixSchurPresentedB ^ 2) *
    alternatingSixSchurFiveCentral

/-- The order-four lift which inverts the chosen five-element. -/
def alternatingSixSchurFiveNormalizerElement :
    AlternatingSixSchurPresentedGroup :=
  alternatingSixSchurPresentedA *
    alternatingSixSchurFiveCentral

/-- The order-ten dicyclic generator assembled from the order-five
element and the central involution. -/
def alternatingSixSchurFiveDicyclicGenerator :
    AlternatingSixSchurPresentedGroup :=
  alternatingSixSchurFiveElement ^ 3 *
    alternatingSixSchurFiveCentral ^ 3

theorem alternatingSixSchurPresentedK1_eq_k0_pow_three :
    alternatingSixSchurPresentedK 1 =
      alternatingSixSchurFiveCentral ^ 3 := by
  have h :=
    congrArg Additive.toMul
      alternatingSixSchurCentralKAdditive_reduce.1
  have hcoe := congrArg Subtype.val h
  simpa [alternatingSixSchurCentralKAdditive,
    alternatingSixSchurCentralK,
    alternatingSixSchurFiveCentral] using hcoe

theorem alternatingSixSchurPresentedK2_eq_k0_inv :
    alternatingSixSchurPresentedK 2 =
      alternatingSixSchurFiveCentral⁻¹ := by
  have h :=
    congrArg Additive.toMul
      alternatingSixSchurCentralKAdditive_reduce.2.1
  have hcoe := congrArg Subtype.val h
  simpa [alternatingSixSchurCentralKAdditive,
    alternatingSixSchurCentralK,
    alternatingSixSchurFiveCentral] using hcoe

theorem alternatingSixSchurPresentedK3_eq_k0 :
    alternatingSixSchurPresentedK 3 =
      alternatingSixSchurFiveCentral := by
  have h :=
    congrArg Additive.toMul
      alternatingSixSchurCentralKAdditive_reduce.2.2.1
  have hcoe := congrArg Subtype.val h
  simpa [alternatingSixSchurCentralKAdditive,
    alternatingSixSchurCentralK,
    alternatingSixSchurFiveCentral] using hcoe

theorem alternatingSixSchurPresentedA_sq :
    alternatingSixSchurPresentedA ^ 2 =
      alternatingSixSchurFiveCentral := by
  simpa [alternatingSixSchurBaseRelator,
    alternatingSixSchurFreeA, alternatingSixSchurPresentedA,
    alternatingSixSchurGenerator,
    alternatingSixSchurPresentedGenerator, PresentedGroup.of,
    alternatingSixSchurFiveCentral] using
      alternatingSixSchurPresented_baseRelator 0

theorem alternatingSixSchurPresentedB_pow_four :
    alternatingSixSchurPresentedB ^ 4 =
      alternatingSixSchurFiveCentral ^ 3 := by
  rw [← alternatingSixSchurPresentedK1_eq_k0_pow_three]
  simpa [alternatingSixSchurBaseRelator,
    alternatingSixSchurFreeB, alternatingSixSchurPresentedB,
    alternatingSixSchurGenerator,
    alternatingSixSchurPresentedGenerator, PresentedGroup.of] using
      alternatingSixSchurPresented_baseRelator 1

theorem alternatingSixSchurPresentedABSq_pow_five :
    (alternatingSixSchurPresentedA *
        alternatingSixSchurPresentedB ^ 2) ^ 5 =
      alternatingSixSchurFiveCentral := by
  rw [← alternatingSixSchurPresentedK3_eq_k0]
  simpa [alternatingSixSchurBaseRelator,
    alternatingSixSchurFreeA, alternatingSixSchurFreeB,
    alternatingSixSchurPresentedA, alternatingSixSchurPresentedB,
    alternatingSixSchurGenerator,
    alternatingSixSchurPresentedGenerator, PresentedGroup.of,
    pow_succ, mul_assoc] using
      alternatingSixSchurPresented_baseRelator 3

theorem alternatingSixSchurFiveCentral_mem_center :
    alternatingSixSchurFiveCentral ∈
      Subgroup.center AlternatingSixSchurPresentedGroup :=
  alternatingSixSchurPresentedK_mem_center 0

theorem alternatingSixSchurFiveCentral_commute
    (g : AlternatingSixSchurPresentedGroup) :
    Commute alternatingSixSchurFiveCentral g :=
  (Subgroup.mem_center_iff.mp
    alternatingSixSchurFiveCentral_mem_center g).symm

@[simp]
theorem alternatingSixSchurFiveElement_pow_five :
    alternatingSixSchurFiveElement ^ 5 = 1 := by
  rw [alternatingSixSchurFiveElement,
    Commute.mul_pow
      (alternatingSixSchurFiveCentral_commute
        (alternatingSixSchurPresentedA *
          alternatingSixSchurPresentedB ^ 2)).symm,
    alternatingSixSchurPresentedABSq_pow_five]
  calc
    alternatingSixSchurFiveCentral *
          alternatingSixSchurFiveCentral ^ 5 =
        alternatingSixSchurFiveCentral ^ 6 := by group
    _ = 1 := alternatingSixSchurPresentedK0_pow_six

@[simp]
theorem alternatingSixSchurFiveNormalizerElement_sq :
    alternatingSixSchurFiveNormalizerElement ^ 2 =
      alternatingSixSchurFiveCentral ^ 3 := by
  rw [alternatingSixSchurFiveNormalizerElement,
    Commute.mul_pow
      (alternatingSixSchurFiveCentral_commute
        alternatingSixSchurPresentedA).symm,
    alternatingSixSchurPresentedA_sq]
  group

theorem alternatingSixSchurFiveNormalizerElement_conj :
    alternatingSixSchurFiveNormalizerElement *
          alternatingSixSchurFiveElement *
          alternatingSixSchurFiveNormalizerElement⁻¹ =
      alternatingSixSchurFiveElement⁻¹ := by
  have hcA :=
    alternatingSixSchurFiveCentral_commute
      alternatingSixSchurPresentedA
  have hcB :=
    alternatingSixSchurFiveCentral_commute
      alternatingSixSchurPresentedB
  have hAinv :
      alternatingSixSchurPresentedA⁻¹ =
        alternatingSixSchurPresentedA *
          alternatingSixSchurFiveCentral⁻¹ := by
    rw [inv_eq_iff_mul_eq_one]
    calc
      alternatingSixSchurPresentedA *
            (alternatingSixSchurPresentedA *
              alternatingSixSchurFiveCentral⁻¹) =
          alternatingSixSchurPresentedA ^ 2 *
            alternatingSixSchurFiveCentral⁻¹ := by
              rw [pow_two]
              group
      _ = 1 := by
        rw [alternatingSixSchurPresentedA_sq]
        group
  have hBsqInv :
      (alternatingSixSchurPresentedB ^ 2)⁻¹ =
        alternatingSixSchurPresentedB ^ 2 *
          alternatingSixSchurFiveCentral ^ 3 := by
    rw [inv_eq_iff_mul_eq_one]
    calc
      alternatingSixSchurPresentedB ^ 2 *
            (alternatingSixSchurPresentedB ^ 2 *
              alternatingSixSchurFiveCentral ^ 3) =
          alternatingSixSchurPresentedB ^ 4 *
            alternatingSixSchurFiveCentral ^ 3 := by group
      _ = alternatingSixSchurFiveCentral ^ 3 *
            alternatingSixSchurFiveCentral ^ 3 := by
          rw [alternatingSixSchurPresentedB_pow_four]
      _ = 1 := by
        rw [← pow_add,
          alternatingSixSchurPresentedK0_pow_six]
  have hcBsq :
      Commute alternatingSixSchurFiveCentral
        (alternatingSixSchurPresentedB ^ 2) :=
    hcB.pow_right 2
  let t :=
    alternatingSixSchurPresentedA *
      alternatingSixSchurPresentedB ^ 2
  have hconjByProduct
      (g : AlternatingSixSchurPresentedGroup) :
      (alternatingSixSchurPresentedA *
          alternatingSixSchurFiveCentral) *
            g *
            (alternatingSixSchurPresentedA *
              alternatingSixSchurFiveCentral)⁻¹ =
        alternatingSixSchurPresentedA * g *
          alternatingSixSchurPresentedA⁻¹ := by
    calc
      (alternatingSixSchurPresentedA *
          alternatingSixSchurFiveCentral) *
            g *
            (alternatingSixSchurPresentedA *
              alternatingSixSchurFiveCentral)⁻¹ =
          alternatingSixSchurPresentedA *
            (alternatingSixSchurFiveCentral * g *
              alternatingSixSchurFiveCentral⁻¹) *
            alternatingSixSchurPresentedA⁻¹ := by
              rw [mul_inv_rev]
              group
      _ = alternatingSixSchurPresentedA * g *
          alternatingSixSchurPresentedA⁻¹ := by
            rw [(alternatingSixSchurFiveCentral_commute g).mul_inv_cancel]
  have htConj :
      alternatingSixSchurPresentedA * t *
          alternatingSixSchurPresentedA⁻¹ =
        alternatingSixSchurPresentedB ^ 2 *
          alternatingSixSchurPresentedA := by
    calc
      alternatingSixSchurPresentedA * t *
            alternatingSixSchurPresentedA⁻¹ =
          alternatingSixSchurPresentedA ^ 2 *
            alternatingSixSchurPresentedB ^ 2 *
              alternatingSixSchurPresentedA⁻¹ := by
                dsimp [t]
                simp only [pow_two]
                group
      _ =
          alternatingSixSchurFiveCentral *
            alternatingSixSchurPresentedB ^ 2 *
              (alternatingSixSchurPresentedA *
                alternatingSixSchurFiveCentral⁻¹) := by
                  rw [alternatingSixSchurPresentedA_sq, hAinv]
      _ =
          alternatingSixSchurPresentedB ^ 2 *
            alternatingSixSchurPresentedA := by
              calc
                alternatingSixSchurFiveCentral *
                      alternatingSixSchurPresentedB ^ 2 *
                        (alternatingSixSchurPresentedA *
                          alternatingSixSchurFiveCentral⁻¹) =
                    alternatingSixSchurPresentedB ^ 2 *
                      (alternatingSixSchurFiveCentral *
                        alternatingSixSchurPresentedA) *
                          alternatingSixSchurFiveCentral⁻¹ := by
                            rw [hcBsq.eq]
                            group
                _ =
                    alternatingSixSchurPresentedB ^ 2 *
                      (alternatingSixSchurPresentedA *
                        alternatingSixSchurFiveCentral) *
                          alternatingSixSchurFiveCentral⁻¹ := by
                            rw [hcA.eq]
                _ =
                    alternatingSixSchurPresentedB ^ 2 *
                      alternatingSixSchurPresentedA := by group
  calc
    alternatingSixSchurFiveNormalizerElement *
          alternatingSixSchurFiveElement *
          alternatingSixSchurFiveNormalizerElement⁻¹ =
        alternatingSixSchurPresentedA *
          alternatingSixSchurFiveElement *
          alternatingSixSchurPresentedA⁻¹ :=
      hconjByProduct alternatingSixSchurFiveElement
    _ =
        alternatingSixSchurPresentedB ^ 2 *
          alternatingSixSchurPresentedA *
          alternatingSixSchurFiveCentral := by
      change
        alternatingSixSchurPresentedA *
              (t * alternatingSixSchurFiveCentral) *
              alternatingSixSchurPresentedA⁻¹ =
          _
      calc
        alternatingSixSchurPresentedA *
              (t * alternatingSixSchurFiveCentral) *
              alternatingSixSchurPresentedA⁻¹ =
            (alternatingSixSchurPresentedA * t *
              alternatingSixSchurPresentedA⁻¹) *
                alternatingSixSchurFiveCentral := by
          calc
            alternatingSixSchurPresentedA *
                  (t * alternatingSixSchurFiveCentral) *
                  alternatingSixSchurPresentedA⁻¹ =
                alternatingSixSchurPresentedA * t *
                  (alternatingSixSchurFiveCentral *
                    alternatingSixSchurPresentedA⁻¹) := by group
            _ =
                alternatingSixSchurPresentedA * t *
                  (alternatingSixSchurPresentedA⁻¹ *
                    alternatingSixSchurFiveCentral) := by
                      rw [(hcA.inv_right).eq]
            _ = _ := by group
        _ = _ := by rw [htConj]
    _ =
        alternatingSixSchurFiveElement⁻¹ := by
      change
        _ =
          (t * alternatingSixSchurFiveCentral)⁻¹
      rw [mul_inv_rev]
      change
        _ =
          alternatingSixSchurFiveCentral⁻¹ *
            (alternatingSixSchurPresentedB ^ 2)⁻¹ *
              alternatingSixSchurPresentedA⁻¹
      rw [hBsqInv, hAinv]
      symm
      calc
        alternatingSixSchurFiveCentral⁻¹ *
              (alternatingSixSchurPresentedB ^ 2 *
                alternatingSixSchurFiveCentral ^ 3) *
              (alternatingSixSchurPresentedA *
                alternatingSixSchurFiveCentral⁻¹) =
            alternatingSixSchurPresentedB ^ 2 *
              (alternatingSixSchurFiveCentral⁻¹ *
                alternatingSixSchurFiveCentral ^ 3) *
              (alternatingSixSchurPresentedA *
                alternatingSixSchurFiveCentral⁻¹) := by
          calc
            alternatingSixSchurFiveCentral⁻¹ *
                  (alternatingSixSchurPresentedB ^ 2 *
                    alternatingSixSchurFiveCentral ^ 3) *
                  (alternatingSixSchurPresentedA *
                    alternatingSixSchurFiveCentral⁻¹) =
                (alternatingSixSchurFiveCentral⁻¹ *
                  alternatingSixSchurPresentedB ^ 2) *
                    alternatingSixSchurFiveCentral ^ 3 *
                  (alternatingSixSchurPresentedA *
                    alternatingSixSchurFiveCentral⁻¹) := by group
            _ =
                (alternatingSixSchurPresentedB ^ 2 *
                  alternatingSixSchurFiveCentral⁻¹) *
                    alternatingSixSchurFiveCentral ^ 3 *
                  (alternatingSixSchurPresentedA *
                    alternatingSixSchurFiveCentral⁻¹) := by
                      rw [hcBsq.inv_left.eq]
            _ = _ := by group
        _ =
            alternatingSixSchurPresentedB ^ 2 *
              alternatingSixSchurFiveCentral ^ 2 *
              (alternatingSixSchurPresentedA *
                alternatingSixSchurFiveCentral⁻¹) := by group
        _ =
            alternatingSixSchurPresentedB ^ 2 *
              alternatingSixSchurPresentedA *
                alternatingSixSchurFiveCentral := by
          calc
            alternatingSixSchurPresentedB ^ 2 *
                  alternatingSixSchurFiveCentral ^ 2 *
                  (alternatingSixSchurPresentedA *
                    alternatingSixSchurFiveCentral⁻¹) =
                alternatingSixSchurPresentedB ^ 2 *
                  ((alternatingSixSchurFiveCentral ^ 2 *
                    alternatingSixSchurPresentedA) *
                      alternatingSixSchurFiveCentral⁻¹) := by group
            _ =
                alternatingSixSchurPresentedB ^ 2 *
                  ((alternatingSixSchurPresentedA *
                    alternatingSixSchurFiveCentral ^ 2) *
                      alternatingSixSchurFiveCentral⁻¹) := by
                        rw [(hcA.pow_left 2).eq]
            _ = _ := by group

end GroupTheory
end McKayConjecture
