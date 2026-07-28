/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.CoprimeCommutingFactors
import McKayConjecture.GroupTheory.PPrimeKernelSylowNormalizer
import Mathlib.GroupTheory.Complement

/-!
# Central elements in a normal `p′`-by-`p` decomposition

Suppose a finite group is the product of a normal `p′`-subgroup and a
complementary `p`-subgroup.  The unique two coordinates of a central
element are themselves central.

The key point is that the normal coordinate normalizes the `p`-factor,
and hence centralizes it.  Its order is coprime to the order of the
`p`-coordinate, so both coordinates are powers of their central
product.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

variable {G : Type*} [Group G]

/-- The normal-subgroup coordinate belonging to a complementary
factorization. -/
def normalComplementKernelPart
    (N H : Subgroup G)
    (hcomp : N.IsComplement' H)
    (g : G) :
    N :=
  (hcomp.equiv g).1

/-- The complement coordinate belonging to a complementary
factorization. -/
def normalComplementFactorPart
    (N H : Subgroup G)
    (hcomp : N.IsComplement' H)
    (g : G) :
    H :=
  (hcomp.equiv g).2

/-- The two complementary coordinates multiply to the original
element. -/
@[simp]
theorem normalComplementKernelPart_mul_factorPart
    (N H : Subgroup G)
    (hcomp : N.IsComplement' H)
    (g : G) :
    (normalComplementKernelPart N H hcomp g : G) *
        (normalComplementFactorPart N H hcomp g : G) =
      g :=
  hcomp.equiv_fst_mul_equiv_snd g

variable [Finite G]
variable {p : ℕ}

/-- The two coordinates of a central element in a normal
`p′`-by-`p` complementary factorization are central. -/
theorem normalComplement_central_parts
    (N H : Subgroup G)
    [N.Normal]
    (hN : IsPPrimeGroup p N)
    (hH : IsPGroup p H)
    (hcomp : N.IsComplement' H)
    {z : G}
    (hz : z ∈ Subgroup.center G) :
    (normalComplementKernelPart N H hcomp z : G) ∈
        Subgroup.center G ∧
      (normalComplementFactorPart N H hcomp z : G) ∈
        Subgroup.center G := by
  let a : N :=
    normalComplementKernelPart N H hcomp z
  let b : H :=
    normalComplementFactorPart N H hcomp z
  have habz : (a : G) * (b : G) = z :=
    normalComplementKernelPart_mul_factorPart N H hcomp z
  have haNormalizer :
      (a : G) ∈ Subgroup.normalizer (H : Set G) := by
    have haeq : (a : G) = z * (b : G)⁻¹ := by
      rw [← habz]
      group
    rw [haeq]
    exact
      (Subgroup.normalizer (H : Set G)).mul_mem
        (Subgroup.center_le_normalizer (H : Set G) hz)
        ((Subgroup.normalizer (H : Set G)).inv_mem
          (Subgroup.le_normalizer b.2))
  have haCentralizes :
      (a : G) ∈ Subgroup.centralizer (H : Set G) :=
    inf_normalizer_le_centralizer_of_normal_isPPrime
      (p := p) H N hH hN
      ⟨a.2, haNormalizer⟩
  have hab : Commute (a : G) (b : G) := by
    exact
      (Subgroup.mem_centralizer_iff.mp
        haCentralizes (b : G) b.2).symm
  have haOrderDvd :
      orderOf (a : G) ∣ Nat.card N :=
    N.orderOf_dvd_natCard a.2
  have hpOrder :
      p.Coprime (orderOf (a : G)) :=
    hN.coprime_dvd_right haOrderDvd
  have horders :
      (orderOf (a : G)).Coprime
        (orderOf (b : G)) := by
    have hsubtype :
        (orderOf b).Coprime
          (orderOf (a : G)) :=
      hH.orderOf_coprime hpOrder b
    simpa only [Subgroup.orderOf_coe] using hsubtype.symm
  have hproductCenter :
      (a : G) * (b : G) ∈
        Subgroup.center G := by
    simpa only [habz] using hz
  simpa only [a, b] using
    factors_mem_of_mul_mem_of_commute_coprime_order
      (Subgroup.center G) hab horders hproductCenter

end GroupTheory
end McKayConjecture
