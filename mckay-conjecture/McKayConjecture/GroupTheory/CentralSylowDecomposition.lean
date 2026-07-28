/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Transfer
import McKayConjecture.GroupTheory.PPrimeCoreSylowIntersection

/-!
# Decomposition along a central Sylow subgroup

Burnside transfer produces a canonical normal `p`-complement whenever a
Sylow `p`-subgroup is central.  Since the Sylow subgroup commutes with that
complement, multiplication upgrades the complementary-subgroup bijection to
an internal direct-product equivalence.

This is the elementary group-theoretic reduction used in the
central-intersection step of the McKay argument: if `K ∩ P` is central in an
ambient group, then it is central in `K`, and `K` splits as its normal
`p`-complement times `K ∩ P`.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

variable {G : Type u} [Group G]

/-- Multiplication from two commuting subgroups is a homomorphism. -/
def commutingProductMulHom
    (H K : Subgroup G)
    (hcommute :
      H ≤ Subgroup.centralizer (K : Set G)) :
    H × K →* G where
  toFun := fun x ↦ (x.1 : G) * (x.2 : G)
  map_one' := by simp
  map_mul' := by
    intro x y
    change
      ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G)) =
        ((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G))
    have hcomm :
        (x.2 : G) * (y.1 : G) = (y.1 : G) * (x.2 : G) :=
      hcommute y.1.2 (x.2 : G) x.2.2
    symm
    calc
      ((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G)) =
          (x.1 : G) * ((x.2 : G) * (y.1 : G)) * (y.2 : G) := by
            simp only [mul_assoc]
      _ = (x.1 : G) * ((y.1 : G) * (x.2 : G)) * (y.2 : G) := by
            rw [hcomm]
      _ = ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G)) := by
            simp only [mul_assoc]

@[simp]
theorem commutingProductMulHom_apply
    (H K : Subgroup G)
    (hcommute :
      H ≤ Subgroup.centralizer (K : Set G))
    (x : H × K) :
    commutingProductMulHom H K hcommute x =
      (x.1 : G) * (x.2 : G) :=
  rfl

/-- Multiplication identifies two commuting complementary subgroups with
their ambient group. -/
def complementaryCommutingProductMulEquiv
    (H K : Subgroup G)
    (hcomplement : H.IsComplement' K)
    (hcommute :
      H ≤ Subgroup.centralizer (K : Set G)) :
    H × K ≃* G :=
  MulEquiv.ofBijective
    (commutingProductMulHom H K hcommute)
    ((Subgroup.isComplement_iff_bijective H K).mp hcomplement)

@[simp]
theorem complementaryCommutingProductMulEquiv_apply
    (H K : Subgroup G)
    (hcomplement : H.IsComplement' K)
    (hcommute :
      H ≤ Subgroup.centralizer (K : Set G))
    (x : H × K) :
    complementaryCommutingProductMulEquiv
      H K hcomplement hcommute x =
        (x.1 : G) * (x.2 : G) :=
  rfl

/-- Multiplication from two subgroups is a homomorphism when the right-hand
subgroup is central. -/
def centralProductMulHom
    (H K : Subgroup G)
    (hKcentral : K ≤ Subgroup.center G) :
    H × K →* G where
  toFun := fun x ↦ (x.1 : G) * (x.2 : G)
  map_one' := by simp
  map_mul' := by
    intro x y
    change
      ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G)) =
        ((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G))
    have hcomm :
        (x.2 : G) * (y.1 : G) = (y.1 : G) * (x.2 : G) :=
      (Subgroup.mem_center_iff.mp (hKcentral x.2.2) (y.1 : G)).symm
    symm
    calc
      ((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G)) =
          (x.1 : G) * ((x.2 : G) * (y.1 : G)) * (y.2 : G) := by
            simp only [mul_assoc]
      _ = (x.1 : G) * ((y.1 : G) * (x.2 : G)) * (y.2 : G) := by
            rw [hcomm]
      _ = ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G)) := by
            simp only [mul_assoc]

@[simp]
theorem centralProductMulHom_apply
    (H K : Subgroup G)
    (hKcentral : K ≤ Subgroup.center G)
    (x : H × K) :
    centralProductMulHom H K hKcentral x =
      (x.1 : G) * (x.2 : G) :=
  rfl

/-- Multiplication from two complementary subgroups is a group isomorphism
when the right-hand subgroup is central. -/
def complementaryCentralProductMulEquiv
    (H K : Subgroup G)
    (hcomplement : H.IsComplement' K)
    (hKcentral : K ≤ Subgroup.center G) :
    H × K ≃* G :=
  MulEquiv.ofBijective
    (centralProductMulHom H K hKcentral)
    ((Subgroup.isComplement_iff_bijective H K).mp hcomplement)

@[simp]
theorem complementaryCentralProductMulEquiv_apply
    (H K : Subgroup G)
    (hcomplement : H.IsComplement' K)
    (hKcentral : K ≤ Subgroup.center G)
    (x : H × K) :
    complementaryCentralProductMulEquiv H K hcomplement hKcentral x =
      (x.1 : G) * (x.2 : G) :=
  rfl

variable [Finite G] {p : ℕ} [Fact p.Prime]

omit [Finite G] in
/-- A central subgroup has full centralizer, hence in particular its
normalizer centralizes it. -/
theorem normalizer_le_centralizer_of_le_center
    (P : Subgroup G)
    (hPcentral : P ≤ Subgroup.center G) :
    Subgroup.normalizer P ≤ Subgroup.centralizer (P : Set G) := by
  rw [Subgroup.centralizer_eq_top_iff_subset.mpr hPcentral]
  exact le_top

/-- The canonical normal `p`-complement supplied by Burnside transfer for a
central Sylow subgroup. -/
def centralSylowComplement
    (P : Sylow p G)
    (hPcentral : (P : Subgroup G) ≤ Subgroup.center G) :
    Subgroup G :=
  (MonoidHom.transferSylow P
    (normalizer_le_centralizer_of_le_center
      (P : Subgroup G) hPcentral)).ker

instance centralSylowComplement_normal
    (P : Sylow p G)
    (hPcentral : (P : Subgroup G) ≤ Subgroup.center G) :
    (centralSylowComplement P hPcentral).Normal :=
  (MonoidHom.transferSylow P
    (normalizer_le_centralizer_of_le_center
      (P : Subgroup G) hPcentral)).normal_ker

/-- The Burnside-transfer complement and the central Sylow subgroup are
complementary subgroups. -/
theorem centralSylowComplement_isComplement'
    (P : Sylow p G)
    (hPcentral : (P : Subgroup G) ≤ Subgroup.center G) :
    (centralSylowComplement P hPcentral).IsComplement' P :=
  MonoidHom.ker_transferSylow_isComplement' P
    (normalizer_le_centralizer_of_le_center
      (P : Subgroup G) hPcentral)

/-- The Burnside-transfer complement has order prime to `p`. -/
theorem not_dvd_card_centralSylowComplement
    (P : Sylow p G)
    (hPcentral : (P : Subgroup G) ≤ Subgroup.center G) :
    ¬p ∣ Nat.card (centralSylowComplement P hPcentral) :=
  MonoidHom.not_dvd_card_ker_transferSylow P
    (normalizer_le_centralizer_of_le_center
      (P : Subgroup G) hPcentral)

/-- For a central Sylow subgroup, the transfer complement is exactly the
`p′`-core.  This identifies the canonical construction with a
characteristic subgroup, which is important when an ambient group acts by
automorphisms. -/
theorem centralSylowComplement_eq_pPrimeCore
    (P : Sylow p G)
    (hPcentral : (P : Subgroup G) ≤ Subgroup.center G) :
    centralSylowComplement P hPcentral =
      pPrimeCore p G := by
  apply le_antisymm
  · exact le_pPrimeCore
      ((isPPrimeGroup_iff_not_dvd
        (Fact.out : p.Prime)).mpr
          (not_dvd_card_centralSylowComplement P hPcentral))
      inferInstance
  · intro x hx
    let H := centralSylowComplement P hPcentral
    have hHcore : H ≤ pPrimeCore p G :=
      le_pPrimeCore
        ((isPPrimeGroup_iff_not_dvd
          (Fact.out : p.Prime)).mpr
            (not_dvd_card_centralSylowComplement P hPcentral))
        inferInstance
    obtain ⟨y, hy⟩ :=
      (centralSylowComplement_isComplement'
        P hPcentral).2 x
    rcases y with ⟨h, z⟩
    have hzcore : (z : G) ∈ pPrimeCore p G := by
      have hhcore : (h : G) ∈ pPrimeCore p G :=
        hHcore h.2
      have hzEq : (z : G) = (h : G)⁻¹ * x := by
        rw [← hy]
        group
      rw [hzEq]
      exact mul_mem (inv_mem hhcore) hx
    have hzbot :
        (z : G) ∈
          pPrimeCore p G ⊓ (P : Subgroup G) :=
      ⟨hzcore, z.2⟩
    have hzOne : (z : G) = 1 := by
      rw [pPrimeCore_inf_sylow_eq_bot P] at hzbot
      exact Subgroup.mem_bot.mp hzbot
    change x ∈ H
    rw [← hy]
    change (h : G) * (z : G) ∈ H
    rw [hzOne, mul_one]
    exact h.2

instance centralSylowComplement_characteristic
    (P : Sylow p G)
    (hPcentral : (P : Subgroup G) ≤ Subgroup.center G) :
    (centralSylowComplement P hPcentral).Characteristic := by
  rw [centralSylowComplement_eq_pPrimeCore P hPcentral]
  infer_instance

/-- A finite group with a central Sylow subgroup is the direct product of
its canonical normal `p`-complement and that Sylow subgroup. -/
def centralSylowProductEquiv
    (P : Sylow p G)
    (hPcentral : (P : Subgroup G) ≤ Subgroup.center G) :
    centralSylowComplement P hPcentral × P ≃* G :=
  complementaryCentralProductMulEquiv
    (centralSylowComplement P hPcentral)
    P
    (centralSylowComplement_isComplement' P hPcentral)
    hPcentral

@[simp]
theorem centralSylowProductEquiv_apply
    (P : Sylow p G)
    (hPcentral : (P : Subgroup G) ≤ Subgroup.center G)
    (x : centralSylowComplement P hPcentral × P) :
    centralSylowProductEquiv P hPcentral x =
      (x.1 : G) * (x.2 : G) :=
  rfl

end GroupTheory
end McKayConjecture
