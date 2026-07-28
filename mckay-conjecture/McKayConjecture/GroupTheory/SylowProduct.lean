/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Sylow
import McKayConjecture.Statement

/-!
# Sylow subgroups and normalizers of direct products

The direct product of Sylow `p`-subgroups is Sylow in the direct product.
Its normalizer is the direct product of the two factor normalizers.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

variable {G H : Type u} [Group G] [Group H]
variable {p : ℕ}

/-- The direct product of two Sylow `p`-subgroups. -/
def sylowProduct
    [Finite G] [Finite H] [Fact p.Prime]
    (P : Sylow p G) (Q : Sylow p H) :
    Sylow p (G × H) where
  toSubgroup := (P : Subgroup G).prod (Q : Subgroup H)
  isPGroup' := by
    rw [IsPGroup.iff_card]
    obtain ⟨m, hm⟩ :=
      IsPGroup.iff_card.mp P.isPGroup'
    obtain ⟨n, hn⟩ :=
      IsPGroup.iff_card.mp Q.isPGroup'
    refine ⟨m + n, ?_⟩
    rw [Nat.card_congr
      (Subgroup.prodEquiv
        (P : Subgroup G) (Q : Subgroup H)).toEquiv,
      Nat.card_prod, hm, hn, pow_add]
  is_maximal' := by
    intro R hR hprodR
    apply le_antisymm
    · intro z hz
      have hfstP :
          (P : Subgroup G) ≤
            R.map (MonoidHom.fst G H) := by
        intro x hx
        refine ⟨(x, 1), hprodR ?_, rfl⟩
        exact Subgroup.mem_prod.mpr
          ⟨hx, (Q : Subgroup H).one_mem⟩
      have hsndQ :
          (Q : Subgroup H) ≤
            R.map (MonoidHom.snd G H) := by
        intro y hy
        refine ⟨(1, y), hprodR ?_, rfl⟩
        exact Subgroup.mem_prod.mpr
          ⟨(P : Subgroup G).one_mem, hy⟩
      have hfstEq :
          R.map (MonoidHom.fst G H) = P :=
        P.is_maximal' (hR.map (MonoidHom.fst G H))
          hfstP
      have hsndEq :
          R.map (MonoidHom.snd G H) = Q :=
        Q.is_maximal' (hR.map (MonoidHom.snd G H))
          hsndQ
      apply Subgroup.mem_prod.mpr
      constructor
      · rw [← hfstEq]
        exact ⟨z, hz, rfl⟩
      · rw [← hsndEq]
        exact ⟨z, hz, rfl⟩
    · exact hprodR

@[simp]
theorem coe_sylowProduct
    [Finite G] [Finite H] [Fact p.Prime]
    (P : Sylow p G) (Q : Sylow p H) :
    (sylowProduct P Q : Subgroup (G × H)) =
      (P : Subgroup G).prod (Q : Subgroup H) :=
  rfl

/-- The normalizer of a product subgroup is the product of the
normalizers. -/
theorem normalizer_prod
    (A : Subgroup G) (B : Subgroup H) :
    Subgroup.normalizer (A.prod B : Set (G × H)) =
      (Subgroup.normalizer (A : Set G)).prod
        (Subgroup.normalizer (B : Set H)) := by
  ext z
  constructor
  · intro hz
    apply Subgroup.mem_prod.mpr
    constructor
    · rw [Subgroup.mem_normalizer_iff]
      intro x
      have h :=
        (Subgroup.mem_normalizer_iff.mp hz) (x, 1)
      simpa [Subgroup.mem_prod] using h
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      have h :=
        (Subgroup.mem_normalizer_iff.mp hz) (1, y)
      simpa [Subgroup.mem_prod] using h
  · intro hz
    obtain ⟨hzg, hzh⟩ :=
      Subgroup.mem_prod.mp hz
    rw [Subgroup.mem_normalizer_iff] at hzg hzh ⊢
    intro x
    exact and_congr (hzg x.1) (hzh x.2)

/-- The normalizer of a Sylow product, as a group, is naturally isomorphic
to the product of the two factor normalizers. -/
def sylowProductNormalizerEquiv
    [Finite G] [Finite H] [Fact p.Prime]
    (P : Sylow p G) (Q : Sylow p H) :
    SylowNormalizer (sylowProduct P Q) ≃*
      SylowNormalizer P × SylowNormalizer Q :=
  (MulEquiv.subgroupCongr (by
      change
        Subgroup.normalizer
            ((P : Subgroup G).prod
              (Q : Subgroup H) : Set (G × H)) =
          (Subgroup.normalizer (P : Set G)).prod
            (Subgroup.normalizer (Q : Set H))
      exact normalizer_prod
        (P : Subgroup G) (Q : Subgroup H))).trans
    (Subgroup.prodEquiv
      (Subgroup.normalizer (P : Set G))
      (Subgroup.normalizer (Q : Set H)))

end GroupTheory
end McKayConjecture
