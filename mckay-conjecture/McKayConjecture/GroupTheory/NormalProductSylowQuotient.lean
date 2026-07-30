/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.SylowQuotient

/-!
# A normal product as the full preimage of a quotient Sylow subgroup

Let `K` be normal in a finite group `G`, and let `S` be a Sylow
`p`-subgroup of `G`.  The image of `S` in `G ⧸ K` is Sylow.  Its full
preimage is exactly `K ⊔ S`; consequently, normality of the normal product
`K ⊔ S` makes the quotient Sylow subgroup normal.

These small wrappers put the subgroup correspondence identities used by the
normal-product character argument into directly reusable form.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- The image of an ambient Sylow subgroup in a quotient by a normal
subgroup, named for its normal-product application. -/
abbrev normalProductQuotientSylow
    (K : Subgroup G) [K.Normal] (S : Sylow p G) :
    Sylow p (G ⧸ K) :=
  Sylow.mapQuotient S K

@[simp, norm_cast]
theorem coe_normalProductQuotientSylow
    (K : Subgroup G) [K.Normal] (S : Sylow p G) :
    (normalProductQuotientSylow K S : Subgroup (G ⧸ K)) =
      (S : Subgroup G).map (QuotientGroup.mk' K) :=
  rfl

/-- The normal product and the image Sylow have the same image in the
quotient by the normal factor. -/
theorem map_normalProduct_eq_normalProductQuotientSylow
    (K : Subgroup G) [K.Normal] (S : Sylow p G) :
    (K ⊔ (S : Subgroup G)).map (QuotientGroup.mk' K) =
      (normalProductQuotientSylow K S :
        Subgroup (G ⧸ K)) := by
  rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  rfl

/-- The full preimage of the quotient Sylow is the normal product
`K ⊔ S`. -/
@[simp]
theorem comap_normalProductQuotientSylow
    (K : Subgroup G) [K.Normal] (S : Sylow p G) :
    (normalProductQuotientSylow K S :
        Subgroup (G ⧸ K)).comap (QuotientGroup.mk' K) =
      K ⊔ (S : Subgroup G) := by
  exact QuotientGroup.comap_map_mk' K (S : Subgroup G)

/-- Normality of `K ⊔ S` descends to the image Sylow in `G ⧸ K`. -/
theorem normalProductQuotientSylow_normal
    (K : Subgroup G) [K.Normal] (S : Sylow p G)
    (hKS : (K ⊔ (S : Subgroup G)).Normal) :
    (normalProductQuotientSylow K S :
      Subgroup (G ⧸ K)).Normal := by
  rw [← map_normalProduct_eq_normalProductQuotientSylow K S]
  exact hKS.map
    (QuotientGroup.mk' K)
    (QuotientGroup.mk'_surjective K)

/-- Normality of the quotient Sylow is equivalent to normality of its full
preimage `K ⊔ S`. -/
theorem normalProductQuotientSylow_normal_iff
    (K : Subgroup G) [K.Normal] (S : Sylow p G) :
    (normalProductQuotientSylow K S :
        Subgroup (G ⧸ K)).Normal ↔
      (K ⊔ (S : Subgroup G)).Normal := by
  constructor
  · intro h
    rw [← comap_normalProductQuotientSylow K S]
    exact h.comap (QuotientGroup.mk' K)
  · exact normalProductQuotientSylow_normal K S

/-- The quotient map from the normal product onto the image Sylow
subgroup. -/
def normalProductQuotientProjection
    (K : Subgroup G) [K.Normal] (S : Sylow p G) :
    ↥(K ⊔ (S : Subgroup G)) →*
      ↥(normalProductQuotientSylow K S :
        Subgroup (G ⧸ K)) where
  toFun x :=
    ⟨QuotientGroup.mk' K (x : G), by
      rw [← map_normalProduct_eq_normalProductQuotientSylow K S]
      exact ⟨x, x.property, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' _ _ := rfl

@[simp]
theorem normalProductQuotientProjection_apply
    (K : Subgroup G) [K.Normal] (S : Sylow p G)
    (x : ↥(K ⊔ (S : Subgroup G))) :
    ((normalProductQuotientProjection K S x :
        normalProductQuotientSylow K S) : G ⧸ K) =
      QuotientGroup.mk' K (x : G) :=
  rfl

/-- The normal-product quotient projection is onto the quotient Sylow. -/
theorem normalProductQuotientProjection_surjective
    (K : Subgroup G) [K.Normal] (S : Sylow p G) :
    Function.Surjective
      (normalProductQuotientProjection K S) := by
  intro y
  have hy :
    (y : G ⧸ K) ∈
      (S : Subgroup G).map (QuotientGroup.mk' K) :=
    y.property
  obtain ⟨s, hs, hsy⟩ := hy
  refine
    ⟨⟨s, (show
        (S : Subgroup G) ≤ K ⊔ (S : Subgroup G) from
        le_sup_right) hs⟩, ?_⟩
  apply Subtype.ext
  exact hsy

/-- The kernel of the normal-product quotient projection is the normal
factor, regarded inside `K ⊔ S`. -/
theorem ker_normalProductQuotientProjection
    (K : Subgroup G) [K.Normal] (S : Sylow p G) :
    (normalProductQuotientProjection K S).ker =
      K.subgroupOf (K ⊔ (S : Subgroup G)) := by
  ext x
  constructor
  · intro hx
    change normalProductQuotientProjection K S x = 1 at hx
    have hx' :=
      congrArg
        (fun z :
          ↥(normalProductQuotientSylow K S :
            Subgroup (G ⧸ K)) =>
          (z : G ⧸ K))
        hx
    change QuotientGroup.mk' K (x : G) = 1 at hx'
    exact (QuotientGroup.eq_one_iff (x : G)).mp hx'
  · intro hx
    change (x : G) ∈ K at hx
    change normalProductQuotientProjection K S x = 1
    apply Subtype.ext
    change QuotientGroup.mk' K (x : G) = 1
    exact (QuotientGroup.eq_one_iff (x : G)).mpr hx

/-- The canonical equivalence from the normal-product quotient to the
image Sylow subgroup in the ambient quotient.

The construction factors through the range of
`normalProductQuotientProjection`, so it is the first isomorphism theorem
equivalence rather than an arbitrary cardinality argument. -/
def normalProductQuotientEquiv
    (K : Subgroup G) [K.Normal] (S : Sylow p G) :
    ↥(K ⊔ (S : Subgroup G)) ⧸
        K.subgroupOf (K ⊔ (S : Subgroup G)) ≃*
      ↥(normalProductQuotientSylow K S :
        Subgroup (G ⧸ K)) := by
  let f := normalProductQuotientProjection K S
  have hker :
      K.subgroupOf (K ⊔ (S : Subgroup G)) = f.ker :=
    (ker_normalProductQuotientProjection K S).symm
  have hrange : f.range = ⊤ :=
    MonoidHom.range_eq_top.mpr
      (normalProductQuotientProjection_surjective K S)
  exact
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      ((QuotientGroup.quotientKerEquivRange f).trans
        ((MulEquiv.subgroupCongr hrange).trans
          Subgroup.topEquiv))

@[simp]
theorem normalProductQuotientEquiv_mk
    (K : Subgroup G) [K.Normal] (S : Sylow p G)
    (x : ↥(K ⊔ (S : Subgroup G))) :
    normalProductQuotientEquiv K S
        (QuotientGroup.mk' (K.subgroupOf
          (K ⊔ (S : Subgroup G))) x) =
      normalProductQuotientProjection K S x := by
  rfl

/-- Homomorphism-level form of the representative formula for the
normal-product quotient equivalence. -/
@[simp]
theorem normalProductQuotientEquiv_comp_quotientMk
    (K : Subgroup G) [K.Normal] (S : Sylow p G) :
    (normalProductQuotientEquiv K S).toMonoidHom.comp
        (QuotientGroup.mk' (K.subgroupOf
          (K ⊔ (S : Subgroup G)))) =
      normalProductQuotientProjection K S := by
  apply MonoidHom.ext
  intro x
  exact normalProductQuotientEquiv_mk K S x

/-- On representatives, the normal-product quotient equivalence is the
ambient quotient map. -/
@[simp]
theorem coe_normalProductQuotientEquiv_mk
    (K : Subgroup G) [K.Normal] (S : Sylow p G)
    (x : ↥(K ⊔ (S : Subgroup G))) :
    ((normalProductQuotientEquiv K S
        (QuotientGroup.mk' (K.subgroupOf
          (K ⊔ (S : Subgroup G))) x) :
        normalProductQuotientSylow K S) : G ⧸ K) =
      QuotientGroup.mk' K (x : G) := by
  rw [normalProductQuotientEquiv_mk,
    normalProductQuotientProjection_apply]

end GroupTheory
end McKayConjecture
