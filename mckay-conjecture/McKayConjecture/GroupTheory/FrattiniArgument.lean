/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.PPrimeCore
import McKayConjecture.GroupTheory.SylowQuotient

/-!
# The Frattini argument

Let `N` be a normal subgroup of a finite group `G`, and let `Q` be a
Sylow `p`-subgroup of `N`.  The Frattini argument says that

`G = N N_G(Q)`.

Here `Q` is first mapped from `N` into the ambient group.  Besides the
subgroup and product forms of the argument, this file records the exact
transport of its normalizer, the induced quotient isomorphism

`N_G(Q) / N_N(Q) ≃ G / N`,

and the corresponding index and cardinality identities.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory
namespace Sylow

open scoped Pointwise

variable {G : Type u} [Group G]
variable {p : ℕ}
variable {N : Subgroup G}

/-- A Sylow subgroup of a normal subgroup, mapped into the ambient
group. -/
def ambientSubgroup (Q : Sylow p N) : Subgroup G :=
  (Q : Subgroup N).map N.subtype

@[simp]
theorem coe_ambientSubgroup (Q : Sylow p N) :
    ambientSubgroup Q =
      (Q : Subgroup N).map N.subtype :=
  rfl

/-- The ambient copy of `Q` is contained in `N`. -/
theorem ambientSubgroup_le (Q : Sylow p N) :
    ambientSubgroup Q ≤ N := by
  exact
    (Subgroup.map_le_range
      N.subtype (Q : Subgroup N)).trans_eq
        N.range_subtype

/-- Pulling the ambient copy of `Q` back to `N` recovers `Q`. -/
@[simp]
theorem comap_ambientSubgroup (Q : Sylow p N) :
    (ambientSubgroup Q).comap N.subtype =
      (Q : Subgroup N) := by
  rw [ambientSubgroup,
    Subgroup.comap_map_eq_self_of_injective
      N.subtype_injective]

/-- The ambient copy of `Q` has the same order as `Q`. -/
theorem card_ambientSubgroup (Q : Sylow p N) :
    Nat.card (ambientSubgroup Q) =
      Nat.card Q :=
  Subgroup.card_map_of_injective
    N.subtype_injective

/-- Mapping a Sylow subgroup of `N` into `G` is injective. -/
theorem ambientSubgroup_injective :
    Function.Injective
      (ambientSubgroup :
        Sylow p N → Subgroup G) := by
  intro Q R h
  rw [Sylow.ext_iff]
  have hcomap :=
    congrArg
      (Subgroup.comap N.subtype) h
  change
    (ambientSubgroup Q).comap N.subtype =
      (ambientSubgroup R).comap N.subtype
    at hcomap
  simpa only [comap_ambientSubgroup]
    using hcomap

/-- Normalizer transport along the inclusion `N ↪ G`: the elements of
`N` that normalize the ambient copy of `Q` are exactly `N_N(Q)`. -/
theorem comap_normalizer_ambientSubgroup
    (Q : Sylow p N) :
    (Subgroup.normalizer
        (ambientSubgroup Q : Set G)).comap
          N.subtype =
      Subgroup.normalizer (Q : Set N) := by
  calc
    (Subgroup.normalizer
        (ambientSubgroup Q : Set G)).comap
          N.subtype =
        Subgroup.normalizer
          ((ambientSubgroup Q).comap
            N.subtype) :=
      Subgroup.comap_normalizer_eq_of_le_range
        (Subgroup.map_le_range
          N.subtype (Q : Subgroup N))
    _ = Subgroup.normalizer
          (Q : Set N) := by
      rw [comap_ambientSubgroup, Q.coe_coe]

/-- Mapping `N_N(Q)` into `G` gives the intersection
`N ∩ N_G(Q)`. -/
theorem map_normalizer_eq_inf_ambientNormalizer
    (Q : Sylow p N) :
    (Subgroup.normalizer (Q : Set N)).map
        N.subtype =
      Subgroup.normalizer
          (ambientSubgroup Q : Set G) ⊓
        N := by
  rw [← comap_normalizer_ambientSubgroup Q,
    Subgroup.map_comap_eq,
    N.range_subtype, inf_comm]

/-- The intrinsic normalizer `N_N(Q)` is naturally isomorphic to the
intersection `N ∩ N_G(Q)`, with the latter viewed as a subgroup of the
ambient normalizer. -/
def normalizerEquivAmbientIntersection
    (Q : Sylow p N) :
    Subgroup.normalizer (Q : Set N) ≃*
      N.subgroupOf
        (Subgroup.normalizer
          (ambientSubgroup Q : Set G)) where
  toFun x := by
    have hx :
        (x : N) ∈
          (Subgroup.normalizer
            (ambientSubgroup Q :
              Set G)).comap N.subtype := by
      rw [comap_normalizer_ambientSubgroup Q]
      exact x.property
    exact
      ⟨⟨(x : G), hx⟩, x.1.property⟩
  invFun x := by
    let xN : N :=
      ⟨(x : G), x.property⟩
    have hx :
        xN ∈
          Subgroup.normalizer
            (Q : Set N) := by
      rw [← comap_normalizer_ambientSubgroup Q]
      exact x.1.property
    exact ⟨xN, hx⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    rfl

@[simp]
theorem normalizerEquivAmbientIntersection_apply_coe
    (Q : Sylow p N)
    (x : Subgroup.normalizer (Q : Set N)) :
    (((normalizerEquivAmbientIntersection
          Q x :
        N.subgroupOf
          (Subgroup.normalizer
            (ambientSubgroup Q :
              Set G))) :
      Subgroup.normalizer
        (ambientSubgroup Q : Set G)) :
      G) =
        (x : N) :=
  rfl

/-- Cardinality form of the intrinsic/ambient normalizer transport. -/
theorem card_normalizer_eq_card_ambientIntersection
    (Q : Sylow p N) :
    Nat.card
        (Subgroup.normalizer (Q : Set N)) =
      Nat.card
        (N.subgroupOf
          (Subgroup.normalizer
            (ambientSubgroup Q : Set G))) :=
  Nat.card_congr
    (normalizerEquivAmbientIntersection Q).toEquiv

section Normal

variable [N.Normal]

/-- Conjugation by an ambient element acts on the Sylow subgroups of
the normal subgroup `N`. -/
def ambientConj (g : G) (Q : Sylow p N) :
    Sylow p N :=
  (MulAut.conjNormal (H := N) g) • Q

/-- Mapping an ambient conjugate into `G` agrees with conjugating the
mapped subgroup in `G`. -/
theorem ambientSubgroup_ambientConj
    (g : G) (Q : Sylow p N) :
    ambientSubgroup (ambientConj g Q) =
      (ambientSubgroup Q).map
        (MulAut.conj g).toMonoidHom := by
  let eN : N →* N :=
    MulDistribMulAction.toMonoidEnd
      (MulAut N) N
      (MulAut.conjNormal (H := N) g)
  have hcomp :
      N.subtype.comp eN =
        (MulAut.conj g).toMonoidHom.comp
          N.subtype := by
    ext x
    rfl
  change
    (((Q : Subgroup N).map eN).map
        N.subtype) =
      ((Q : Subgroup N).map N.subtype).map
        (MulAut.conj g).toMonoidHom
  calc
    ((Q : Subgroup N).map eN).map
          N.subtype =
        (Q : Subgroup N).map
          (N.subtype.comp eN) :=
      Subgroup.map_map
        (Q : Subgroup N) N.subtype eN
    _ = (Q : Subgroup N).map
          ((MulAut.conj g).toMonoidHom.comp
            N.subtype) := by
      rw [hcomp]
    _ = ((Q : Subgroup N).map
          N.subtype).map
            (MulAut.conj g).toMonoidHom :=
      (Subgroup.map_map
        (Q : Subgroup N)
        (MulAut.conj g).toMonoidHom
        N.subtype).symm

/-- The stabilizer of `Q` under ambient conjugation is its ambient
normalizer. -/
theorem ambientConj_eq_iff_mem_ambientNormalizer
    (g : G) (Q : Sylow p N) :
    ambientConj g Q = Q ↔
      g ∈ Subgroup.normalizer
        (ambientSubgroup Q : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  constructor
  · intro h
    calc
      (ambientSubgroup Q).map
          (MulAut.conj g).toMonoidHom =
        ambientSubgroup (ambientConj g Q) :=
          (ambientSubgroup_ambientConj g Q).symm
      _ = ambientSubgroup Q :=
        congrArg ambientSubgroup h
  · intro h
    apply ambientSubgroup_injective
    exact
      (ambientSubgroup_ambientConj g Q).trans h

/-- A characteristic subgroup of `N` is normal in `G` after mapping
into `G`, provided `N` is normal in `G`. -/
theorem ambientSubgroup_normal_of_characteristic
    (Q : Sylow p N)
    (hQ : (Q : Subgroup N).Characteristic) :
    (ambientSubgroup Q).Normal := by
  letI : (Q : Subgroup N).Characteristic :=
    hQ
  change
    ((Q : Subgroup N).map
      N.subtype).Normal
  exact inferInstance

omit [N.Normal] in
/-- Characteristicity is transitive through the ambient embedding. -/
theorem ambientSubgroup_characteristic_of_characteristic
    (Q : Sylow p N)
    (hN : N.Characteristic)
    (hQ : (Q : Subgroup N).Characteristic) :
    (ambientSubgroup Q).Characteristic := by
  letI : N.Characteristic := hN
  letI : (Q : Subgroup N).Characteristic :=
    hQ
  change
    ((Q : Subgroup N).map
      N.subtype).Characteristic
  exact inferInstance

variable [Finite G] [Fact p.Prime]

/-- A Sylow subgroup normal in `N` is normal in the whole ambient
group: normality makes it the unique Sylow subgroup of `N`, hence
characteristic in `N`. -/
theorem ambientSubgroup_normal_of_normal
    (Q : Sylow p N)
    (hQ : (Q : Subgroup N).Normal) :
    (ambientSubgroup Q).Normal := by
  letI : (Q : Subgroup N).Characteristic :=
    Sylow.characteristic_of_normal Q hQ
  change
    ((Q : Subgroup N).map
      N.subtype).Normal
  exact inferInstance

/-- For a Sylow subgroup of a normal subgroup, normality in `N` is
equivalent to normality of its ambient copy in `G`. -/
theorem ambientSubgroup_normal_iff_normal
    (Q : Sylow p N) :
    (ambientSubgroup Q).Normal ↔
      (Q : Subgroup N).Normal := by
  constructor
  · intro hQ
    have hcomap :=
      Subgroup.Normal.comap hQ N.subtype
    simpa only [comap_ambientSubgroup]
      using hcomap
  · exact ambientSubgroup_normal_of_normal Q

omit [N.Normal] in
/-- For finite groups a Sylow subgroup is characteristic exactly when
it is normal. -/
theorem sylow_characteristic_iff_normal
    (Q : Sylow p N) :
    (Q : Subgroup N).Characteristic ↔
      (Q : Subgroup N).Normal := by
  constructor
  · intro hQ
    letI : (Q : Subgroup N).Characteristic :=
      hQ
    exact inferInstance
  · exact Sylow.characteristic_of_normal Q

/-- The ambient normalizer is all of `G` exactly when `Q` is normal in
`N`. -/
theorem ambientNormalizer_eq_top_iff_normal
    (Q : Sylow p N) :
    Subgroup.normalizer
          (ambientSubgroup Q : Set G) =
        ⊤ ↔
      (Q : Subgroup N).Normal := by
  rw [Subgroup.normalizer_eq_top_iff]
  exact ambientSubgroup_normal_iff_normal Q

/-- **Frattini argument**, in subgroup form. -/
theorem frattiniArgument (Q : Sylow p N) :
    N ⊔
        Subgroup.normalizer
          (ambientSubgroup Q : Set G) =
      ⊤ := by
  rw [sup_comm]
  exact Sylow.normalizer_sup_eq_top Q

/-- The original normalizer-first form of the Frattini argument. -/
theorem ambientNormalizer_sup_eq_top
    (Q : Sylow p N) :
    Subgroup.normalizer
          (ambientSubgroup Q : Set G) ⊔
        N =
      ⊤ :=
  Sylow.normalizer_sup_eq_top Q

/-- **Frattini argument**, as the set-product identity
`G = N N_G(Q)`. -/
theorem frattiniArgument_set_product
    (Q : Sylow p N) :
    (N : Set G) *
        (Subgroup.normalizer
          (ambientSubgroup Q : Set G) :
          Set G) =
      (⊤ : Subgroup G) := by
  rw [← Subgroup.normal_mul,
    frattiniArgument Q]

/-- Every ambient element can be adjusted on the left by an element of
`N` to normalize `Q`. -/
theorem exists_left_adjustment_mem_ambientNormalizer
    (Q : Sylow p N) (g : G) :
    ∃ n : N,
      (n : G)⁻¹ * g ∈
        Subgroup.normalizer
          (ambientSubgroup Q : Set G) := by
  have hg :
      g ∈
        N ⊔
          Subgroup.normalizer
            (ambientSubgroup Q : Set G) := by
    rw [frattiniArgument Q]
    trivial
  obtain ⟨n, hn, x, hx, hnx⟩ :=
    Subgroup.mem_sup_of_normal_left.mp hg
  exact
    ⟨⟨n, hn⟩, by
      rw [← hnx]
      simpa using hx⟩

/-- The quotient map restricted to the ambient normalizer in the
Frattini argument. -/
def frattiniQuotientHom (Q : Sylow p N) :
    Subgroup.normalizer
        (ambientSubgroup Q : Set G) →*
      G ⧸ N :=
  (QuotientGroup.mk' N).domRestrict
    (Subgroup.normalizer
      (ambientSubgroup Q : Set G))

omit [Finite G] [Fact p.Prime] in
@[simp]
theorem frattiniQuotientHom_apply_coe
    (Q : Sylow p N)
    (x : Subgroup.normalizer
      (ambientSubgroup Q : Set G)) :
    frattiniQuotientHom Q x =
      QuotientGroup.mk' N x :=
  rfl

/-- The Frattini quotient homomorphism is surjective. -/
theorem frattiniQuotientHom_surjective
    (Q : Sylow p N) :
    Function.Surjective
      (frattiniQuotientHom Q) := by
  intro y
  obtain ⟨g, rfl⟩ :=
    QuotientGroup.mk'_surjective N y
  obtain ⟨n, hn⟩ :=
    exists_left_adjustment_mem_ambientNormalizer
      Q g
  refine
    ⟨⟨(n : G)⁻¹ * g, hn⟩, ?_⟩
  change
    QuotientGroup.mk' N
        ((n : G)⁻¹ * g) =
      QuotientGroup.mk' N g
  rw [map_mul]
  have hnOne :
      QuotientGroup.mk' N
          ((n : G)⁻¹) =
        1 :=
    (QuotientGroup.eq_one_iff
      ((n : G)⁻¹)).mpr
        (N.inv_mem n.property)
  rw [hnOne, one_mul]

omit [Finite G] [Fact p.Prime] in
/-- The kernel of the Frattini quotient homomorphism is
`N ∩ N_G(Q)`, viewed inside `N_G(Q)`. -/
theorem frattiniQuotientHom_ker
    (Q : Sylow p N) :
    (frattiniQuotientHom Q).ker =
      N.subgroupOf
        (Subgroup.normalizer
          (ambientSubgroup Q : Set G)) := by
  ext x
  rw [MonoidHom.mem_ker,
    Subgroup.mem_subgroupOf]
  change
    QuotientGroup.mk' N (x : G) = 1 ↔
      (x : G) ∈ N
  exact QuotientGroup.eq_one_iff (x : G)

/-- The quotient form of the Frattini argument:
`N_G(Q) / N_N(Q) ≃ G / N`. -/
def frattiniQuotientEquiv (Q : Sylow p N) :
    (Subgroup.normalizer
          (ambientSubgroup Q : Set G) ⧸
        N.subgroupOf
          (Subgroup.normalizer
            (ambientSubgroup Q : Set G))) ≃*
      G ⧸ N :=
  (QuotientGroup.quotientMulEquivOfEq
      (frattiniQuotientHom_ker Q).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (frattiniQuotientHom Q)
      (frattiniQuotientHom_surjective Q))

@[simp]
theorem frattiniQuotientEquiv_mk
    (Q : Sylow p N)
    (x : Subgroup.normalizer
      (ambientSubgroup Q : Set G)) :
    frattiniQuotientEquiv Q
        (QuotientGroup.mk x) =
      QuotientGroup.mk' N x := by
  rw [frattiniQuotientEquiv,
    MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  change
    QuotientGroup.kerLift
        (frattiniQuotientHom Q)
        (QuotientGroup.mk x) =
      QuotientGroup.mk' N x
  rw [QuotientGroup.kerLift_mk]
  rfl

/-- Cardinality form of the Frattini quotient isomorphism. -/
theorem card_frattiniNormalizer_quotient
    (Q : Sylow p N) :
    Nat.card
        (Subgroup.normalizer
            (ambientSubgroup Q : Set G) ⧸
          N.subgroupOf
            (Subgroup.normalizer
              (ambientSubgroup Q : Set G))) =
      Nat.card (G ⧸ N) :=
  Nat.card_congr
    (frattiniQuotientEquiv Q).toEquiv

/-- Index form of the Frattini argument:
`[G : N] = [N_G(Q) : N_N(Q)]`. -/
theorem index_eq_relIndex_ambientNormalizer
    (Q : Sylow p N) :
    N.index =
      N.relIndex
        (Subgroup.normalizer
          (ambientSubgroup Q : Set G)) := by
  rw [← N.relIndex_top_right,
    ← ambientNormalizer_sup_eq_top Q,
    Subgroup.relIndex_sup_right]

/-- Cardinality product form of the Frattini argument. -/
theorem card_mul_card_ambientNormalizer
    (Q : Sylow p N) :
    Nat.card N *
        Nat.card
          (Subgroup.normalizer
            (ambientSubgroup Q : Set G)) =
      Nat.card G *
        Nat.card (
          Subgroup.normalizer
              (ambientSubgroup Q : Set G) ⊓
            N : Subgroup G) := by
  let H : Subgroup G :=
    Subgroup.normalizer
      (ambientSubgroup Q : Set G)
  have hHcard :
      Nat.card (H ⊓ N : Subgroup G) *
          N.relIndex H =
        Nat.card H := by
    have hrel :=
      Subgroup.relIndex_mul_relIndex
        (⊥ : Subgroup G) (H ⊓ N) H
        bot_le inf_le_left
    simpa only [Subgroup.relIndex_bot_left,
      Subgroup.inf_relIndex_left]
      using hrel
  have hGcard :
      Nat.card N * N.relIndex H =
        Nat.card G := by
    rw [← index_eq_relIndex_ambientNormalizer
      Q]
    exact N.card_mul_index
  change
    Nat.card N * Nat.card H =
      Nat.card G *
        Nat.card (H ⊓ N : Subgroup G)
  calc
    Nat.card N * Nat.card H =
        Nat.card N *
          (Nat.card (H ⊓ N : Subgroup G) *
            N.relIndex H) := by
      rw [hHcard]
    _ = (Nat.card N * N.relIndex H) *
          Nat.card (H ⊓ N : Subgroup G) := by
      ac_rfl
    _ = Nat.card G *
          Nat.card (H ⊓ N : Subgroup G) := by
      rw [hGcard]

/-- The Frattini argument applied to the intersection Sylow subgroup
constructed in `SylowQuotient`. -/
theorem frattiniArgument_intersectionNormal
    (P : Sylow p G) :
    N ⊔
        Subgroup.normalizer
          (((P : Subgroup G) ⊓ N) :
            Set G) =
      ⊤ := by
  simpa [ambientSubgroup,
    map_intersectionNormal_subtype]
    using
      frattiniArgument
        (intersectionNormal P N)

/-- The Frattini argument for the normal `p′`-core. -/
theorem pPrimeCore_frattiniArgument
    (r : ℕ)
    (Q : Sylow p (pPrimeCore r G)) :
    pPrimeCore r G ⊔
        Subgroup.normalizer
          (ambientSubgroup Q : Set G) =
      ⊤ :=
  frattiniArgument Q

end Normal

end Sylow
end GroupTheory
end McKayConjecture
