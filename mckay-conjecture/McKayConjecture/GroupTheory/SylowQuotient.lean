/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Sylow

/-!
# Sylow subgroups of normal subgroups and quotients

If `N ◁ G` and `P` is a Sylow `p`-subgroup of a finite group `G`, then
`P ∩ N`, regarded as a subgroup of `N`, is Sylow in `N`, while the image
of `P` in `G ⧸ N` is Sylow in the quotient.

The quotient normalizer comparison is exact: the quotient map sends
`N_G(P)` onto the normalizer of the image Sylow subgroup.  Consequently
the latter is canonically isomorphic to
`N_G(P) / (N ∩ N_G(P))`.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

open scoped Pointwise

namespace Sylow

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

private theorem intersectionNormal_isMaximal
    (P : Sylow p G) (N : Subgroup G) [N.Normal] :
    ∀ {Q : Subgroup N},
      IsPGroup p Q →
      (P : Subgroup G).comap N.subtype ≤ Q →
      Q = (P : Subgroup G).comap N.subtype := by
  classical
  let I : Subgroup N :=
    (P : Subgroup G).comap N.subtype
  have hI : IsPGroup p I :=
    P.isPGroup'.comap_subtype
  let S : Sylow p N := Classical.choice Sylow.nonempty
  obtain ⟨R, hSR⟩ :=
    (S.isPGroup'.map N.subtype).exists_le_sylow
  obtain ⟨g, hg⟩ :=
    MulAction.exists_smul_eq G R P
  let S' : Sylow p N :=
    (MulAut.conjNormal (H := N) g) • S
  have hS'I : (S' : Subgroup N) ≤ I := by
    intro x hx
    change
      x ∈
        (MulAut.conjNormal (H := N) g) •
          (S : Subgroup N) at hx
    rw [Subgroup.pointwise_smul_def] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyR : (y : G) ∈ R :=
      hSR ⟨y, hy, rfl⟩
    have hgy :
        MulAut.conj g (y : G) ∈
          (g • R : Sylow p G) := by
      change
        MulAut.conj g (y : G) ∈
          (MulAut.conj g) •
            (R : Subgroup G)
      rw [Subgroup.pointwise_smul_def]
      exact ⟨y, hyR, rfl⟩
    rw [hg] at hgy
    exact hgy
  have hIeq : I = (S' : Subgroup N) :=
    S'.is_maximal' hI hS'I
  intro Q hQ hIQ
  change I ≤ Q at hIQ
  change Q = I
  rw [hIeq] at hIQ ⊢
  exact S'.is_maximal' hQ hIQ

/-- The intersection of a Sylow subgroup with a normal subgroup,
regarded as a Sylow subgroup of the normal subgroup. -/
def intersectionNormal
    (P : Sylow p G) (N : Subgroup G) [N.Normal] :
    Sylow p N where
  toSubgroup :=
    (P : Subgroup G).comap N.subtype
  isPGroup' :=
    P.isPGroup'.comap_subtype
  is_maximal' :=
    intersectionNormal_isMaximal P N

@[simp, norm_cast]
theorem coe_intersectionNormal
    (P : Sylow p G) (N : Subgroup G) [N.Normal] :
    (intersectionNormal P N : Subgroup N) =
      (P : Subgroup G).comap N.subtype :=
  rfl

@[simp]
theorem mem_intersectionNormal
    (P : Sylow p G) (N : Subgroup G) [N.Normal]
    (x : N) :
    x ∈ intersectionNormal P N ↔
      (x : G) ∈ P :=
  Iff.rfl

/-- Mapping the intersection Sylow subgroup back into `G` recovers
the ambient intersection `P ∩ N`. -/
theorem map_intersectionNormal_subtype
    (P : Sylow p G) (N : Subgroup G) [N.Normal] :
    (intersectionNormal P N : Subgroup N).map
        N.subtype =
      (P : Subgroup G) ⊓ N := by
  rw [coe_intersectionNormal,
    Subgroup.map_comap_eq,
    N.range_subtype, inf_comm]

/-- The intersection Sylow has the same cardinality as the ambient
intersection subgroup. -/
theorem card_intersectionNormal
    (P : Sylow p G) (N : Subgroup G) [N.Normal] :
    Nat.card (intersectionNormal P N) =
      Nat.card ↥((P : Subgroup G) ⊓ N) := by
  rw [← map_intersectionNormal_subtype P N]
  exact
    (Subgroup.card_map_of_injective
      N.subtype_injective).symm

/-- The image of a Sylow subgroup in a quotient by a normal subgroup. -/
def mapQuotient
    (P : Sylow p G) (N : Subgroup G) [N.Normal] :
    Sylow p (G ⧸ N) :=
  P.mapSurjective
    (QuotientGroup.mk'_surjective N)

@[simp, norm_cast]
theorem coe_mapQuotient
    (P : Sylow p G) (N : Subgroup G) [N.Normal] :
    (mapQuotient P N : Subgroup (G ⧸ N)) =
      (P : Subgroup G).map
        (QuotientGroup.mk' N) :=
  rfl

@[simp]
theorem mk_mem_mapQuotient
    (P : Sylow p G) (N : Subgroup G) [N.Normal]
    (g : G) :
    QuotientGroup.mk' N g ∈ mapQuotient P N ↔
      ∃ x ∈ P,
        QuotientGroup.mk' N x =
          QuotientGroup.mk' N g := by
  change
    QuotientGroup.mk' N g ∈
        (P : Subgroup G).map
          (QuotientGroup.mk' N) ↔ _
  exact Subgroup.mem_map

/-- The order of `P` factors as the orders of its intersection with `N`
and its image in `G ⧸ N`. -/
theorem card_intersectionNormal_mul_card_mapQuotient
    (P : Sylow p G) (N : Subgroup G) [N.Normal] :
    Nat.card (intersectionNormal P N) *
        Nat.card (mapQuotient P N) =
      Nat.card P := by
  let f :
      P →* G ⧸ N :=
    (QuotientGroup.mk' N).domRestrict
      (P : Subgroup G)
  have hker :
      f.ker =
        N.subgroupOf (P : Subgroup G) := by
    rw [MonoidHom.ker_domRestrict,
      QuotientGroup.ker_mk']
  have hkerCard :
      Nat.card f.ker =
        Nat.card (intersectionNormal P N) := by
    rw [hker, card_intersectionNormal]
    rw [← Subgroup.card_map_of_injective
      (K := N.subgroupOf (P : Subgroup G))
      P.toSubgroup.subtype_injective]
    congr 1
    rw [Subgroup.subgroupOf,
      Subgroup.map_comap_eq,
      P.toSubgroup.range_subtype, inf_comm]
  have hrange :
      f.range =
        (mapQuotient P N :
          Subgroup (G ⧸ N)) := by
    change
      ((QuotientGroup.mk' N).domRestrict
        (P : Subgroup G)).range =
          (mapQuotient P N :
            Subgroup (G ⧸ N))
    rw [MonoidHom.domRestrict_range,
      coe_mapQuotient]
  calc
    Nat.card (intersectionNormal P N) *
          Nat.card (mapQuotient P N) =
        Nat.card f.ker * Nat.card f.range := by
      rw [hkerCard, hrange]
    _ = Nat.card f.ker * f.ker.index := by
      rw [Subgroup.index_ker f]
    _ = Nat.card P :=
      f.ker.card_mul_index

/-! ### Normalizers -/

/-- The quotient map sends the ambient normalizer onto the normalizer
of the image Sylow subgroup. -/
theorem map_normalizer_eq_normalizer_mapQuotient
    (P : Sylow p G) (N : Subgroup G) [N.Normal] :
    (Subgroup.normalizer (P : Set G)).map
        (QuotientGroup.mk' N) =
      Subgroup.normalizer
        (mapQuotient P N :
          Set (G ⧸ N)) := by
  classical
  apply le_antisymm
  · exact
      Subgroup.le_normalizer_map
        (H := (P : Subgroup G))
        (QuotientGroup.mk' N)
  · intro q hq
    obtain ⟨g, rfl⟩ :=
      QuotientGroup.mk'_surjective N q
    have hgp :
        (g • P : Sylow p G) ≤
          (P : Subgroup G) ⊔ N := by
      intro z hz
      change
        z ∈
          (MulAut.conj g) •
            (P : Subgroup G) at hz
      rw [Subgroup.pointwise_smul_def] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      have hqx :
          QuotientGroup.mk' N x ∈
            mapQuotient P N :=
        ⟨x, hx, rfl⟩
      have hqconj :=
        (Subgroup.mem_normalizer_iff.mp hq
          (QuotientGroup.mk' N x)).mp hqx
      have hqconj' :
          ∃ a ∈ (P : Subgroup G),
            QuotientGroup.mk' N a =
              QuotientGroup.mk' N
                (g * x * g⁻¹) := by
        simpa using hqconj
      obtain ⟨a, ha, haeq⟩ :=
        hqconj'
      obtain ⟨n, hn, han⟩ :=
        (QuotientGroup.mk'_eq_mk' N).mp haeq
      exact
        Subgroup.mem_sup_of_normal_right.mpr
          ⟨a, ha, n, hn, han⟩
    let H : Subgroup G :=
      (P : Subgroup G) ⊔ N
    let Pg : Sylow p G :=
      g • P
    have hPgH : (Pg : Subgroup G) ≤ H :=
      hgp
    have hPH : (P : Subgroup G) ≤ H :=
      le_sup_left
    let PgH : Sylow p H :=
      Pg.subtype hPgH
    let PH : Sylow p H :=
      P.subtype hPH
    obtain ⟨x, hx⟩ :=
      MulAction.exists_smul_eq H PgH PH
    have hx' := hx
    change
      x • Pg.subtype hPgH =
        P.subtype hPH at hx'
    rw [Sylow.smul_subtype] at hx'
    have hxambient :
        (x : G) • Pg = P :=
      Sylow.subtype_injective hx'
    obtain ⟨a, ha, n, hn, han⟩ :=
      Subgroup.mem_sup_of_normal_right.mp
        x.property
    let y : G :=
      a⁻¹ * (x : G) * g
    have hxgNormalizer :
        (x : G) * g ∈
          Subgroup.normalizer (P : Set G) := by
      rw [← Sylow.smul_eq_iff_mem_normalizer]
      simpa [Pg, mul_smul] using hxambient
    have hyNormalizer :
        y ∈
          Subgroup.normalizer (P : Set G) := by
      dsimp [y]
      rw [mul_assoc]
      exact
        (Subgroup.normalizer
          (P : Set G)).mul_mem
          (Subgroup.le_normalizer
            (P.toSubgroup.inv_mem ha))
          hxgNormalizer
    refine ⟨y, hyNormalizer, ?_⟩
    simpa [y, ← han, mul_assoc] using hn

/-- Elements of `N` that normalize `P` also normalize the intersection
Sylow subgroup inside `N`.  Equality need not hold in general. -/
theorem comap_normalizer_le_normalizer_intersectionNormal
    (P : Sylow p G) (N : Subgroup G) [N.Normal] :
    (Subgroup.normalizer (P : Set G)).comap
        N.subtype ≤
      Subgroup.normalizer
        (intersectionNormal P N : Set N) := by
  change
    (Subgroup.normalizer
        (P : Subgroup G)).comap N.subtype ≤
      Subgroup.normalizer
        ((P : Subgroup G).comap N.subtype)
  exact
    Subgroup.le_normalizer_comap
      (H := (P : Subgroup G)) N.subtype

/-- The quotient homomorphism from the ambient Sylow normalizer to the
normalizer of the quotient Sylow. -/
def quotientNormalizerHom
    (P : Sylow p G) (N : Subgroup G) [N.Normal] :
    Subgroup.normalizer (P : Set G) →*
      Subgroup.normalizer
        (mapQuotient P N :
          Set (G ⧸ N)) :=
  ((QuotientGroup.mk' N).domRestrict
      (Subgroup.normalizer (P : Set G))).codRestrict
    (Subgroup.normalizer
      (mapQuotient P N :
        Set (G ⧸ N)))
    (by
      intro x
      have hx :
          QuotientGroup.mk' N x ∈
            (Subgroup.normalizer
              (P : Set G)).map
                (QuotientGroup.mk' N) :=
        ⟨x, x.2, rfl⟩
      rw [map_normalizer_eq_normalizer_mapQuotient
        P N] at hx
      exact hx)

@[simp]
theorem quotientNormalizerHom_apply_coe
    (P : Sylow p G) (N : Subgroup G) [N.Normal]
    (x : Subgroup.normalizer (P : Set G)) :
    ((quotientNormalizerHom P N x :
        Subgroup.normalizer
          (mapQuotient P N :
            Set (G ⧸ N))) :
      G ⧸ N) =
        QuotientGroup.mk' N x :=
  rfl

/-- The normalizer quotient homomorphism is surjective. -/
theorem quotientNormalizerHom_surjective
    (P : Sylow p G) (N : Subgroup G) [N.Normal] :
    Function.Surjective
      (quotientNormalizerHom P N) := by
  intro y
  have hy :
      y.1 ∈
        (Subgroup.normalizer
          (P : Set G)).map
            (QuotientGroup.mk' N) := by
    rw [map_normalizer_eq_normalizer_mapQuotient
      P N]
    exact y.2
  obtain ⟨x, hx, hxy⟩ := hy
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  exact hxy

/-- The kernel of the normalizer quotient homomorphism is precisely
`N ∩ N_G(P)`, regarded as a subgroup of `N_G(P)`. -/
theorem quotientNormalizerHom_ker
    (P : Sylow p G) (N : Subgroup G) [N.Normal] :
    (quotientNormalizerHom P N).ker =
      N.subgroupOf
        (Subgroup.normalizer (P : Set G)) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
    Subtype.ext_iff]
  change
    QuotientGroup.mk' N (x : G) = 1 ↔
      (x : G) ∈ N
  exact
    QuotientGroup.eq_one_iff
      (N := N) (x : G)

/-- The exact normalizer comparison across the quotient:
`N_G(P) / (N ∩ N_G(P)) ≃ N_{G/N}(P̄)`. -/
def quotientNormalizerEquiv
    (P : Sylow p G) (N : Subgroup G) [N.Normal] :
    (Subgroup.normalizer (P : Set G) ⧸
        N.subgroupOf
          (Subgroup.normalizer (P : Set G))) ≃*
      Subgroup.normalizer
        (mapQuotient P N :
          Set (G ⧸ N)) :=
  (QuotientGroup.quotientMulEquivOfEq
      (quotientNormalizerHom_ker P N).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (quotientNormalizerHom P N)
      (quotientNormalizerHom_surjective P N))

@[simp]
theorem quotientNormalizerEquiv_mk
    (P : Sylow p G) (N : Subgroup G) [N.Normal]
    (x : Subgroup.normalizer (P : Set G)) :
    quotientNormalizerEquiv P N
        (QuotientGroup.mk x) =
      quotientNormalizerHom P N x := by
  rw [quotientNormalizerEquiv,
    MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  change
    QuotientGroup.kerLift
        (quotientNormalizerHom P N)
        (QuotientGroup.mk x) =
      quotientNormalizerHom P N x
  exact
    QuotientGroup.kerLift_mk
      (quotientNormalizerHom P N) x

@[simp]
theorem quotientNormalizerEquiv_mk_coe
    (P : Sylow p G) (N : Subgroup G) [N.Normal]
    (x : Subgroup.normalizer (P : Set G)) :
    ((quotientNormalizerEquiv P N
        (QuotientGroup.mk x) :
          Subgroup.normalizer
            (mapQuotient P N :
              Set (G ⧸ N))) :
      G ⧸ N) =
        QuotientGroup.mk' N x := by
  rw [quotientNormalizerEquiv_mk]
  rfl

/-- Cardinality form of the exact quotient-normalizer equivalence. -/
theorem card_quotient_normalizer_eq
    (P : Sylow p G) (N : Subgroup G) [N.Normal] :
    Nat.card
        (Subgroup.normalizer (P : Set G) ⧸
          N.subgroupOf
            (Subgroup.normalizer (P : Set G))) =
      Nat.card
        (Subgroup.normalizer
          (mapQuotient P N :
            Set (G ⧸ N))) :=
  Nat.card_congr
    (quotientNormalizerEquiv P N).toEquiv

end Sylow

end GroupTheory
end McKayConjecture
