/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.SylowQuotient

/-!
# Sylow normalizers in quotients of intermediate subgroups

Let `J ≤ I ≤ G`, with `J` normal in `G`, and let a Sylow subgroup `P` of
`G` lie in `I`.  Write `P_I` for `P` inside `I`, `J_I` for `J` inside `I`,
and `Q` for the image of `P_I` in `I / J_I`.

The full preimage of `N_{I/J_I}(Q)` is

`J_I ⊔ N_I(P_I)`.

It follows that the quotient of this preimage by `J_I` is canonically
isomorphic to `N_{I/J_I}(Q)`.  After mapping back into `G`, the preimage is
exactly

`I ∩ (J ⊔ N_G(P))`.

The Sylow hypothesis is essential for the reverse normalizer containment:
without it, a lift of an element normalizing the image of `P` may conjugate
`P` to a distinct subgroup having the same quotient image.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

open scoped Pointwise

/-- A Dedekind modular-law identity for a normal subgroup. -/
theorem sup_inf_eq_inf_sup_of_normal_left
    {G : Type u} [Group G]
    (J I N : Subgroup G) [J.Normal]
    (hJI : J ≤ I) :
    J ⊔ (N ⊓ I) = I ⊓ (J ⊔ N) := by
  apply le_antisymm
  · apply sup_le
    · exact le_inf hJI le_sup_left
    · exact
        le_inf inf_le_right
          (inf_le_left.trans le_sup_right)
  · intro x hx
    obtain ⟨j, hj, n, hn, hjn⟩ :=
      (Subgroup.mem_sup_of_normal_left).mp hx.2
    have hnI : n ∈ I := by
      have hjI : j ∈ I := hJI hj
      have hn_eq : n = j⁻¹ * x := by
        rw [← hjn]
        simp
      rw [hn_eq]
      exact I.mul_mem (I.inv_mem hjI) hx.1
    exact
      (Subgroup.mem_sup_of_normal_left).mpr
        ⟨j, hj, n, ⟨hn, hnI⟩, hjn⟩

namespace Sylow

variable {X : Type u} [Group X] [Finite X]
variable {p : ℕ} [Fact p.Prime]

/-- The full preimage in `X` of the normalizer of the quotient Sylow
subgroup. -/
def quotientNormalizerPreimage
    (P : Sylow p X) (N : Subgroup X) [N.Normal] :
    Subgroup X :=
  N ⊔ Subgroup.normalizer (P : Set X)

/-- The normalizer of the quotient Sylow has exactly the expected full
preimage. -/
theorem comap_normalizer_mapQuotient_eq_preimage
    (P : Sylow p X) (N : Subgroup X) [N.Normal] :
    (Subgroup.normalizer
        (mapQuotient P N : Set (X ⧸ N))).comap
        (QuotientGroup.mk' N) =
      quotientNormalizerPreimage P N := by
  rw [← map_normalizer_eq_normalizer_mapQuotient P N,
    Subgroup.comap_map_eq,
    QuotientGroup.ker_mk',
    sup_comm]
  rfl

/-- The quotient map restricted from the full preimage to the quotient
Sylow normalizer. -/
def preimageQuotientNormalizerHom
    (P : Sylow p X) (N : Subgroup X) [N.Normal] :
    quotientNormalizerPreimage P N →*
      Subgroup.normalizer
        (mapQuotient P N : Set (X ⧸ N)) :=
  ((QuotientGroup.mk' N).domRestrict
      (quotientNormalizerPreimage P N)).codRestrict
    (Subgroup.normalizer
      (mapQuotient P N : Set (X ⧸ N)))
    (by
      intro x
      have hx :
          (x : X) ∈
            (Subgroup.normalizer
              (mapQuotient P N :
                Set (X ⧸ N))).comap
              (QuotientGroup.mk' N) := by
        rw [comap_normalizer_mapQuotient_eq_preimage]
        exact x.property
      exact hx)

@[simp]
theorem preimageQuotientNormalizerHom_apply_coe
    (P : Sylow p X) (N : Subgroup X) [N.Normal]
    (x : quotientNormalizerPreimage P N) :
    ((preimageQuotientNormalizerHom P N x :
        Subgroup.normalizer
          (mapQuotient P N :
            Set (X ⧸ N))) :
      X ⧸ N) =
        QuotientGroup.mk' N (x : X) :=
  rfl

/-- The restricted quotient map is surjective. -/
theorem preimageQuotientNormalizerHom_surjective
    (P : Sylow p X) (N : Subgroup X) [N.Normal] :
    Function.Surjective
      (preimageQuotientNormalizerHom P N) := by
  intro y
  obtain ⟨x, hx⟩ :=
    quotientNormalizerHom_surjective P N y
  let xPreimage :
      quotientNormalizerPreimage P N :=
    ⟨(x : X),
      (show
          Subgroup.normalizer (P : Set X) ≤
            quotientNormalizerPreimage P N
        from le_sup_right) x.property⟩
  refine ⟨xPreimage, ?_⟩
  apply Subtype.ext
  exact congrArg Subtype.val hx

/-- The kernel of the restricted quotient map is precisely `N`, viewed in
the full preimage. -/
@[simp]
theorem preimageQuotientNormalizerHom_ker
    (P : Sylow p X) (N : Subgroup X) [N.Normal] :
    (preimageQuotientNormalizerHom P N).ker =
      N.subgroupOf
        (quotientNormalizerPreimage P N) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
    Subtype.ext_iff]
  change
    QuotientGroup.mk' N (x : X) = 1 ↔
      (x : X) ∈ N
  exact QuotientGroup.eq_one_iff (x : X)

/-- Canonical quotient identification

`(N ⊔ N_X(P)) / N ≃ N_{X/N}(P̄)`.
-/
def preimageQuotientNormalizerEquiv
    (P : Sylow p X) (N : Subgroup X) [N.Normal] :
    (quotientNormalizerPreimage P N ⧸
        N.subgroupOf
          (quotientNormalizerPreimage P N)) ≃*
      Subgroup.normalizer
        (mapQuotient P N : Set (X ⧸ N)) :=
  (QuotientGroup.quotientMulEquivOfEq
      (preimageQuotientNormalizerHom_ker P N).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (preimageQuotientNormalizerHom P N)
      (preimageQuotientNormalizerHom_surjective P N))

@[simp]
theorem preimageQuotientNormalizerEquiv_mk
    (P : Sylow p X) (N : Subgroup X) [N.Normal]
    (x : quotientNormalizerPreimage P N) :
    preimageQuotientNormalizerEquiv P N
        (QuotientGroup.mk x) =
      preimageQuotientNormalizerHom P N x := by
  rw [preimageQuotientNormalizerEquiv,
    MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  change
    QuotientGroup.kerLift
        (preimageQuotientNormalizerHom P N)
        (QuotientGroup.mk x) =
      preimageQuotientNormalizerHom P N x
  exact QuotientGroup.kerLift_mk _ _

@[simp]
theorem preimageQuotientNormalizerEquiv_mk_coe
    (P : Sylow p X) (N : Subgroup X) [N.Normal]
    (x : quotientNormalizerPreimage P N) :
    ((preimageQuotientNormalizerEquiv P N
        (QuotientGroup.mk x) :
          Subgroup.normalizer
            (mapQuotient P N :
              Set (X ⧸ N))) :
      X ⧸ N) =
        QuotientGroup.mk' N (x : X) := by
  rw [preimageQuotientNormalizerEquiv_mk]
  rfl

end Sylow

section Intermediate

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (I J : Subgroup G) [J.Normal]
variable (P : Sylow p G)
variable (hJI : J ≤ I) (hPI : (P : Subgroup G) ≤ I)

/-- The normal subgroup `J`, regarded inside the intermediate subgroup
`I`. -/
abbrev normalSubgroupInIntermediate (_hJI : J ≤ I) :
    Subgroup I :=
  J.subgroupOf I

/-- The Sylow subgroup `P`, regarded inside `I`. -/
abbrev sylowInIntermediate :
    Sylow p I :=
  P.subtype hPI

/-- The image of `P` in `I/J`. -/
abbrev quotientSylowInIntermediate :
    Sylow p
      (I ⧸ normalSubgroupInIntermediate I J hJI) :=
  Sylow.mapQuotient
    (sylowInIntermediate I P hPI)
    (normalSubgroupInIntermediate I J hJI)

/-- The precise subtype version of
`I ∩ (J ⊔ N_G(P))`: it is `J_I ⊔ N_I(P)`. -/
abbrev intermediateQuotientNormalizerPreimage :
    Subgroup I :=
  Sylow.quotientNormalizerPreimage
    (sylowInIntermediate I P hPI)
    (normalSubgroupInIntermediate I J hJI)

omit [Finite G] [Fact p.Prime] in
/-- The intrinsic normalizer of `P` in `I` is the ambient normalizer cut
down to `I`. -/
theorem normalizer_sylowInIntermediate_eq_subgroupOf :
    Subgroup.normalizer
        (sylowInIntermediate I P hPI : Set I) =
      (Subgroup.normalizer (P : Set G)).subgroupOf I := by
  change
    Subgroup.normalizer
        ((P : Subgroup G).subgroupOf I : Set I) =
      (Subgroup.normalizer (P : Set G)).subgroupOf I
  exact
    (Subgroup.subgroupOf_normalizer_eq hPI).symm

omit [Finite G] [Fact p.Prime] in
/-- Mapping the precise subtype preimage into `G` gives exactly
`I ∩ (J ⊔ N_G(P))`. -/
theorem map_intermediateQuotientNormalizerPreimage :
    (intermediateQuotientNormalizerPreimage
        I J P hJI hPI).map I.subtype =
      I ⊓
        (J ⊔ Subgroup.normalizer (P : Set G)) := by
  rw [intermediateQuotientNormalizerPreimage,
    Sylow.quotientNormalizerPreimage,
    Subgroup.map_sup,
    normalizer_sylowInIntermediate_eq_subgroupOf
      I P hPI,
    Subgroup.map_subgroupOf_eq_of_le hJI,
    Subgroup.subgroupOf_map_subtype]
  exact
    sup_inf_eq_inf_sup_of_normal_left
      J I (Subgroup.normalizer (P : Set G)) hJI

omit [Finite G] [Fact p.Prime] in
/-- Inside `I`, the precise preimage is also the pullback of the ambient
intersection `I ∩ (J ⊔ N_G(P))`. -/
theorem intermediateQuotientNormalizerPreimage_eq_subgroupOf :
    intermediateQuotientNormalizerPreimage
        I J P hJI hPI =
      (I ⊓
        (J ⊔ Subgroup.normalizer (P : Set G))).subgroupOf I := by
  apply Subgroup.map_injective I.subtype_injective
  rw [map_intermediateQuotientNormalizerPreimage
      I J P hJI hPI,
    Subgroup.map_subgroupOf_eq_of_le inf_le_left]

/-- Canonical Rossi quotient-normalizer identification in the precise
subtype formulation:

`(I ∩ (J N_G(P))) / J ≃ N_{I/J}(P̄)`.
-/
def intermediateQuotientNormalizerEquiv :
    (intermediateQuotientNormalizerPreimage
          I J P hJI hPI ⧸
        (normalSubgroupInIntermediate I J hJI).subgroupOf
          (intermediateQuotientNormalizerPreimage
            I J P hJI hPI)) ≃*
      Subgroup.normalizer
        (quotientSylowInIntermediate
          I J P hJI hPI :
          Set
            (I ⧸ normalSubgroupInIntermediate I J hJI)) :=
  Sylow.preimageQuotientNormalizerEquiv
    (sylowInIntermediate I P hPI)
    (normalSubgroupInIntermediate I J hJI)

@[simp]
theorem intermediateQuotientNormalizerEquiv_mk_coe
    (x :
      intermediateQuotientNormalizerPreimage
        I J P hJI hPI) :
    ((intermediateQuotientNormalizerEquiv
        I J P hJI hPI
        (QuotientGroup.mk x) :
          Subgroup.normalizer
            (quotientSylowInIntermediate
              I J P hJI hPI :
              Set
                (I ⧸
                  normalSubgroupInIntermediate I J hJI))) :
      I ⧸ normalSubgroupInIntermediate I J hJI) =
        QuotientGroup.mk'
          (normalSubgroupInIntermediate I J hJI)
          (x : I) :=
  Sylow.preimageQuotientNormalizerEquiv_mk_coe
    (sylowInIntermediate I P hPI)
    (normalSubgroupInIntermediate I J hJI)
    x

end Intermediate

end GroupTheory
end McKayConjecture
