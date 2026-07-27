/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.CentralSylowDecomposition
import McKayConjecture.GroupTheory.PPrimeKernelSylowNormalizer
import McKayConjecture.GroupTheory.SylowQuotient

/-!
# A normal subgroup with central Sylow intersection

If `K ◁ G`, then `P ∩ K` is a Sylow `p`-subgroup of `K`.  When the
ambient intersection is central in `G`, this internal Sylow subgroup is
central in `K`; consequently `K` is the direct product of
`O_{p′}(K)` and `P ∩ K`.

The `p′` factor is characteristic in `K`, so its image is normal in `G`.
This is the invariant normal-complement package used by the
Okuyama--Wajima form of the central-intersection reduction.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (P : Sylow p G) (K : Subgroup G) [K.Normal]

/-- The internal Sylow subgroup `P ∩ K` of a normal subgroup `K`. -/
abbrev normalIntersectionSylow : Sylow p K :=
  Sylow.intersectionNormal P K

/-- Ambient centrality of `K ∩ P` implies internal centrality of the
intersection Sylow subgroup in `K`. -/
theorem normalIntersectionSylow_le_center
    (hcentral :
      K ⊓ (P : Subgroup G) ≤ Subgroup.center G) :
    (normalIntersectionSylow P K : Subgroup K) ≤
      Subgroup.center K := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact
    Subgroup.mem_center_iff.mp
      (hcentral ⟨x.2, hx⟩) (y : G)

/-- The canonical `p′`-factor of `K`, defined by Burnside transfer from
the central Sylow intersection. -/
abbrev normalIntersectionComplement
    (hcentral :
      K ⊓ (P : Subgroup G) ≤ Subgroup.center G) :
    Subgroup K :=
  centralSylowComplement
    (normalIntersectionSylow P K)
    (normalIntersectionSylow_le_center P K hcentral)

/-- The canonical complement is the `p′`-core of `K`. -/
theorem normalIntersectionComplement_eq_pPrimeCore
    (hcentral :
      K ⊓ (P : Subgroup G) ≤ Subgroup.center G) :
    normalIntersectionComplement P K hcentral =
      pPrimeCore p K :=
  centralSylowComplement_eq_pPrimeCore
    (normalIntersectionSylow P K)
    (normalIntersectionSylow_le_center P K hcentral)

/-- The order of the normal-complement factor is prime to `p`. -/
theorem normalIntersectionComplement_isPPrimeGroup
    (hcentral :
      K ⊓ (P : Subgroup G) ≤ Subgroup.center G) :
    IsPPrimeGroup p
      (normalIntersectionComplement P K hcentral) := by
  rw [normalIntersectionComplement_eq_pPrimeCore P K hcentral]
  exact pPrimeCore_isPPrimeGroup

/-- Internal direct-product decomposition
`K ≅ O_{p′}(K) × (P ∩ K)`, with the transfer complement retained as the
left factor so that multiplication is definitionally transparent. -/
def normalIntersectionProductEquiv
    (hcentral :
      K ⊓ (P : Subgroup G) ≤ Subgroup.center G) :
    normalIntersectionComplement P K hcentral ×
        normalIntersectionSylow P K ≃* K :=
  centralSylowProductEquiv
    (normalIntersectionSylow P K)
    (normalIntersectionSylow_le_center P K hcentral)

@[simp]
theorem normalIntersectionProductEquiv_apply
    (hcentral :
      K ⊓ (P : Subgroup G) ≤ Subgroup.center G)
    (x :
      normalIntersectionComplement P K hcentral ×
        normalIntersectionSylow P K) :
    normalIntersectionProductEquiv P K hcentral x =
      (x.1 : K) * (x.2 : K) :=
  rfl

/-- The `p′` factor, mapped back into the ambient group. -/
abbrev ambientNormalIntersectionComplement
    (hcentral :
      K ⊓ (P : Subgroup G) ≤ Subgroup.center G) :
    Subgroup G :=
  (normalIntersectionComplement P K hcentral).map K.subtype

/-- The `p′` factor is normal in the ambient group: it is the image of
the characteristic subgroup `O_{p′}(K)` of the normal subgroup `K`. -/
instance ambientNormalIntersectionComplement_normal
    (hcentral :
      K ⊓ (P : Subgroup G) ≤ Subgroup.center G) :
    (ambientNormalIntersectionComplement P K hcentral).Normal := by
  haveI :
      (normalIntersectionComplement P K hcentral).Characteristic := by
    rw [normalIntersectionComplement_eq_pPrimeCore P K hcentral]
    infer_instance
  infer_instance

/-- The ambient image of the complement still has order prime to `p`. -/
theorem ambientNormalIntersectionComplement_isPPrimeGroup
    (hcentral :
      K ⊓ (P : Subgroup G) ≤ Subgroup.center G) :
    IsPPrimeGroup p
      (ambientNormalIntersectionComplement P K hcentral) :=
  (normalIntersectionComplement_isPPrimeGroup
    P K hcentral).map K.subtype

/-- The ambient `p′` factor together with the Sylow intersection
recovers the original normal subgroup. -/
theorem ambientNormalIntersectionComplement_sup_sylow_inf_eq
    (hcentral :
      K ⊓ (P : Subgroup G) ≤ Subgroup.center G) :
    ambientNormalIntersectionComplement P K hcentral ⊔
        ((P : Subgroup G) ⊓ K) =
      K := by
  have hinside :
      normalIntersectionComplement P K hcentral ⊔
          (normalIntersectionSylow P K : Subgroup K) =
        ⊤ :=
    (centralSylowComplement_isComplement'
      (normalIntersectionSylow P K)
      (normalIntersectionSylow_le_center
        P K hcentral)).sup_eq_top
  have hmapped :=
    congrArg
      (fun H : Subgroup K => H.map K.subtype)
      hinside
  have htopmap :
      (⊤ : Subgroup K).map K.subtype = K := by
    ext x
    simp
  simpa only [Subgroup.map_sup, htopmap,
    Sylow.map_intersectionNormal_subtype] using hmapped

/-- Adjoining the ambient center to a normal subgroup with central Sylow
intersection is the same as adjoining it to the subgroup's canonical
normal `p′` factor. -/
theorem ambientNormalIntersectionComplement_sup_center_eq
    (hcentral :
      K ⊓ (P : Subgroup G) ≤ Subgroup.center G) :
    ambientNormalIntersectionComplement P K hcentral ⊔
        Subgroup.center G =
      K ⊔ Subgroup.center G := by
  apply le_antisymm
  · apply sup_le
    · refine (show
        ambientNormalIntersectionComplement P K hcentral ≤ K from ?_).trans
          le_sup_left
      rintro x ⟨y, hy, rfl⟩
      exact y.2
    · exact le_sup_right
  · apply sup_le
    · calc
        K ≤
            ambientNormalIntersectionComplement P K hcentral ⊔
              ((P : Subgroup G) ⊓ K) :=
          (ambientNormalIntersectionComplement_sup_sylow_inf_eq
            P K hcentral).symm.le
        _ ≤
            ambientNormalIntersectionComplement P K hcentral ⊔
              Subgroup.center G := by
          apply sup_le le_sup_left
          have hSylowInfCenter :
              (P : Subgroup G) ⊓ K ≤
                Subgroup.center G := by
            intro x hx
            exact hcentral ⟨hx.2, hx.1⟩
          exact hSylowInfCenter.trans le_sup_right
    · exact le_sup_right

/-- If a normal subgroup meets a Sylow subgroup only in the ambient
center, adjoining the ambient center preserves that property. -/
theorem normal_sup_center_inf_sylow_le_center
    (hcentral :
      K ⊓ (P : Subgroup G) ≤ Subgroup.center G) :
    (K ⊔ Subgroup.center G) ⊓
        (P : Subgroup G) ≤
      Subgroup.center G := by
  rw [←
    ambientNormalIntersectionComplement_sup_center_eq
      P K hcentral]
  exact
    sup_center_inf_sylow_le_center
      (ambientNormalIntersectionComplement P K hcentral)
      (ambientNormalIntersectionComplement_isPPrimeGroup
        P K hcentral)
      P

/-- Exact intersection form of
`normal_sup_center_inf_sylow_le_center`. -/
theorem normal_sup_center_inf_sylow_eq
    (hcentral :
      K ⊓ (P : Subgroup G) ≤ Subgroup.center G) :
    (K ⊔ Subgroup.center G) ⊓
        (P : Subgroup G) =
      (P : Subgroup G) ⊓
        Subgroup.center G := by
  apply le_antisymm
  · exact
      le_inf inf_le_right
        (normal_sup_center_inf_sylow_le_center
          P K hcentral)
  · exact
      le_inf
        (inf_le_right.trans le_sup_right)
        inf_le_left

/-- The ambient `p′` factor and the Sylow subgroup generate the ambient
group whenever the original normal subgroup and Sylow subgroup do. -/
theorem ambientNormalIntersectionComplement_sup_sylow_eq_top
    (hcentral :
      K ⊓ (P : Subgroup G) ≤ Subgroup.center G)
    (hgenerate :
      K ⊔ (P : Subgroup G) = ⊤) :
    ambientNormalIntersectionComplement P K hcentral ⊔
        (P : Subgroup G) =
      ⊤ := by
  have hkernel :
      ambientNormalIntersectionComplement P K hcentral ⊔
          ((P : Subgroup G) ⊓ K) =
        K :=
    ambientNormalIntersectionComplement_sup_sylow_inf_eq
      P K hcentral
  apply top_unique
  intro g _
  have hgKP : g ∈ K ⊔ (P : Subgroup G) := by
    rw [hgenerate]
    exact Subgroup.mem_top g
  have hKle :
      K ≤
        ambientNormalIntersectionComplement P K hcentral ⊔
          (P : Subgroup G) := by
    intro k hk
    have hk' :
        k ∈
          ambientNormalIntersectionComplement P K hcentral ⊔
            ((P : Subgroup G) ⊓ K) := by
      rw [hkernel]
      exact hk
    have hsmall :
        ambientNormalIntersectionComplement P K hcentral ⊔
            ((P : Subgroup G) ⊓ K) ≤
          ambientNormalIntersectionComplement P K hcentral ⊔
            (P : Subgroup G) :=
      sup_le
        (show
          ambientNormalIntersectionComplement P K hcentral ≤
            ambientNormalIntersectionComplement P K hcentral ⊔
              (P : Subgroup G) from
          le_sup_left)
        (show
          (P : Subgroup G) ⊓ K ≤
            ambientNormalIntersectionComplement P K hcentral ⊔
              (P : Subgroup G) from
          inf_le_left.trans le_sup_right)
    exact hsmall hk'
  exact (sup_le hKle le_sup_right) hgKP

/-- The ambient `p′` factor meets the Sylow subgroup trivially. -/
theorem ambientNormalIntersectionComplement_inf_sylow_eq_bot
    (hcentral :
      K ⊓ (P : Subgroup G) ≤ Subgroup.center G) :
    ambientNormalIntersectionComplement P K hcentral ⊓
        (P : Subgroup G) =
      ⊥ := by
  rw [inf_comm]
  exact
    IsPGroup.inf_eq_bot_of_isPPrimeGroup
      P.isPGroup'
      (ambientNormalIntersectionComplement_isPPrimeGroup
        P K hcentral)

/-- After replacing `K` by its canonical normal `p′` factor, the Sylow
normalizer has the elementary form `C_R(P)P`. -/
theorem normalizer_eq_complement_inf_centralizer_sup
    (hcentral :
      K ⊓ (P : Subgroup G) ≤ Subgroup.center G)
    (hgenerate :
      K ⊔ (P : Subgroup G) = ⊤) :
    Subgroup.normalizer (P : Set G) =
      (ambientNormalIntersectionComplement P K hcentral ⊓
          Subgroup.centralizer (P : Set G)) ⊔
        (P : Subgroup G) :=
  normalizer_eq_inf_centralizer_sup
    P
    (ambientNormalIntersectionComplement P K hcentral)
    (ambientNormalIntersectionComplement_isPPrimeGroup
      P K hcentral)
    (ambientNormalIntersectionComplement_sup_sylow_eq_top
      P K hcentral hgenerate)

end GroupTheory
end McKayConjecture
