/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.PPrimeCore
import Mathlib.GroupTheory.Subgroup.Center

/-!
# The `p′`-core and a Sylow subgroup modulo the center

If `P` is a Sylow `p`-subgroup of a finite group `G`, then

`(O_{p′}(G) Z(G)) ∩ P ≤ Z(G)`.

The proof works more generally for any subgroup of order coprime to
`p`.  After quotienting by the center, its image has order coprime to
`p`, while the image of `P` is a `p`-group, so the two images are
disjoint.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace GroupTheory

variable {G : Type u} [Group G]
variable {p : ℕ}

namespace IsPGroup

/-- A `p`-subgroup is disjoint from a finite subgroup whose order is
coprime to `p`. -/
theorem disjoint_of_isPPrimeGroup
    {H K : Subgroup G} [Finite K]
    (hH : IsPGroup p H)
    (hK : IsPPrimeGroup p K) :
    Disjoint H K := by
  refine
    Subgroup.disjoint_def.mpr
      fun {g} hgH hgK ↦ ?_
  obtain ⟨n, hn⟩ :=
    hH ⟨g, hgH⟩
  have horderPow :
      orderOf g ∣ p ^ n :=
    Subgroup.orderOf_mk g hgH ▸
      orderOf_dvd_of_pow_eq_one hn
  have horderCard :
      orderOf g ∣ Nat.card K :=
    Subgroup.orderOf_mk g hgK ▸
      orderOf_dvd_natCard
        (⟨g, hgK⟩ : K)
  exact
    orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes
        (hK.symm.pow_right n)
        horderCard horderPow)

/-- Images of a finite `p`-subgroup and a finite `p′`-subgroup are
disjoint. -/
theorem disjoint_map_of_isPPrimeGroup
    {L : Type v} [Group L] [Finite L]
    {H K : Subgroup G}
    (hH : IsPGroup p H)
    (hK : IsPPrimeGroup p K)
    (f : G →* L) :
    Disjoint (H.map f) (K.map f) :=
  disjoint_of_isPPrimeGroup
    (hH.map f)
    (hK.map f)

/-- Intersection form of `disjoint_of_isPPrimeGroup`. -/
theorem inf_eq_bot_of_isPPrimeGroup
    {H K : Subgroup G} [Finite K]
    (hH : IsPGroup p H)
    (hK : IsPPrimeGroup p K) :
    H ⊓ K = ⊥ :=
  disjoint_iff_inf_le.mp
    (disjoint_of_isPPrimeGroup hH hK)
    |>.antisymm bot_le

end IsPGroup

/-- Modulo the center, adjoining the center to a subgroup has no
effect on its image. -/
theorem map_sup_center_quotient_eq
    (K : Subgroup G) :
    (K ⊔ Subgroup.center G).map
        (QuotientGroup.mk'
          (Subgroup.center G)) =
      K.map
        (QuotientGroup.mk'
          (Subgroup.center G)) := by
  have hcenter :
      (Subgroup.center G).map
          (QuotientGroup.mk'
            (Subgroup.center G)) =
        ⊥ := by
    rw [Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
  rw [Subgroup.map_sup, hcenter, sup_bot_eq]

variable [Finite G]

/-- In the quotient by the center, the image of a `p`-subgroup is
disjoint from the image of a `p′`-subgroup. -/
theorem quotientCenter_images_disjoint
    {H K : Subgroup G}
    (hH : IsPGroup p H)
    (hK : IsPPrimeGroup p K) :
    Disjoint
      (H.map
        (QuotientGroup.mk'
          (Subgroup.center G)))
      (K.map
        (QuotientGroup.mk'
          (Subgroup.center G))) :=
  IsPGroup.disjoint_map_of_isPPrimeGroup
    hH hK
    (QuotientGroup.mk'
      (Subgroup.center G))

/-- General central-intersection lemma: adjoining the center to any
finite `p′`-subgroup cannot add a noncentral element of a
`p`-subgroup. -/
theorem sup_center_inf_isPGroup_le_center
    {H K : Subgroup G}
    (hH : IsPGroup p H)
    (hK : IsPPrimeGroup p K) :
    (K ⊔ Subgroup.center G) ⊓ H ≤
      Subgroup.center G := by
  intro x hx
  let q : G →*
      G ⧸ Subgroup.center G :=
    QuotientGroup.mk'
      (Subgroup.center G)
  have hxH :
      q x ∈ H.map q :=
    ⟨x, hx.2, rfl⟩
  have hxK :
      q x ∈ K.map q := by
    have hxJoin :
        q x ∈
          (K ⊔ Subgroup.center G).map q :=
      ⟨x, hx.1, rfl⟩
    simpa only [q,
      map_sup_center_quotient_eq]
      using hxJoin
  have hqOne :
      q x = 1 :=
    Subgroup.disjoint_def.mp
      (quotientCenter_images_disjoint
        hH hK)
      hxH hxK
  exact
    (QuotientGroup.eq_one_iff x).mp
      hqOne

/-- Sylow form of the general central-intersection lemma.  Normality of
`K` is not needed. -/
theorem sup_center_inf_sylow_le_center
    (K : Subgroup G)
    (hK : IsPPrimeGroup p K)
    (P : Sylow p G) :
    (K ⊔ Subgroup.center G) ⊓
        (P : Subgroup G) ≤
      Subgroup.center G :=
  sup_center_inf_isPGroup_le_center
    P.isPGroup' hK

/-- Exact intersection form of the central-intersection lemma. -/
theorem sup_center_inf_sylow_eq
    (K : Subgroup G)
    (hK : IsPPrimeGroup p K)
    (P : Sylow p G) :
    (K ⊔ Subgroup.center G) ⊓
        (P : Subgroup G) =
      (P : Subgroup G) ⊓
        Subgroup.center G := by
  apply le_antisymm
  · exact
      le_inf inf_le_right
        (sup_center_inf_sylow_le_center
          K hK P)
  · exact
      le_inf
        (inf_le_right.trans le_sup_right)
        inf_le_left

/-- Inside a Sylow subgroup, membership in `K Z(G)` is equivalent to
centrality whenever `K` is a `p′`-subgroup. -/
theorem mem_sup_center_iff_of_mem_sylow
    (K : Subgroup G)
    (hK : IsPPrimeGroup p K)
    (P : Sylow p G)
    {x : G} (hxP : x ∈ P) :
    x ∈ K ⊔ Subgroup.center G ↔
      x ∈ Subgroup.center G := by
  constructor
  · intro hx
    exact
      sup_center_inf_sylow_le_center
        K hK P ⟨hx, hxP⟩
  · exact
      fun hx ↦
        (show
          Subgroup.center G ≤
            K ⊔ Subgroup.center G from
          le_sup_right) hx

/-- A Sylow `p`-subgroup intersects the `p′`-core trivially. -/
theorem sylow_inf_pPrimeCore_eq_bot
    (P : Sylow p G) :
    (P : Subgroup G) ⊓
        pPrimeCore p G =
      ⊥ :=
  IsPGroup.inf_eq_bot_of_isPPrimeGroup
    P.isPGroup'
    pPrimeCore_isPPrimeGroup

/-- Symmetric orientation of the trivial Sylow/`p′`-core
intersection. -/
theorem pPrimeCore_inf_sylow_eq_bot
    (P : Sylow p G) :
    pPrimeCore p G ⊓
        (P : Subgroup G) =
      ⊥ := by
  rw [inf_comm]
  exact sylow_inf_pPrimeCore_eq_bot P

/-- The Rossi central-intersection lemma:
`(O_{p′}(G) Z(G)) ∩ P ≤ Z(G)`. -/
theorem pPrimeCore_sup_center_inf_sylow_le_center
    (P : Sylow p G) :
    (pPrimeCore p G ⊔
          Subgroup.center G) ⊓
        (P : Subgroup G) ≤
      Subgroup.center G :=
  sup_center_inf_sylow_le_center
    (pPrimeCore p G)
    pPrimeCore_isPPrimeGroup P

/-- Exact form of the Rossi central-intersection lemma. -/
theorem pPrimeCore_sup_center_inf_sylow_eq
    (P : Sylow p G) :
    (pPrimeCore p G ⊔
          Subgroup.center G) ⊓
        (P : Subgroup G) =
      (P : Subgroup G) ⊓
        Subgroup.center G :=
  sup_center_inf_sylow_eq
    (pPrimeCore p G)
    pPrimeCore_isPPrimeGroup P

/-- Elementwise form of the exact intersection identity. -/
@[simp]
theorem mem_pPrimeCore_sup_center_inf_sylow_iff
    (P : Sylow p G) (x : G) :
    x ∈
        (pPrimeCore p G ⊔
            Subgroup.center G) ⊓
          (P : Subgroup G) ↔
      x ∈ P ∧
        x ∈ Subgroup.center G := by
  rw [pPrimeCore_sup_center_inf_sylow_eq]
  rfl

/-- Membership form of the Rossi central-intersection lemma. -/
theorem mem_pPrimeCore_sup_center_iff_of_mem_sylow
    (P : Sylow p G)
    {x : G} (hxP : x ∈ P) :
    x ∈ pPrimeCore p G ⊔
          Subgroup.center G ↔
      x ∈ Subgroup.center G :=
  mem_sup_center_iff_of_mem_sylow
    (pPrimeCore p G)
    pPrimeCore_isPPrimeGroup P hxP

end GroupTheory
end McKayConjecture
