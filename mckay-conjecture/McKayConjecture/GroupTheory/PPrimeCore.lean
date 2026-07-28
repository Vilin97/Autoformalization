/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Sylow
import Mathlib.Order.SupClosed

/-!
# The largest normal `p′`-subgroup

For a finite group `G`, the `p′`-core `O_{p′}(G)` is the largest normal
subgroup whose order is coprime to `p`.  We use coprimality, rather than
nondivisibility by `p`, so that the elementary closure and functoriality
results remain useful without a primality hypothesis on `p`.
-/

noncomputable section

universe u v

namespace McKayConjecture.GroupTheory

open scoped Pointwise

variable (p : ℕ) (G : Type u) [Group G]

/-- A group is a `p′`-group when its order is coprime to `p`.

This predicate is intended for finite groups. -/
def IsPPrimeGroup : Prop :=
  Nat.Coprime p (Nat.card G)

variable {p G}

namespace IsPPrimeGroup

/-- The trivial group is a `p′`-group for every `p`. -/
theorem of_subsingleton [Subsingleton G] :
    IsPPrimeGroup p G := by
  simp [IsPPrimeGroup]

/-- Subgroups of a `p′`-group are `p′`-groups. -/
theorem to_subgroup
    (hG : IsPPrimeGroup p G)
    (H : Subgroup G) :
    IsPPrimeGroup p H :=
  hG.coprime_dvd_right
    (Subgroup.card_subgroup_dvd_card H)

/-- Images of `p′`-subgroups remain `p′`. -/
theorem map
    {H : Type v} [Group H]
    {N : Subgroup G}
    (hN : IsPPrimeGroup p N)
    (f : G →* H) :
    IsPPrimeGroup p (N.map f) :=
  hN.coprime_dvd_right
    (Subgroup.card_map_dvd N f)

/-- Quotients of `p′`-groups are `p′`-groups. -/
theorem to_quotient
    (hG : IsPPrimeGroup p G)
    (N : Subgroup G) [N.Normal] :
    IsPPrimeGroup p (G ⧸ N) :=
  hG.coprime_dvd_right
    (Subgroup.card_quotient_dvd_card N)

/-- The `p′`-group property is preserved by group isomorphisms. -/
theorem of_equiv
    {H : Type v} [Group H]
    (hG : IsPPrimeGroup p G)
    (e : G ≃* H) :
    IsPPrimeGroup p H := by
  rw [IsPPrimeGroup,
    ← Nat.card_congr e.toEquiv]
  exact hG

/-- Pullback along a surjection preserves the `p′`-group property when the
kernel is also a `p′`-group. -/
theorem comap_of_surjective
    {H : Type v} [Group H]
    (f : G →* H) (hf : Function.Surjective f)
    (hker : IsPPrimeGroup p f.ker)
    {K : Subgroup H}
    (hK : IsPPrimeGroup p K) :
    IsPPrimeGroup p (K.comap f) := by
  have hkerLe :
      f.ker ≤ K.comap f := by
    intro x hx
    change f x ∈ K
    rw [MonoidHom.mem_ker.mp hx]
    exact K.one_mem
  have hcard :
      Nat.card f.ker *
          Nat.card K =
        Nat.card (K.comap f) := by
    have hrel :=
      Subgroup.relIndex_mul_relIndex
        (⊥ : Subgroup G) f.ker
        (K.comap f) bot_le hkerLe
    simp only [Subgroup.relIndex_bot_left] at hrel
    rw [Subgroup.relIndex_ker,
      Subgroup.map_comap_eq_self_of_surjective
        hf] at hrel
    exact hrel
  rw [IsPPrimeGroup, ← hcard]
  exact hker.mul_right hK

end IsPPrimeGroup

omit [Group G] in
/-- For prime `p`, being a `p′`-group is equivalent to `p` not dividing
the group order. -/
theorem isPPrimeGroup_iff_not_dvd
    (hp : p.Prime) :
    IsPPrimeGroup p G ↔
      ¬p ∣ Nat.card G :=
  hp.coprime_iff_not_dvd

/-- If `K` is normal, the order of `H ⊔ K` divides the product of the
orders of `H` and `K`. -/
theorem card_sup_dvd_card_mul_card
    [Finite G] (H K : Subgroup G) [K.Normal] :
    Nat.card (H ⊔ K : Subgroup G) ∣
      Nat.card H * Nat.card K := by
  have hcard :
      Nat.card K *
          K.relIndex (H ⊔ K) =
        Nat.card (H ⊔ K : Subgroup G) := by
    simpa only [Subgroup.relIndex_bot_left] using
      Subgroup.relIndex_mul_relIndex
        (⊥ : Subgroup G) K (H ⊔ K)
        bot_le le_sup_right
  rw [Subgroup.relIndex_sup_right] at hcard
  calc
    Nat.card (H ⊔ K : Subgroup G) =
        Nat.card K * K.relIndex H :=
      hcard.symm
    _ ∣ Nat.card K * Nat.card H :=
      Nat.mul_dvd_mul_left
        (Nat.card K)
        (Subgroup.relIndex_dvd_card K H)
    _ = Nat.card H * Nat.card K :=
      mul_comm _ _

namespace IsPPrimeGroup

/-- The join of two normal `p′`-subgroups is a `p′`-subgroup.  Normality
of the left factor is only needed to make the resulting join normal; the
cardinality argument uses normality of the right factor. -/
theorem sup_of_normal
    [Finite G] {H K : Subgroup G}
    (hH : IsPPrimeGroup p H)
    (hK : IsPPrimeGroup p K)
    [H.Normal] [K.Normal] :
    IsPPrimeGroup p (H ⊔ K : Subgroup G) :=
  (hH.mul_right hK).coprime_dvd_right
    (card_sup_dvd_card_mul_card H K)

/-- The product of two normal subgroups is their join.  Thus
`sup_of_normal` is also the closure theorem for products of normal
`p′`-subgroups. -/
theorem coe_sup_eq_mul_of_normal
    {H K : Subgroup G} [K.Normal] :
    ((H ⊔ K : Subgroup G) : Set G) =
      (H : Set G) * (K : Set G) :=
  Subgroup.mul_normal H K

end IsPPrimeGroup

variable (p G)

/-- The set of normal `p′`-subgroups of `G`. -/
def normalPPrimeSubgroups
    [Finite G] :
    Set (Subgroup G) :=
  {N |
    IsPPrimeGroup p N ∧ N.Normal}

/-- Normal `p′`-subgroups are closed under joins. -/
theorem normalPPrimeSubgroups_supClosed
    [Finite G] :
    SupClosed (normalPPrimeSubgroups p G) := by
  intro H hH K hK
  letI : H.Normal := hH.2
  letI : K.Normal := hK.2
  exact
    ⟨IsPPrimeGroup.sup_of_normal hH.1 hK.1,
      inferInstance⟩

/-- The trivial subgroup is a normal `p′`-subgroup. -/
theorem bot_mem_normalPPrimeSubgroups
    [Finite G] :
    (⊥ : Subgroup G) ∈
      normalPPrimeSubgroups p G :=
  ⟨IsPPrimeGroup.of_subsingleton,
    inferInstance⟩

/-- The largest normal `p′`-subgroup, traditionally denoted
`O_{p′}(G)`. -/
def pPrimeCore [Finite G] :
    Subgroup G :=
  sSup (normalPPrimeSubgroups p G)

variable {p G}

variable [Finite G]

/-- Every normal `p′`-subgroup lies in the `p′`-core. -/
theorem le_pPrimeCore
    {N : Subgroup G}
    (hpN : IsPPrimeGroup p N)
    (hN : N.Normal) :
    N ≤ pPrimeCore p G :=
  le_sSup ⟨hpN, hN⟩

/-- The `p′`-core is itself a `p′`-group. -/
theorem pPrimeCore_isPPrimeGroup :
    IsPPrimeGroup p (pPrimeCore p G) := by
  have hmem :
      pPrimeCore p G ∈
        normalPPrimeSubgroups p G := by
    apply
      (normalPPrimeSubgroups_supClosed
        (p := p) (G := G)).sSup_mem
    · exact Set.toFinite _
    · exact
        bot_mem_normalPPrimeSubgroups
          (p := p) (G := G)
    · exact fun _ h ↦ h
  exact hmem.1

/-- The `p′`-core is normal. -/
instance pPrimeCore_normal :
    (pPrimeCore p G).Normal :=
  Subgroup.sSup_normal
    (normalPPrimeSubgroups p G)
    (fun _ hN ↦ hN.2)

/-- For a normal subgroup, containment in the `p′`-core is equivalent to
having order coprime to `p`. -/
theorem le_pPrimeCore_iff_of_normal
    {N : Subgroup G} (hN : N.Normal) :
    N ≤ pPrimeCore p G ↔
      IsPPrimeGroup p N := by
  constructor
  · intro hle
    exact
      pPrimeCore_isPPrimeGroup.to_subgroup
        (N.subgroupOf (pPrimeCore p G))
        |>.of_equiv
          (Subgroup.subgroupOfEquivOfLe hle)
  · intro hpN
    exact le_pPrimeCore hpN hN

/-- A `p′`-group has full `p′`-core. -/
theorem pPrimeCore_eq_top_of_isPPrimeGroup
    (hG : IsPPrimeGroup p G) :
    pPrimeCore p G = ⊤ := by
  apply top_unique
  exact
    le_pPrimeCore
      (hG.to_subgroup ⊤) inferInstance

/-- The `p′`-core is the whole group exactly for `p′`-groups. -/
theorem pPrimeCore_eq_top_iff :
    pPrimeCore p G = ⊤ ↔
      IsPPrimeGroup p G := by
  constructor
  · intro htop
    have htopPPrime :
        IsPPrimeGroup p (⊤ : Subgroup G) := by
      rw [← htop]
      exact pPrimeCore_isPPrimeGroup
    exact
      htopPPrime.of_equiv
        Subgroup.topEquiv
  · exact pPrimeCore_eq_top_of_isPPrimeGroup

/-- The `p′`-core is characteristic. -/
instance pPrimeCore_characteristic :
    (pPrimeCore p G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro e
  apply le_pPrimeCore
  · exact
      pPrimeCore_isPPrimeGroup.map
        e.toMonoidHom
  · exact
      Subgroup.Normal.map inferInstance
        e.toMonoidHom e.surjective

/-- Mapping the `p′`-core along a surjective homomorphism lands in the
`p′`-core of the target. -/
theorem map_pPrimeCore_le
    {H : Type v} [Group H] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) :
    (pPrimeCore p G).map f ≤
      pPrimeCore p H := by
  apply le_pPrimeCore
  · exact pPrimeCore_isPPrimeGroup.map f
  · exact
      Subgroup.Normal.map inferInstance f hf

/-- Pulling back a target `p′`-core along a surjection with `p′`-kernel
lands in the source `p′`-core. -/
theorem comap_pPrimeCore_le_of_ker_isPPrimeGroup
    {H : Type v} [Group H] [Finite H]
    (f : G →* H) (hf : Function.Surjective f)
    (hker : IsPPrimeGroup p f.ker) :
    (pPrimeCore p H).comap f ≤
      pPrimeCore p G := by
  apply le_pPrimeCore
  · exact
      IsPPrimeGroup.comap_of_surjective
        f hf hker pPrimeCore_isPPrimeGroup
  · exact
      Subgroup.Normal.comap inferInstance f

/-- A surjective homomorphism with `p′`-kernel maps the `p′`-core onto
the `p′`-core. -/
theorem map_pPrimeCore_eq_of_ker_isPPrimeGroup
    {H : Type v} [Group H] [Finite H]
    (f : G →* H) (hf : Function.Surjective f)
    (hker : IsPPrimeGroup p f.ker) :
    (pPrimeCore p G).map f =
      pPrimeCore p H := by
  apply le_antisymm
  · exact map_pPrimeCore_le f hf
  · have hle :
        (pPrimeCore p H).comap f ≤
          pPrimeCore p G :=
      comap_pPrimeCore_le_of_ker_isPPrimeGroup
        f hf hker
    have hmap :
        ((pPrimeCore p H).comap f).map f ≤
          (pPrimeCore p G).map f :=
      Subgroup.map_mono hle
    rw [Subgroup.map_comap_eq_self_of_surjective hf]
      at hmap
    exact hmap

/-- Group isomorphisms carry `p′`-cores to `p′`-cores. -/
theorem map_pPrimeCore_equiv
    {H : Type v} [Group H] [Finite H]
    (e : G ≃* H) :
    (pPrimeCore p G).map e.toMonoidHom =
      pPrimeCore p H := by
  apply le_antisymm
  · exact
      map_pPrimeCore_le
        e.toMonoidHom e.surjective
  · intro y hy
    have hreverse :
        (pPrimeCore p H).map
            e.symm.toMonoidHom ≤
          pPrimeCore p G :=
      map_pPrimeCore_le
        e.symm.toMonoidHom
        e.symm.surjective
    have hx :
        e.symm y ∈ pPrimeCore p G :=
      hreverse ⟨y, hy, rfl⟩
    exact
      ⟨e.symm y, hx,
        e.apply_symm_apply y⟩

/-- The `p′`-core is trivial exactly when every normal `p′`-subgroup is
trivial. -/
theorem pPrimeCore_eq_bot_iff :
    pPrimeCore p G = ⊥ ↔
      ∀ N : Subgroup G,
        IsPPrimeGroup p N →
        N.Normal → N = ⊥ := by
  constructor
  · intro hcore N hpN hN
    exact
      eq_bot_iff.mpr
        ((le_pPrimeCore hpN hN).trans_eq
          hcore)
  · intro h
    exact
      h (pPrimeCore p G)
        pPrimeCore_isPPrimeGroup
        inferInstance

/-- A nontrivial normal `p′`-subgroup forces the `p′`-core to be
nontrivial. -/
theorem pPrimeCore_ne_bot_of_normal
    {N : Subgroup G}
    (hpN : IsPPrimeGroup p N)
    (hN : N.Normal) (hne : N ≠ ⊥) :
    pPrimeCore p G ≠ ⊥ := by
  intro hcore
  exact
    hne
      (eq_bot_iff.mpr
        ((le_pPrimeCore hpN hN).trans_eq
          hcore))

/-- Factoring out the `p′`-core leaves a group with trivial
`p′`-core. -/
theorem pPrimeCore_quotient_pPrimeCore_eq_bot :
    pPrimeCore p (G ⧸ pPrimeCore p G) =
      ⊥ := by
  let q : G →* G ⧸ pPrimeCore p G :=
    QuotientGroup.mk' (pPrimeCore p G)
  have hker :
      IsPPrimeGroup p q.ker := by
    change
      IsPPrimeGroup p
        (QuotientGroup.mk'
          (pPrimeCore p G)).ker
    rw [QuotientGroup.ker_mk']
    exact pPrimeCore_isPPrimeGroup
  have hmap :=
    map_pPrimeCore_eq_of_ker_isPPrimeGroup
      q
      (QuotientGroup.mk'_surjective
        (pPrimeCore p G))
      hker
  have hmapBot :
      (pPrimeCore p G).map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    simp [q, QuotientGroup.ker_mk']
  rw [hmapBot] at hmap
  exact hmap.symm

end McKayConjecture.GroupTheory
