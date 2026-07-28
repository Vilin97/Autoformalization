/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.Fitting
import Mathlib.GroupTheory.Nilpotent

/-!
# The Fitting subgroup as a product of prime cores

For a finite group, only primes dividing the group order contribute to the
Fitting subgroup.  The corresponding prime cores commute and have pairwise
coprime orders, so their multiplication map is an internal direct-product
equivalence onto the Fitting subgroup.

This file also proves that the Fitting subgroup is nilpotent and is the
largest normal nilpotent subgroup.
-/

noncomputable section

universe u

namespace McKayConjecture.GroupTheory

variable {G : Type u} [Group G] [Finite G]

/-- A prime which does not divide the order of a finite group has trivial
prime core. -/
theorem pCore_eq_bot_of_not_dvd_card {p : ℕ}
    (hp : p.Prime) (hpdvd : ¬p ∣ Nat.card G) :
    pCore p G = ⊥ := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hcard⟩ :=
    IsPGroup.iff_card.mp
      (pCore_isPGroup (p := p) (G := G))
  have hcoreDvd :
      Nat.card (pCore p G) ∣ Nat.card G :=
    Subgroup.card_subgroup_dvd_card (pCore p G)
  have hn : n = 0 := by
    by_contra hn
    apply hpdvd
    apply
      (show p ∣ Nat.card (pCore p G) from ?_).trans
        hcoreDvd
    rw [hcard]
    exact dvd_pow_self p hn
  apply (pCore p G).eq_bot_of_card_eq
  simpa [hn] using hcard

/-- In a finite group the defining supremum for the Fitting subgroup can be
restricted to primes dividing the group order. -/
theorem fittingSubgroup_eq_iSup_primeFactors :
    fittingSubgroup G =
      ⨆ q : (Nat.card G).primeFactors,
        pCore (q : ℕ) G := by
  apply le_antisymm
  · apply fittingSubgroup_le
    intro p hp
    by_cases hpdvd : p ∣ Nat.card G
    · have hmem :
          p ∈ (Nat.card G).primeFactors :=
        Nat.mem_primeFactors.mpr
          ⟨hp, hpdvd, Nat.card_pos.ne'⟩
      exact
        le_iSup_of_le
          (⟨p, hmem⟩ :
            (Nat.card G).primeFactors)
          le_rfl
    · rw [pCore_eq_bot_of_not_dvd_card hp hpdvd]
      exact bot_le
  · apply iSup_le
    rintro ⟨p, hp⟩
    exact
      pCore_le_fittingSubgroup
        (Nat.prime_of_mem_primeFactors hp)

omit [Finite G] in
/-- Prime cores indexed by the prime divisors of the group order commute
pairwise. -/
theorem pCores_primeFactors_pairwise_commute :
    Pairwise
      fun q r : (Nat.card G).primeFactors =>
        ∀ x y : G,
          x ∈ pCore (q : ℕ) G →
          y ∈ pCore (r : ℕ) G →
          Commute x y := by
  rintro ⟨q, hq⟩ ⟨r, hr⟩ hqr x y hx hy
  have hne : q ≠ r := by
    intro h
    apply hqr
    exact Subtype.ext h
  exact
    pCore_commute
      (Nat.prime_of_mem_primeFactors hq)
      (Nat.prime_of_mem_primeFactors hr)
      hne hx hy

/-- Prime cores belonging to distinct prime divisors have coprime orders. -/
theorem pCores_primeFactors_pairwise_coprime_card :
    Pairwise
      fun q r : (Nat.card G).primeFactors =>
        Nat.Coprime
          (Nat.card (pCore (q : ℕ) G))
          (Nat.card (pCore (r : ℕ) G)) := by
  rintro ⟨q, hq⟩ ⟨r, hr⟩ hqr
  letI : Fact q.Prime :=
    ⟨Nat.prime_of_mem_primeFactors hq⟩
  letI : Fact r.Prime :=
    ⟨Nat.prime_of_mem_primeFactors hr⟩
  have hne : q ≠ r := by
    intro h
    apply hqr
    exact Subtype.ext h
  exact
    IsPGroup.coprime_card_of_ne q r hne
      (pCore q G) (pCore r G)
      pCore_isPGroup pCore_isPGroup

/-- The family of prime cores supported on the prime divisors of the group
order is independent. -/
theorem pCores_primeFactors_iSupIndep :
    iSupIndep
      fun q : (Nat.card G).primeFactors =>
        pCore (q : ℕ) G := by
  letI :
      ∀ q : (Nat.card G).primeFactors,
        Fintype (pCore (q : ℕ) G) :=
    fun _ ↦ Fintype.ofFinite _
  apply
    Subgroup.independent_of_coprime_order
      (pCores_primeFactors_pairwise_commute
        (G := G))
  intro q r hqr
  simpa only [Nat.card_eq_fintype_card] using
    pCores_primeFactors_pairwise_coprime_card
      (G := G) hqr

/-- The canonical multiplication homomorphism from the product of the
nontrivial prime cores into the Fitting subgroup. -/
def fittingProductHom :
    (∀ q : (Nat.card G).primeFactors,
        pCore (q : ℕ) G) →*
      fittingSubgroup G :=
  (Subgroup.noncommPiCoprod
      (pCores_primeFactors_pairwise_commute
        (G := G))).codRestrict
    (fittingSubgroup G)
    (by
      intro x
      have hx :
          Subgroup.noncommPiCoprod
              (pCores_primeFactors_pairwise_commute
                (G := G)) x ∈
            (Subgroup.noncommPiCoprod
              (pCores_primeFactors_pairwise_commute
                (G := G))).range :=
        ⟨x, rfl⟩
      rw [Subgroup.noncommPiCoprod_range] at hx
      rw [fittingSubgroup_eq_iSup_primeFactors
        (G := G)]
      exact hx)

@[simp]
theorem fittingProductHom_apply_coe
    (x :
      ∀ q : (Nat.card G).primeFactors,
        pCore (q : ℕ) G) :
    ((fittingProductHom (G := G) x :
        fittingSubgroup G) :
      G) =
      Subgroup.noncommPiCoprod
        (pCores_primeFactors_pairwise_commute
          (G := G)) x :=
  rfl

/-- The prime-core multiplication homomorphism is injective. -/
theorem fittingProductHom_injective :
    Function.Injective
      (fittingProductHom (G := G)) := by
  intro x y hxy
  apply
    Subgroup.injective_noncommPiCoprod_of_iSupIndep
      (pCores_primeFactors_iSupIndep
        (G := G))
  exact congrArg Subtype.val hxy

/-- The prime-core multiplication homomorphism is surjective onto the
Fitting subgroup. -/
theorem fittingProductHom_surjective :
    Function.Surjective
      (fittingProductHom (G := G)) := by
  intro y
  have hy :
      (y : G) ∈
        (Subgroup.noncommPiCoprod
          (pCores_primeFactors_pairwise_commute
            (G := G))).range := by
    rw [Subgroup.noncommPiCoprod_range,
      ← fittingSubgroup_eq_iSup_primeFactors
        (G := G)]
    exact y.2
  obtain ⟨x, hx⟩ := hy
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hx

/-- Multiplication gives an internal direct-product equivalence from the
prime cores onto the Fitting subgroup. -/
def fittingProductEquiv :
    (∀ q : (Nat.card G).primeFactors,
        pCore (q : ℕ) G) ≃*
      fittingSubgroup G :=
  MulEquiv.ofBijective
    (fittingProductHom (G := G))
    ⟨fittingProductHom_injective (G := G),
      fittingProductHom_surjective (G := G)⟩

@[simp]
theorem fittingProductEquiv_apply_coe
    (x :
      ∀ q : (Nat.card G).primeFactors,
        pCore (q : ℕ) G) :
    ((fittingProductEquiv (G := G) x :
        fittingSubgroup G) :
      G) =
      Subgroup.noncommPiCoprod
        (pCores_primeFactors_pairwise_commute
          (G := G)) x :=
  rfl

/-- The order of the Fitting subgroup is the product of the orders of its
prime cores. -/
theorem card_fittingSubgroup :
    Nat.card (fittingSubgroup G) =
      ∏ q : (Nat.card G).primeFactors,
        Nat.card (pCore (q : ℕ) G) := by
  rw [← Nat.card_congr
    (fittingProductEquiv (G := G)).toEquiv,
    Nat.card_pi]

/-- The subtype of a pointwise product of subgroups is naturally the
dependent product of their subtype groups. -/
def subgroupPiEquiv
    {ι : Type*} {A : ι → Type*}
    [∀ i, Group (A i)]
    (H : ∀ i, Subgroup (A i)) :
    (∀ i, H i) ≃*
      Subgroup.pi Set.univ H where
  toFun x :=
    ⟨fun i ↦ x i,
      fun i _ ↦ (x i).2⟩
  invFun x :=
    fun i ↦
      ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
  left_inv x := by
    funext i
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    rfl

/-- The center of the Fitting subgroup is the product of the centers of
its prime cores. -/
def fittingCenterProductEquiv :
    (∀ q : (Nat.card G).primeFactors,
        Subgroup.center (pCore (q : ℕ) G)) ≃*
      Subgroup.center (fittingSubgroup G) :=
  (subgroupPiEquiv
      (fun q : (Nat.card G).primeFactors ↦
        Subgroup.center (pCore (q : ℕ) G))).trans
    ((MulEquiv.subgroupCongr
      (Subgroup.center_pi.symm)).trans
        (Subgroup.centerCongr
          (fittingProductEquiv (G := G))))

/-- Cardinality formula for the center of the Fitting subgroup. -/
theorem card_center_fittingSubgroup :
    Nat.card
        (Subgroup.center (fittingSubgroup G)) =
      ∏ q : (Nat.card G).primeFactors,
        Nat.card
          (Subgroup.center (pCore (q : ℕ) G)) := by
  rw [← Nat.card_congr
    (fittingCenterProductEquiv (G := G)).toEquiv,
    Nat.card_pi]

/-- The Fitting subgroup of a finite group is nilpotent. -/
instance fittingSubgroup_isNilpotent :
    Group.IsNilpotent (fittingSubgroup G) := by
  letI :
      ∀ q : (Nat.card G).primeFactors,
        Fact (q : ℕ).Prime :=
    fun q ↦
      ⟨Nat.prime_of_mem_primeFactors q.2⟩
  letI :
      ∀ q : (Nat.card G).primeFactors,
        Group.IsNilpotent (pCore (q : ℕ) G) :=
    fun _ ↦
      IsPGroup.isNilpotent
        (pCore_isPGroup
          (G := G))
  exact
    Group.nilpotent_of_mulEquiv
      (fittingProductEquiv (G := G))

omit [Finite G] in
/-- The normalizer of the Fitting subgroup is the whole ambient group. -/
@[simp]
theorem normalizer_fittingSubgroup :
    Subgroup.normalizer
        (fittingSubgroup G : Set G) =
      ⊤ :=
  Subgroup.normalizer_eq_top_iff.mpr inferInstance

/-- A nontrivial Fitting subgroup has nontrivial center. -/
theorem center_fittingSubgroup_ne_bot
    (hF : fittingSubgroup G ≠ ⊥) :
    Subgroup.center (fittingSubgroup G) ≠ ⊥ := by
  letI : Nontrivial (fittingSubgroup G) :=
    (Subgroup.nontrivial_iff_ne_bot
      (fittingSubgroup G)).mpr hF
  exact
    Group.IsNilpotent.center_ne_bot
      (fittingSubgroup G)

omit [Finite G] in
/-- If `N` is normal, the image of its Fitting subgroup under the inclusion
`N → G` lies in the Fitting subgroup of `G`. -/
theorem map_fittingSubgroup_subtype_le
    (N : Subgroup G) [N.Normal] :
    (fittingSubgroup N).map N.subtype ≤
      fittingSubgroup G := by
  rw [Subgroup.map_le_iff_le_comap]
  apply fittingSubgroup_le
  intro p hp
  rw [← Subgroup.map_le_iff_le_comap]
  exact
    (le_pCore
      (pCore_isPGroup.map N.subtype)
      (inferInstance :
        ((pCore p N).map N.subtype).Normal)).trans
      (pCore_le_fittingSubgroup hp)

/-- A finite nilpotent group is its own Fitting subgroup. -/
theorem fittingSubgroup_eq_top_of_isNilpotent
    (hG : Group.IsNilpotent G) :
    fittingSubgroup G = ⊤ := by
  letI : Group.IsNilpotent G := hG
  apply (fittingSubgroup G).eq_top_of_card_eq
  rw [card_fittingSubgroup (G := G)]
  calc
    (∏ q : (Nat.card G).primeFactors,
        Nat.card (pCore (q : ℕ) G)) =
        ∏ q : (Nat.card G).primeFactors,
          Nat.card
            (default :
              Sylow (q : ℕ) G) := by
      congr 1 with q
      letI : Fact (q : ℕ).Prime :=
        ⟨Nat.prime_of_mem_primeFactors q.2⟩
      rw [pCore_eq_sylow_of_normal
        (default : Sylow (q : ℕ) G)
        (inferInstance :
          ((default :
            Sylow (q : ℕ) G) :
              Subgroup G).Normal)]
    _ =
        ∏ q : (Nat.card G).primeFactors,
          (q : ℕ) ^
            (Nat.card G).factorization
              (q : ℕ) := by
      congr 1 with ⟨q, hq⟩
      exact
        @Sylow.card_eq_multiplicity
          G _ _ q
          ⟨Nat.prime_of_mem_primeFactors hq⟩
          (default : Sylow q G)
    _ =
        ∏ q ∈ (Nat.card G).primeFactors,
          q ^ (Nat.card G).factorization q :=
      Finset.prod_finset_coe
        (fun q ↦
          q ^ (Nat.card G).factorization q)
        _
    _ =
        (Nat.card G).factorization.prod
          (· ^ ·) :=
      rfl
    _ = Nat.card G :=
      Nat.prod_factorization_pow_eq_self
        Nat.card_pos.ne'

/-- The Fitting subgroup is the whole finite group exactly when the group
is nilpotent. -/
theorem fittingSubgroup_eq_top_iff_isNilpotent :
    fittingSubgroup G = ⊤ ↔
      Group.IsNilpotent G := by
  constructor
  · intro htop
    apply Group.isNilpotent_top.mp
    rw [← htop]
    infer_instance
  · exact fittingSubgroup_eq_top_of_isNilpotent

/-- The Fitting subgroup contains every normal nilpotent subgroup. -/
theorem normal_isNilpotent_le_fittingSubgroup
    (N : Subgroup G) (hN : N.Normal)
    (hnil : Group.IsNilpotent N) :
    N ≤ fittingSubgroup G := by
  letI : N.Normal := hN
  letI : Group.IsNilpotent N := hnil
  have hmap :=
    map_fittingSubgroup_subtype_le
      (G := G) N
  rw [fittingSubgroup_eq_top_of_isNilpotent
    (G := N) hnil] at hmap
  rw [← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at hmap
  exact hmap

/-- Every subgroup of the Fitting subgroup is nilpotent. -/
theorem isNilpotent_of_le_fittingSubgroup
    {N : Subgroup G}
    (hN : N ≤ fittingSubgroup G) :
    Group.IsNilpotent N := by
  haveI :
      Group.IsNilpotent
        (N.subgroupOf (fittingSubgroup G)) :=
    inferInstance
  exact
    Group.nilpotent_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hN)

/-- Among normal subgroups, containment in the Fitting subgroup is
equivalent to nilpotence. -/
theorem normal_isNilpotent_iff_le_fittingSubgroup
    (N : Subgroup G) (hN : N.Normal) :
    Group.IsNilpotent N ↔
      N ≤ fittingSubgroup G := by
  constructor
  · exact
      normal_isNilpotent_le_fittingSubgroup
        N hN
  · exact isNilpotent_of_le_fittingSubgroup

end McKayConjecture.GroupTheory
