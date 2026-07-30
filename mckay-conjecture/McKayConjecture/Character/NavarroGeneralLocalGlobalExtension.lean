/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.NavarroAbelianLocalGlobalExtension
import McKayConjecture.Character.OkuyamaWajimaPrimeAwayOriginal
import McKayConjecture.CharacterTriple.AssociatedProjectiveObstructionExponent
import McKayConjecture.CharacterTriple.FactorSetCoprimeClassVanishing
import McKayConjecture.CharacterTriple.FactorSetFiniteGroupAnnihilation
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Navarro local--global extension for arbitrary outer quotients

This file develops the cochain-level Sylow-detection argument for the
projective obstruction of a character triple.

The key construction is a relative determinant/transfer formula.  If a
factor set becomes a coboundary on a subgroup `H`, inducing the resulting
one-dimensional projective representation from `H` gives a monomial
projective representation of dimension `[G : H]`.  Taking the product of
its monomial weights gives an explicit coboundary for the pointwise
`[G : H]`th power of the original factor set.

Combining this index annihilator over Sylow subgroups detects the zero
class without relying on a group-cohomology corestriction API.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace CharacterTriple
namespace FactorSet

variable {G A : Type} [Group G] [Finite G] [CommGroup A]

noncomputable local instance leftCosetFintype
    (H : Subgroup G) :
    Fintype (G ⧸ H) :=
  Fintype.ofFinite (G ⧸ H)

/-- The `H`-component in the chosen left-coset decomposition
`g * q.out = (g • q).out * inducedTransition H g q`. -/
def inducedTransition
    (H : Subgroup G) (g : G) (q : G ⧸ H) :
    H :=
  ⟨(g • q).out⁻¹ * g * q.out, by
    rw [mul_assoc]
    rw [← QuotientGroup.leftRel_apply]
    apply Quotient.exact'
    calc
      QuotientGroup.mk (s := H) (g • q).out =
          g • q :=
        QuotientGroup.out_eq' (g • q)
      _ =
          QuotientGroup.mk (s := H) (g * q.out) := by
        simpa only [smul_eq_mul] using
          (MulAction.Quotient.mk_smul_out H g q).symm⟩

omit [Finite G] in
@[simp]
theorem inducedTransition_factorization
    (H : Subgroup G) (g : G) (q : G ⧸ H) :
    (g • q).out * (inducedTransition H g q : G) =
      g * q.out := by
  simp [inducedTransition, mul_assoc]

omit [Finite G] in
/-- The chosen transition elements satisfy the usual Schreier cocycle
identity. -/
theorem inducedTransition_mul
    (H : Subgroup G) (g k : G) (q : G ⧸ H) :
    inducedTransition H (g * k) q =
      inducedTransition H g (k • q) *
        inducedTransition H k q := by
  apply Subtype.ext
  simp only [inducedTransition, Subgroup.coe_mul]
  rw [mul_smul]
  group

/-- The scalar weight of the projectively induced monomial operator.

The cochain `c` is intended to trivialize the restriction of `alpha` to
`H`; its inverse is then the associated one-dimensional projective
representation of `H`. -/
def inducedWeight
    (alpha : FactorSet G A)
    (H : Subgroup G)
    (c : H → A)
    (g : G) (q : G ⧸ H) :
    A :=
  alpha g q.out /
      alpha (g • q).out (inducedTransition H g q : G) *
    (c (inducedTransition H g q))⁻¹

omit [Finite G] in
/-- The induced monomial weights have the original factor set as their
projective multiplication scalar. -/
theorem inducedWeight_mul
    (alpha : FactorSet G A)
    (H : Subgroup G)
    (c : H → A)
    (hc :
      (alpha.comap H.subtype).gauge c =
        (FactorSet.one : FactorSet H A))
    (g k : G) (q : G ⧸ H) :
    inducedWeight alpha H c k q *
        inducedWeight alpha H c g (k • q) =
      alpha g k *
        inducedWeight alpha H c (g * k) q := by
  let h : H := inducedTransition H k q
  let j : H := inducedTransition H g (k • q)
  let l : H := inducedTransition H (g * k) q
  let t : G := q.out
  let u : G := (k • q).out
  let v : G := (g • (k • q)).out
  have hl : l = j * h := by
    exact inducedTransition_mul H g k q
  have hkt : k * t = u * (h : G) := by
    exact (inducedTransition_factorization H k q).symm
  have hgu : g * u = v * (j : G) := by
    exact
      (inducedTransition_factorization H g (k • q)).symm
  have hlambda :
      (c j)⁻¹ * (c h)⁻¹ =
        alpha (j : G) (h : G) * (c (j * h))⁻¹ := by
    have hvalue :=
      congrArg
        (fun beta : FactorSet H A => beta j h)
        hc
    simp only [gauge_apply, comap_apply, one_apply] at hvalue
    have hinv :
        (c j * c h / c (j * h))⁻¹ =
          alpha (j : G) (h : G) :=
      inv_eq_of_mul_eq_one_right hvalue
    calc
      (c j)⁻¹ * (c h)⁻¹ =
          (c j * c h / c (j * h))⁻¹ *
            (c (j * h))⁻¹ := by
        simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
        simp [mul_assoc, mul_comm, mul_left_comm]
      _ =
          alpha (j : G) (h : G) *
            (c (j * h))⁻¹ := by rw [hinv]
  have hcocycle₁ := alpha.cocycle g k t
  have hcocycle₂ := alpha.cocycle g u (h : G)
  have hcocycle₃ := alpha.cocycle v (j : G) (h : G)
  have hthird :
      alpha (v * (j : G)) (h : G) =
        alpha (j : G) (h : G) *
          alpha v ((j : G) * (h : G)) /
          alpha v (j : G) := by
    calc
      alpha (v * (j : G)) (h : G) =
          (alpha (v * (j : G)) (h : G) *
            alpha v (j : G)) /
            alpha v (j : G) := by simp
      _ =
          (alpha (j : G) (h : G) *
            alpha v ((j : G) * (h : G))) /
            alpha v (j : G) := by
        rw [hcocycle₃]
  have halpha :
      alpha g k * alpha (g * k) t =
        alpha k t * alpha g u *
          alpha (j : G) (h : G) *
          alpha v ((j : G) * (h : G)) /
          (alpha u (h : G) * alpha v (j : G)) := by
    calc
      alpha g k * alpha (g * k) t =
          alpha (g * k) t * alpha g k := by
            ac_rfl
      _ = alpha k t * alpha g (k * t) :=
        hcocycle₁
      _ = alpha k t * alpha g (u * (h : G)) := by
        rw [hkt]
      _ =
          alpha k t *
            (alpha (g * u) (h : G) * alpha g u /
              alpha u (h : G)) := by
        congr 1
        calc
          alpha g (u * (h : G)) =
              (alpha u (h : G) *
                alpha g (u * (h : G))) /
                alpha u (h : G) := by simp
          _ =
              (alpha (g * u) (h : G) *
                alpha g u) /
                alpha u (h : G) := by
            rw [hcocycle₂]
      _ =
          alpha k t *
            (alpha (v * (j : G)) (h : G) *
              alpha g u /
              alpha u (h : G)) := by
        rw [hgu]
      _ =
          alpha k t *
            ((alpha (j : G) (h : G) *
                alpha v ((j : G) * (h : G)) /
                alpha v (j : G)) *
              alpha g u /
              alpha u (h : G)) := by
        rw [hthird]
      _ =
          alpha k t * alpha g u *
            alpha (j : G) (h : G) *
            alpha v ((j : G) * (h : G)) /
            (alpha u (h : G) * alpha v (j : G)) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ac_rfl
  simp only [inducedWeight]
  change
    (alpha k t / alpha u (h : G) * (c h)⁻¹) *
        (alpha g u / alpha v (j : G) * (c j)⁻¹) =
      alpha g k *
        (alpha (g * k) t /
          alpha ((g * k) • q).out (l : G) *
          (c l)⁻¹)
  rw [mul_smul]
  change
    (alpha k t / alpha u (h : G) * (c h)⁻¹) *
        (alpha g u / alpha v (j : G) * (c j)⁻¹) =
      alpha g k *
        (alpha (g * k) t / alpha v (l : G) *
          (c l)⁻¹)
  rw [hl]
  simp only [Subgroup.coe_mul]
  calc
    (alpha k t / alpha u (h : G) * (c h)⁻¹) *
          (alpha g u / alpha v (j : G) * (c j)⁻¹) =
        (alpha k t * alpha g u /
            (alpha u (h : G) * alpha v (j : G))) *
          ((c j)⁻¹ * (c h)⁻¹) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ac_rfl
    _ =
        (alpha k t * alpha g u /
            (alpha u (h : G) * alpha v (j : G))) *
          (alpha (j : G) (h : G) *
            (c (j * h))⁻¹) := by
      rw [hlambda]
    _ =
        (alpha k t * alpha g u *
            alpha (j : G) (h : G) /
            (alpha u (h : G) * alpha v (j : G))) *
          (c (j * h))⁻¹ := by
      simp only [div_eq_mul_inv]
      ac_rfl
    _ =
        ((alpha k t * alpha g u *
              alpha (j : G) (h : G) *
              alpha v ((j : G) * (h : G)) /
              (alpha u (h : G) * alpha v (j : G))) /
            alpha v ((j : G) * (h : G))) *
          (c (j * h))⁻¹ := by
      simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    _ =
        (alpha g k * alpha (g * k) t /
            alpha v ((j : G) * (h : G))) *
          (c (j * h))⁻¹ := by
      rw [← halpha]
    _ =
        alpha g k *
          (alpha (g * k) t /
            alpha v ((j : G) * (h : G)) *
            (c (j * h))⁻¹) := by
      simp only [div_eq_mul_inv]
      ac_rfl

/-- Product of the induced monomial weights, i.e. the determinant cochain
with the permutation sign omitted.  The omitted sign is itself an honest
linear character and therefore contributes no factor set. -/
def inducedWeightProduct
    (alpha : FactorSet G A)
    (H : Subgroup G)
    (c : H → A)
    (g : G) :
    A :=
  ∏ q : G ⧸ H, inducedWeight alpha H c g q

/-- The product of induced weights has coboundary equal to the original
factor set raised to the subgroup index. -/
theorem inducedWeightProduct_coboundary
    (alpha : FactorSet G A)
    (H : Subgroup G)
    (c : H → A)
    (hc :
      (alpha.comap H.subtype).gauge c =
        (FactorSet.one : FactorSet H A))
    (g k : G) :
    inducedWeightProduct alpha H c k /
          inducedWeightProduct alpha H c (g * k) *
        inducedWeightProduct alpha H c g =
      alpha g k ^ H.index := by
  have hpointwise :
      ∀ q : G ⧸ H,
        inducedWeight alpha H c k q *
            inducedWeight alpha H c g (k • q) =
          alpha g k *
            inducedWeight alpha H c (g * k) q :=
    inducedWeight_mul alpha H c hc g k
  have hproduct :=
    Fintype.prod_congr
      (fun q : G ⧸ H =>
        inducedWeight alpha H c k q *
          inducedWeight alpha H c g (k • q))
      (fun q : G ⧸ H =>
        alpha g k *
          inducedWeight alpha H c (g * k) q)
      hpointwise
  simp only [Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ] at hproduct
  have hpermute :
      (∏ q : G ⧸ H,
          inducedWeight alpha H c g (k • q)) =
        ∏ q : G ⧸ H,
          inducedWeight alpha H c g q :=
    (MulAction.toPerm k).bijective.prod_comp
      (fun q : G ⧸ H =>
        inducedWeight alpha H c g q)
  rw [hpermute] at hproduct
  change
    inducedWeightProduct alpha H c k /
          inducedWeightProduct alpha H c (g * k) *
        inducedWeightProduct alpha H c g =
      alpha g k ^ H.index
  rw [H.index_eq_card, Nat.card_eq_fintype_card]
  change
    inducedWeightProduct alpha H c k *
        inducedWeightProduct alpha H c g =
      alpha g k ^ Fintype.card (G ⧸ H) *
        inducedWeightProduct alpha H c (g * k) at hproduct
  calc
    inducedWeightProduct alpha H c k /
          inducedWeightProduct alpha H c (g * k) *
        inducedWeightProduct alpha H c g =
      (inducedWeightProduct alpha H c k *
          inducedWeightProduct alpha H c g) /
        inducedWeightProduct alpha H c (g * k) := by
      simp only [div_eq_mul_inv]
      ac_rfl
    _ =
      (alpha g k ^ Fintype.card (G ⧸ H) *
          inducedWeightProduct alpha H c (g * k)) /
        inducedWeightProduct alpha H c (g * k) := by
      rw [hproduct]
    _ = alpha g k ^ Fintype.card (G ⧸ H) := by
      simp

/-- Relative determinant/transfer formula for factor sets: if the
restriction to `H` is cohomologically trivial, then the subgroup index
annihilates the ambient `H²` class. -/
theorem index_nsmul_h2Class_eq_zero_of_comap_cohomologous_one
    (alpha : FactorSet G A)
    (H : Subgroup G)
    (hlocal :
      (alpha.comap H.subtype).Cohomologous
        (FactorSet.one : FactorSet H A)) :
    letI := trivialMulDistribMulAction G A
    H.index • alpha.h2Class = 0 := by
  obtain ⟨c, hc⟩ := hlocal
  apply
    alpha.nsmul_h2Class_eq_zero_of_pow_isMulCoboundary₂
      H.index
  letI := trivialMulDistribMulAction G A
  refine
    ⟨inducedWeightProduct alpha H c, ?_⟩
  intro g k
  exact
    inducedWeightProduct_coboundary
      alpha H c hc.symm g k

/-- An element of an additive group annihilated by every Sylow index is
zero.

Indeed its additive order divides every Sylow index.  If that order were
not one, any prime divisor `r` would divide the index of an `r`-Sylow
subgroup, contradicting the defining Sylow index property. -/
theorem eq_zero_of_sylowIndex_nsmul_eq_zero
    {M : Type} [AddCommGroup M]
    (x : M)
    (hindex :
      ∀ (r : ℕ) (hr : r.Prime),
        letI : Fact r.Prime := ⟨hr⟩
        ∀ R : Sylow r G,
          (R : Subgroup G).index • x = 0) :
    x = 0 := by
  have horder : addOrderOf x = 1 := by
    by_contra hne
    obtain ⟨r, hr, hrorder⟩ :=
      Nat.exists_prime_and_dvd hne
    letI : Fact r.Prime := ⟨hr⟩
    let R : Sylow r G := default
    have horderIndex :
        addOrderOf x ∣ (R : Subgroup G).index :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr
        (hindex r hr R)
    exact
      R.not_dvd_index
        (hrorder.trans horderIndex)
  have horderDvdOne : addOrderOf x ∣ 1 := by
    rw [horder]
  have hone : (1 : ℕ) • x = 0 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mp
      horderDvdOne
  simpa using hone

/-- Sylow restrictions detect the zero class of a factor set on an
arbitrary finite group.  This is the cochain-level replacement for the
usual restriction--corestriction argument. -/
theorem h2Class_eq_zero_of_sylowRestriction_cohomologous_one
    (alpha : FactorSet G A)
    (hlocal :
      ∀ (r : ℕ) (hr : r.Prime),
        letI : Fact r.Prime := ⟨hr⟩
        ∀ R : Sylow r G,
          (alpha.comap (R : Subgroup G).subtype).Cohomologous
            (FactorSet.one : FactorSet R A)) :
    letI := trivialMulDistribMulAction G A
    alpha.h2Class = 0 := by
  letI := trivialMulDistribMulAction G A
  apply
    eq_zero_of_sylowIndex_nsmul_eq_zero
      (G := G) alpha.h2Class
  intro r hr
  letI : Fact r.Prime := ⟨hr⟩
  intro R
  exact
    index_nsmul_h2Class_eq_zero_of_comap_cohomologous_one
      alpha (R : Subgroup G) (hlocal r hr R)

end FactorSet

end CharacterTriple

namespace GroupTheory

variable {G : Type} [Group G] [Finite G]

/-- The index form of the second isomorphism theorem, without assuming
that the left subgroup is normal.  If `N` is normal, then the index of
`H` in `H ⊔ N` is the relative index of `H ⊓ N` in `N`. -/
theorem relIndex_sup_eq_inf_relIndex_of_normal
    (H N : Subgroup G) [N.Normal] :
    H.relIndex (H ⊔ N) =
      (H ⊓ N).relIndex N := by
  have hnormalIndex :
      N.relIndex (H ⊔ N) =
        (H ⊓ N).relIndex H := by
    rw [Subgroup.relIndex_sup_right]
    exact
      (Subgroup.inf_relIndex_left H N).symm
  have hleft :=
    Subgroup.relIndex_mul_relIndex
      (H ⊓ N) H (H ⊔ N)
      inf_le_left le_sup_left
  have hright :=
    Subgroup.relIndex_mul_relIndex
      (H ⊓ N) N (H ⊔ N)
      inf_le_right le_sup_right
  rw [hnormalIndex] at hright
  have hnonzero :
      (H ⊓ N).relIndex H ≠ 0 :=
    by
      change
        ((H ⊓ N).subgroupOf H).index ≠ 0
      exact Subgroup.index_ne_zero_of_finite
  exact
    Nat.eq_of_mul_eq_mul_left
      (Nat.pos_of_ne_zero hnonzero)
      (by
        rw [mul_comm] at hright
        exact hleft.trans hright.symm)

/-- If `W` normalizes `Q`, the index of the internal copy of `W` in
`Q ⊔ W` divides the order of `Q`. -/
theorem index_subgroupOf_sup_dvd_card_of_le_normalizer
    (Q W : Subgroup G)
    (hWN : W ≤ Subgroup.normalizer (Q : Set G)) :
    (W.subgroupOf (Q ⊔ W)).index ∣ Nat.card Q := by
  let L : Subgroup G := Q ⊔ W
  let Qi : Subgroup L := Q.subgroupOf L
  let Wi : Subgroup L := W.subgroupOf L
  have hLN :
      L ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le Subgroup.le_normalizer hWN
  letI : Qi.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hLN
  have hsup : Wi ⊔ Qi = ⊤ := by
    change
      W.subgroupOf L ⊔ Q.subgroupOf L = ⊤
    rw [← Subgroup.subgroupOf_sup
      le_sup_right le_sup_left]
    simp [L, sup_comm]
  rw [← Subgroup.relIndex_top_right]
  change
    Wi.relIndex (⊤ : Subgroup L) ∣ Nat.card Q
  rw [← hsup,
    relIndex_sup_eq_inf_relIndex_of_normal]
  have hcard :
      Nat.card Qi = Nat.card Q :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  simpa [hcard] using
    Subgroup.relIndex_dvd_card (Wi ⊓ Qi) Qi

end GroupTheory

namespace CharacterTriple

section GeneralNavarro

open GroupTheory
open AssociatedProjectiveRepresentation

variable {G : Type} [Group G] [Finite G]

/-- Extension existence for a restricted triple is equivalently extension
of the original character along the direct inclusion into the
intermediate subgroup. -/
theorem restrictTo_hasExtension_iff_exists_extensionAlong_inclusion
    (T : CharacterTriple G)
    (H : Subgroup G)
    (hNH : T.normalSubgroup ≤ H) :
    (T.restrictTo H hNH).HasExtension ↔
      ∃ eta : IrreducibleCharacter H,
        IrreducibleCharacter.IsExtensionAlong
          (Subgroup.inclusion hNH)
          T.character eta := by
  constructor
  · rintro ⟨eta, heta⟩
    refine ⟨eta, ?_⟩
    intro n
    let x : (T.restrictTo H hNH).normalSubgroup :=
      ⟨⟨n, hNH n.2⟩, n.2⟩
    exact heta x
  · rintro ⟨eta, heta⟩
    refine ⟨eta, ?_⟩
    intro x
    exact heta (T.normalSubgroupInEquiv H hNH x)

/-- Extension existence for restricted triples is insensitive to replacing
the intermediate subgroup by an equal subgroup. -/
theorem restrictTo_hasExtension_congr
    (T : CharacterTriple G)
    (B C : Subgroup G)
    (hBC : B = C)
    (hNB : T.normalSubgroup ≤ B)
    (hNC : T.normalSubgroup ≤ C) :
    (T.restrictTo B hNB).HasExtension ↔
      (T.restrictTo C hNC).HasExtension := by
  subst C
  rfl

/-- A global extension yields an extension on the full preimage of any
outer-quotient subgroup. -/
theorem restrictToQuotientSubgroupPreimage_hasExtension_of_hasExtension
    (T : CharacterTriple G)
    (R : Subgroup (G ⧸ T.normalSubgroup))
    (hglobal : T.HasExtension) :
    let H :=
      quotientSubgroupPreimage T.normalSubgroup R
    let hNH :
        T.normalSubgroup ≤ H :=
      normal_le_quotientSubgroupPreimage
        T.normalSubgroup R
    (T.restrictTo H hNH).HasExtension := by
  dsimp only
  obtain ⟨psi, hpsi⟩ := hglobal
  let H :=
    quotientSubgroupPreimage T.normalSubgroup R
  let hNH :
      T.normalSubgroup ≤ H :=
    normal_le_quotientSubgroupPreimage
      T.normalSubgroup R
  let TR := T.restrictTo H hNH
  have hpsi' :
      IrreducibleCharacter.IsExtensionAlong
        (H.subtype.comp TR.normalSubgroup.subtype)
        TR.character psi := by
    intro x
    change
      psi.values (((x : TR.normalSubgroup) : H) : G) =
        T.character.values
          (T.normalSubgroupInEquiv H hNH x)
    rw [← normalSubgroupInEquiv_apply_coe T H hNH x]
    exact hpsi (T.normalSubgroupInEquiv H hNH x)
  obtain ⟨eta, heta, _⟩ :=
    IrreducibleCharacter.IsExtensionAlong.exists_intermediate
      hpsi'
  exact ⟨eta, heta⟩

/-- A single quotient-subgroup preimage detects global extension whenever
its index is coprime to the unconditional associated-factor exponent.

This is the one-local-piece form of the relative determinant argument and
is particularly suited to deleting a normal Sylow subgroup. -/
theorem hasExtension_of_quotientSubgroupPreimage_of_coprime_index
    (T : CharacterTriple G)
    (S : Subgroup (G ⧸ T.normalSubgroup))
    (hlocal :
      let H :=
        quotientSubgroupPreimage T.normalSubgroup S
      let hNH :
          T.normalSubgroup ≤ H :=
        normal_le_quotientSubgroupPreimage
          T.normalSubgroup S
      (T.restrictTo H hNH).HasExtension)
    (hcoprime :
      Nat.Coprime
        (associatedFactorExponent
          T T.character.realization)
        S.index) :
    T.HasExtension := by
  let R := AssociatedGeneralExistence.associated T
  let alpha := R.quotientFactorSet
  have halpha :
      alpha.IsNormalized :=
    R.quotientFactorSet_isNormalized
  have hsection :=
    exists_canonicalAssociatedFactor_section_of_preimageExtension
      T S hlocal
  have hcohomologous :
      (alpha.comap S.subtype).Cohomologous
        (FactorSet.one : FactorSet S ℂˣ) :=
    (FactorSet.CentralExtensionGroup.cohomologous_one_iff_exists_section
      (alpha.comap S.subtype)
      (alpha.comap_isNormalized S.subtype halpha)).mpr
        hsection
  have hindex :
      letI :=
        trivialMulDistribMulAction
          (G ⧸ T.normalSubgroup) ℂˣ
      S.index • alpha.h2Class = 0 :=
    FactorSet.index_nsmul_h2Class_eq_zero_of_comap_cohomologous_one
      alpha S hcohomologous
  have hexponent :
      letI :=
        trivialMulDistribMulAction
          (G ⧸ T.normalSubgroup) ℂˣ
      associatedFactorExponent
          T T.character.realization •
        alpha.h2Class = 0 :=
    R.associatedFactorExponent_nsmul_quotientFactorSet_h2Class_eq_zero
  have hclass :
      letI :=
        trivialMulDistribMulAction
          (G ⧸ T.normalSubgroup) ℂˣ
      alpha.h2Class = 0 :=
    eq_zero_of_coprime_nsmul_eq_zero
      hcoprime hexponent hindex
  have hzero :
      letI :=
        trivialMulDistribMulAction
          (G ⧸ T.normalSubgroup) ℂˣ
      T.projectiveObstructionClass = 0 := by
    rw [← R.quotientFactorSet_h2Class_eq_projectiveObstructionClass]
    exact hclass
  exact
    T.exists_extension_of_projectiveObstructionClass_eq_zero
      hzero

/-- Coprime-index deletion criterion in equivalence form. -/
theorem hasExtension_iff_restrictToQuotientSubgroupPreimage_of_coprime_index
    (T : CharacterTriple G)
    (S : Subgroup (G ⧸ T.normalSubgroup))
    (hcoprime :
      Nat.Coprime
        (associatedFactorExponent
          T T.character.realization)
        S.index) :
    T.HasExtension ↔
      let H :=
        quotientSubgroupPreimage T.normalSubgroup S
      let hNH :
          T.normalSubgroup ≤ H :=
        normal_le_quotientSubgroupPreimage
          T.normalSubgroup S
      (T.restrictTo H hNH).HasExtension := by
  constructor
  · exact
      T.restrictToQuotientSubgroupPreimage_hasExtension_of_hasExtension
        S
  · intro hlocal
    exact
      T.hasExtension_of_quotientSubgroupPreimage_of_coprime_index
        S hlocal hcoprime

/-- Coprime-index extension lifting, stated for an arbitrary intermediate
subgroup containing the distinguished normal subgroup. -/
theorem hasExtension_of_restrictTo_of_coprime_index
    (T : CharacterTriple G)
    (H : Subgroup G)
    (hNH : T.normalSubgroup ≤ H)
    (hlocal : (T.restrictTo H hNH).HasExtension)
    (hcoprime :
      Nat.Coprime
        (associatedFactorExponent
          T T.character.realization)
        H.index) :
    T.HasExtension := by
  let S : Subgroup (G ⧸ T.normalSubgroup) :=
    H.map (QuotientGroup.mk' T.normalSubgroup)
  have hpreimage :
      quotientSubgroupPreimage T.normalSubgroup S = H := by
    change
      S.comap (QuotientGroup.mk' T.normalSubgroup) = H
    dsimp only [S]
    rw [QuotientGroup.comap_map_mk',
      sup_eq_right.mpr hNH]
  have hlocal' :
      let L :=
        quotientSubgroupPreimage T.normalSubgroup S
      let hNL :
          T.normalSubgroup ≤ L :=
        normal_le_quotientSubgroupPreimage
          T.normalSubgroup S
      (T.restrictTo L hNL).HasExtension := by
    dsimp only
    exact
      (restrictTo_hasExtension_congr
        T
        (quotientSubgroupPreimage T.normalSubgroup S)
        H hpreimage
        (normal_le_quotientSubgroupPreimage
          T.normalSubgroup S)
        hNH).mpr hlocal
  have hindex : S.index = H.index := by
    dsimp only [S]
    exact
      H.index_map_eq
        (QuotientGroup.mk'_surjective
          T.normalSubgroup)
        (by
          simpa only [QuotientGroup.ker_mk'] using hNH)
  apply
    T.hasExtension_of_quotientSubgroupPreimage_of_coprime_index
      S hlocal'
  rwa [hindex]

/-- Equivalence form of coprime-index extension lifting for an arbitrary
intermediate subgroup. -/
theorem hasExtension_iff_restrictTo_of_coprime_index
    (T : CharacterTriple G)
    (H : Subgroup G)
    (hNH : T.normalSubgroup ≤ H)
    (hcoprime :
      Nat.Coprime
        (associatedFactorExponent
          T T.character.realization)
        H.index) :
    T.HasExtension ↔
      (T.restrictTo H hNH).HasExtension := by
  constructor
  · intro hglobal
    let S : Subgroup (G ⧸ T.normalSubgroup) :=
      H.map (QuotientGroup.mk' T.normalSubgroup)
    have hpreimage :
        quotientSubgroupPreimage T.normalSubgroup S = H := by
      change
        S.comap (QuotientGroup.mk' T.normalSubgroup) = H
      dsimp only [S]
      rw [QuotientGroup.comap_map_mk',
        sup_eq_right.mpr hNH]
    have hrestricted :=
      T.restrictToQuotientSubgroupPreimage_hasExtension_of_hasExtension
        S hglobal
    dsimp only at hrestricted
    exact
      (restrictTo_hasExtension_congr
        T
        (quotientSubgroupPreimage T.normalSubgroup S)
        H hpreimage
        (normal_le_quotientSubgroupPreimage
          T.normalSubgroup S)
        hNH).mp hrestricted
  · intro hlocal
    exact
      T.hasExtension_of_restrictTo_of_coprime_index
        H hNH hlocal hcoprime

/-- Prime-power-index form of the coprime-index deletion criterion.

The two hypotheses saying that the distinguished character triple has
`p'` kernel and `p'` character degree make its associated-factor
exponent prime to `p`. -/
theorem hasExtension_iff_restrictTo_of_index_dvd_prime_power
    {p n : ℕ} [Fact p.Prime]
    (T : CharacterTriple G)
    (H : Subgroup G)
    (hNH : T.normalSubgroup ≤ H)
    (hN :
      IsPPrimeGroup p T.normalSubgroup)
    (hdegree :
      T.character.IsPPrimeDegree p)
    (hindex : H.index ∣ p ^ n) :
    T.HasExtension ↔
      (T.restrictTo H hNH).HasExtension := by
  have hfactorNotDvd :
      ¬p ∣
        associatedFactorExponent
          T T.character.realization := by
    rw [associatedFactorExponent,
      T.character.realization_finrank]
    intro hdivides
    obtain hdegreeDvd | hcardDvd :=
      (Fact.out : p.Prime).dvd_mul.mp hdivides
    · exact hdegree hdegreeDvd
    · exact
        ((isPPrimeGroup_iff_not_dvd
          (G := T.normalSubgroup)
          (Fact.out : p.Prime)).mp hN)
          hcardDvd
  exact
    T.hasExtension_iff_restrictTo_of_coprime_index
      H hNH
      (Nat.Coprime.coprime_dvd_right hindex
        ((Fact.out : p.Prime).coprime_pow_of_not_dvd
          hfactorNotDvd))

/-- Extension on every quotient Sylow preimage implies global extension,
with no commutativity assumption on the outer quotient. -/
theorem hasExtension_of_quotientSylowPreimageExtensions
    (T : CharacterTriple G)
    (hlocal :
      ∀ (r : ℕ) (hr : r.Prime),
        letI : Fact r.Prime := ⟨hr⟩
        ∀ R : Sylow r (G ⧸ T.normalSubgroup),
          T.ExtendsToQuotientSylowPreimage R) :
    T.HasExtension := by
  let R := AssociatedGeneralExistence.associated T
  let alpha := R.quotientFactorSet
  have halpha :
      alpha.IsNormalized :=
    R.quotientFactorSet_isNormalized
  have hsylow :
      ∀ (r : ℕ) (hr : r.Prime),
        letI : Fact r.Prime := ⟨hr⟩
        ∀ P : Sylow r (G ⧸ T.normalSubgroup),
          (alpha.comap
              (P : Subgroup
                (G ⧸ T.normalSubgroup)).subtype).Cohomologous
            (FactorSet.one : FactorSet P ℂˣ) := by
    intro r hr
    letI : Fact r.Prime := ⟨hr⟩
    intro P
    have hlocalP :
        let H :=
          quotientSubgroupPreimage T.normalSubgroup
            (P : Subgroup (G ⧸ T.normalSubgroup))
        let hNH :
            T.normalSubgroup ≤ H :=
          normal_le_quotientSubgroupPreimage
            T.normalSubgroup
            (P : Subgroup (G ⧸ T.normalSubgroup))
        (T.restrictTo H hNH).HasExtension := by
      simpa only [ExtendsToQuotientSylowPreimage, HasExtension] using
        hlocal r hr P
    have hsection :=
      exists_canonicalAssociatedFactor_section_of_preimageExtension
        T (P : Subgroup (G ⧸ T.normalSubgroup)) hlocalP
    exact
      (FactorSet.CentralExtensionGroup.cohomologous_one_iff_exists_section
          (alpha.comap
            (P : Subgroup
              (G ⧸ T.normalSubgroup)).subtype)
          (alpha.comap_isNormalized
            (P : Subgroup
              (G ⧸ T.normalSubgroup)).subtype halpha)).mpr
        hsection
  have hclass :
      letI :=
        trivialMulDistribMulAction
          (G ⧸ T.normalSubgroup) ℂˣ
      alpha.h2Class = 0 :=
    FactorSet.h2Class_eq_zero_of_sylowRestriction_cohomologous_one
      alpha hsylow
  have hzero :
      letI :=
        trivialMulDistribMulAction
          (G ⧸ T.normalSubgroup) ℂˣ
      T.projectiveObstructionClass = 0 := by
    rw [← R.quotientFactorSet_h2Class_eq_projectiveObstructionClass]
    exact hclass
  exact
    T.exists_extension_of_projectiveObstructionClass_eq_zero
      hzero

/-- Navarro's Sylow-preimage local--global extension criterion for every
finite character triple. -/
theorem navarroSylowPreimageExtensionConclusion
    (T : CharacterTriple G) :
    NavarroSylowPreimageExtensionConclusion T := by
  constructor
  · intro hglobal r hr
    letI : Fact r.Prime := ⟨hr⟩
    exact
      T.extendsToQuotientSylowPreimage_of_hasExtension
        hglobal
  · exact
      T.hasExtension_of_quotientSylowPreimageExtensions

end GeneralNavarro

end CharacterTriple

section OkuyamaWajimaQDeletion

open CharacterTriple
open GroupTheory

variable {A : Type} [Group A] [Finite A]
variable {p : ℕ} [Fact p.Prime]
variable (K Q W : Subgroup A) [K.Normal]

omit [Fact p.Prime] in
/-- On the source side of the prime-away Okuyama--Wajima argument, the
index of `W K` in `Q W K` divides the order of `Q`.

The normal-product intersection is
`(W ⊔ K) ⊓ (K ⊔ Q) = K`; the index form of the second isomorphism theorem
then reduces the claim to a relative index inside `Q`. -/
theorem okuyamaWajimaSourceDeletion_index_dvd_card
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hKQ : (K ⊔ Q).Normal)
    (hW : IsPPrimeGroup p W)
    (hWN : W ≤ Subgroup.normalizer (Q : Set A))
    (hCW : coprimeFixedPoints K Q ≤ W) :
    ((W ⊔ K).subgroupOf ((Q ⊔ W) ⊔ K)).index ∣
      Nat.card Q := by
  let H : Subgroup A := W ⊔ K
  let N : Subgroup A := K ⊔ Q
  let B : Subgroup A := (Q ⊔ W) ⊔ K
  letI : N.Normal := hKQ
  have hWN' :
      W ⊓ N = coprimeFixedPoints K Q :=
    pPrimeNormalizer_inf_normalProduct_eq_fixedPoints
      K Q W hQ hK hW hWN hCW
  have hinter : H ⊓ N = K := by
    apply le_antisymm
    · intro x hx
      obtain ⟨w, hwW, k, hkK, hwk⟩ :=
        Subgroup.mem_sup_of_normal_right.mp hx.1
      have hkN : k ∈ N :=
        (show K ≤ N from le_sup_left) hkK
      have hwN : w ∈ N := by
        have hwEq : w = x * k⁻¹ := by
          rw [← hwk]
          group
        rw [hwEq]
        exact N.mul_mem hx.2 (N.inv_mem hkN)
      have hwK : w ∈ K := by
        have hwC :
            w ∈ coprimeFixedPoints K Q := by
          rw [← hWN']
          exact ⟨hwW, hwN⟩
        exact hwC.1
      rw [← hwk]
      exact K.mul_mem hwK hkK
    · exact le_inf le_sup_right le_sup_left
  have hB : B = H ⊔ N := by
    dsimp only [B, H, N]
    ac_rfl
  change H.relIndex B ∣ Nat.card Q
  rw [hB,
    relIndex_sup_eq_inf_relIndex_of_normal,
    hinter,
    Subgroup.relIndex_sup_left]
  exact Subgroup.relIndex_dvd_card K Q

/-- Source-side Navarro deletion: adjoining the normal `p`-subgroup `Q`
does not change whether `theta` extends from `K` to `W K`. -/
theorem invariantOkuyamaWajimaSource_adjoinQ_extension_iff
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hKQ : (K ⊔ Q).Normal)
    (hWN : W ≤ Subgroup.normalizer (Q : Set A))
    (hCW : coprimeFixedPoints K Q ≤ W)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hW : IsPPrimeGroup p W) :
    ((∃ psi : IrreducibleCharacter (W ⊔ K : Subgroup A),
        IrreducibleCharacter.IsExtensionAlong
          (Subgroup.inclusion le_sup_right)
          theta.1.1 psi) ↔
      ∃ psi :
          IrreducibleCharacter ((Q ⊔ W) ⊔ K : Subgroup A),
        IrreducibleCharacter.IsExtensionAlong
          (Subgroup.inclusion le_sup_right)
          theta.1.1 psi) := by
  let U : Subgroup A := Q ⊔ W
  let B : Subgroup A := U ⊔ K
  let T :=
    invariantOkuyamaWajimaSourceTriple
      K Q U theta hinvariant
  let H : Subgroup B := (W ⊔ K).subgroupOf B
  have hU : U ≤ Subgroup.normalizer (Q : Set A) :=
    sup_le Subgroup.le_normalizer hWN
  have hCU : coprimeFixedPoints K Q ≤ U :=
    hCW.trans le_sup_right
  have hNH : T.normalSubgroup ≤ H := by
    change K.subgroupOf B ≤ (W ⊔ K).subgroupOf B
    intro x hx
    exact
      (show K ≤ W ⊔ K from le_sup_right) hx
  have hN : IsPPrimeGroup p T.normalSubgroup :=
    (invariantOkuyamaWajima_internalKernels_isPPrime
      K Q U hK hU hCU d theta hinvariant).1
  have hdegree : T.character.IsPPrimeDegree p :=
    theta.1.2
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  have hindexCard :
      H.index ∣ Nat.card Q :=
    okuyamaWajimaSourceDeletion_index_dvd_card
      K Q W hQ hK hKQ hW hWN hCW
  have hindex : H.index ∣ p ^ n := by
    rwa [← hn]
  have hnav :
      T.HasExtension ↔
        (T.restrictTo H hNH).HasExtension :=
    T.hasExtension_iff_restrictTo_of_index_dvd_prime_power
      H hNH hN hdegree hindex
  have hKMap : K ≤ H.map B.subtype := by
    intro k hk
    let b : B :=
      ⟨k, (show K ≤ U ⊔ K from le_sup_right) hk⟩
    let x : H :=
      ⟨b, (show K ≤ W ⊔ K from le_sup_right) hk⟩
    exact ⟨x, x.2, rfl⟩
  have himage :
      H.map B.subtype = W ⊔ K := by
    dsimp only [H]
    exact
      Subgroup.map_subgroupOf_eq_of_le
        (show W ⊔ K ≤ B by
          dsimp only [B, U]
          exact sup_le
            (le_sup_right.trans le_sup_left)
            le_sup_right)
  have hmap :=
    IrreducibleCharacter.exists_extensionAlong_map_subtype_iff
      K B le_sup_right H hNH hKMap theta.1.1
  have hcoord :=
    IrreducibleCharacter.exists_extensionAlong_inclusion_congr
      K (H.map B.subtype) (W ⊔ K)
      hKMap le_sup_right himage theta.1.1
  have hinternal :
      (∃ eta : IrreducibleCharacter H,
          IrreducibleCharacter.IsExtensionAlong
            (Subgroup.inclusion hNH)
            T.character eta) ↔
        (T.restrictTo H hNH).HasExtension :=
    (CharacterTriple.restrictTo_hasExtension_iff_exists_extensionAlong_inclusion
      T H hNH).symm
  have hsmall :
      (∃ psi : IrreducibleCharacter (W ⊔ K : Subgroup A),
          IrreducibleCharacter.IsExtensionAlong
            (Subgroup.inclusion le_sup_right)
            theta.1.1 psi) ↔
        (T.restrictTo H hNH).HasExtension := by
    have hmap' :
        ((∃ psi :
            IrreducibleCharacter (H.map B.subtype),
            IrreducibleCharacter.IsExtensionAlong
              (Subgroup.inclusion hKMap)
              theta.1.1 psi) ↔
          ∃ eta : IrreducibleCharacter H,
            IrreducibleCharacter.IsExtensionAlong
              (Subgroup.inclusion hNH)
              T.character eta) := by
      have hTcharacter :
          T.character =
            theta.1.1.comap
              (Subgroup.subgroupOfEquivOfLe
                (show K ≤ B from le_sup_right)) := by
        rfl
      rw [hTcharacter]
      convert hmap using 1
      rfl
    exact (hcoord.symm.trans hmap').trans hinternal
  have hbig :
      (∃ psi :
          IrreducibleCharacter ((Q ⊔ W) ⊔ K : Subgroup A),
          IrreducibleCharacter.IsExtensionAlong
            (Subgroup.inclusion le_sup_right)
            theta.1.1 psi) ↔
        T.HasExtension := by
    rw [exists_extensionAlong_inclusion_iff_subgroupOf]
    rfl
  exact hsmall.trans (hnav.symm.trans hbig.symm)

/-- Target-side Navarro deletion: adjoining `Q` does not change whether
the Glauberman correspondent extends from `C_K(Q)` to `W`. -/
theorem invariantOkuyamaWajimaTarget_adjoinQ_extension_iff
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hWN : W ≤ Subgroup.normalizer (Q : Set A))
    (hCW : coprimeFixedPoints K Q ≤ W)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) :
    ((∃ phi : IrreducibleCharacter W,
        IrreducibleCharacter.IsExtensionAlong
          (Subgroup.inclusion hCW)
          (d.characterEquiv theta).1 phi) ↔
      ∃ phi : IrreducibleCharacter (Q ⊔ W : Subgroup A),
        IrreducibleCharacter.IsExtensionAlong
          (Subgroup.inclusion (hCW.trans le_sup_right))
          (d.characterEquiv theta).1 phi) := by
  let C : Subgroup A := coprimeFixedPoints K Q
  let B : Subgroup A := Q ⊔ W
  have hB : B ≤ Subgroup.normalizer (Q : Set A) :=
    sup_le Subgroup.le_normalizer hWN
  have hCB : C ≤ B :=
    hCW.trans le_sup_right
  let T :=
    invariantOkuyamaWajimaTargetTriple
      K Q B hB hCB d theta hinvariant
  let H : Subgroup B := W.subgroupOf B
  have hNH : T.normalSubgroup ≤ H := by
    change C.subgroupOf B ≤ W.subgroupOf B
    intro x hx
    exact hCW hx
  have hN : IsPPrimeGroup p T.normalSubgroup :=
    (invariantOkuyamaWajima_internalKernels_isPPrime
      K Q B hK hB hCB d theta hinvariant).2
  have hdegree : T.character.IsPPrimeDegree p :=
    (d.characterEquiv theta).2
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  have hindexCard :
      H.index ∣ Nat.card Q :=
    index_subgroupOf_sup_dvd_card_of_le_normalizer
      Q W hWN
  have hindex : H.index ∣ p ^ n := by
    rwa [← hn]
  have hnav :
      T.HasExtension ↔
        (T.restrictTo H hNH).HasExtension :=
    T.hasExtension_iff_restrictTo_of_index_dvd_prime_power
      H hNH hN hdegree hindex
  have hCMap : C ≤ H.map B.subtype := by
    intro c hc
    let b : B := ⟨c, hCB hc⟩
    let x : H := ⟨b, hCW hc⟩
    exact ⟨x, x.2, rfl⟩
  have himage :
      H.map B.subtype = W := by
    dsimp only [H]
    exact
      Subgroup.map_subgroupOf_eq_of_le le_sup_right
  have hmap :=
    IrreducibleCharacter.exists_extensionAlong_map_subtype_iff
      C B hCB H hNH hCMap (d.characterEquiv theta).1
  have hcoord :=
    IrreducibleCharacter.exists_extensionAlong_inclusion_congr
      C (H.map B.subtype) W
      hCMap hCW himage (d.characterEquiv theta).1
  have hinternal :
      (∃ eta : IrreducibleCharacter H,
          IrreducibleCharacter.IsExtensionAlong
            (Subgroup.inclusion hNH)
            T.character eta) ↔
        (T.restrictTo H hNH).HasExtension :=
    (CharacterTriple.restrictTo_hasExtension_iff_exists_extensionAlong_inclusion
      T H hNH).symm
  have hsmall :
      (∃ phi : IrreducibleCharacter W,
          IrreducibleCharacter.IsExtensionAlong
            (Subgroup.inclusion hCW)
            (d.characterEquiv theta).1 phi) ↔
        (T.restrictTo H hNH).HasExtension := by
    have hmap' :
        ((∃ phi :
            IrreducibleCharacter (H.map B.subtype),
            IrreducibleCharacter.IsExtensionAlong
              (Subgroup.inclusion hCMap)
              (d.characterEquiv theta).1 phi) ↔
          ∃ eta : IrreducibleCharacter H,
            IrreducibleCharacter.IsExtensionAlong
              (Subgroup.inclusion hNH)
              T.character eta) := by
      have hTcharacter :
          T.character =
            (d.characterEquiv theta).1.comap
              (Subgroup.subgroupOfEquivOfLe hCB) := by
        rfl
      rw [hTcharacter]
      convert hmap using 1
      rfl
    exact (hcoord.symm.trans hmap').trans hinternal
  have hbig :
      (∃ phi : IrreducibleCharacter (Q ⊔ W : Subgroup A),
          IrreducibleCharacter.IsExtensionAlong
            (Subgroup.inclusion
              (hCW.trans le_sup_right))
            (d.characterEquiv theta).1 phi) ↔
        T.HasExtension := by
    rw [exists_extensionAlong_inclusion_iff_subgroupOf]
    rfl
  exact hsmall.trans (hnav.symm.trans hbig.symm)

variable (V : Subgroup A)

/-- The general Navarro theorem discharges the entire prime-away
Okuyama--Wajima `Q`-deletion input whenever `K Q` is normal. -/
theorem invariantOkuyamaWajimaPrimeAwayQDeletionInput_of_normalProduct
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hKQ : (K ⊔ Q).Normal)
    (hV : V ≤ Subgroup.normalizer (Q : Set A))
    (hCV : coprimeFixedPoints K Q ≤ V)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) :
    InvariantOkuyamaWajimaPrimeAwayQDeletionInput
      K Q V hQ hK hV hCV d theta hinvariant := by
  intro r hr hrp
  letI : Fact r.Prime := ⟨hr⟩
  intro R
  let W :=
    okuyamaWajimaTargetSylowPreimageImage
      K Q V hV hCV d theta hinvariant R
  have hCW : coprimeFixedPoints K Q ≤ W :=
    coprimeFixedPoints_le_okuyamaWajimaTargetSylowPreimageImage
      K Q V hV hCV d theta hinvariant R
  have hWN : W ≤ Subgroup.normalizer (Q : Set A) :=
    okuyamaWajimaTargetSylowPreimageImage_le_normalizer
      K Q V hV hCV d theta hinvariant R
  have hW : IsPPrimeGroup p W :=
    isPPrimeGroup_okuyamaWajimaTargetSylowPreimageImage_of_ne
      K Q V hK hV hCV d theta hinvariant hrp R
  exact
    ⟨invariantOkuyamaWajimaSource_adjoinQ_extension_iff
        K Q W hQ hK hKQ hWN hCW
        d theta hinvariant hW,
      invariantOkuyamaWajimaTarget_adjoinQ_extension_iff
        K Q W hQ hK hWN hCW
        d theta hinvariant⟩

end OkuyamaWajimaQDeletion

end McKayConjecture
