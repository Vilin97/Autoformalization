/-
Copyright (c) 2026 Vasil Dimitrov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil Dimitrov
-/
import McKayConjecture.Endopermutation.Module
import McKayConjecture.Endopermutation.RelativeSyzygyBasic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# An explicit permutation basis for the augmentation kernel

Let `X` be a finite nonempty `P`-set and let `σ` be a fixed-point-free
permutation of `X` commuting with the `P`-action. This file constructs an
explicit `P`-permuted basis of

`End_k (ker (k[X] → k))`.

The basis consists of the operator induced by `σ`, together with rank-one
operators indexed by pairs `(a, b)` lying off both the diagonal and the graph
of `σ`.
-/

noncomputable section
open scoped BigOperators
namespace Representation

variable {k X : Type} [Field k]
  [hXfinite : Finite X] [hXnonempty : Nonempty X]

local instance : Fintype X := Fintype.ofFinite X
local instance : DecidableEq X := Classical.decEq X

def DerangementEndomorphismIndex (σ : Equiv.Perm X) :=
  PUnit.{1} ⊕ {ab : X × X // ab.1 ≠ ab.2 ∧ ab.1 ≠ σ ab.2}

noncomputable instance (σ : Equiv.Perm X) :
    Fintype (DerangementEndomorphismIndex σ) := by
  unfold DerangementEndomorphismIndex
  infer_instance

private def ambientDerangementEndomorphism
    (σ : Equiv.Perm X) :
    Module.End k (MonoidAlgebra k X) :=
  (MonoidAlgebra.mapDomainLinearEquiv k k σ).toLinearMap

private def ambientOffGraphEndomorphism
    (σ : Equiv.Perm X) (a b : X) :
    Module.End k (MonoidAlgebra k X) where
  toFun v := v.coeff b •
    (MonoidAlgebra.single a 1 - MonoidAlgebra.single (σ b) 1)
  map_add' u v := by
    simp [add_smul]
  map_smul' c v := by
    simp [mul_smul]

private def ambientDerangementFamily
    (σ : Equiv.Perm X) :
    DerangementEndomorphismIndex σ → Module.End k (MonoidAlgebra k X)
  | Sum.inl _ => ambientDerangementEndomorphism σ
  | Sum.inr ab => ambientOffGraphEndomorphism σ ab.1.1 ab.1.2

omit hXfinite hXnonempty in
private theorem ambientDerangementFamily_mem_augmentationKernel
    (σ : Equiv.Perm X)
    (i : DerangementEndomorphismIndex σ)
    (v : MonoidAlgebra k X)
    (hv : v ∈ augmentationKernel k X) :
    ambientDerangementFamily σ i v ∈ augmentationKernel k X := by
  rcases i with u | ab
  · rw [mem_augmentationKernel]
    exact (permutationAugmentation_mapDomainLinearEquiv k σ v).trans
      ((mem_augmentationKernel k X).mp hv)
  · rw [mem_augmentationKernel]
    change permutationAugmentation k X
      (v.coeff ab.1.2 •
        (MonoidAlgebra.single ab.1.1 1 -
          MonoidAlgebra.single (σ ab.1.2) 1)) = 0
    rw [map_smul, map_sub,
      permutationAugmentation_single,
      permutationAugmentation_single, sub_self, smul_zero]

private def derangementEndomorphismFamily
    (σ : Equiv.Perm X) :
    DerangementEndomorphismIndex σ → Module.End k (augmentationKernel k X) :=
  fun i => (ambientDerangementFamily σ i).restrict
    (ambientDerangementFamily_mem_augmentationKernel σ i)

omit hXfinite hXnonempty in
@[simp] private theorem derangementEndomorphismFamily_inl_apply
    (σ : Equiv.Perm X) (u : PUnit) (v : augmentationKernel k X) :
    derangementEndomorphismFamily (k := k) σ (Sum.inl u) v =
      augmentationKernelEquiv k σ v :=
  rfl

omit hXfinite hXnonempty in
@[simp] private theorem derangementEndomorphismFamily_inr_apply_coe
    (σ : Equiv.Perm X)
    (ab : {ab : X × X // ab.1 ≠ ab.2 ∧ ab.1 ≠ σ ab.2})
    (v : augmentationKernel k X) :
    ((derangementEndomorphismFamily (k := k) σ (Sum.inr ab) v :
        augmentationKernel k X) : MonoidAlgebra k X) =
      v.1.coeff ab.1.2 •
        (MonoidAlgebra.single ab.1.1 1 -
          MonoidAlgebra.single (σ ab.1.2) 1) :=
  rfl

omit hXfinite hXnonempty in
@[simp] private theorem ambientDerangementEndomorphism_single
    (σ : Equiv.Perm X) (b : X) :
    ambientDerangementEndomorphism (k := k) σ
        (MonoidAlgebra.single b 1) =
      MonoidAlgebra.single (σ b) 1 := by
  simp [ambientDerangementEndomorphism]

omit hXfinite hXnonempty in
@[simp] private theorem ambientOffGraphEndomorphism_single
    (σ : Equiv.Perm X) (a b c : X) :
    ambientOffGraphEndomorphism (k := k) σ a b
        (MonoidAlgebra.single c 1) =
      if b = c then
        MonoidAlgebra.single a 1 - MonoidAlgebra.single (σ b) 1
      else 0 := by
  by_cases h : b = c
  · subst c
    simp [ambientOffGraphEndomorphism]
  · simp [ambientOffGraphEndomorphism, h]

omit hXfinite hXnonempty in
@[simp] private theorem ambientDerangementFamily_single_coeff_self
    (σ : Equiv.Perm X) (hσ : ∀ x, σ x ≠ x)
    (i : DerangementEndomorphismIndex σ) (b : X) :
    (ambientDerangementFamily (k := k) σ i
      (MonoidAlgebra.single b 1)).coeff b = 0 := by
  rcases i with u | ab
  · simp [ambientDerangementFamily, hσ b]
  · by_cases hb : ab.1.2 = b
    · subst b
      rw [ambientDerangementFamily, ambientOffGraphEndomorphism_single]
      rw [if_pos rfl]
      rw [MonoidAlgebra.coeff_sub, Finsupp.sub_apply,
        MonoidAlgebra.coeff_single, Finsupp.single_apply,
        MonoidAlgebra.coeff_single, Finsupp.single_apply]
      rw [if_neg ab.2.1, if_neg (hσ _)]
      exact sub_self 0
    · simp [ambientDerangementFamily, hb]

omit hXfinite hXnonempty in
@[simp] private theorem ambientDerangementEndomorphism_single_coeff
    (σ : Equiv.Perm X) (b a : X) :
    (ambientDerangementEndomorphism (k := k) σ
      (MonoidAlgebra.single b 1)).coeff a =
        if σ b = a then 1 else 0 := by
  rw [ambientDerangementEndomorphism_single]
  rw [MonoidAlgebra.coeff_single]
  exact Finsupp.single_apply

omit hXfinite hXnonempty in
@[simp] private theorem ambientOffGraphEndomorphism_single_coeff
    (σ : Equiv.Perm X) (a b c d : X) :
    (ambientOffGraphEndomorphism (k := k) σ a b
      (MonoidAlgebra.single c 1)).coeff d =
      if b = c then
        (if a = d then 1 else 0) - (if σ b = d then 1 else 0)
      else 0 := by
  rw [ambientOffGraphEndomorphism_single]
  by_cases h : b = c
  · rw [if_pos h, MonoidAlgebra.coeff_sub, Finsupp.sub_apply,
      MonoidAlgebra.coeff_single, Finsupp.single_apply,
      MonoidAlgebra.coeff_single, Finsupp.single_apply]
    rw [if_pos h]
  · simp [h]

omit hXfinite hXnonempty in
@[simp] private theorem ambientOffGraphEndomorphism_extract
    (σ : Equiv.Perm X) (ab x :
      {ab : X × X // ab.1 ≠ ab.2 ∧ ab.1 ≠ σ ab.2}) :
    (ambientOffGraphEndomorphism (k := k) σ x.1.1 x.1.2
      (MonoidAlgebra.single ab.1.2 1)).coeff ab.1.1 =
        if x = ab then 1 else 0 := by
  rw [ambientOffGraphEndomorphism_single_coeff]
  by_cases hx : x = ab
  · subst x
    rw [if_pos rfl, if_pos rfl, if_neg (Ne.symm ab.2.2), if_pos rfl]
    exact sub_zero 1
  · by_cases hb : x.1.2 = ab.1.2
    · rw [if_pos hb]
      have ha : x.1.1 ≠ ab.1.1 := by
        intro h
        apply hx
        apply Subtype.ext
        exact Prod.ext h hb
      rw [if_neg ha]
      have hs : σ x.1.2 ≠ ab.1.1 := by
        rw [hb]
        exact Ne.symm ab.2.2
      rw [if_neg hs, if_neg hx]
      exact sub_self 0
    · rw [if_neg hb, if_neg hx]

omit hXfinite hXnonempty in
@[simp] private theorem ambientDerangementFamily_inl_single_coeff
    (σ : Equiv.Perm X) (u : PUnit) (b a : X) :
    (ambientDerangementFamily (k := k) σ (Sum.inl u)
      (MonoidAlgebra.single b 1)).coeff a =
        if σ b = a then 1 else 0 := by
  exact ambientDerangementEndomorphism_single_coeff σ b a

omit hXfinite hXnonempty in
@[simp] private theorem ambientDerangementFamily_inr_extract
    (σ : Equiv.Perm X)
    (ab x : {ab : X × X // ab.1 ≠ ab.2 ∧ ab.1 ≠ σ ab.2}) :
    (ambientDerangementFamily (k := k) σ (Sum.inr x)
      (MonoidAlgebra.single ab.1.2 1)).coeff ab.1.1 =
        if x = ab then 1 else 0 := by
  exact ambientOffGraphEndomorphism_extract σ ab x

private theorem derangementEndomorphismFamily_linearIndependent
    (σ : Equiv.Perm X) (hσ : ∀ x, σ x ≠ x) :
    LinearIndependent k (derangementEndomorphismFamily (k := k) σ) := by
  letI : Fintype (DerangementEndomorphismIndex σ) := by
    unfold DerangementEndomorphismIndex
    infer_instance
  apply Fintype.linearIndependent_iffₛ.mpr
  intro f g hfg i
  let c : DerangementEndomorphismIndex σ → k := f - g
  have hc : ∑ j, c j • derangementEndomorphismFamily (k := k) σ j = 0 := by
    calc
      (∑ j, c j • derangementEndomorphismFamily (k := k) σ j) =
          ∑ j, (f j • derangementEndomorphismFamily (k := k) σ j -
            g j • derangementEndomorphismFamily (k := k) σ j) := by
              apply Finset.sum_congr rfl
              intro j _
              change (f j - g j) •
                derangementEndomorphismFamily (k := k) σ j = _
              exact sub_smul (f j) (g j)
                (derangementEndomorphismFamily (k := k) σ j)
      _ = (∑ j, f j • derangementEndomorphismFamily (k := k) σ j) -
            ∑ j, g j • derangementEndomorphismFamily (k := k) σ j := by
              exact Finset.sum_sub_distrib
                (s := Finset.univ)
                (fun j => f j • derangementEndomorphismFamily (k := k) σ j)
                (fun j => g j • derangementEndomorphismFamily (k := k) σ j)
      _ = 0 := sub_eq_zero.mpr hfg
  have hzero (v : augmentationKernel k X) :
      ∑ j, c j • derangementEndomorphismFamily (k := k) σ j v = 0 := by
    have hz := congrArg
      (fun q : Module.End k (augmentationKernel k X) => q v) hc
    simpa using hz
  let ambientCombination : Module.End k (MonoidAlgebra k X) :=
    ∑ j, c j • ambientDerangementFamily (k := k) σ j
  let col (b : X) : MonoidAlgebra k X :=
    ambientCombination (MonoidAlgebra.single b 1)
  have hcol_eq (b d : X) : col b = col d := by
    let v : augmentationKernel k X :=
      ⟨MonoidAlgebra.single b 1 - MonoidAlgebra.single d 1, by
        rw [mem_augmentationKernel, map_sub,
          permutationAugmentation_single,
          permutationAugmentation_single, sub_self]⟩
    have hz := congrArg Subtype.val (hzero v)
    have hz' : ambientCombination (v : MonoidAlgebra k X) = 0 := by
      simpa [ambientCombination, derangementEndomorphismFamily] using hz
    rw [← sub_eq_zero]
    exact (ambientCombination.map_sub _ _).symm.trans hz'
  have hdiag (b : X) : (col b).coeff b = 0 := by
    simp [col, ambientCombination,
      ambientDerangementFamily_single_coeff_self (k := k) σ hσ]
  have hcol_zero (b : X) : col b = 0 := by
    apply MonoidAlgebra.coeff_injective
    apply Finsupp.ext
    intro a
    rw [hcol_eq b a, hdiag a]
    rfl
  have hcoeff (b a : X) :
      (col b).coeff a =
        ∑ j, c j * (ambientDerangementFamily (k := k) σ j
          (MonoidAlgebra.single b 1)).coeff a := by
    simp [col, ambientCombination, MonoidAlgebra.coeff_sum,
      MonoidAlgebra.coeff_smul, Finset.sum_apply, smul_eq_mul]
  have hoff (ab :
      {ab : X × X // ab.1 ≠ ab.2 ∧ ab.1 ≠ σ ab.2}) :
      c (Sum.inr ab) = 0 := by
    have hz := congrArg (fun v : MonoidAlgebra k X => v.coeff ab.1.1)
      (hcol_zero ab.1.2)
    rw [hcoeff] at hz
    unfold DerangementEndomorphismIndex at hz
    rw [Fintype.sum_sum_type] at hz
    simp only [Fintype.sum_unique] at hz
    simpa [Ne.symm ab.2.2] using hz
  rcases i with u | ab
  · let b : X := Classical.choice (inferInstance : Nonempty X)
    have hz := congrArg (fun v : MonoidAlgebra k X => v.coeff (σ b))
      (hcol_zero b)
    rw [hcoeff] at hz
    unfold DerangementEndomorphismIndex at hz
    rw [Fintype.sum_sum_type] at hz
    simp only [Fintype.sum_unique] at hz
    have hc0 : c (Sum.inl (default : PUnit)) = 0 := by
      simpa [hoff] using hz
    rw [show u = default from Subsingleton.elim _ _]
    change f (Sum.inl (default : PUnit)) -
      g (Sum.inl (default : PUnit)) = 0 at hc0
    exact sub_eq_zero.mp hc0
  · exact sub_eq_zero.mp (hoff ab)

omit hXnonempty in
private theorem card_two_point_complement
    (b d : X) (hbd : b ≠ d) :
    Fintype.card {a : X // a ≠ b ∧ a ≠ d} =
      Fintype.card X - 2 := by
  have heq :
      {a ∈ (Finset.univ : Finset X) | a ≠ b ∧ a ≠ d} =
        ((Finset.univ : Finset X).erase b).erase d := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    aesop
  rw [Fintype.card_subtype, heq, Finset.card_erase_of_mem]
  · rw [Finset.card_erase_of_mem]
    · simp only [Finset.card_univ]
      omega
    · simp
  · simpa using hbd.symm

omit hXnonempty in
private theorem card_off_graph_pairs
    (σ : Equiv.Perm X) (hσ : ∀ b, σ b ≠ b) :
    Fintype.card
        {ab : X × X // ab.1 ≠ ab.2 ∧ ab.1 ≠ σ ab.2} =
      Fintype.card X * (Fintype.card X - 2) := by
  let e :
      {ab : X × X // ab.1 ≠ ab.2 ∧ ab.1 ≠ σ ab.2} ≃
        Σ b : X, {a : X // a ≠ b ∧ a ≠ σ b} :=
    { toFun := fun ab => ⟨ab.1.2, ⟨ab.1.1, ab.2⟩⟩
      invFun := fun ba => ⟨(ba.2.1, ba.1), ba.2.2⟩
      left_inv := by intro ab; rfl
      right_inv := by intro ba; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp_rw [card_two_point_complement _ _ (Ne.symm (hσ _))]
  simp

private theorem two_le_card_of_derangement
    (σ : Equiv.Perm X) (hσ : ∀ b, σ b ≠ b) :
    2 ≤ Fintype.card X := by
  let b : X := Classical.choice (inferInstance : Nonempty X)
  letI : Nontrivial X := ⟨⟨σ b, b, hσ b⟩⟩
  exact Fintype.one_lt_card

private theorem card_derangementEndomorphismIndex
    (σ : Equiv.Perm X) (hσ : ∀ b, σ b ≠ b) :
    Fintype.card (DerangementEndomorphismIndex σ) =
      (Fintype.card X - 1) * (Fintype.card X - 1) := by
  unfold DerangementEndomorphismIndex
  rw [Fintype.card_sum, card_off_graph_pairs σ hσ]
  simp only [Fintype.card_punit]
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le
    (two_le_card_of_derangement σ hσ)
  rw [hm]
  simp
  ring

private theorem finrank_augmentationKernel :
    Module.finrank k (augmentationKernel k X) =
      Fintype.card X - 1 := by
  have hsur : Function.Surjective (permutationAugmentation k X) := by
    intro a
    let x : X := Classical.choice (inferInstance : Nonempty X)
    exact ⟨MonoidAlgebra.single x a,
      permutationAugmentation_single k X x a⟩
  have hrange : LinearMap.range (permutationAugmentation k X) = ⊤ :=
    LinearMap.range_eq_top.mpr hsur
  have hrank := LinearMap.finrank_range_add_finrank_ker
    (permutationAugmentation k X)
  rw [hrange, finrank_top, CommSemiring.finrank_self] at hrank
  have hfree : Module.finrank k (MonoidAlgebra k X) = Fintype.card X := by
    calc
      Module.finrank k (MonoidAlgebra k X) =
          Module.finrank k (X →₀ k) :=
        (MonoidAlgebra.coeffLinearEquiv (S := k) (M := X) k).finrank_eq
      _ = Fintype.card X := Module.finrank_finsupp_self k
  rw [hfree] at hrank
  rw [Nat.add_comm] at hrank
  exact Nat.eq_sub_of_add_eq hrank

private theorem card_derangementEndomorphismIndex_eq_finrank
    (σ : Equiv.Perm X) (hσ : ∀ b, σ b ≠ b) :
    Fintype.card (DerangementEndomorphismIndex σ) =
      Module.finrank k (Module.End k (augmentationKernel k X)) := by
  rw [card_derangementEndomorphismIndex σ hσ,
    Module.finrank_linearMap k k,
    finrank_augmentationKernel]

/-- The explicit endomorphism basis associated with a fixed-point-free
permutation of a finite set.  It consists of the permutation itself and
rank-one maps indexed off the diagonal and off its graph. -/
def augmentationKernelDerangementBasis
    (σ : Equiv.Perm X) (hσ : ∀ b, σ b ≠ b) :
    Module.Basis (DerangementEndomorphismIndex σ) k
      (Module.End k (augmentationKernel k X)) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (derangementEndomorphismFamily (k := k) σ)
    (derangementEndomorphismFamily_linearIndependent σ hσ)
    (card_derangementEndomorphismIndex_eq_finrank σ hσ)

@[simp] theorem augmentationKernelDerangementBasis_apply
    (σ : Equiv.Perm X) (hσ : ∀ b, σ b ≠ b)
    (i : DerangementEndomorphismIndex σ) :
    augmentationKernelDerangementBasis (k := k) σ hσ i =
      derangementEndomorphismFamily (k := k) σ i := by
  exact congrFun
    (coe_basisOfLinearIndependentOfCardEqFinrank'
      (derangementEndomorphismFamily (k := k) σ)
      (derangementEndomorphismFamily_linearIndependent σ hσ)
      (card_derangementEndomorphismIndex_eq_finrank σ hσ)) i


section Equivariance

variable {P : Type} [Group P] [MulAction P X]

/-- The permutation representation on the augmentation kernel of a
finite `P`-set. -/
def augmentationKernelRepresentation :
    Representation k P (augmentationKernel k X) :=
  (Representation.ofMulAction k P X).subrepresentation
    (augmentationKernel k X) (by
      intro g v hv
      rw [Submodule.mem_comap, mem_augmentationKernel]
      have hcomp :
          permutationAugmentation k X ∘ₗ
              Representation.ofMulAction k P X g =
            permutationAugmentation k X := by
        apply MonoidAlgebra.lhom_ext'
        intro x
        apply LinearMap.ext
        intro a
        simp
      change (permutationAugmentation k X ∘ₗ
        Representation.ofMulAction k P X g) v = 0
      rw [hcomp]
      exact (mem_augmentationKernel k X).mp hv)

omit hXfinite hXnonempty in
@[simp] theorem augmentationKernelRepresentation_apply_coe
    [Finite X] [Nonempty X]
    (g : P) (v : augmentationKernel k X) :
    ((augmentationKernelRepresentation (k := k) (P := P) (X := X) g v :
        augmentationKernel k X) : MonoidAlgebra k X) =
      Representation.ofMulAction k P X g (v : MonoidAlgebra k X) :=
  rfl

omit hXfinite hXnonempty in
private theorem augmentationKernelEquiv_action_comm
    (σ : Equiv.Perm X)
    (hcomm : ∀ g : P, ∀ x, σ (g • x) = g • σ x)
    (g : P) (v : augmentationKernel k X) :
    augmentationKernelRepresentation (k := k) (P := P) (X := X) g
        (augmentationKernelEquiv k σ v) =
      augmentationKernelEquiv k σ
        (augmentationKernelRepresentation (k := k) (P := P) (X := X) g v) := by
  apply Subtype.ext
  have hlinear :
      Representation.ofMulAction k P X g ∘ₗ
          (MonoidAlgebra.mapDomainLinearEquiv k k σ).toLinearMap =
        (MonoidAlgebra.mapDomainLinearEquiv k k σ).toLinearMap ∘ₗ
          Representation.ofMulAction k P X g := by
    apply MonoidAlgebra.lhom_ext'
    intro x
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply]
    let e := MonoidAlgebra.mapDomainLinearEquiv k k σ
    calc
      Representation.ofMulAction k P X g (e (MonoidAlgebra.single x a)) =
          Representation.ofMulAction k P X g
            (MonoidAlgebra.single (σ x) a) := by
              exact congrArg _ (MonoidAlgebra.mapDomainLinearEquiv_single σ a x)
      _ = MonoidAlgebra.single (g • σ x) a :=
        Representation.ofMulAction_single g (σ x) a
      _ = MonoidAlgebra.single (σ (g • x)) a := by rw [hcomm]
      _ = e (MonoidAlgebra.single (g • x) a) := by
        exact (MonoidAlgebra.mapDomainLinearEquiv_single σ a (g • x)).symm
      _ = e (Representation.ofMulAction k P X g
          (MonoidAlgebra.single x a)) := by
        exact congrArg e (Representation.ofMulAction_single g x a).symm
  exact LinearMap.congr_fun hlinear v

omit hXfinite hXnonempty in
private theorem ofMulAction_coeff
    (g : P) (b : X) (v : MonoidAlgebra k X) :
    (Representation.ofMulAction k P X g v).coeff (g • b) =
      v.coeff b := by
  rw [Representation.coeff_ofMulAction]
  simp


private def derangementIndexSMul
    (σ : Equiv.Perm X)
    (hcomm : ∀ g : P, ∀ x, σ (g • x) = g • σ x)
    (g : P) :
    DerangementEndomorphismIndex σ → DerangementEndomorphismIndex σ
  | Sum.inl u => Sum.inl u
  | Sum.inr ab => Sum.inr
      ⟨(g • ab.1.1, g • ab.1.2),
        ⟨fun h => ab.2.1 (smul_left_cancel g h),
          fun h => ab.2.2 (smul_left_cancel g
            (by simpa only [hcomm] using h))⟩⟩

/-- The natural action on the explicit endomorphism-basis indices. -/
@[instance_reducible]
def derangementEndomorphismIndexMulAction
    (σ : Equiv.Perm X)
    (hcomm : ∀ g : P, ∀ x, σ (g • x) = g • σ x) :
    MulAction P (DerangementEndomorphismIndex σ) where
  smul := derangementIndexSMul σ hcomm
  one_smul i := by
    rcases i with u | ab
    · rfl
    · apply congrArg Sum.inr
      apply Subtype.ext
      simp
  mul_smul g h i := by
    rcases i with u | ab
    · rfl
    · apply congrArg Sum.inr
      apply Subtype.ext
      simp [mul_smul]



omit hXfinite hXnonempty in
private theorem offGraphEndomorphism_action_comm
    (σ : Equiv.Perm X)
    (hcomm : ∀ g : P, ∀ x, σ (g • x) = g • σ x)
    (g : P)
    (ab : {ab : X × X // ab.1 ≠ ab.2 ∧ ab.1 ≠ σ ab.2})
    (v : augmentationKernel k X) :
    augmentationKernelRepresentation (k := k) (P := P) (X := X) g
        (derangementEndomorphismFamily (k := k) σ (Sum.inr ab) v) =
      derangementEndomorphismFamily (k := k) σ
        (Sum.inr
          ⟨(g • ab.1.1, g • ab.1.2),
            ⟨fun h => ab.2.1 (smul_left_cancel g h),
              fun h => ab.2.2 (smul_left_cancel g
                (by simpa only [hcomm] using h))⟩⟩)
        (augmentationKernelRepresentation
          (k := k) (P := P) (X := X) g v) := by
  apply Subtype.ext
  change Representation.ofMulAction k P X g
      (v.1.coeff ab.1.2 •
        (MonoidAlgebra.single ab.1.1 1 -
          MonoidAlgebra.single (σ ab.1.2) 1)) = _
  rw [map_smul, map_sub,
    Representation.ofMulAction_single,
    Representation.ofMulAction_single,
    derangementEndomorphismFamily_inr_apply_coe]
  change v.1.coeff ab.1.2 •
      (MonoidAlgebra.single (g • ab.1.1) 1 -
        MonoidAlgebra.single (g • σ ab.1.2) 1) =
    (Representation.ofMulAction k P X g v.1).coeff (g • ab.1.2) •
      (MonoidAlgebra.single (g • ab.1.1) 1 -
        MonoidAlgebra.single (σ (g • ab.1.2)) 1)
  rw [ofMulAction_coeff, hcomm]

/-- The explicit derangement basis is permuted by conjugation whenever
the derangement commutes with the group action. -/
def augmentationKernelDerangementPermutationBasis
    (σ : Equiv.Perm X) (hσ : ∀ b, σ b ≠ b)
    (hcomm : ∀ g : P, ∀ x, σ (g • x) = g • σ x) :
    let action := representationLinearAction
      (augmentationKernelRepresentation (k := k) (P := P) (X := X))
    letI := endomorphismConjugationMulSemiringAction action
    letI := endomorphismConjugation_smulCommClass action
    letI := derangementEndomorphismIndexMulAction σ hcomm
    PermutationModuleBasis
      (k := k) (P := P)
      (V := Module.End k (augmentationKernel k X))
      (ι := DerangementEndomorphismIndex σ) := by
  let action := representationLinearAction
    (augmentationKernelRepresentation (k := k) (P := P) (X := X))
  letI := endomorphismConjugationMulSemiringAction action
  letI := endomorphismConjugation_smulCommClass action
  letI := derangementEndomorphismIndexMulAction σ hcomm
  refine
    { basis := augmentationKernelDerangementBasis (k := k) σ hσ
      smul_basis := ?_ }
  intro g i
  rw [augmentationKernelDerangementBasis_apply,
    augmentationKernelDerangementBasis_apply]
  rcases i with u | ab
  · apply LinearMap.ext
    intro v
    rw [endomorphismConjugation_smul action]
    have hinv :
        (↑((linearActionUnit action g)⁻¹) :
          Module.End k (augmentationKernel k X)) =
          augmentationKernelRepresentation
            (k := k) (P := P) (X := X) g⁻¹ := by
      rw [← map_inv]
      exact linearActionUnit_representationLinearAction
        (augmentationKernelRepresentation
          (k := k) (P := P) (X := X)) g⁻¹
    rw [hinv]
    simp only [Module.End.mul_apply]
    change augmentationKernelRepresentation
        (k := k) (P := P) (X := X) g
          (augmentationKernelEquiv k σ
            (augmentationKernelRepresentation
              (k := k) (P := P) (X := X) g⁻¹ v)) =
      augmentationKernelEquiv k σ v
    rw [augmentationKernelEquiv_action_comm σ hcomm]
    simp
  · apply LinearMap.ext
    intro v
    rw [endomorphismConjugation_smul action]
    have hinv :
        (↑((linearActionUnit action g)⁻¹) :
          Module.End k (augmentationKernel k X)) =
          augmentationKernelRepresentation
            (k := k) (P := P) (X := X) g⁻¹ := by
      rw [← map_inv]
      exact linearActionUnit_representationLinearAction
        (augmentationKernelRepresentation
          (k := k) (P := P) (X := X)) g⁻¹
    rw [hinv]
    simp only [Module.End.mul_apply]
    change augmentationKernelRepresentation
        (k := k) (P := P) (X := X) g
          (derangementEndomorphismFamily (k := k) σ (Sum.inr ab)
            (augmentationKernelRepresentation
              (k := k) (P := P) (X := X) g⁻¹ v)) =
      derangementEndomorphismFamily (k := k) σ
        (Sum.inr
          ⟨(g • ab.1.1, g • ab.1.2),
            ⟨fun h => ab.2.1 (smul_left_cancel g h),
              fun h => ab.2.2 (smul_left_cancel g
                (by simpa only [hcomm] using h))⟩⟩) v
    rw [offGraphEndomorphism_action_comm σ hcomm]
    have hv :
        augmentationKernelRepresentation
          (k := k) (P := P) (X := X) g
            (augmentationKernelRepresentation
              (k := k) (P := P) (X := X) g⁻¹ v) = v := by
      let ρ := augmentationKernelRepresentation
        (k := k) (P := P) (X := X)
      calc
        ρ g (ρ g⁻¹ v) = (ρ g * ρ g⁻¹) v := rfl
        _ = ρ (g * g⁻¹) v :=
          congrArg (fun q : Module.End k (augmentationKernel k X) => q v)
            (map_mul ρ g g⁻¹).symm
        _ = v := by simp
    rw [hv]

end Equivariance

end Representation
