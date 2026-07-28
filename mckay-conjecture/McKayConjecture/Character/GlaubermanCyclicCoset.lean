/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanCyclicReduction
import McKayConjecture.GroupTheory.CoprimeOrderPowers
import Mathlib.GroupTheory.SchurZassenhaus

/-!
# Conjugacy in the generating coset of a cyclic coprime action

This file formalizes the group-theoretic coset lemma used in the norm
calculation in the cyclic Glauberman correspondence.
-/

noncomputable section

namespace McKayConjecture

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]
variable (K P : Subgroup G) [K.Normal]
variable [IsCyclic P]
variable {p : ℕ} [Fact p.Prime]

/-- In the coprime split situation, the normal kernel and acting
subgroup are complementary. -/
theorem cyclicCoprimeKernel_isComplement'
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤) :
    K.IsComplement' P := by
  apply
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · exact
      Subgroup.disjoint_of_coprime_natCard
        (card_coprime_pPrimeGroup_pGroup
          K P hK hP)
  · rw [← Subgroup.normal_mul K P, hgenerate]
    rfl

/-- The acting `p`-subgroup is a Sylow subgroup of the generated
coprime extension. -/
def cyclicActingSylow
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤) :
    Sylow p G :=
  hP.toSylow (by
    rw [(cyclicCoprimeKernel_isComplement'
      K P hK hP hgenerate).index_eq_card]
    exact
      (Fact.out : p.Prime).coprime_iff_not_dvd.mp hK)

@[simp]
theorem cyclicActingSylow_coe
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤) :
    (cyclicActingSylow K P hK hP hgenerate :
      Subgroup G) =
        P :=
  rfl

/-- Any element in the generator coset generates the whole quotient
through its cyclic subgroup. -/
theorem cyclicGeneratorCoset_zpowers_quotient_surjective
    (hgenerate : K ⊔ P = ⊤)
    {x : G}
    (hx :
      QuotientGroup.mk' K x =
        QuotientGroup.mk' K
          ((cyclicSubgroupGenerator P : P) : G)) :
    Function.Surjective
      ((QuotientGroup.mk' K).comp
        (Subgroup.zpowers x).subtype) := by
  intro y
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective K y
  obtain ⟨i, hi⟩ :=
    cyclicSubgroupGenerator_coset_normalForm
      K P hgenerate a
  refine
    ⟨⟨x ^ i,
      (Subgroup.zpowers x).zpow_mem
        (Subgroup.mem_zpowers x) i⟩, ?_⟩
  change
    QuotientGroup.mk' K (x ^ i) =
      QuotientGroup.mk' K a
  rw [map_zpow, hx, ← map_zpow]
  apply QuotientGroup.eq_iff_div_mem.mpr
  simpa only [div_eq_mul_inv,
    mul_inv_rev, inv_inv] using
      K.inv_mem
        ((inferInstance : K.Normal).mem_comm hi)

/-- Every element of the generator coset is conjugate to the
generator times a fixed point of the kernel.  This is the first part
of the cyclic coprime coset lemma used in Glauberman's norm
calculation. -/
theorem exists_conjugate_cyclicGenerator_mul_fixedPoint
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (k : K) :
    ∃ a : G,
      ∃ c : cyclicFixedPoints K
          ((cyclicSubgroupGenerator P : P) : G),
        a * (((cyclicSubgroupGenerator P : P) : G) * (k : G)) * a⁻¹ =
          ((cyclicSubgroupGenerator P : P) : G) * (c : G) := by
  let g : G := ((cyclicSubgroupGenerator P : P) : G)
  let x : G := g * (k : G)
  let qK : G →* G ⧸ K := QuotientGroup.mk' K
  have hx : qK x = qK g := by
    change qK (g * (k : G)) = qK g
    rw [map_mul, show qK (k : G) = 1 from
      (QuotientGroup.eq_one_iff (k : G)).mpr k.2,
      mul_one]
  let L : Subgroup G := Subgroup.zpowers x
  let f : L →* G ⧸ K := qK.comp L.subtype
  have hf : Function.Surjective f :=
    cyclicGeneratorCoset_zpowers_quotient_surjective
      K P hgenerate hx
  let Q : Sylow p L := Sylow.nonempty.some
  let e : G ⧸ K ≃* P :=
    (cyclicCoprimeKernel_isComplement'
      K P hK hP hgenerate).symm.QuotientMulEquiv
  have hquotP : IsPGroup p (G ⧸ K) :=
    hP.of_equiv e.symm
  have hQmap : Q.1.map f = ⊤ := by
    let T : Sylow p (G ⧸ K) := Q.mapSurjective hf
    have htop :
        (⊤ : Subgroup (G ⧸ K)) =
          (T : Subgroup (G ⧸ K)) :=
      T.is_maximal' (hquotP.to_subgroup ⊤) le_top
    exact htop.symm
  have hqf :
      Function.Surjective (f.comp Q.1.subtype) := by
    intro y
    have hy : y ∈ Q.1.map f := by
      rw [hQmap]
      exact Subgroup.mem_top y
    obtain ⟨z, hzQ, hzy⟩ := hy
    exact ⟨⟨z, hzQ⟩, hzy⟩
  let R : Subgroup G := Q.1.map L.subtype
  have hRP : IsPGroup p R :=
    Q.isPGroup'.map L.subtype
  have hKR : K.IsComplement' R := by
    apply
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · apply Subgroup.disjoint_of_coprime_natCard
      obtain ⟨n, hn⟩ := hRP.exists_card_eq
      rw [hn]
      exact (hK.pow_left n).symm
    · apply Set.eq_univ_iff_forall.mpr
      intro y
      obtain ⟨z, hz⟩ := hqf (qK y)
      let r : R :=
        ⟨(z : G), ⟨z, z.2, rfl⟩⟩
      have hry : qK (r : G) = qK y := hz
      have hky : y * (r : G)⁻¹ ∈ K := by
        simpa only [div_eq_mul_inv] using
          (QuotientGroup.eq_iff_div_mem.mp
            hry.symm)
      exact
        ⟨y * (r : G)⁻¹, hky,
          (r : G), r.2, by group⟩
  let RSylow : Sylow p G :=
    hRP.toSylow (by
      rw [hKR.index_eq_card]
      exact
        (Fact.out : p.Prime).coprime_iff_not_dvd.mp hK)
  let PSylow : Sylow p G :=
    cyclicActingSylow K P hK hP hgenerate
  obtain ⟨a, ha⟩ :=
    MulAction.exists_smul_eq G RSylow PSylow
  have hgq : qK g ∈ Q.1.map f := by
    rw [hQmap]
    exact Subgroup.mem_top _
  obtain ⟨b, hbQ, hbg⟩ := hgq
  let bR : R :=
    ⟨(b : G), ⟨b, hbQ, rfl⟩⟩
  have hbconjP : a * (b : G) * a⁻¹ ∈ P := by
    change
      a * (b : G) * a⁻¹ ∈
        (PSylow : Subgroup G)
    rw [← ha]
    change
      a * (b : G) * a⁻¹ ∈
        Subgroup.map (MulAut.conj a)
          (RSylow : Subgroup G)
    apply Subgroup.mem_map.mpr
    exact
      ⟨(b : G), bR.2,
        MulAut.conj_apply a (b : G)⟩
  letI : CommGroup P := IsCyclic.commGroup
  letI : IsMulCommutative (G ⧸ K) :=
    ⟨⟨fun u v ↦ e.injective (by
      simpa only [map_mul] using
        mul_comm (e u) (e v))⟩⟩
  have hbquot : qK (b : G) = qK g := hbg
  have hbconjquot :
      qK (a * (b : G) * a⁻¹) = qK g := by
    rw [map_mul, map_mul, map_inv, hbquot]
    rw [IsMulCommutative.is_comm.comm
      (qK a) (qK g),
      mul_assoc, mul_inv_cancel, mul_one]
  have hbconj : a * (b : G) * a⁻¹ = g := by
    have hdivK :
        (a * (b : G) * a⁻¹) / g ∈ K :=
      QuotientGroup.eq_iff_div_mem.mp hbconjquot
    have hdivP :
        (a * (b : G) * a⁻¹) / g ∈ P :=
      P.div_mem hbconjP
        (cyclicSubgroupGenerator P).2
    have hone :=
      eq_one_of_mem_pPrimeGroup_and_pGroup
        K P hK hP hdivK hdivP
    exact div_eq_one.mp hone
  let h : G := (b : G)⁻¹ * x
  have hhK : h ∈ K := by
    apply (QuotientGroup.eq_one_iff h).mp
    change qK ((b : G)⁻¹ * x) = 1
    rw [map_mul, map_inv, hx, hbquot,
      inv_mul_cancel]
  have hcomm : Commute (b : G) h := by
    have hbx : Commute (b : G) x := by
      obtain ⟨i, hi⟩ :=
        Subgroup.mem_zpowers_iff.mp b.2
      rw [← hi]
      exact Commute.zpow_self x i
    exact
      (Commute.refl (b : G)).inv_right.mul_right hbx
  let cG : G := a * h * a⁻¹
  have hcK : cG ∈ K :=
    (inferInstance : K.Normal).conj_mem h hhK a
  have hcg : Commute g cG := by
    rw [← hbconj]
    exact hcomm.conj a
  let c : cyclicFixedPoints K g :=
    ⟨cG, hcK, by
      exact
        Subgroup.mem_centralizer_singleton_iff.mpr
          hcg.eq.symm⟩
  refine ⟨a, c, ?_⟩
  change a * x * a⁻¹ = g * cG
  rw [show x = (b : G) * h by simp [h]]
  calc
    a * ((b : G) * h) * a⁻¹ =
        (a * (b : G) * a⁻¹) *
          (a * h * a⁻¹) := by group
    _ = g * cG := by rw [hbconj]

/-- A fixed-point correction has order coprime to the generator, so
the generator can be recovered as a power of their product. -/
theorem cyclicSubgroupGenerator_mem_zpowers_mul_fixedPoint
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (c : cyclicFixedPoints K
      ((cyclicSubgroupGenerator P : P) : G)) :
    ((cyclicSubgroupGenerator P : P) : G) ∈
      Subgroup.zpowers
        (((cyclicSubgroupGenerator P : P) : G) *
          (c : G)) := by
  let gP : P := cyclicSubgroupGenerator P
  let cK : K := ⟨(c : G), c.2.1⟩
  have hgdiv :
      orderOf ((gP : P) : G) ∣ Nat.card P := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_dvd_natCard gP
  have hcdiv :
      orderOf ((cK : K) : G) ∣ Nat.card K := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_dvd_natCard cK
  have hcoprime :
      (orderOf ((gP : P) : G)).Coprime
        (orderOf ((cK : K) : G)) :=
    Nat.Coprime.of_dvd hgdiv hcdiv
      (card_coprime_pPrimeGroup_pGroup
        K P hK hP).symm
  apply
    left_mem_zpowers_mul_of_commute_of_coprime_orderOf
  · show
      Commute
        ((cyclicSubgroupGenerator P : P) : G)
        (c : G)
    exact
      (Subgroup.mem_centralizer_singleton_iff.mp
        c.2.2).symm
  · exact hcoprime

/-- Any element centralizing a generator times a fixed point also
centralizes the generator itself. -/
theorem centralizer_mul_fixedPoint_le_generator
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (c : cyclicFixedPoints K
      ((cyclicSubgroupGenerator P : P) : G)) :
    Subgroup.centralizer
        ({((cyclicSubgroupGenerator P : P) : G) *
          (c : G)} : Set G) ≤
      Subgroup.centralizer
        ({((cyclicSubgroupGenerator P : P) : G)} :
          Set G) := by
  intro y hy
  have hyx :
      Commute y
        (((cyclicSubgroupGenerator P : P) : G) *
          (c : G)) :=
    Subgroup.mem_centralizer_singleton_iff.mp hy
  obtain ⟨i, hi⟩ :=
    Subgroup.mem_zpowers_iff.mp
      (cyclicSubgroupGenerator_mem_zpowers_mul_fixedPoint
        K P hK hP c)
  have hygi :
      Commute y
        ((((cyclicSubgroupGenerator P : P) : G) *
          (c : G)) ^ i) :=
    hyx.zpow_right i
  rw [hi] at hygi
  exact
    Subgroup.mem_centralizer_singleton_iff.mpr
      hygi.eq

/-- Inside the coprime kernel, centralizing a generator times a fixed
point is the same as centralizing the generator and the fixed point
separately. -/
theorem kernelCentralizer_generator_mul_fixedPoint
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (c : cyclicFixedPoints K
      ((cyclicSubgroupGenerator P : P) : G)) :
    K ⊓ Subgroup.centralizer
        ({((cyclicSubgroupGenerator P : P) : G) *
          (c : G)} : Set G) =
      cyclicFixedPoints K
          ((cyclicSubgroupGenerator P : P) : G) ⊓
        Subgroup.centralizer ({(c : G)} : Set G) := by
  ext y
  constructor
  · intro hy
    have hyg :
        y ∈ Subgroup.centralizer
          ({((cyclicSubgroupGenerator P : P) : G)} :
            Set G) :=
      centralizer_mul_fixedPoint_le_generator
        K P hK hP c hy.2
    have hyx :
        Commute y
          (((cyclicSubgroupGenerator P : P) : G) *
            (c : G)) :=
      Subgroup.mem_centralizer_singleton_iff.mp
        hy.2
    have hyg' :
        Commute y
          ((cyclicSubgroupGenerator P : P) : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hyg
    have hyc : Commute y (c : G) := by
      apply mul_left_cancel
        (a :=
          ((cyclicSubgroupGenerator P : P) : G))
      calc
        ((cyclicSubgroupGenerator P : P) : G) *
              (y * (c : G)) =
            (((cyclicSubgroupGenerator P : P) : G) *
              y) * (c : G) := by
                rw [mul_assoc]
        _ =
            (y *
              ((cyclicSubgroupGenerator P : P) : G)) *
                (c : G) := by
                  rw [← hyg'.eq]
        _ =
            y *
              (((cyclicSubgroupGenerator P : P) : G) *
                (c : G)) := by
                  rw [mul_assoc]
        _ =
            (((cyclicSubgroupGenerator P : P) : G) *
              (c : G)) * y :=
          hyx.eq
        _ =
            ((cyclicSubgroupGenerator P : P) : G) *
              ((c : G) * y) := by
                rw [mul_assoc]
    exact
      ⟨⟨hy.1, hyg⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr
          hyc.eq⟩
  · intro hy
    have hyg :
        Commute y
          ((cyclicSubgroupGenerator P : P) : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp
        hy.1.2
    have hyc : Commute y (c : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp
        hy.2
    exact
      ⟨hy.1.1,
        Subgroup.mem_centralizer_singleton_iff.mpr
          (hyg.mul_right hyc).eq⟩

/-- The centralizer of a generator-coset representative splits into
its kernel centralizer and the cyclic complement.  This is the
centralizer-cardinality part of Glauberman's cyclic coset lemma. -/
theorem card_centralizer_generator_mul_fixedPoint
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (c : cyclicFixedPoints K
      ((cyclicSubgroupGenerator P : P) : G)) :
    Nat.card
        (Subgroup.centralizer
          ({((cyclicSubgroupGenerator P : P) : G) *
            (c : G)} : Set G)) =
      Nat.card
          ↥(K ⊓ Subgroup.centralizer
            ({((cyclicSubgroupGenerator P : P) : G) *
              (c : G)} : Set G)) *
        Nat.card P := by
  let g : G :=
    ((cyclicSubgroupGenerator P : P) : G)
  let x : G := g * (c : G)
  let Z : Subgroup G :=
    Subgroup.centralizer ({x} : Set G)
  have hPZ : P ≤ Z := by
    intro y hyP
    have hyg : Commute (y : G) g := by
      letI : CommGroup P := IsCyclic.commGroup
      exact
        congrArg Subtype.val
          (mul_comm (⟨y, hyP⟩ : P)
            (cyclicSubgroupGenerator P))
    have hcP :
        (c : G) ∈
          Subgroup.centralizer (P : Set G) := by
      rw [
        ← centralizer_singleton_cyclicSubgroupGenerator P]
      exact c.2.2
    have hyc : Commute (y : G) (c : G) :=
      Subgroup.mem_centralizer_iff.mp hcP y hyP
    exact
      Subgroup.mem_centralizer_singleton_iff.mpr
        (hyg.mul_right hyc).eq
  let KZ : Subgroup Z := K.comap Z.subtype
  let PZ : Subgroup Z := P.comap Z.subtype
  letI : KZ.Normal :=
    Subgroup.normal_comap Z.subtype
  have hdisj : Disjoint KZ PZ := by
    rw [Subgroup.disjoint_def]
    intro z hzK hzP
    apply Subtype.ext
    exact
      eq_one_of_mem_pPrimeGroup_and_pGroup
        K P hK hP hzK hzP
  have hmul :
      (KZ : Set Z) * (PZ : Set Z) =
        Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro z
    have hzG :
        (z : G) ∈ (K ⊔ P : Subgroup G) := by
      rw [hgenerate]
      exact Subgroup.mem_top _
    rw [← SetLike.mem_coe,
      Subgroup.normal_mul K P] at hzG
    obtain ⟨k, hkK, y, hyP, hky⟩ := hzG
    change k * y = (z : G) at hky
    have hyZ : y ∈ Z := hPZ hyP
    have hkZ : k ∈ Z := by
      have heq : k = (z : G) * y⁻¹ := by
        calc
          k = (k * y) * y⁻¹ := by group
          _ = (z : G) * y⁻¹ := by rw [hky]
      rw [heq]
      exact Z.mul_mem z.2 (Z.inv_mem hyZ)
    let kz : KZ :=
      ⟨⟨k, hkZ⟩, hkK⟩
    let pz : PZ :=
      ⟨⟨y, hyZ⟩, hyP⟩
    exact
      ⟨kz, kz.2, pz, pz.2, by
        apply Subtype.ext
        exact hky⟩
  have hcomp : KZ.IsComplement' PZ :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
      hdisj hmul
  let eK : KZ ≃* ↥(K ⊓ Z) :=
    { toFun := fun z ↦
        ⟨(z : G), z.2, z.1.2⟩
      invFun := fun z ↦
        ⟨⟨(z : G), z.2.2⟩, z.2.1⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }
  let eP : PZ ≃* P :=
    Subgroup.subgroupOfEquivOfLe hPZ
  change
    Nat.card Z =
      Nat.card ↥(K ⊓ Z) * Nat.card P
  calc
    Nat.card Z =
        Nat.card PZ * PZ.index :=
      (PZ.card_mul_index).symm
    _ = Nat.card PZ * Nat.card KZ := by
      rw [hcomp.index_eq_card]
    _ = Nat.card KZ * Nat.card PZ :=
      Nat.mul_comm _ _
    _ = Nat.card ↥(K ⊓ Z) * Nat.card P := by
      rw [Nat.card_congr eK.toEquiv,
        Nat.card_congr eP.toEquiv]

/-- The cyclic complement centralizes every representative `g c` of
the fixed-point slice of the generator coset. -/
theorem cyclicSubgroup_le_centralizer_generator_mul_fixedPoint
    (c : cyclicFixedPoints K
      ((cyclicSubgroupGenerator P : P) : G)) :
    P ≤
      Subgroup.centralizer
        ({((cyclicSubgroupGenerator P : P) : G) *
          (c : G)} : Set G) := by
  intro y hyP
  have hyg :
      Commute (y : G)
        ((cyclicSubgroupGenerator P : P) : G) := by
    letI : CommGroup P := IsCyclic.commGroup
    exact
      congrArg Subtype.val
        (mul_comm (⟨y, hyP⟩ : P)
          (cyclicSubgroupGenerator P))
  have hcP :
      (c : G) ∈
        Subgroup.centralizer (P : Set G) := by
    rw [
      ← centralizer_singleton_cyclicSubgroupGenerator P]
    exact c.2.2
  have hyc : Commute (y : G) (c : G) :=
    Subgroup.mem_centralizer_iff.mp hcP y hyP
  exact
    Subgroup.mem_centralizer_singleton_iff.mpr
      (hyg.mul_right hyc).eq

/-- Rewriting the kernel factor in the preceding centralizer formula
gives the centralizer in the fixed-point group itself. -/
theorem
    card_centralizer_generator_mul_fixedPoint_eq_fixedCentralizer
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (c : cyclicFixedPoints K
      ((cyclicSubgroupGenerator P : P) : G)) :
    Nat.card
        (Subgroup.centralizer
          ({((cyclicSubgroupGenerator P : P) : G) *
            (c : G)} : Set G)) =
      Nat.card
          (Subgroup.centralizer
            ({c} :
              Set
                (cyclicFixedPoints K
                  ((cyclicSubgroupGenerator P : P) :
                    G)))) *
        Nat.card P := by
  let C : Subgroup G :=
    cyclicFixedPoints K
      ((cyclicSubgroupGenerator P : P) : G)
  let D : Subgroup G :=
    C ⊓
      Subgroup.centralizer ({(c : G)} : Set G)
  let E : Subgroup C :=
    Subgroup.centralizer ({c} : Set C)
  let e : E ≃* D :=
    { toFun := fun z ↦
        ⟨(z : G), z.1.2,
          Subgroup.mem_centralizer_singleton_iff.mpr
            (congrArg Subtype.val
              (Subgroup.mem_centralizer_singleton_iff.mp
                z.2))⟩
      invFun := fun z ↦
        ⟨⟨(z : G), z.2.1⟩,
          Subgroup.mem_centralizer_singleton_iff.mpr
            (Subtype.ext
              (Subgroup.mem_centralizer_singleton_iff.mp
                z.2.2))⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }
  rw [
    card_centralizer_generator_mul_fixedPoint
      K P hK hP hgenerate c,
    kernelCentralizer_generator_mul_fixedPoint
      K P hK hP c]
  exact
    congrArg (fun n : ℕ ↦ n * Nat.card P)
      (Nat.card_congr e.toEquiv).symm

/-- The copy of the cyclic complement in the centralizer of `g c`
is a Sylow subgroup of that centralizer. -/
def cyclicActingCentralizerSylow
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (c : cyclicFixedPoints K
      ((cyclicSubgroupGenerator P : P) : G)) :
    Sylow p
      (Subgroup.centralizer
        ({((cyclicSubgroupGenerator P : P) : G) *
          (c : G)} : Set G)) := by
  let Z : Subgroup G :=
    Subgroup.centralizer
      ({((cyclicSubgroupGenerator P : P) : G) *
        (c : G)} : Set G)
  have hPZ : P ≤ Z :=
    cyclicSubgroup_le_centralizer_generator_mul_fixedPoint
      K P c
  let PZ : Subgroup Z := P.subgroupOf Z
  let eP : PZ ≃* P :=
    Subgroup.subgroupOfEquivOfLe hPZ
  have hPZp : IsPGroup p PZ :=
    hP.of_equiv eP.symm
  apply hPZp.toSylow
  have hcardPZ : Nat.card PZ = Nat.card P :=
    Nat.card_congr eP.toEquiv
  have hcardZ :
      Nat.card Z =
        Nat.card ↥(K ⊓ Z) * Nat.card P :=
    card_centralizer_generator_mul_fixedPoint
      K P hK hP hgenerate c
  have hindex :
      PZ.index = Nat.card ↥(K ⊓ Z) := by
    have hmul := PZ.card_mul_index
    rw [hcardPZ, hcardZ,
      Nat.mul_comm
        (Nat.card ↥(K ⊓ Z))
        (Nat.card P)] at hmul
    exact
      Nat.eq_of_mul_eq_mul_left
        (Nat.card_pos (α := P)) hmul
  rw [hindex]
  apply
    (Fact.out : p.Prime).coprime_iff_not_dvd.mp
  apply hK.coprime_dvd_right
  let Ksub : Subgroup K :=
    (K ⊓ Z).subgroupOf K
  have he :
      Nat.card Ksub =
        Nat.card ↥(K ⊓ Z) :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (show K ⊓ Z ≤ K from inf_le_left)).toEquiv
  rw [← he]
  exact Ksub.card_subgroup_dvd_card

end McKayConjecture
