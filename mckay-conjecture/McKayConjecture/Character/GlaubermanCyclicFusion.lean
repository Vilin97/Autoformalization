/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanCyclicCoset

/-!
# Fusion in the generator coset of a cyclic coprime action

This file proves the Sylow-adjustment step in the cyclic coprime coset
lemma: a conjugator between two fixed-point representatives can be
replaced by one that centralizes the chosen cyclic generator.
-/

noncomputable section

namespace McKayConjecture

variable {G : Type} [Group G] [Finite G]
variable (K P : Subgroup G) [K.Normal]
variable [IsCyclic P]
variable {p : ℕ} [Fact p.Prime]

/-- A conjugator between `g c` and `g d` can be adjusted inside the
target centralizer so that it centralizes the cyclic generator `g`.
This is the Sylow-theoretic core of fusion control in Glauberman's
cyclic coset lemma. -/
theorem exists_generatorCentralizing_conjugator
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (c d : cyclicFixedPoints K
      ((cyclicSubgroupGenerator P : P) : G))
    (a : G)
    (ha :
      a * (((cyclicSubgroupGenerator P : P) : G) *
          (c : G)) * a⁻¹ =
        ((cyclicSubgroupGenerator P : P) : G) *
          (d : G)) :
    ∃ b : G,
      Commute b
          ((cyclicSubgroupGenerator P : P) : G) ∧
        b * (((cyclicSubgroupGenerator P : P) : G) *
            (c : G)) * b⁻¹ =
          ((cyclicSubgroupGenerator P : P) : G) *
            (d : G) := by
  let g : G :=
    ((cyclicSubgroupGenerator P : P) : G)
  let xc : G := g * (c : G)
  let xd : G := g * (d : G)
  let Z : Subgroup G :=
    Subgroup.centralizer ({xd} : Set G)
  have hPZ : P ≤ Z :=
    cyclicSubgroup_le_centralizer_generator_mul_fixedPoint
      K P d
  let PS : Sylow p Z :=
    cyclicActingCentralizerSylow
      K P hK hP hgenerate d
  let ca : G →* G :=
    (MulAut.conj a).toMonoidHom
  let QG : Subgroup G := P.map ca
  have hQGZ : QG ≤ Z := by
    intro q hq
    obtain ⟨y, hyP, rfl⟩ :=
      Subgroup.mem_map.mp hq
    have hyxc : Commute (y : G) xc :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (cyclicSubgroup_le_centralizer_generator_mul_fixedPoint
          K P c hyP)
    have hconj := hyxc.conj a
    rw [ha] at hconj
    exact
      Subgroup.mem_centralizer_singleton_iff.mpr
        hconj.eq
  let QZ : Subgroup Z := QG.subgroupOf Z
  let eQ : QZ ≃* QG :=
    Subgroup.subgroupOfEquivOfLe hQGZ
  let eConj : P ≃* P.map ca :=
    P.equivMapOfInjective ca
      (MulAut.conj a).injective
  have hQGp : IsPGroup p QG := by
    change IsPGroup p (P.map ca)
    exact hP.of_equiv eConj
  have hQZp : IsPGroup p QZ :=
    hQGp.of_equiv eQ.symm
  have hcardQZ :
      Nat.card QZ = Nat.card P := by
    calc
      Nat.card QZ = Nat.card QG :=
        Nat.card_congr eQ.toEquiv
      _ = Nat.card P :=
        (Nat.card_congr eConj.toEquiv).symm
  have hcardZ :
      Nat.card Z =
        Nat.card ↥(K ⊓ Z) * Nat.card P :=
    card_centralizer_generator_mul_fixedPoint
      K P hK hP hgenerate d
  have hindexQZ :
      QZ.index = Nat.card ↥(K ⊓ Z) := by
    have hmul := QZ.card_mul_index
    rw [hcardQZ, hcardZ,
      Nat.mul_comm
        (Nat.card ↥(K ⊓ Z))
        (Nat.card P)] at hmul
    exact
      Nat.eq_of_mul_eq_mul_left
        (Nat.card_pos (α := P)) hmul
  let QS : Sylow p Z :=
    hQZp.toSylow (by
      rw [hindexQZ]
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
            (show K ⊓ Z ≤ K from
              inf_le_left)).toEquiv
      rw [← he]
      exact Ksub.card_subgroup_dvd_card)
  obtain ⟨z, hz⟩ :=
    MulAction.exists_smul_eq Z QS PS
  let qG : G := a * g * a⁻¹
  have hqGQ : qG ∈ QG := by
    apply Subgroup.mem_map.mpr
    exact
      ⟨g, (cyclicSubgroupGenerator P).2,
        MulAut.conj_apply a g⟩
  have hqGZ : qG ∈ Z := hQGZ hqGQ
  let qZ : QZ :=
    ⟨⟨qG, hqGZ⟩, hqGQ⟩
  have hqQS :
      (qZ : Z) ∈ (QS : Subgroup Z) := by
    change (qZ : Z) ∈ QZ
    exact qZ.2
  have hqsmul :
      (MulAut.conj z) qZ ∈
        ((z : Z) • QS : Sylow p Z) := by
    change
      (MulAut.conj z) qZ ∈
        Subgroup.map
          (MulAut.conj z).toMonoidHom
          (QS : Subgroup Z)
    exact
      Subgroup.mem_map_of_mem
        (MulAut.conj z).toMonoidHom hqQS
  rw [hz] at hqsmul
  have hbgbP :
      (z : G) * qG * (z : G)⁻¹ ∈ P := by
    change
      ((MulAut.conj z) qZ : Z) ∈
        (PS : Subgroup Z) at hqsmul
    change
      ((MulAut.conj z) qZ : G) ∈ P at hqsmul
    simpa only [MulAut.conj_apply,
      Subgroup.coe_mul, Subgroup.coe_inv] using hqsmul
  let b : G := (z : G) * a
  have hbgbP' : b * g * b⁻¹ ∈ P := by
    change
      ((z : G) * a) * g *
          ((z : G) * a)⁻¹ ∈ P
    simpa only [qG, mul_inv_rev,
      mul_assoc] using hbgbP
  let qK : G →* G ⧸ K :=
    QuotientGroup.mk' K
  let e : G ⧸ K ≃* P :=
    (cyclicCoprimeKernel_isComplement'
      K P hK hP hgenerate).symm.QuotientMulEquiv
  letI : CommGroup P := IsCyclic.commGroup
  letI : IsMulCommutative (G ⧸ K) :=
    ⟨⟨fun u v ↦ e.injective (by
      simpa only [map_mul] using
        mul_comm (e u) (e v))⟩⟩
  have hbquot :
      qK (b * g * b⁻¹) = qK g := by
    rw [map_mul, map_mul, map_inv]
    rw [IsMulCommutative.is_comm.comm
      (qK b) (qK g),
      mul_assoc, mul_inv_cancel, mul_one]
  have hbgb : b * g * b⁻¹ = g := by
    have hdivK : (b * g * b⁻¹) / g ∈ K :=
      QuotientGroup.eq_iff_div_mem.mp hbquot
    have hdivP : (b * g * b⁻¹) / g ∈ P :=
      P.div_mem hbgbP'
        (cyclicSubgroupGenerator P).2
    exact
      div_eq_one.mp
        (eq_one_of_mem_pPrimeGroup_and_pGroup
          K P hK hP hdivK hdivP)
  have hbcomm : Commute b g := by
    apply (commute_iff_eq b g).mpr
    calc
      b * g = (b * g * b⁻¹) * b := by group
      _ = g * b := by rw [hbgb]
  have hzxd : Commute (z : G) xd :=
    Subgroup.mem_centralizer_singleton_iff.mp
      z.2
  have hbx : b * xc * b⁻¹ = xd := by
    calc
      b * xc * b⁻¹ =
          (z : G) * (a * xc * a⁻¹) *
            (z : G)⁻¹ := by
              simp only [b, mul_inv_rev]
              group
      _ = (z : G) * xd * (z : G)⁻¹ := by
        rw [ha]
      _ = xd := hzxd.mul_inv_cancel
  exact ⟨b, hbcomm, hbx⟩

/-- Fusion of two fixed-point representatives in the generator coset
is realized by an element of the fixed-point subgroup itself. -/
theorem exists_fixedPoint_conjugator_of_generatorCoset_conjugate
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (c d : cyclicFixedPoints K
      ((cyclicSubgroupGenerator P : P) : G))
    (a : G)
    (ha :
      a * (((cyclicSubgroupGenerator P : P) : G) *
          (c : G)) * a⁻¹ =
        ((cyclicSubgroupGenerator P : P) : G) *
          (d : G)) :
    ∃ k :
        cyclicFixedPoints K
          ((cyclicSubgroupGenerator P : P) : G),
      k * c * k⁻¹ = d := by
  let g : G :=
    ((cyclicSubgroupGenerator P : P) : G)
  obtain ⟨b, hbcomm, hbx⟩ :=
    exists_generatorCentralizing_conjugator
      K P hK hP hgenerate c d a ha
  have hbc :
      b * (c : G) * b⁻¹ = (d : G) := by
    apply mul_left_cancel (a := g)
    calc
      g * (b * (c : G) * b⁻¹) =
          (b * g * b⁻¹) *
            (b * (c : G) * b⁻¹) := by
              rw [hbcomm.mul_inv_cancel]
      _ = b * (g * (c : G)) * b⁻¹ := by
        group
      _ = g * (d : G) := hbx
  obtain ⟨i, hiK⟩ :=
    cyclicSubgroupGenerator_coset_normalForm
      K P hgenerate b
  let s : G := g ^ i
  let kG : G := s⁻¹ * b
  have hkK : kG ∈ K := hiK
  have hkcomm : Commute kG g :=
    (Commute.zpow_self g i).inv_left.mul_left
      hbcomm
  let k : cyclicFixedPoints K g :=
    ⟨kG, hkK,
      Subgroup.mem_centralizer_singleton_iff.mpr
        hkcomm.eq⟩
  have hbEq : b = s * kG := by
    simp only [kG, s]
    group
  have hsgk : Commute s kG :=
    (hkcomm.zpow_right i).symm
  have hgc : Commute g (c : G) :=
    (show Commute (c : G) g from
      Subgroup.mem_centralizer_singleton_iff.mp
        c.2.2).symm
  have hsc : Commute s (c : G) :=
    hgc.zpow_left i
  have hsconj :
      Commute s
        (kG * (c : G) * kG⁻¹) :=
    (hsgk.mul_right hsc).mul_right
      hsgk.inv_right
  have hkc :
      kG * (c : G) * kG⁻¹ = (d : G) := by
    rw [hbEq] at hbc
    calc
      kG * (c : G) * kG⁻¹ =
          s * (kG * (c : G) * kG⁻¹) *
            s⁻¹ :=
        hsconj.mul_inv_cancel.symm
      _ =
          (s * kG) * (c : G) *
            (s * kG)⁻¹ := by
        group
      _ = (d : G) := hbc
  refine ⟨k, ?_⟩
  apply Subtype.ext
  exact hkc

/-- Two fixed-point representatives in the generator coset are
conjugate in the ambient group exactly when their fixed-point factors
are conjugate in the fixed-point subgroup. -/
theorem
    generatorCoset_conjugate_iff_fixedPoint_conjugate
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (c d : cyclicFixedPoints K
      ((cyclicSubgroupGenerator P : P) : G)) :
    (∃ a : G,
      a * (((cyclicSubgroupGenerator P : P) : G) *
          (c : G)) * a⁻¹ =
        ((cyclicSubgroupGenerator P : P) : G) *
          (d : G)) ↔
      ∃ k :
          cyclicFixedPoints K
            ((cyclicSubgroupGenerator P : P) : G),
        k * c * k⁻¹ = d := by
  constructor
  · rintro ⟨a, ha⟩
    exact
      exists_fixedPoint_conjugator_of_generatorCoset_conjugate
        K P hK hP hgenerate c d a ha
  · rintro ⟨k, hk⟩
    refine ⟨(k : G), ?_⟩
    have hkg :
        Commute (k : G)
          ((cyclicSubgroupGenerator P : P) : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp
        k.2.2
    have hkG :
        (k : G) * (c : G) * (k : G)⁻¹ =
          (d : G) :=
      congrArg Subtype.val hk
    calc
      (k : G) *
            (((cyclicSubgroupGenerator P : P) : G) *
              (c : G)) *
            (k : G)⁻¹ =
          ((k : G) *
              ((cyclicSubgroupGenerator P : P) : G) *
              (k : G)⁻¹) *
            ((k : G) * (c : G) *
              (k : G)⁻¹) := by
                group
      _ =
          ((cyclicSubgroupGenerator P : P) : G) *
            (d : G) := by
              rw [hkg.mul_inv_cancel, hkG]

end McKayConjecture
