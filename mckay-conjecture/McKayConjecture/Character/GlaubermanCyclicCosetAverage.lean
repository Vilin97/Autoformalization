/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanCyclicFusion
import McKayConjecture.GroupTheory.ConjugacyClassCard

/-!
# Class-function averages on a cyclic generator coset

The cyclic coprime coset lemma identifies conjugacy classes in the
generator coset `gK` with conjugacy classes in the fixed-point subgroup
`C_K(g)`. Together with the corresponding centralizer-cardinality
formula, this transports class-function averages between the two
spaces.

The theorem below is stated for an arbitrary ambient class function.
Its principal application is the product
`x ↦ χ(x) χ(x⁻¹)` for a cyclic extension character.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture

variable {G : Type} [Group G] [Finite G]
variable (K P : Subgroup G) [K.Normal]
variable [IsCyclic P]
variable {p : ℕ} [Fact p.Prime]

/-- The class-function sum over the generator coset, normalized by
`|K|`, equals the sum over the fixed-point slice, normalized by the
order of the fixed-point subgroup. The equality is written without
division so it is valid over any characteristic-zero coefficient
field specialized here to `ℂ`. -/
theorem cyclicGeneratorCoset_classFunction_sum
    [Fintype K]
    [Fintype
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G))]
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (f : ClassFunction G) :
    (Nat.card
          (cyclicFixedPoints K
            ((cyclicSubgroupGenerator P : P) : G)) : ℂ) *
        ∑ k : K,
          f (((cyclicSubgroupGenerator P : P) : G) *
            (k : G)) =
      (Nat.card K : ℂ) *
        ∑ c :
            cyclicFixedPoints K
              ((cyclicSubgroupGenerator P : P) : G),
          f (((cyclicSubgroupGenerator P : P) : G) *
            (c : G)) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let g : G :=
    ((cyclicSubgroupGenerator P : P) : G)
  let C : Type :=
    cyclicFixedPoints K g
  let Q : Type := G ⧸ K
  let e : Q ≃* P :=
    (cyclicCoprimeKernel_isComplement'
      K P hK hP hgenerate).symm.QuotientMulEquiv
  letI : CommGroup P := IsCyclic.commGroup
  letI : CommGroup Q :=
    e.toMonoidHom.commGroupOfInjective e.injective
  let qK : G →* Q := QuotientGroup.mk' K
  let phi : ConjClasses C → ConjClasses G :=
    Quotient.lift
      (fun c : C ↦ ConjClasses.mk (g * (c : G)))
      (by
        intro c d hcd
        apply ConjClasses.mk_eq_mk_iff_isConj.mpr
        apply isConj_iff.mpr
        exact
          (generatorCoset_conjugate_iff_fixedPoint_conjugate
            K P hK hP hgenerate c d).mpr
              (isConj_iff.mp hcd))
  have hphi_mk (c : C) :
      phi (ConjClasses.mk c) =
        ConjClasses.mk (g * (c : G)) :=
    rfl
  have hphi_injective : Function.Injective phi := by
    intro X Y hXY
    induction X using Quotient.inductionOn with
    | _ c =>
      induction Y using Quotient.inductionOn with
      | _ d =>
        apply ConjClasses.mk_eq_mk_iff_isConj.mpr
        apply isConj_iff.mpr
        apply
          (generatorCoset_conjugate_iff_fixedPoint_conjugate
            K P hK hP hgenerate c d).mp
        apply isConj_iff.mp
        exact
          ConjClasses.mk_eq_mk_iff_isConj.mp
            (by
              change
                ConjClasses.mk (g * (c : G)) =
                  ConjClasses.mk (g * (d : G)) at hXY
              exact hXY)
  let phiEquiv :
      ConjClasses C ≃ Set.range phi :=
    Equiv.ofInjective phi hphi_injective
  let classK : K → Set.range phi :=
    fun k ↦ by
      let hex :=
        exists_conjugate_cyclicGenerator_mul_fixedPoint
          K P hK hP hgenerate k
      let a : G := Classical.choose hex
      let c : C :=
        Classical.choose (Classical.choose_spec hex)
      have hc :
          a * (g * (k : G)) * a⁻¹ =
            g * (c : G) :=
        Classical.choose_spec
          (Classical.choose_spec hex)
      refine
        ⟨ConjClasses.mk (g * (k : G)), ?_⟩
      refine ⟨ConjClasses.mk c, ?_⟩
      rw [hphi_mk]
      apply
        (ConjClasses.mk_eq_mk_iff_isConj.mpr
          (isConj_iff.mpr ⟨a, hc⟩)).symm
  have hclassK_val (k : K) :
      (classK k : ConjClasses G) =
        ConjClasses.mk (g * (k : G)) :=
    rfl
  have hphiEquiv_val (X : ConjClasses C) :
      ((phiEquiv X : Set.range phi) :
          ConjClasses G) =
        phi X :=
    rfl
  have hsumK :
      (∑ k : K, f (g * (k : G))) =
        ∑ X : Set.range phi,
          ∑ k : {k : K // classK k = X},
            f (g * (k : K) : G) := by
    calc
      _ =
          ∑ z :
              (X : Set.range phi) ×
                {k : K // classK k = X},
            f (g * ((z.2 : K) : G)) := by
        exact
          (Equiv.sum_comp
            (Equiv.sigmaFiberEquiv classK)
            (fun k : K ↦ f (g * (k : G)))).symm
      _ = _ :=
        Fintype.sum_sigma
          (fun z :
            (X : Set.range phi) ×
              {k : K // classK k = X} ↦
            f (g * ((z.2 : K) : G)))
  have hsumC :
      (∑ c : C, f (g * (c : G))) =
        ∑ X : ConjClasses C,
          ∑ c : {c : C // ConjClasses.mk c = X},
            f (g * (c : C) : G) := by
    calc
      _ =
          ∑ z :
              (X : ConjClasses C) ×
                {c : C // ConjClasses.mk c = X},
            f (g * ((z.2 : C) : G)) := by
        exact
          (Equiv.sum_comp
            (Equiv.sigmaFiberEquiv
              (fun c : C ↦ ConjClasses.mk c))
            (fun c : C ↦ f (g * (c : G)))).symm
      _ = _ :=
        Fintype.sum_sigma
          (fun z :
            (X : ConjClasses C) ×
              {c : C // ConjClasses.mk c = X} ↦
            f (g * ((z.2 : C) : G)))
  have hclass (X : ConjClasses C) :
      (Nat.card C : ℂ) *
          ∑ k :
              {k : K // classK k = phiEquiv X},
            f (g * ((k : K) : G)) =
        (Nat.card K : ℂ) *
          ∑ d :
              {d : C // ConjClasses.mk d = X},
            f (g * ((d : C) : G)) := by
    induction X using Quotient.inductionOn with
    | _ c =>
      change
        (Nat.card C : ℂ) *
            ∑ k :
                {k : K //
                  classK k =
                    phiEquiv
                      (ConjClasses.mk c)},
              f (g * ((k : K) : G)) =
          (Nat.card K : ℂ) *
            ∑ d :
                {d : C //
                  ConjClasses.mk d =
                    ConjClasses.mk c},
              f (g * ((d : C) : G))
      let carrierC :=
        (ConjClasses.mk c).carrier
      let carrierG :=
        (ConjClasses.mk (g * (c : G))).carrier
      let cFiberEquiv :
          {d : C //
            ConjClasses.mk d =
              ConjClasses.mk c} ≃ carrierC := {
        toFun := fun d ↦
          ⟨(d : C),
            ConjClasses.mem_carrier_iff_mk_eq.mpr
              d.property⟩
        invFun := fun d ↦
          ⟨(d : C),
            ConjClasses.mem_carrier_iff_mk_eq.mp
              d.property⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
      }
      let kFiberEquiv :
          {k : K //
            classK k =
              phiEquiv (ConjClasses.mk c)} ≃
            carrierG := {
        toFun := fun k ↦ by
          refine ⟨g * ((k : K) : G), ?_⟩
          apply
            ConjClasses.mem_carrier_iff_mk_eq.mpr
          have hk :=
            congrArg Subtype.val k.property
          rw [hclassK_val,
            hphiEquiv_val, hphi_mk] at hk
          exact hk
        invFun := fun y ↦ by
          have hyClass :
              ConjClasses.mk (y : G) =
                ConjClasses.mk (g * (c : G)) :=
            ConjClasses.mem_carrier_iff_mk_eq.mp
              y.property
          have hyConj :
              IsConj (y : G) (g * (c : G)) :=
            ConjClasses.mk_eq_mk_iff_isConj.mp
              hyClass
          let hex := isConj_iff.mp hyConj
          let a : G := Classical.choose hex
          have ha :
              a * (y : G) * a⁻¹ =
                g * (c : G) :=
            Classical.choose_spec hex
          have hyq :
              qK (y : G) =
                qK (g * (c : G)) := by
            calc
              qK (y : G) =
                  qK a * qK (y : G) *
                    (qK a)⁻¹ := by
                calc
                  qK (y : G) =
                      qK (y : G) *
                        (qK a * (qK a)⁻¹) := by
                    simp
                  _ = _ := by
                    ac_rfl
              _ = qK (g * (c : G)) := by
                simpa only [map_mul, map_inv] using
                  congrArg qK ha
          have hqgc :
              qK (g * (c : G)) = qK g := by
            rw [map_mul, show qK (c : G) = 1 from
              (QuotientGroup.eq_one_iff (c : G)).mpr
                c.2.1,
              mul_one]
          let k : K := by
            refine ⟨g⁻¹ * (y : G), ?_⟩
            apply
              (QuotientGroup.eq_one_iff
                (g⁻¹ * (y : G))).mp
            change qK (g⁻¹ * (y : G)) = 1
            rw [map_mul, map_inv, hyq, hqgc]
            simp
          refine ⟨k, ?_⟩
          apply Subtype.ext
          change
            ConjClasses.mk (g * (k : G)) =
              phi (ConjClasses.mk c)
          rw [hphi_mk]
          simpa [k] using hyClass
        left_inv := by
          intro k
          apply Subtype.ext
          simp
        right_inv := by
          intro y
          apply Subtype.ext
          simp
      }
      have hsumKClass :
          (∑ k :
              {k : K //
                classK k =
                  phiEquiv
                    (ConjClasses.mk c)},
              f (g * ((k : K) : G))) =
            (Nat.card carrierG : ℂ) *
              f (g * (c : G)) := by
        calc
          _ =
              ∑ _k :
                  {k : K //
                    classK k =
                      phiEquiv
                        (ConjClasses.mk c)},
                f (g * (c : G)) := by
            apply Finset.sum_congr rfl
            intro k _
            have hkClass :
                ConjClasses.mk
                    (g * ((k : K) : G)) =
                  ConjClasses.mk
                    (g * (c : G)) := by
              have hk :=
                congrArg Subtype.val k.property
              rw [hclassK_val,
                hphiEquiv_val, hphi_mk] at hk
              exact hk
            have hvalue :=
              congrArg
                (ClassFunction.toConjClassesLinearMap f)
                hkClass
            simpa only [
              ClassFunction.toConjClassesLinearMap_mk] using
                hvalue
          _ =
              (Nat.card
                {k : K //
                  classK k =
                    phiEquiv
                      (ConjClasses.mk c)} : ℂ) *
                f (g * (c : G)) := by
            simp only [Finset.sum_const,
              Finset.card_univ, nsmul_eq_mul,
              Nat.card_eq_fintype_card]
          _ = _ := by
            rw [Nat.card_congr kFiberEquiv]
      have hsumCClass :
          (∑ d :
              {d : C //
                ConjClasses.mk d =
                  ConjClasses.mk c},
              f (g * ((d : C) : G))) =
            (Nat.card carrierC : ℂ) *
              f (g * (c : G)) := by
        calc
          _ =
              ∑ _d :
                  {d : C //
                    ConjClasses.mk d =
                      ConjClasses.mk c},
                f (g * (c : G)) := by
            apply Finset.sum_congr rfl
            intro d _
            have hdClass :
                ConjClasses.mk (d : C) =
                  ConjClasses.mk c :=
              d.property
            have hdGClass :
                ConjClasses.mk
                    (g * ((d : C) : G)) =
                  ConjClasses.mk
                    (g * (c : G)) := by
              have hd := congrArg phi hdClass
              rw [hphi_mk, hphi_mk] at hd
              exact hd
            have hvalue :=
              congrArg
                (ClassFunction.toConjClassesLinearMap f)
                hdGClass
            simpa only [
              ClassFunction.toConjClassesLinearMap_mk] using
                hvalue
          _ =
              (Nat.card
                {d : C //
                  ConjClasses.mk d =
                    ConjClasses.mk c} : ℂ) *
                f (g * (c : G)) := by
            simp only [Finset.sum_const,
              Finset.card_univ, nsmul_eq_mul,
              Nat.card_eq_fintype_card]
          _ = _ := by
            rw [Nat.card_congr cFiberEquiv]
      have hGclass :=
        card_conjClass_mul_card_centralizer
          (g * (c : G))
      have hCclass :=
        card_conjClass_mul_card_centralizer c
      have hcentral :
          Nat.card
              (Subgroup.centralizer
                ({g * (c : G)} : Set G)) =
            Nat.card
                (Subgroup.centralizer
                  ({c} : Set C)) *
              Nat.card P := by
        exact
          card_centralizer_generator_mul_fixedPoint_eq_fixedCentralizer
            K P hK hP hgenerate c
      have hGcard :
          Nat.card K * Nat.card P =
            Nat.card G :=
        (cyclicCoprimeKernel_isComplement'
          K P hK hP hgenerate).card_mul
      have hcancel :
          Nat.card carrierG *
              Nat.card
                (Subgroup.centralizer
                  ({c} : Set C)) =
            Nat.card K := by
        apply Nat.mul_right_cancel
          (Nat.card_pos : 0 < Nat.card P)
        calc
          (Nat.card carrierG *
                Nat.card
                  (Subgroup.centralizer
                    ({c} : Set C))) *
              Nat.card P =
            Nat.card carrierG *
              (Nat.card
                  (Subgroup.centralizer
                    ({c} : Set C)) *
                Nat.card P) := by
                  ac_rfl
          _ =
              Nat.card carrierG *
                Nat.card
                  (Subgroup.centralizer
                    ({g * (c : G)} :
                      Set G)) := by
                rw [hcentral]
          _ = Nat.card G := hGclass
          _ = Nat.card K * Nat.card P :=
            hGcard.symm
      have hcarrier :
          Nat.card carrierG * Nat.card C =
            Nat.card carrierC * Nat.card K := by
        calc
          Nat.card carrierG * Nat.card C =
              Nat.card carrierG *
                (Nat.card carrierC *
                  Nat.card
                    (Subgroup.centralizer
                      ({c} : Set C))) := by
                rw [hCclass]
          _ =
              Nat.card carrierC *
                (Nat.card carrierG *
                  Nat.card
                    (Subgroup.centralizer
                      ({c} : Set C))) := by
                ac_rfl
          _ = Nat.card carrierC * Nat.card K := by
            rw [hcancel]
      rw [hsumKClass, hsumCClass]
      have hcarrierCast :
          (Nat.card carrierG : ℂ) *
              (Nat.card C : ℂ) =
            (Nat.card carrierC : ℂ) *
              (Nat.card K : ℂ) := by
        exact_mod_cast hcarrier
      calc
        (Nat.card C : ℂ) *
              ((Nat.card carrierG : ℂ) *
                f (g * (c : G))) =
            ((Nat.card carrierG : ℂ) *
              (Nat.card C : ℂ)) *
                f (g * (c : G)) := by
                  ring
        _ =
            ((Nat.card carrierC : ℂ) *
              (Nat.card K : ℂ)) *
                f (g * (c : G)) := by
                  rw [hcarrierCast]
        _ =
            (Nat.card K : ℂ) *
              ((Nat.card carrierC : ℂ) *
                f (g * (c : G))) := by
                  ring
  change
    (Nat.card C : ℂ) *
        ∑ k : K, f (g * (k : G)) =
      (Nat.card K : ℂ) *
        ∑ c : C, f (g * (c : G))
  rw [hsumK, hsumC]
  calc
    (Nat.card C : ℂ) *
          ∑ X : Set.range phi,
            ∑ k :
                {k : K // classK k = X},
              f (g * ((k : K) : G)) =
        (Nat.card C : ℂ) *
          ∑ X : ConjClasses C,
            ∑ k :
                {k : K //
                  classK k = phiEquiv X},
              f (g * ((k : K) : G)) := by
      congr 1
      exact
        (Equiv.sum_comp phiEquiv
          (fun X : Set.range phi ↦
            ∑ k :
                {k : K // classK k = X},
              f (g * ((k : K) : G)))).symm
    _ =
        ∑ X : ConjClasses C,
          (Nat.card C : ℂ) *
            ∑ k :
                {k : K //
                  classK k = phiEquiv X},
              f (g * ((k : K) : G)) := by
      rw [Finset.mul_sum]
    _ =
        ∑ X : ConjClasses C,
          (Nat.card K : ℂ) *
            ∑ d :
                {d : C //
                  ConjClasses.mk d = X},
              f (g * ((d : C) : G)) := by
      apply Finset.sum_congr rfl
      intro X _
      exact hclass X
    _ =
        (Nat.card K : ℂ) *
          ∑ X : ConjClasses C,
            ∑ d :
                {d : C //
                  ConjClasses.mk d = X},
              f (g * ((d : C) : G)) := by
      rw [Finset.mul_sum]

end McKayConjecture
