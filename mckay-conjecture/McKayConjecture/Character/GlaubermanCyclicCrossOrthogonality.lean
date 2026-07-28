/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanCyclicCosetOrthogonality
import McKayConjecture.Character.GlaubermanCyclicCosetAverage
import McKayConjecture.Character.InverseConjugate

/-!
# Off-diagonal orthogonality on a cyclic generator coset

Extensions of two distinct invariant irreducible kernel characters are
orthogonal already on the generator coset.  This is the off-diagonal
counterpart of the norm computation in
`GlaubermanCyclicCosetOrthogonality`.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace McKayConjecture

variable {G : Type} [Group G] [Finite G]
variable (K P : Subgroup G) [K.Normal]
variable [IsCyclic P]
variable {p : ℕ} [Fact p.Prime]

noncomputable local instance cyclicCrossFixedPointsFintype :
    Fintype
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G)) :=
  Fintype.ofFinite _

/-- Distinct invariant kernel characters have orthogonal irreducible
extensions on the chosen generator coset. -/
theorem cyclicExtensions_generatorCoset_bilinearPairing_eq_zero_of_ne
    [Fintype K]
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ η : PInvariantPPrimeIrreducibleCharacter K P p)
    (chi psi : IrreducibleCharacter G)
    (hchi :
      IrreducibleCharacter.IsExtensionAlong
        K.subtype θ.1.1 chi)
    (hpsi :
      IrreducibleCharacter.IsExtensionAlong
        K.subtype η.1.1 psi)
    (hne : θ ≠ η) :
    ∑ k : K,
        chi.values
          (((cyclicSubgroupGenerator P : P) : G) * (k : G)) *
        psi.values
          ((((cyclicSubgroupGenerator P : P) : G) * (k : G))⁻¹) =
      0 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let Q : Type := G ⧸ K
  let e : Q ≃* P :=
    (cyclicCoprimeKernel_isComplement'
      K P hK hP hgenerate).symm.QuotientMulEquiv
  letI : CommGroup P := IsCyclic.commGroup
  letI : CommGroup Q :=
    e.toMonoidHom.commGroupOfInjective e.injective
  let qK : G →* Q := QuotientGroup.mk' K
  letI : Fintype Q := Fintype.ofFinite Q
  letI : Fintype (Q →* ℂˣ) := Fintype.ofFinite _
  have hpair :
      ∀ beta : Q →* ℂˣ,
        ClassFunction.normalizedPairing chi.toClassFunction
          (IrreducibleCharacter.twist
            (IrreducibleCharacter.inflateLinearCharacter K beta)
            psi).toClassFunction =
          0 := by
    intro beta
    apply
      ClassFunction.normalizedPairing_irreducible_eq_zero_of_ne
    intro heq
    apply hne
    apply Subtype.ext
    apply Subtype.ext
    apply IrreducibleCharacter.ext
    funext k
    have htwist :
        IrreducibleCharacter.IsExtensionAlong K.subtype η.1.1
          (IrreducibleCharacter.twist
            (IrreducibleCharacter.inflateLinearCharacter K beta)
            psi) :=
      hpsi.twist_of_eq_one
        (IrreducibleCharacter.inflateLinearCharacter K beta)
        (fun x => by
          exact
            IrreducibleCharacter.inflateLinearCharacter_subgroup
              K beta x)
    calc
      θ.1.1.values k = chi.values (K.subtype k) :=
        (hchi k).symm
      _ =
          (IrreducibleCharacter.twist
            (IrreducibleCharacter.inflateLinearCharacter K beta)
            psi).values (K.subtype k) := by rw [heq]
      _ = η.1.1.values k := htwist k
  have hweighted :
      ∑ beta : Q →* ℂˣ,
          (beta (qK
            ((cyclicSubgroupGenerator P : P) : G)) : ℂ) *
            ClassFunction.normalizedPairing chi.toClassFunction
              (IrreducibleCharacter.twist
                (IrreducibleCharacter.inflateLinearCharacter K beta)
                psi).toClassFunction =
        0 := by
    simp_rw [hpair]
    simp
  have hweighted' :
      ∑ beta : Q →* ℂˣ,
          (beta (qK
            ((cyclicSubgroupGenerator P : P) : G)) : ℂ) *
            ((Nat.card G : ℂ)⁻¹ *
              ∑ x : G,
                chi.values x *
                  ((beta (qK x⁻¹) : ℂ) *
                    psi.values x⁻¹)) =
        0 := by
    change
      ∑ beta : Q →* ℂˣ,
          (beta (qK
            ((cyclicSubgroupGenerator P : P) : G)) : ℂ) *
            ((Nat.card G : ℂ)⁻¹ *
              ∑ x : G,
                chi.values x *
                  (IrreducibleCharacter.twist
                    (IrreducibleCharacter.inflateLinearCharacter
                      K beta) psi).values x⁻¹) =
        0 at hweighted
    simpa only [IrreducibleCharacter.twist_values,
      IrreducibleCharacter.inflateLinearCharacter_apply] using
        hweighted
  have hrearrange :
      (∑ beta : Q →* ℂˣ,
          (beta (qK
            ((cyclicSubgroupGenerator P : P) : G)) : ℂ) *
            ((Nat.card G : ℂ)⁻¹ *
              ∑ x : G,
                chi.values x *
                  ((beta (qK x⁻¹) : ℂ) *
                    psi.values x⁻¹))) =
        (Nat.card G : ℂ)⁻¹ *
          ∑ x : G,
            chi.values x * psi.values x⁻¹ *
              ∑ beta : Q →* ℂˣ,
                (beta
                  (qK ((cyclicSubgroupGenerator P : P) : G) *
                    (qK x)⁻¹) : ℂ) := by
    calc
      _ = (Nat.card G : ℂ)⁻¹ *
          ∑ beta : Q →* ℂˣ,
            ∑ x : G,
              (beta (qK
                ((cyclicSubgroupGenerator P : P) : G)) : ℂ) *
                (chi.values x *
                  ((beta (qK x⁻¹) : ℂ) *
                    psi.values x⁻¹)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro beta _
              rw [Finset.mul_sum]
              rw [Finset.mul_sum, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x _
              ring
      _ = (Nat.card G : ℂ)⁻¹ *
          ∑ x : G,
            ∑ beta : Q →* ℂˣ,
              (beta (qK
                ((cyclicSubgroupGenerator P : P) : G)) : ℂ) *
                (chi.values x *
                  ((beta (qK x⁻¹) : ℂ) *
                    psi.values x⁻¹)) := by
              rw [Finset.sum_comm]
      _ = _ := by
              congr 1
              apply Finset.sum_congr rfl
              intro x _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro beta _
              simp only [map_inv, map_mul, Units.val_mul,
                Units.val_inv_eq_inv_val]
              ring
  rw [hrearrange] at hweighted'
  have hdual (x : G) :
      (∑ beta : Q →* ℂˣ,
          (beta
            (qK ((cyclicSubgroupGenerator P : P) : G) *
              (qK x)⁻¹) : ℂ)) =
        if qK x =
            qK ((cyclicSubgroupGenerator P : P) : G)
          then (Nat.card Q : ℂ)
          else 0 := by
    by_cases hx :
        qK x =
          qK ((cyclicSubgroupGenerator P : P) : G)
    · simp only [hx, if_pos]
      simpa using
        (sum_complexUnitCharacters_apply_one
          (A := Q))
    · simp only [hx, if_false]
      apply sum_complexUnitCharacters_apply_eq_zero
      intro hone
      apply hx
      have :
          qK ((cyclicSubgroupGenerator P : P) : G) =
            qK x := by
        exact (mul_inv_eq_one.mp hone)
      exact this.symm
  simp_rw [hdual] at hweighted'
  let generator : G :=
    ((cyclicSubgroupGenerator P : P) : G)
  let fiber :=
    {x : G // qK x = qK generator}
  let fiberEquiv : K ≃ fiber := {
    toFun k := by
      refine ⟨generator * (k : G), ?_⟩
      rw [map_mul, show qK (k : G) = 1 from
        (QuotientGroup.eq_one_iff (k : G)).mpr k.2,
        mul_one]
    invFun x := by
      refine
        ⟨generator⁻¹ * (x : G), ?_⟩
      apply
        (QuotientGroup.eq_one_iff
          (generator⁻¹ * (x : G))).mp
      change qK (generator⁻¹ * (x : G)) = 1
      rw [map_mul, map_inv, x.property]
      simp
    left_inv k := by
      apply Subtype.ext
      simp
    right_inv x := by
      apply Subtype.ext
      simp
  }
  have hfiber :
      (∑ x : G,
          if qK x = qK generator
            then chi.values x * psi.values x⁻¹
            else 0) =
        ∑ k : K,
          chi.values (generator * (k : G)) *
            psi.values (generator * (k : G))⁻¹ := by
    calc
      _ =
          ∑ x ∈
              Finset.univ.filter
                (fun x : G ↦ qK x = qK generator),
            chi.values x * psi.values x⁻¹ := by
              symm
              exact
                Finset.sum_filter
                  (fun x : G ↦ qK x = qK generator)
                  (fun x : G ↦
                    chi.values x * psi.values x⁻¹)
      _ =
          ∑ x : fiber,
            chi.values (x : G) *
              psi.values (x : G)⁻¹ := by
              exact
                Finset.sum_subtype
                  (Finset.univ.filter
                    (fun x : G ↦
                      qK x = qK generator))
                  (by simp)
                  (fun x : G ↦
                    chi.values x * psi.values x⁻¹)
      _ = _ := by
        exact
          (Equiv.sum_comp fiberEquiv
            (fun x : fiber ↦
              chi.values (x : G) *
                psi.values (x : G)⁻¹)).symm
  change
    (Nat.card G : ℂ)⁻¹ *
        (∑ x : G,
          chi.values x * psi.values x⁻¹ *
            (if qK x = qK generator
              then (Nat.card Q : ℂ)
              else 0)) =
      0 at hweighted'
  have hfactor :
      (∑ x : G,
          chi.values x * psi.values x⁻¹ *
            if qK x = qK generator
              then (Nat.card Q : ℂ)
              else 0) =
        (Nat.card Q : ℂ) *
          ∑ x : G,
            if qK x = qK generator
              then chi.values x * psi.values x⁻¹
              else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : qK x = qK generator <;>
      simp [hx]
    ring
  rw [hfactor, hfiber] at hweighted'
  have hcard :
      Nat.card G =
        Nat.card K * Nat.card Q := by
    calc
      Nat.card G =
          Nat.card K * Nat.card P :=
        (cyclicCoprimeKernel_isComplement'
          K P hK hP hgenerate).card_mul.symm
      _ = Nat.card K * Nat.card Q := by
        rw [Nat.card_congr e.toEquiv]
  have hKne : (Nat.card K : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card K).ne'
  have hQne : (Nat.card Q : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card Q).ne'
  rw [hcard, Nat.cast_mul] at hweighted'
  field_simp [hKne, hQne] at hweighted'
  simpa [generator] using hweighted'

/-- The determinant-normalized cyclic extensions attached to distinct
invariant kernel characters are orthogonal on the generator coset. -/
theorem
    determinantNormalizedCyclicExtensions_generatorCoset_bilinearPairing_eq_zero_of_ne
    [Fintype K]
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ η : PInvariantPPrimeIrreducibleCharacter K P p)
    (hne : θ ≠ η) :
    ∑ k : K,
        (determinantNormalizedCyclicExtensionCharacter
          K P hK hP hgenerate θ).values
            (((cyclicSubgroupGenerator P : P) : G) * (k : G)) *
        (determinantNormalizedCyclicExtensionCharacter
          K P hK hP hgenerate η).values
            ((((cyclicSubgroupGenerator P : P) : G) * (k : G))⁻¹) =
      0 :=
  cyclicExtensions_generatorCoset_bilinearPairing_eq_zero_of_ne
    K P hK hP hgenerate θ η
      (determinantNormalizedCyclicExtensionCharacter
        K P hK hP hgenerate θ)
      (determinantNormalizedCyclicExtensionCharacter
        K P hK hP hgenerate η)
      (determinantNormalizedCyclicExtensionCharacter_isExtension
        K P hK hP hgenerate θ)
      (determinantNormalizedCyclicExtensionCharacter_isExtension
        K P hK hP hgenerate η)
      hne

/-- The ambient class function used for the Hermitian cross-pairing of two
irreducible characters. -/
def irreducibleCharacterCrossBilinearClassFunction
    (chi psi : IrreducibleCharacter G) :
    ClassFunction G :=
  ⟨fun x ↦ chi.values x * psi.values x⁻¹, by
    intro x a
    change
      chi.toClassFunction (a * x * a⁻¹) *
          psi.toClassFunction (a * x * a⁻¹)⁻¹ =
        chi.toClassFunction x *
          psi.toClassFunction x⁻¹
    rw [conj_inv,
      ClassFunction.conj_apply,
      ClassFunction.conj_apply]⟩

omit [Finite G] in
@[simp]
theorem irreducibleCharacterCrossBilinearClassFunction_apply
    (chi psi : IrreducibleCharacter G) (x : G) :
    irreducibleCharacterCrossBilinearClassFunction chi psi x =
      chi.values x * psi.values x⁻¹ :=
  rfl

/-- Distinct cyclic source characters give Hermitian-orthogonal normalized
cyclic traces. -/
theorem
    determinantNormalizedCyclicTrace_hermitianSum_eq_zero_of_ne
    [Fintype K]
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ η : PInvariantPPrimeIrreducibleCharacter K P p)
    (hne : θ ≠ η) :
    ∑ c :
        cyclicFixedPoints K
          ((cyclicSubgroupGenerator P : P) : G),
      determinantNormalizedCyclicTrace
          K P hK hP hgenerate θ c *
        conj
          (determinantNormalizedCyclicTrace
            K P hK hP hgenerate η c) =
      0 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let C : Type :=
    cyclicFixedPoints K
      ((cyclicSubgroupGenerator P : P) : G)
  letI : Fintype C := Fintype.ofFinite C
  let chi : IrreducibleCharacter G :=
    determinantNormalizedCyclicExtensionCharacter
      K P hK hP hgenerate θ
  let psi : IrreducibleCharacter G :=
    determinantNormalizedCyclicExtensionCharacter
      K P hK hP hgenerate η
  let F : ClassFunction G :=
    irreducibleCharacterCrossBilinearClassFunction chi psi
  have havg :=
    cyclicGeneratorCoset_classFunction_sum
      K P hK hP hgenerate F
  have hcoset :=
    determinantNormalizedCyclicExtensions_generatorCoset_bilinearPairing_eq_zero_of_ne
      K P hK hP hgenerate θ η hne
  change
    (Nat.card C : ℂ) *
        ∑ k : K, F
          (((cyclicSubgroupGenerator P : P) : G) *
            (k : G)) =
      (Nat.card K : ℂ) *
        ∑ c : C, F
          (((cyclicSubgroupGenerator P : P) : G) *
            (c : G)) at havg
  change
    ∑ k : K, F
        (((cyclicSubgroupGenerator P : P) : G) *
          (k : G)) =
      0 at hcoset
  rw [hcoset, mul_zero] at havg
  have hKne : (Nat.card K : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card K).ne'
  have hfixed :
      (∑ c : C, F
          (((cyclicSubgroupGenerator P : P) : G) *
            (c : G))) =
        0 := by
    apply mul_left_cancel₀ hKne
    simpa using havg.symm
  change
    ∑ c : C,
      determinantNormalizedCyclicTrace
          K P hK hP hgenerate θ c *
        conj
          (determinantNormalizedCyclicTrace
            K P hK hP hgenerate η c) =
      0
  have hconj (c : C) :
      conj
          (determinantNormalizedCyclicTrace
            K P hK hP hgenerate η c) =
        psi.values
          ((((cyclicSubgroupGenerator P : P) : G) *
            (c : G))⁻¹) := by
    rw [
      determinantNormalizedCyclicTrace_eq_extensionCharacter,
      ← IrreducibleCharacter.value_inv_eq_conj]
  simp_rw [hconj]
  simp_rw [
    determinantNormalizedCyclicTrace_eq_extensionCharacter]
  exact hfixed

end McKayConjecture
