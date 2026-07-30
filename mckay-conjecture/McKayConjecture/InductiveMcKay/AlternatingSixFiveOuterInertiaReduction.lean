/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAutomorphismStabilizerGeneration
import McKayConjecture.InductiveMcKay.AlternatingSixFiveCTblLibInvariantSafeRowIdentification

/-!
# The remaining outer inertia at five for the universal cover of `A₆`

The audited five-prime position action has twelve positions in free outer
orbits, ten positions in outer orbits of size two, the trivial position,
and one further fully fixed position.  Turning this combinatorial partition
into genuine character inertia requires a row identification satisfying
both semantic ambient generator bridges.

This file isolates that conditional, reusable group-theoretic reduction.
Every element of a character stabilizer is a product of an exact-normalizer
inner automorphism and a corrected audited outer representative.  Given the
two semantic ambient bridges, a size-two CT position admits only the
identity representative and one explicitly recorded nonidentity
representative.

Thus the outer inertia of each of these ten rows has at most two cosets.
This does not itself construct the remaining projective implementer:
one still has to compare the order-two outer implementers (and their
central scalars) on the ambient and local sides.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixFiveOuterInertiaReductionFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-! ### A generic inner-times-audited-outer normal form -/

/-- Inner correction to a Sylow subgroup does not change whether an audited
outer representative fixes an ordinary character. -/
def alternatingSixCorrectedOuterCharacterStabilizer
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p AlternatingSixUniversalCover)
    (χ : PPrimeIrreducibleCharacter AlternatingSixUniversalCover p)
    (i : Fin 4)
    (hi :
      alternatingSixUniversalCoverOuterRepresentative i • χ = χ) :
    PPrimeCharacterStabilizer P χ :=
  ⟨SylowAutStabilizer.corrected P
      (alternatingSixUniversalCoverOuterRepresentative i), by
    rw [PPrimeCharacterStabilizer.mem_iff]
    change
      (SylowAutStabilizer.corrected P
          (alternatingSixUniversalCoverOuterRepresentative i) :
        MulAut AlternatingSixUniversalCover) • χ = χ
    rw [SylowAutStabilizer.corrected_coe]
    simpa [mul_smul] using hi⟩

/-- Every character-stabilizing Sylow automorphism is an exact-normalizer
inner automorphism times one corrected member of the four audited outer
representatives.  The representative occurring in the factorization fixes
the character before correction.

This is the normal form needed to reduce concrete character inertia to the
finite four-point outer action. -/
theorem alternatingSixCharacterStabilizer_inner_mul_correctedOuter
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p AlternatingSixUniversalCover)
    (χ : PPrimeIrreducibleCharacter AlternatingSixUniversalCover p)
    (a : PPrimeCharacterStabilizer P χ) :
    ∃ (n : SylowNormalizer P) (i : Fin 4)
        (hi :
          alternatingSixUniversalCoverOuterRepresentative i • χ = χ),
      a =
        normalizerInnerCharacterStabilizerHom P χ n *
          alternatingSixCorrectedOuterCharacterStabilizer P χ i hi := by
  obtain ⟨⟨g, i⟩, hgi⟩ :=
    alternatingSixUniversalCoverAutomorphismFamily_surjective
      (PPrimeCharacterStabilizer.ambientAction a)
  obtain ⟨q, hq⟩ :=
    alternatingSixUniversalCoverInnerAutomorphism_mem g
  have hgi' :
      alternatingSixUniversalCoverInnerAutomorphism g *
          alternatingSixUniversalCoverOuterRepresentative i =
        PPrimeCharacterStabilizer.ambientAction a := by
    simpa [alternatingSixUniversalCoverAutomorphismFamily] using hgi
  have hi :
      alternatingSixUniversalCoverOuterRepresentative i • χ = χ := by
    calc
      alternatingSixUniversalCoverOuterRepresentative i • χ =
          (MulAut.conj q *
              alternatingSixUniversalCoverOuterRepresentative i) • χ := by
            simp [mul_smul]
      _ =
          (alternatingSixUniversalCoverInnerAutomorphism g *
              alternatingSixUniversalCoverOuterRepresentative i) • χ := by
            rw [hq]
      _ = PPrimeCharacterStabilizer.ambientAction a • χ := by
        rw [hgi']
      _ = χ := by
        exact (PPrimeCharacterStabilizer.mem_iff a.1).mp a.2
  let c :
      PPrimeCharacterStabilizer P χ :=
    alternatingSixCorrectedOuterCharacterStabilizer P χ i hi
  let residual : SylowAutStabilizer P :=
    a.1 * c.1⁻¹
  have hResidualInner :
      ∃ x : AlternatingSixUniversalCover,
        (residual : MulAut AlternatingSixUniversalCover) =
          MulAut.conj x := by
    refine
      ⟨q *
          (SylowAutStabilizer.correctionConjugator P
            (alternatingSixUniversalCoverOuterRepresentative i))⁻¹, ?_⟩
    change
      PPrimeCharacterStabilizer.ambientAction a *
          (SylowAutStabilizer.corrected P
            (alternatingSixUniversalCoverOuterRepresentative i) :
              MulAut AlternatingSixUniversalCover)⁻¹ =
        MulAut.conj
          (q *
            (SylowAutStabilizer.correctionConjugator P
              (alternatingSixUniversalCoverOuterRepresentative i))⁻¹)
    rw [← hgi', ← hq,
      SylowAutStabilizer.corrected_coe, map_mul, map_inv]
    group
  have hResidualRange :
      residual ∈
        (SylowAutStabilizer.normalizerInnerHom P).range :=
    (SylowAutStabilizer.mem_normalizerInnerHom_range_iff_isInner
      P residual).mpr hResidualInner
  obtain ⟨n, hn⟩ := hResidualRange
  refine ⟨n, i, hi, ?_⟩
  apply Subtype.ext
  calc
    a.1 = residual * c.1 := by
      simp [residual]
    _ = SylowAutStabilizer.normalizerInnerHom P n * c.1 := by
      rw [← hn]

/-- The exact-normalizer inner image is normal in every character
stabilizer.  Hence the outer inertia quotient used below is a genuine
quotient group, not merely a set of cosets. -/
theorem normalizerInnerCharacterStabilizerHom_range_normal
    {G : Type*} [Group G]
    {p : ℕ}
    (P : Sylow p G)
    (χ : PPrimeIrreducibleCharacter G p) :
    ((normalizerInnerCharacterStabilizerHom P χ).range).Normal := by
  constructor
  intro x hx a
  obtain ⟨n, rfl⟩ := hx
  let n' : SylowNormalizer P :=
    ⟨a.1.1 n.1, by
      have hnImage :
          a.1.1 n.1 ∈
            (Subgroup.normalizer (P : Subgroup G)).map
              (a.1.1 : G →* G) :=
        Subgroup.mem_map.mpr ⟨n.1, n.2, rfl⟩
      rw [SylowAutStabilizer.map_normalizer_eq a.1] at hnImage
      exact hnImage⟩
  refine ⟨n', ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply MulEquiv.ext
  intro y
  change
    a.1.1 n.1 * y * (a.1.1 n.1)⁻¹ =
      a.1.1 (n.1 * a.1.1.symm y * n.1⁻¹)
  simp

/-- A group covered by a subgroup and one of its right cosets has quotient
of cardinality at most two. -/
theorem quotient_natCard_le_two_of_twoCosetNormalForm
    {A : Type*} [Group A] [Finite A]
    (H : Subgroup A) [H.Normal]
    (c : A)
    (hNormalForm :
      ∀ a : A, ∃ h : H, a = h.1 ∨ a = h.1 * c) :
    Nat.card (A ⧸ H) ≤ 2 := by
  let representatives : Fin 2 → A ⧸ H :=
    ![1, QuotientGroup.mk' H c]
  have hSurjective :
      Function.Surjective representatives := by
    intro q
    obtain ⟨a, rfl⟩ :=
      QuotientGroup.mk'_surjective H q
    obtain ⟨h, ha | ha⟩ := hNormalForm a
    · refine ⟨0, ?_⟩
      change 1 = QuotientGroup.mk' H a
      rw [ha]
      exact ((QuotientGroup.eq_one_iff h.1).mpr h.2).symm
    · refine ⟨1, ?_⟩
      change QuotientGroup.mk' H c = QuotientGroup.mk' H a
      rw [ha, map_mul]
      simpa [QuotientGroup.eq_one_iff] using h.2
  simpa using
    Nat.card_le_card_of_surjective representatives hSurjective

/-- Every finite group with at most two elements is cyclic. -/
theorem isCyclic_of_natCard_le_two
    {A : Type*} [Group A] [Finite A]
    (hcard : Nat.card A ≤ 2) :
    IsCyclic A := by
  by_cases hSubsingleton : Subsingleton A
  · letI : Subsingleton A := hSubsingleton
    exact isCyclic_of_subsingleton
  · letI : Nontrivial A :=
      not_subsingleton_iff_nontrivial.mp hSubsingleton
    have hTwoLe : 2 ≤ Nat.card A :=
      Finite.one_lt_card
    have hCardEq : Nat.card A = 2 :=
      le_antisymm hcard hTwoLe
    obtain ⟨g, hg⟩ :=
      (nontrivial_iff_exists_ne (1 : A)).mp inferInstance
    letI : Fact (Nat.Prime 2) :=
      ⟨Nat.prime_two⟩
    rw [isCyclic_iff_exists_zpowers_eq_top]
    exact
      ⟨g, zpowers_eq_top_of_prime_card hCardEq hg⟩

/-! ### The finite five-local outer inertia partition -/

/-- Action of the four audited outer representatives on the five-prime
CT positions.  The entries are, in order, the identity, the first
generator, the second generator, and their product. -/
def alternatingSixFiveCTblLibOuterRepresentativeAction
    (j : Fin 4) (i : Fin 24) :
    Fin 24 :=
  ![i,
    alternatingSixCTblLibFivePPrimeActionData.ambientAlphaOne i,
    alternatingSixCTblLibFivePPrimeActionData.ambientAlphaTwo i,
    alternatingSixCTblLibFivePPrimeActionData.ambientAlphaOne
      (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaTwo i)] j

/-- A five-prime CT position lying in an outer orbit of size two, expressed
intrinsically by saying that exactly two of the four audited representatives
fix it. -/
def AlternatingSixFiveOuterOrbitTwoCTPosition
    (i : Fin 24) :
    Prop :=
  Fintype.card
      {j : Fin 4 //
        alternatingSixFiveCTblLibOuterRepresentativeAction j i = i} =
    2

instance alternatingSixFiveOuterOrbitTwoCTPositionDecidable
    (i : Fin 24) :
    Decidable (AlternatingSixFiveOuterOrbitTwoCTPosition i) := by
  unfold AlternatingSixFiveOuterOrbitTwoCTPosition
  infer_instance

/-- Exactly ten five-prime CT positions lie in outer orbits of size two. -/
theorem alternatingSixFiveOuterOrbitTwoCTPosition_card :
    Fintype.card
        {i : Fin 24 // AlternatingSixFiveOuterOrbitTwoCTPosition i} =
      10 := by
  decide

/-- The ten size-two positions are precisely the five displayed pairs. -/
theorem alternatingSixFiveOuterOrbitTwoCTPosition_iff
    (i : Fin 24) :
    AlternatingSixFiveOuterOrbitTwoCTPosition i ↔
      i.val = 1 ∨ i.val = 2 ∨
      i.val = 4 ∨ i.val = 5 ∨
      i.val = 6 ∨ i.val = 7 ∨
      i.val = 12 ∨ i.val = 13 ∨
      i.val = 14 ∨ i.val = 15 := by
  fin_cases i <;> decide

/-- The unique nonidentity audited representative fixing a size-two
position.  Values away from the ten size-two positions are irrelevant. -/
def alternatingSixFiveOuterOrbitTwoFixedRepresentative
    (i : Fin 24) :
    Fin 4 :=
  ![0, 2, 2, 0, 1, 1, 2, 2, 0, 0, 0, 0,
    3, 3, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0] i

/-- On a size-two position, the fixing audited representatives are exactly
the identity and the recorded nonidentity representative. -/
theorem alternatingSixFiveOuterOrbitTwo_fixed_iff
    (i : Fin 24)
    (hi : AlternatingSixFiveOuterOrbitTwoCTPosition i)
    (j : Fin 4) :
    alternatingSixFiveCTblLibOuterRepresentativeAction j i = i ↔
      j = 0 ∨
        j = alternatingSixFiveOuterOrbitTwoFixedRepresentative i := by
  have hpos :=
    (alternatingSixFiveOuterOrbitTwoCTPosition_iff i).mp hi
  fin_cases i <;> simp_all
  all_goals fin_cases j <;> decide

/-- The recorded representative of a size-two position is nonidentity. -/
theorem alternatingSixFiveOuterOrbitTwo_fixedRepresentative_ne_zero
    (i : Fin 24)
    (hi : AlternatingSixFiveOuterOrbitTwoCTPosition i) :
    alternatingSixFiveOuterOrbitTwoFixedRepresentative i ≠ 0 := by
  have hpos :=
    (alternatingSixFiveOuterOrbitTwoCTPosition_iff i).mp hi
  fin_cases i <;> simp_all
  all_goals decide

/-- The only nontrivial five-prime CT position fixed by both audited
generators is position `3`; position `0` is the trivial row. -/
theorem alternatingSixFive_nontrivial_fullyOuterFixed_iff
    (i : Fin 24)
    (hi : i ≠ 0) :
    (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaOne i = i ∧
      alternatingSixCTblLibFivePPrimeActionData.ambientAlphaTwo i = i) ↔
      i = 3 := by
  fin_cases i <;> simp_all
  all_goals decide

/-- The ten size-two positions in increasing CT-position order. -/
def alternatingSixFiveOuterOrbitTwoPositionEquiv :
    Fin 10 ≃
      {i : Fin 24 // AlternatingSixFiveOuterOrbitTwoCTPosition i} :=
  Equiv.ofBijective
    ![⟨1, by decide⟩,
      ⟨2, by decide⟩,
      ⟨4, by decide⟩,
      ⟨5, by decide⟩,
      ⟨6, by decide⟩,
      ⟨7, by decide⟩,
      ⟨12, by decide⟩,
      ⟨13, by decide⟩,
      ⟨14, by decide⟩,
      ⟨15, by decide⟩]
    (by decide)

/-- Ambient row names carried combinatorially by the ten size-two positions
in the invariant-safe orientation.  The orientation's ambient bridges are
known to fail, so this list is not an unconditional genuine-inertia
identification. -/
def alternatingSixFiveInvariantSafeOuterOrbitTwoAmbientRow :
    Fin 10 → AlternatingSixAmbientOrdinaryRow :=
  ![.row16, .row17, .row06, .row07, .row18,
    .row19, .row11, .row10, .row22, .row21]

/-- The invariant-safe position equivalence labels the ten size-two
positions by exactly the displayed ten ambient rows. -/
theorem alternatingSixFiveInvariantSafeAmbientPosition_outerOrbitTwo
    (i : Fin 10) :
    (alternatingSixFiveCTblLibInvariantSafeAmbientPositionEquiv
        (alternatingSixFiveOuterOrbitTwoPositionEquiv i).1).1 =
      alternatingSixFiveInvariantSafeOuterOrbitTwoAmbientRow i := by
  fin_cases i <;> rfl

/-- The invariant-safe position equivalence labels the sole nontrivial
fully fixed position by `row20`. -/
theorem alternatingSixFiveInvariantSafeAmbientPosition_fullyOuterFixed :
    (alternatingSixFiveCTblLibInvariantSafeAmbientPositionEquiv 3).1 =
      .row20 :=
  rfl

/-! ### Transport to genuine five-prime character inertia -/

@[simp]
theorem alternatingSixUniversalCoverOuterRepresentative_zero :
    alternatingSixUniversalCoverOuterRepresentative 0 = 1 := by
  simpa [
    alternatingSixUniversalCoverOuterRepresentative,
    alternatingSixSchurOuterRepresentative
  ] using
    map_one
      (MulAut.congr
        alternatingSixSchurCoordinatesEquivUniversalCover)

theorem alternatingSixUniversalCoverOuterRepresentative_three :
    alternatingSixUniversalCoverOuterRepresentative 3 =
      alternatingSixUniversalCoverTransportedAlphaOne *
        alternatingSixUniversalCoverTransportedAlphaTwo := by
  simpa [
    alternatingSixUniversalCoverOuterRepresentative,
    alternatingSixSchurOuterRepresentative,
    alternatingSixUniversalCoverTransportedAlphaOne,
    alternatingSixUniversalCoverTransportedAlphaTwo,
    alternatingSixUniversalCoverAutomorphismOfSchur
  ] using
    map_mul
      (MulAut.congr
        alternatingSixSchurCoordinatesEquivUniversalCover)
      alternatingSixSchurAlphaOneAutomorphism
      alternatingSixSchurAlphaTwoAutomorphism

/-- The corrected identity representative belongs to the exact-normalizer
inner image in every character stabilizer. -/
theorem alternatingSixCorrectedOuterCharacterStabilizer_zero_mem_range
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p AlternatingSixUniversalCover)
    (χ : PPrimeIrreducibleCharacter AlternatingSixUniversalCover p)
    (hfix :
      alternatingSixUniversalCoverOuterRepresentative 0 • χ = χ) :
    alternatingSixCorrectedOuterCharacterStabilizer P χ 0 hfix ∈
      (normalizerInnerCharacterStabilizerHom P χ).range := by
  have hInner :
      (alternatingSixCorrectedOuterCharacterStabilizer P χ 0 hfix).1 ∈
        (SylowAutStabilizer.normalizerInnerHom P).range := by
    apply
      (SylowAutStabilizer.mem_normalizerInnerHom_range_iff_isInner
        P _).mpr
    refine
      ⟨SylowAutStabilizer.correctionConjugator P
          (alternatingSixUniversalCoverOuterRepresentative 0), ?_⟩
    change
      (SylowAutStabilizer.corrected P
          (alternatingSixUniversalCoverOuterRepresentative 0) :
        MulAut AlternatingSixUniversalCover) =
      MulAut.conj
        (SylowAutStabilizer.correctionConjugator P
          (alternatingSixUniversalCoverOuterRepresentative 0))
    rw [SylowAutStabilizer.corrected_coe,
      alternatingSixUniversalCoverOuterRepresentative_zero, mul_one]
  obtain ⟨n, hn⟩ := hInner
  refine ⟨n, ?_⟩
  apply Subtype.ext
  exact hn

namespace AlternatingSixFiveCTblLibRowIdentification

/-- Once the two ambient generator bridges are known, the audited
four-representative finite action detects exactly which representatives
fix the genuine character at every five-prime position. -/
theorem outerRepresentative_smul_character_iff
    (identification : AlternatingSixFiveCTblLibRowIdentification)
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (hAlphaOne :
      identification.AmbientCorrectedAlphaOneBridge T)
    (hAlphaTwo :
      identification.AmbientCorrectedAlphaTwoBridge T)
    (i : Fin 24)
    (j : Fin 4) :
    alternatingSixUniversalCoverOuterRepresentative j •
          alternatingSixAmbientPPrimeCharacterEquiv T 5
            (identification.ambientPositionEquiv i) =
        alternatingSixAmbientPPrimeCharacterEquiv T 5
          (identification.ambientPositionEquiv i) ↔
      alternatingSixFiveCTblLibOuterRepresentativeAction j i = i := by
  fin_cases j
  · simp [alternatingSixFiveCTblLibOuterRepresentativeAction]
  · have hBridge := hAlphaOne i
    rw [
      alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation_eq
    ] at hBridge
    change
      alternatingSixUniversalCoverTransportedAlphaOne •
            alternatingSixAmbientPPrimeCharacterEquiv T 5
              (identification.ambientPositionEquiv i) =
          alternatingSixAmbientPPrimeCharacterEquiv T 5
            (identification.ambientPositionEquiv i) ↔
        alternatingSixCTblLibFivePPrimeActionData.ambientAlphaOne i = i
    constructor
    · intro hfix
      apply identification.ambientPositionEquiv.injective
      have hSemantic :
          alternatingSixAmbientPPrimeAlphaOneRowPermutation T 5
              (identification.ambientPositionEquiv i) =
            identification.ambientPositionEquiv i := by
        apply (alternatingSixAmbientPPrimeCharacterEquiv T 5).injective
        rw [
          alternatingSixAmbientPPrimeAlphaOneRowPermutation_character
        ]
        exact hfix
      exact hBridge.symm.trans hSemantic
    · intro hfix
      have hSemantic :
          alternatingSixAmbientPPrimeAlphaOneRowPermutation T 5
              (identification.ambientPositionEquiv i) =
            identification.ambientPositionEquiv i :=
        hBridge.trans
          (congrArg identification.ambientPositionEquiv hfix)
      have hCharacter :=
        congrArg
          (alternatingSixAmbientPPrimeCharacterEquiv T 5)
          hSemantic
      rw [
        alternatingSixAmbientPPrimeAlphaOneRowPermutation_character
      ] at hCharacter
      exact hCharacter
  · have hBridge := hAlphaTwo i
    rw [
      alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation_eq
    ] at hBridge
    change
      alternatingSixUniversalCoverTransportedAlphaTwo •
            alternatingSixAmbientPPrimeCharacterEquiv T 5
              (identification.ambientPositionEquiv i) =
          alternatingSixAmbientPPrimeCharacterEquiv T 5
            (identification.ambientPositionEquiv i) ↔
        alternatingSixCTblLibFivePPrimeActionData.ambientAlphaTwo i = i
    constructor
    · intro hfix
      apply identification.ambientPositionEquiv.injective
      have hSemantic :
          alternatingSixAmbientPPrimeAlphaTwoRowPermutation T 5
              (identification.ambientPositionEquiv i) =
            identification.ambientPositionEquiv i := by
        apply (alternatingSixAmbientPPrimeCharacterEquiv T 5).injective
        rw [
          alternatingSixAmbientPPrimeAlphaTwoRowPermutation_character
        ]
        exact hfix
      exact hBridge.symm.trans hSemantic
    · intro hfix
      have hSemantic :
          alternatingSixAmbientPPrimeAlphaTwoRowPermutation T 5
              (identification.ambientPositionEquiv i) =
            identification.ambientPositionEquiv i :=
        hBridge.trans
          (congrArg identification.ambientPositionEquiv hfix)
      have hCharacter :=
        congrArg
          (alternatingSixAmbientPPrimeCharacterEquiv T 5)
          hSemantic
      rw [
        alternatingSixAmbientPPrimeAlphaTwoRowPermutation_character
      ] at hCharacter
      exact hCharacter
  · have hBridgeTwo := hAlphaTwo i
    have hBridgeOne :=
      hAlphaOne
        (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaTwo i)
    rw [
      alternatingSixAmbientPPrimeCorrectedAlphaTwoRowPermutation_eq
    ] at hBridgeTwo
    rw [
      alternatingSixAmbientPPrimeCorrectedAlphaOneRowPermutation_eq
    ] at hBridgeOne
    change
      alternatingSixUniversalCoverOuterRepresentative 3 •
            alternatingSixAmbientPPrimeCharacterEquiv T 5
              (identification.ambientPositionEquiv i) =
          alternatingSixAmbientPPrimeCharacterEquiv T 5
            (identification.ambientPositionEquiv i) ↔
        alternatingSixCTblLibFivePPrimeActionData.ambientAlphaOne
            (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaTwo i) =
          i
    rw [alternatingSixUniversalCoverOuterRepresentative_three]
    change
      alternatingSixUniversalCoverTransportedAlphaOne •
            (alternatingSixUniversalCoverTransportedAlphaTwo •
              alternatingSixAmbientPPrimeCharacterEquiv T 5
                (identification.ambientPositionEquiv i)) =
          alternatingSixAmbientPPrimeCharacterEquiv T 5
            (identification.ambientPositionEquiv i) ↔
        alternatingSixCTblLibFivePPrimeActionData.ambientAlphaOne
            (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaTwo i) =
          i
    have hBridgeProduct :
        alternatingSixAmbientPPrimeAlphaOneRowPermutation T 5
            (alternatingSixAmbientPPrimeAlphaTwoRowPermutation T 5
              (identification.ambientPositionEquiv i)) =
          identification.ambientPositionEquiv
            (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaOne
              (alternatingSixCTblLibFivePPrimeActionData.ambientAlphaTwo i)) := by
      rw [hBridgeTwo, hBridgeOne]
    constructor
    · intro hfix
      apply identification.ambientPositionEquiv.injective
      rw [← hBridgeProduct]
      apply (alternatingSixAmbientPPrimeCharacterEquiv T 5).injective
      rw [
        alternatingSixAmbientPPrimeAlphaOneRowPermutation_character,
        alternatingSixAmbientPPrimeAlphaTwoRowPermutation_character
      ]
      exact hfix
    · intro hfix
      have hSemantic :
          alternatingSixAmbientPPrimeAlphaOneRowPermutation T 5
              (alternatingSixAmbientPPrimeAlphaTwoRowPermutation T 5
                (identification.ambientPositionEquiv i)) =
            identification.ambientPositionEquiv i :=
        hBridgeProduct.trans
          (congrArg identification.ambientPositionEquiv hfix)
      have hCharacter :=
        congrArg
          (alternatingSixAmbientPPrimeCharacterEquiv T 5)
          hSemantic
      rw [
        alternatingSixAmbientPPrimeAlphaOneRowPermutation_character,
        alternatingSixAmbientPPrimeAlphaTwoRowPermutation_character
      ] at hCharacter
      exact hCharacter

/-- For any of the ten size-two positions, every genuine character-inertia
element has one of exactly two possible outer indices: zero or the recorded
nonidentity fixing representative.  In either case the remaining factor is
induced by the exact Sylow normalizer.

This is the concrete small-outer-inertia reduction for all ten rows at once.
-/
theorem outerOrbitTwo_characterStabilizer_normalForm
    (identification : AlternatingSixFiveCTblLibRowIdentification)
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (hAlphaOne :
      identification.AmbientCorrectedAlphaOneBridge T)
    (hAlphaTwo :
      identification.AmbientCorrectedAlphaTwoBridge T)
    (i : Fin 24)
    (hi : AlternatingSixFiveOuterOrbitTwoCTPosition i)
    (a :
      PPrimeCharacterStabilizer
        (alternatingSixUniversalCoverSylow 5)
        (alternatingSixAmbientPPrimeCharacterEquiv T 5
          (identification.ambientPositionEquiv i))) :
    ∃ (n :
          SylowNormalizer
            (alternatingSixUniversalCoverSylow 5))
        (j : Fin 4)
        (_hj :
          j = 0 ∨
            j =
              alternatingSixFiveOuterOrbitTwoFixedRepresentative i)
        (hfix :
          alternatingSixUniversalCoverOuterRepresentative j •
                alternatingSixAmbientPPrimeCharacterEquiv T 5
                  (identification.ambientPositionEquiv i) =
            alternatingSixAmbientPPrimeCharacterEquiv T 5
              (identification.ambientPositionEquiv i)),
      a =
        normalizerInnerCharacterStabilizerHom
            (alternatingSixUniversalCoverSylow 5)
            (alternatingSixAmbientPPrimeCharacterEquiv T 5
              (identification.ambientPositionEquiv i)) n *
          alternatingSixCorrectedOuterCharacterStabilizer
            (alternatingSixUniversalCoverSylow 5)
            (alternatingSixAmbientPPrimeCharacterEquiv T 5
              (identification.ambientPositionEquiv i))
            j hfix := by
  obtain ⟨n, j, hfix, ha⟩ :=
    alternatingSixCharacterStabilizer_inner_mul_correctedOuter
      (alternatingSixUniversalCoverSylow 5)
      (alternatingSixAmbientPPrimeCharacterEquiv T 5
        (identification.ambientPositionEquiv i))
      a
  have hFinite :
      alternatingSixFiveCTblLibOuterRepresentativeAction j i = i :=
    (identification.outerRepresentative_smul_character_iff
      T hAlphaOne hAlphaTwo i j).mp hfix
  have hj :
      j = 0 ∨
        j = alternatingSixFiveOuterOrbitTwoFixedRepresentative i :=
    (alternatingSixFiveOuterOrbitTwo_fixed_iff i hi j).mp hFinite
  exact ⟨n, j, hj, hfix, ha⟩

/-- The canonical corrected nonidentity outer generator of the character
stabilizer at a size-two five-prime position. -/
def outerOrbitTwo_correctedGenerator
    (identification : AlternatingSixFiveCTblLibRowIdentification)
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (hAlphaOne :
      identification.AmbientCorrectedAlphaOneBridge T)
    (hAlphaTwo :
      identification.AmbientCorrectedAlphaTwoBridge T)
    (i : Fin 24)
    (hi : AlternatingSixFiveOuterOrbitTwoCTPosition i) :
    PPrimeCharacterStabilizer
      (alternatingSixUniversalCoverSylow 5)
      (alternatingSixAmbientPPrimeCharacterEquiv T 5
        (identification.ambientPositionEquiv i)) :=
  alternatingSixCorrectedOuterCharacterStabilizer
    (alternatingSixUniversalCoverSylow 5)
    (alternatingSixAmbientPPrimeCharacterEquiv T 5
      (identification.ambientPositionEquiv i))
    (alternatingSixFiveOuterOrbitTwoFixedRepresentative i)
    ((identification.outerRepresentative_smul_character_iff
      T hAlphaOne hAlphaTwo i
      (alternatingSixFiveOuterOrbitTwoFixedRepresentative i)).mpr
        ((alternatingSixFiveOuterOrbitTwo_fixed_iff i hi
          (alternatingSixFiveOuterOrbitTwoFixedRepresentative i)).mpr
            (Or.inr rfl)))

/-- The genuine character stabilizer at each size-two position is covered by
the exact-normalizer inner subgroup and one right coset represented by the
canonical corrected nonidentity outer generator. -/
theorem outerOrbitTwo_characterStabilizer_twoCosetNormalForm
    (identification : AlternatingSixFiveCTblLibRowIdentification)
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (hAlphaOne :
      identification.AmbientCorrectedAlphaOneBridge T)
    (hAlphaTwo :
      identification.AmbientCorrectedAlphaTwoBridge T)
    (i : Fin 24)
    (hi : AlternatingSixFiveOuterOrbitTwoCTPosition i)
    (a :
      PPrimeCharacterStabilizer
        (alternatingSixUniversalCoverSylow 5)
        (alternatingSixAmbientPPrimeCharacterEquiv T 5
          (identification.ambientPositionEquiv i))) :
    ∃ h :
        (normalizerInnerCharacterStabilizerHom
          (alternatingSixUniversalCoverSylow 5)
          (alternatingSixAmbientPPrimeCharacterEquiv T 5
            (identification.ambientPositionEquiv i))).range,
      a = h.1 ∨
        a =
          h.1 *
            identification.outerOrbitTwo_correctedGenerator
              T hAlphaOne hAlphaTwo i hi := by
  obtain ⟨n, j, hj, hfix, ha⟩ :=
    identification.outerOrbitTwo_characterStabilizer_normalForm
      T hAlphaOne hAlphaTwo i hi a
  rcases hj with rfl | rfl
  · have hOuterInner :
        alternatingSixCorrectedOuterCharacterStabilizer
            (alternatingSixUniversalCoverSylow 5)
            (alternatingSixAmbientPPrimeCharacterEquiv T 5
              (identification.ambientPositionEquiv i))
            0 hfix ∈
          (normalizerInnerCharacterStabilizerHom
            (alternatingSixUniversalCoverSylow 5)
            (alternatingSixAmbientPPrimeCharacterEquiv T 5
              (identification.ambientPositionEquiv i))).range :=
      alternatingSixCorrectedOuterCharacterStabilizer_zero_mem_range
        (alternatingSixUniversalCoverSylow 5)
        (alternatingSixAmbientPPrimeCharacterEquiv T 5
          (identification.ambientPositionEquiv i))
        hfix
    refine
      ⟨⟨normalizerInnerCharacterStabilizerHom
            (alternatingSixUniversalCoverSylow 5)
            (alternatingSixAmbientPPrimeCharacterEquiv T 5
              (identification.ambientPositionEquiv i)) n *
          alternatingSixCorrectedOuterCharacterStabilizer
            (alternatingSixUniversalCoverSylow 5)
            (alternatingSixAmbientPPrimeCharacterEquiv T 5
              (identification.ambientPositionEquiv i))
            0 hfix,
        (normalizerInnerCharacterStabilizerHom
            (alternatingSixUniversalCoverSylow 5)
            (alternatingSixAmbientPPrimeCharacterEquiv T 5
              (identification.ambientPositionEquiv i))).range.mul_mem
          ⟨n, rfl⟩ hOuterInner⟩,
        Or.inl ha⟩
  · refine
      ⟨⟨normalizerInnerCharacterStabilizerHom
            (alternatingSixUniversalCoverSylow 5)
            (alternatingSixAmbientPPrimeCharacterEquiv T 5
              (identification.ambientPositionEquiv i)) n,
          ⟨n, rfl⟩⟩,
        Or.inr ?_⟩
    simpa [outerOrbitTwo_correctedGenerator] using ha

/-- The outer inertia quotient of each of the ten size-two rows has
cardinality at most two. -/
theorem outerOrbitTwo_outerInertiaQuotient_natCard_le_two
    (identification : AlternatingSixFiveCTblLibRowIdentification)
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (hAlphaOne :
      identification.AmbientCorrectedAlphaOneBridge T)
    (hAlphaTwo :
      identification.AmbientCorrectedAlphaTwoBridge T)
    (i : Fin 24)
    (hi : AlternatingSixFiveOuterOrbitTwoCTPosition i) :
    let χ :=
      alternatingSixAmbientPPrimeCharacterEquiv T 5
        (identification.ambientPositionEquiv i)
    letI :
        ((normalizerInnerCharacterStabilizerHom
          (alternatingSixUniversalCoverSylow 5) χ).range).Normal :=
      normalizerInnerCharacterStabilizerHom_range_normal
        (alternatingSixUniversalCoverSylow 5) χ
    Nat.card
        (PPrimeCharacterStabilizer
            (alternatingSixUniversalCoverSylow 5) χ ⧸
          (normalizerInnerCharacterStabilizerHom
            (alternatingSixUniversalCoverSylow 5) χ).range) ≤
      2 := by
  dsimp only
  letI :
      ((normalizerInnerCharacterStabilizerHom
        (alternatingSixUniversalCoverSylow 5)
        (alternatingSixAmbientPPrimeCharacterEquiv T 5
          (identification.ambientPositionEquiv i))).range).Normal :=
    normalizerInnerCharacterStabilizerHom_range_normal
      (alternatingSixUniversalCoverSylow 5)
      (alternatingSixAmbientPPrimeCharacterEquiv T 5
        (identification.ambientPositionEquiv i))
  apply quotient_natCard_le_two_of_twoCosetNormalForm
  exact
    identification.outerOrbitTwo_characterStabilizer_twoCosetNormalForm
      T hAlphaOne hAlphaTwo i hi

/-- Consequently, the outer inertia quotient of every size-two row is
cyclic.  This is the cyclic quotient over the already handled inner
normalizer image; it should be used for adjoining the one residual outer
implementer, not confused with the larger canonical semidirect quotient. -/
theorem outerOrbitTwo_outerInertiaQuotient_isCyclic
    (identification : AlternatingSixFiveCTblLibRowIdentification)
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (hAlphaOne :
      identification.AmbientCorrectedAlphaOneBridge T)
    (hAlphaTwo :
      identification.AmbientCorrectedAlphaTwoBridge T)
    (i : Fin 24)
    (hi : AlternatingSixFiveOuterOrbitTwoCTPosition i) :
    let χ :=
      alternatingSixAmbientPPrimeCharacterEquiv T 5
        (identification.ambientPositionEquiv i)
    letI :
        ((normalizerInnerCharacterStabilizerHom
          (alternatingSixUniversalCoverSylow 5) χ).range).Normal :=
      normalizerInnerCharacterStabilizerHom_range_normal
        (alternatingSixUniversalCoverSylow 5) χ
    IsCyclic
      (PPrimeCharacterStabilizer
          (alternatingSixUniversalCoverSylow 5) χ ⧸
        (normalizerInnerCharacterStabilizerHom
          (alternatingSixUniversalCoverSylow 5) χ).range) := by
  dsimp only
  letI :
      ((normalizerInnerCharacterStabilizerHom
        (alternatingSixUniversalCoverSylow 5)
        (alternatingSixAmbientPPrimeCharacterEquiv T 5
          (identification.ambientPositionEquiv i))).range).Normal :=
    normalizerInnerCharacterStabilizerHom_range_normal
      (alternatingSixUniversalCoverSylow 5)
      (alternatingSixAmbientPPrimeCharacterEquiv T 5
        (identification.ambientPositionEquiv i))
  apply isCyclic_of_natCard_le_two
  exact
    identification.outerOrbitTwo_outerInertiaQuotient_natCard_le_two
      T hAlphaOne hAlphaTwo i hi

end AlternatingSixFiveCTblLibRowIdentification

end InductiveMcKay
end McKayConjecture
