/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixTwoInvariantSafeLocalCentralAction

/-!
# Quaternion-sign obstructions for the invariant-safe two-local orientation

Every automorphism in the Sylow-two stabilizer preserves the Sylow subgroup
inside its normalizer.  In the concrete `C₃ × Q₁₆` model this forces two
simple invariants on the linear quaternion rows:

* the sign on the characteristic order-eight cyclic subgroup is fixed; and
* a row trivial on the whole quaternion factor remains trivial there.

The invariant-safe audited permutations violate these invariants.  Thus
both residual quaternion sign bridges, and hence both full local bridges,
are false.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixTwoInvariantSafeLocalSignObstructionsFactPrime :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The quaternion factor of the concrete model, embedded in the actual
fixed Sylow-two normalizer. -/
private def actualNormalizerQuaternionElement
    (q : QuaternionGroup 4) :
    SylowNormalizer (alternatingSixUniversalCoverSylow 2) :=
  alternatingSixTwoNormalizerModelEquivUniversalCoverNormalizer (1, q)

private theorem actualNormalizerQuaternionElement_eq
    (q : QuaternionGroup 4) :
    actualNormalizerQuaternionElement q =
      (quaternionFourEquivAlternatingSixUniversalCoverSylowTwoInNormalizer
          q :
        SylowNormalizer (alternatingSixUniversalCoverSylow 2)) := by
  apply Subtype.ext
  unfold actualNormalizerQuaternionElement
  simp [
    alternatingSixTwoNormalizerModelEquivUniversalCoverNormalizer,
    MulEquiv.prodCongr,
    Equiv.prodCongr,
    Prod.map_apply',
    alternatingSixUniversalCoverTwoNormalizerInternalProductEquiv,
    alternatingSixUniversalCoverTwoNormalizerProductHom
  ]

private theorem actualNormalizerQuaternionElement_mem_sylow
    (q : QuaternionGroup 4) :
    (actualNormalizerQuaternionElement q :
        AlternatingSixUniversalCover) ∈
      alternatingSixUniversalCoverSylow 2 := by
  rw [actualNormalizerQuaternionElement_eq]
  exact
    (quaternionFourEquivAlternatingSixUniversalCoverSylowTwoInNormalizer q).2

private theorem exists_quaternionElement_eq_of_mem_sylow
    (x : SylowNormalizer (alternatingSixUniversalCoverSylow 2))
    (hx : (x : AlternatingSixUniversalCover) ∈
      alternatingSixUniversalCoverSylow 2) :
    ∃ q : QuaternionGroup 4,
      x = actualNormalizerQuaternionElement q := by
  let y : alternatingSixUniversalCoverSylowTwoInNormalizer :=
    ⟨x, hx⟩
  obtain ⟨q, hq⟩ :=
    quaternionFourEquivAlternatingSixUniversalCoverSylowTwoInNormalizer.surjective
      y
  refine ⟨q, ?_⟩
  rw [actualNormalizerQuaternionElement_eq, hq]

private theorem inverse_restriction_mem_sylow
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 2))
    (q : QuaternionGroup 4) :
    (((SylowAutStabilizer.normalizerRestrictionHom
        (alternatingSixUniversalCoverSylow 2) a).symm
      (actualNormalizerQuaternionElement q) :
        SylowNormalizer (alternatingSixUniversalCoverSylow 2)) :
      AlternatingSixUniversalCover) ∈
        alternatingSixUniversalCoverSylow 2 := by
  rw [SylowAutStabilizer.normalizerRestrictionHom_symm_apply_coe]
  have hq := actualNormalizerQuaternionElement_mem_sylow q
  have ha := congrArg Sylow.toSubgroup a.2
  change
    Subgroup.map (a.1 : MulAut AlternatingSixUniversalCover).toMonoidHom
        (alternatingSixUniversalCoverSylow 2 :
          Subgroup AlternatingSixUniversalCover) =
      alternatingSixUniversalCoverSylow 2 at ha
  have hqMap :
      (actualNormalizerQuaternionElement q :
          AlternatingSixUniversalCover) ∈
        Subgroup.map (a.1 : MulAut AlternatingSixUniversalCover).toMonoidHom
          (alternatingSixUniversalCoverSylow 2 :
            Subgroup AlternatingSixUniversalCover) := by
    rw [ha]
    exact hq
  obtain ⟨y, hy, hay⟩ := hqMap
  rw [← hay]
  change a.1.symm (a.1 y) ∈ alternatingSixUniversalCoverSylow 2
  simpa using hy

private theorem actualNormalizerCharacter_values_quaternion_a_one
    (r : AlternatingSixTwoConcreteNormalizerRow) :
    (alternatingSixTwoActualNormalizerPPrimeCharacterEquiv r).1.values
        (actualNormalizerQuaternionElement
          (QuaternionGroup.a (1 : ZMod 8))) =
      (QuaternionGroupFour.signParameter r.2.1 : ℂ) := by
  rw [actualNormalizerQuaternionElement,
    alternatingSixTwoActualNormalizerPPrimeCharacterEquiv_values]
  simpa using
    alternatingSixTwoModelNormalizerPPrimeCharacterEquiv_values_a
      r (1 : Multiplicative (ZMod 3)) 1

private theorem actualNormalizerCharacter_values_quaternion_of_order_eight
    (r : AlternatingSixTwoConcreteNormalizerRow)
    (q : QuaternionGroup 4)
    (hq : orderOf q = 8) :
    (alternatingSixTwoActualNormalizerPPrimeCharacterEquiv r).1.values
        (actualNormalizerQuaternionElement q) =
      (QuaternionGroupFour.signParameter r.2.1 : ℂ) := by
  rw [actualNormalizerQuaternionElement,
    alternatingSixTwoActualNormalizerPPrimeCharacterEquiv_values]
  rcases r with ⟨j, u, v⟩
  rcases q with i | i
  · rw [show
        (alternatingSixTwoModelNormalizerPPrimeCharacterEquiv
            (j, (u, v))).1.values
            (1, QuaternionGroup.a i) =
          (QuaternionGroupFour.signParameter u ^ i.val : ℂˣ) by
        have hvalue :=
          alternatingSixTwoModelNormalizerPPrimeCharacterEquiv_values_a
            (j, (u, v)) (1 : Multiplicative (ZMod 3)) i.val
        rw [ZMod.natCast_zmod_val i, map_one] at hvalue
        norm_num at hvalue
        simpa using hvalue]
    have hiLt : i.val < 8 := ZMod.val_lt i
    interval_cases hi : i.val
    all_goals
      try
        norm_num [QuaternionGroup.orderOf_a, hi] at hq
    all_goals
      fin_cases u
    all_goals
      norm_num [QuaternionGroupFour.signParameter, hi]
  · rw [QuaternionGroup.orderOf_xa] at hq
    omega

private theorem quaternionGroupFourLinearHom_zero :
    QuaternionGroupFour.linearHom
        ((0, 0) : QuaternionGroupFour.LinearIndex) =
      1 := by
  apply MonoidHom.ext
  intro q
  rcases q with i | i
  · simp only [QuaternionGroupFour.linearHom,
      QuaternionGroupFour.linearHomOfSigns,
      QuaternionGroup.lift_apply_a]
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective i
    rw [← hz, QuaternionGroup.zmodPower_intCast]
    simp [QuaternionGroupFour.signParameter]
  · simp only [QuaternionGroupFour.linearHom,
      QuaternionGroupFour.linearHomOfSigns,
      QuaternionGroup.lift_apply_xa]
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective i
    rw [← hz, QuaternionGroup.zmodPower_intCast]
    simp [QuaternionGroupFour.signParameter]

private theorem actualNormalizerCharacter_values_quaternion_zero_sign
    (j : Fin 3)
    (q : QuaternionGroup 4) :
    (alternatingSixTwoActualNormalizerPPrimeCharacterEquiv
        (j, ((0, 0) : QuaternionGroupFour.LinearIndex))).1.values
        (actualNormalizerQuaternionElement q) =
      1 := by
  rw [actualNormalizerQuaternionElement,
    alternatingSixTwoActualNormalizerPPrimeCharacterEquiv_values]
  change
    (AlternatingSixTwoNormalizerModelCharacterTable.pPrimeCharacterEquiv
      (j, ((0, 0) : QuaternionGroupFour.LinearIndex))).1.values
        (1, q) =
      1
  rw [
    AlternatingSixTwoNormalizerModelCharacterTable.pPrimeCharacterEquiv_values
  ]
  change
    (CyclicThree.linearCharacter j).values 1 *
        (QuaternionGroupFour.linearCharacter (0, 0)).values q =
      1
  rw [CyclicThree.linearCharacter,
    QuaternionGroupFour.linearCharacter,
    IrreducibleCharacter.linear_values,
    IrreducibleCharacter.linear_values,
    quaternionGroupFourLinearHom_zero]
  simp

private theorem actualNormalizerCharacter_values_quaternion_xa_zero
    (r : AlternatingSixTwoConcreteNormalizerRow) :
    (alternatingSixTwoActualNormalizerPPrimeCharacterEquiv r).1.values
        (actualNormalizerQuaternionElement
          (QuaternionGroup.xa (0 : ZMod 8))) =
      (QuaternionGroupFour.signParameter r.2.2 : ℂ) := by
  rw [actualNormalizerQuaternionElement,
    alternatingSixTwoActualNormalizerPPrimeCharacterEquiv_values]
  simpa using
    alternatingSixTwoModelNormalizerPPrimeCharacterEquiv_values_xa
      r (1 : Multiplicative (ZMod 3)) 0

/-- Every genuine Sylow-stabilizer action fixes the first quaternion sign
coordinate of every enumerated local row. -/
theorem alternatingSixTwoActualNormalizerRowPermutation_quaternion_fst
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 2))
    (r : AlternatingSixTwoConcreteNormalizerRow) :
    (alternatingSixTwoActualNormalizerRowPermutation a r).2.1 =
      r.2.1 := by
  apply QuaternionGroupFour.signParameter_injective
  apply Units.ext
  have hcharacter :=
    alternatingSixTwoActualNormalizerRowPermutation_character a r
  have hvalue :=
    congrArg
      (fun χ :
          PPrimeIrreducibleCharacter
            (SylowNormalizer (alternatingSixUniversalCoverSylow 2)) 2 =>
        χ.1.values
          (actualNormalizerQuaternionElement
            (QuaternionGroup.a (1 : ZMod 8))))
      hcharacter
  rw [
    actualNormalizerCharacter_values_quaternion_a_one,
    SylowAutStabilizer.smul_normalizer_pPrime_values
  ] at hvalue
  obtain ⟨q, hq⟩ :=
    exists_quaternionElement_eq_of_mem_sylow
      ((SylowAutStabilizer.normalizerRestrictionHom
          (alternatingSixUniversalCoverSylow 2) a).symm
        (actualNormalizerQuaternionElement
          (QuaternionGroup.a (1 : ZMod 8))))
      (inverse_restriction_mem_sylow a
        (QuaternionGroup.a (1 : ZMod 8)))
  rw [hq] at hvalue
  have horder :
      orderOf q = 8 := by
    calc
      orderOf q =
          orderOf ((1, q) : AlternatingSixTwoNormalizerModel) := by
        rw [Prod.orderOf_mk, orderOf_one, Nat.lcm_one_left]
      _ = orderOf (actualNormalizerQuaternionElement q) := by
        exact
          (alternatingSixTwoNormalizerModelEquivUniversalCoverNormalizer
            |>.orderOf_eq (1, q)).symm
      _ =
          orderOf
            ((SylowAutStabilizer.normalizerRestrictionHom
                (alternatingSixUniversalCoverSylow 2) a).symm
              (actualNormalizerQuaternionElement
                (QuaternionGroup.a (1 : ZMod 8)))) := by
        rw [hq]
      _ =
          orderOf
            (actualNormalizerQuaternionElement
              (QuaternionGroup.a (1 : ZMod 8))) := by
        exact
          (SylowAutStabilizer.normalizerRestrictionHom
            (alternatingSixUniversalCoverSylow 2) a).symm.orderOf_eq _
      _ =
          orderOf
            ((1, QuaternionGroup.a (1 : ZMod 8)) :
              AlternatingSixTwoNormalizerModel) := by
        exact
          alternatingSixTwoNormalizerModelEquivUniversalCoverNormalizer
            |>.orderOf_eq _
      _ = 8 := by
        rw [Prod.orderOf_mk, orderOf_one, Nat.lcm_one_left,
          QuaternionGroup.orderOf_a_one]
  rw [actualNormalizerCharacter_values_quaternion_of_order_eight r q horder]
    at hvalue
  exact hvalue

/-- A row whose quaternion sign pair is zero remains zero under every
genuine Sylow-stabilizer action. -/
theorem alternatingSixTwoActualNormalizerRowPermutation_quaternion_zero
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 2))
    (j : Fin 3) :
    (alternatingSixTwoActualNormalizerRowPermutation
        a (j, ((0, 0) : QuaternionGroupFour.LinearIndex))).2 =
      ((0, 0) : QuaternionGroupFour.LinearIndex) := by
  let target :=
    alternatingSixTwoActualNormalizerRowPermutation
      a (j, ((0, 0) : QuaternionGroupFour.LinearIndex))
  apply Prod.ext
  · exact alternatingSixTwoActualNormalizerRowPermutation_quaternion_fst
      a (j, ((0, 0) : QuaternionGroupFour.LinearIndex))
  · apply QuaternionGroupFour.signParameter_injective
    apply Units.ext
    have hcharacter :=
      alternatingSixTwoActualNormalizerRowPermutation_character
        a (j, ((0, 0) : QuaternionGroupFour.LinearIndex))
    have hvalue :=
      congrArg
        (fun χ :
            PPrimeIrreducibleCharacter
              (SylowNormalizer (alternatingSixUniversalCoverSylow 2)) 2 =>
          χ.1.values
            (actualNormalizerQuaternionElement
              (QuaternionGroup.xa (0 : ZMod 8))))
        hcharacter
    rw [
      actualNormalizerCharacter_values_quaternion_xa_zero,
      SylowAutStabilizer.smul_normalizer_pPrime_values
    ] at hvalue
    obtain ⟨q, hq⟩ :=
      exists_quaternionElement_eq_of_mem_sylow
        ((SylowAutStabilizer.normalizerRestrictionHom
            (alternatingSixUniversalCoverSylow 2) a).symm
          (actualNormalizerQuaternionElement
            (QuaternionGroup.xa (0 : ZMod 8))))
        (inverse_restriction_mem_sylow a
          (QuaternionGroup.xa (0 : ZMod 8)))
    rw [hq,
      actualNormalizerCharacter_values_quaternion_zero_sign] at hvalue
    simpa [target, QuaternionGroupFour.signParameter] using hvalue

/-! ### Explicit invariant-safe counterexamples -/

private theorem invariantSafe_localPosition_six :
    (alternatingSixTwoCTblLibInvariantSafeRowIdentification
        |>.localPositionEquiv) (6 : Fin 12) =
      ((1 : Fin 3), ((0 : Fin 2), (0 : Fin 2))) := by
  change
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
        (alternatingSixTwoCTblLibInvariantSafeAmbientPositionEquiv
          (alternatingSixCTblLibTwoPPrimeActionData.candidate.symm 6)) =
      _
  rw [alternatingSixCTblLibTwo_candidate_symm_apply]
  rfl

private theorem invariantSafe_localAlphaOne_six :
    (alternatingSixTwoCTblLibInvariantSafeRowIdentification
        |>.localPositionEquiv)
          (alternatingSixCTblLibTwoPPrimeActionData.localAlphaOne
            (6 : Fin 12)) =
      ((2 : Fin 3), ((0 : Fin 2), (1 : Fin 2))) := by
  change
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
        (alternatingSixTwoCTblLibInvariantSafeAmbientPositionEquiv
          (alternatingSixCTblLibTwoPPrimeActionData.candidate.symm 7)) =
      _
  rw [alternatingSixCTblLibTwo_candidate_symm_apply]
  rfl

private theorem invariantSafe_localPosition_one :
    (alternatingSixTwoCTblLibInvariantSafeRowIdentification
        |>.localPositionEquiv) (1 : Fin 12) =
      ((0 : Fin 3), ((0 : Fin 2), (1 : Fin 2))) := by
  change
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
        (alternatingSixTwoCTblLibInvariantSafeAmbientPositionEquiv
          (alternatingSixCTblLibTwoPPrimeActionData.candidate.symm 1)) =
      _
  rw [alternatingSixCTblLibTwo_candidate_symm_apply]
  rfl

private theorem invariantSafe_localAlphaTwo_one :
    (alternatingSixTwoCTblLibInvariantSafeRowIdentification
        |>.localPositionEquiv)
          (alternatingSixCTblLibTwoPPrimeActionData.localAlphaTwo
            (1 : Fin 12)) =
      ((0 : Fin 3), ((1 : Fin 2), (0 : Fin 2))) := by
  change
    alternatingSixAmbientTwoCentralBlockRowEquivConcreteNormalizerRow
        (alternatingSixTwoCTblLibInvariantSafeAmbientPositionEquiv
          (alternatingSixCTblLibTwoPPrimeActionData.candidate.symm 2)) =
      _
  rw [alternatingSixCTblLibTwo_candidate_symm_apply]
  rfl

/-- At zero-based local position six, the first audited target gives a
nontrivial reflection sign to a row which is trivial on the quaternion
factor.  No genuine Sylow-stabilizer action can do this. -/
theorem
    alternatingSixTwoInvariantSafe_localAlphaOne_sign_counterexample :
    (alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
        (alternatingSixTwoCTblLibInvariantSafeRowIdentification
          |>.localPositionEquiv (6 : Fin 12))).2 ≠
      (alternatingSixTwoCTblLibInvariantSafeRowIdentification
        |>.localPositionEquiv
          (alternatingSixCTblLibTwoPPrimeActionData.localAlphaOne
            (6 : Fin 12))).2 := by
  rw [invariantSafe_localPosition_six,
    invariantSafe_localAlphaOne_six]
  intro h
  have hzero :=
    alternatingSixTwoActualNormalizerRowPermutation_quaternion_zero
      (alternatingSixUniversalCoverCorrectedAlphaOneStabilizer
        (alternatingSixUniversalCoverSylow 2))
      (1 : Fin 3)
  have hzero' :
      (alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
          ((1 : Fin 3), ((0 : Fin 2), (0 : Fin 2)))).2 =
        ((0 : Fin 2), (0 : Fin 2)) := by
    simpa [
      alternatingSixTwoActualNormalizerCorrectedAlphaOneRowPermutation
    ] using hzero
  rw [hzero'] at h
  exact (by decide :
    ((0 : Fin 2), (0 : Fin 2)) ≠ ((0 : Fin 2), (1 : Fin 2))) h

/-- At zero-based local position one, the second audited target changes
the sign on the characteristic order-eight cyclic subgroup.  No genuine
Sylow-stabilizer action can do this. -/
theorem
    alternatingSixTwoInvariantSafe_localAlphaTwo_sign_counterexample :
    (alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
        (alternatingSixTwoCTblLibInvariantSafeRowIdentification
          |>.localPositionEquiv (1 : Fin 12))).2 ≠
      (alternatingSixTwoCTblLibInvariantSafeRowIdentification
        |>.localPositionEquiv
          (alternatingSixCTblLibTwoPPrimeActionData.localAlphaTwo
            (1 : Fin 12))).2 := by
  rw [invariantSafe_localPosition_one,
    invariantSafe_localAlphaTwo_one]
  intro h
  have hfst :=
    alternatingSixTwoActualNormalizerRowPermutation_quaternion_fst
      (alternatingSixUniversalCoverCorrectedAlphaTwoStabilizer
        (alternatingSixUniversalCoverSylow 2))
      ((0 : Fin 3), ((0 : Fin 2), (1 : Fin 2)))
  have hfst' :
      (alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
          ((0 : Fin 3), ((0 : Fin 2), (1 : Fin 2)))).2.1 =
        (0 : Fin 2) := by
    simpa [
      alternatingSixTwoActualNormalizerCorrectedAlphaTwoRowPermutation
    ] using hfst
  have hfstTarget := congrArg Prod.fst h
  rw [hfst'] at hfstTarget
  exact (by decide : (0 : Fin 2) ≠ 1) hfstTarget

/-- The first residual quaternion sign bridge for the invariant-safe
orientation is false. -/
theorem alternatingSixTwoInvariantSafe_not_localAlphaOneSignBridge :
    ¬ AlternatingSixTwoInvariantSafeLocalAlphaOneSignBridge := by
  intro h
  exact
    alternatingSixTwoInvariantSafe_localAlphaOne_sign_counterexample
      (h (6 : Fin 12))

/-- The second residual quaternion sign bridge for the invariant-safe
orientation is false. -/
theorem alternatingSixTwoInvariantSafe_not_localAlphaTwoSignBridge :
    ¬ AlternatingSixTwoInvariantSafeLocalAlphaTwoSignBridge := by
  intro h
  exact
    alternatingSixTwoInvariantSafe_localAlphaTwo_sign_counterexample
      (h (1 : Fin 12))

/-- Consequently the invariant-safe first full local generator bridge is
false. -/
theorem
    alternatingSixTwoCTblLibInvariantSafe_not_localAlphaOneBridge :
    ¬ (alternatingSixTwoCTblLibInvariantSafeRowIdentification
        |>.LocalCorrectedAlphaOneBridge) := by
  intro h
  exact alternatingSixTwoInvariantSafe_not_localAlphaOneSignBridge
    (alternatingSixTwoCTblLibInvariantSafe_localAlphaOneBridge_iff_signBridge.mp
      h)

/-- Consequently the invariant-safe second full local generator bridge is
false. -/
theorem
    alternatingSixTwoCTblLibInvariantSafe_not_localAlphaTwoBridge :
    ¬ (alternatingSixTwoCTblLibInvariantSafeRowIdentification
        |>.LocalCorrectedAlphaTwoBridge) := by
  intro h
  exact alternatingSixTwoInvariantSafe_not_localAlphaTwoSignBridge
    (alternatingSixTwoCTblLibInvariantSafe_localAlphaTwoBridge_iff_signBridge.mp
      h)

end InductiveMcKay
end McKayConjecture
