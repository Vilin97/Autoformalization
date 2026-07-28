/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InnerAutomorphism
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveThreeAutomorphismClassification

/-!
# The equivariant `3'`-character table of `SL(2, 𝔽₅)`

The explicit ambient and normalizer enumerations are matched row by row.
The automorphism classification reduces equivariance to inner
automorphisms, which fix characters, and the single outer representative
whose row action was computed explicitly.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- A stabilizing inner automorphism fixes every ambient `3'`-character. -/
theorem specialLinearTwoFive_sylowThreeInner_smul_ambient
    (a : SylowAutStabilizer specialLinearTwoFiveSylowThree)
    (g : SpecialLinearTwoFive)
    (ha : a.1 = MulAut.conj g)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive 3) :
    a • χ = χ := by
  change a.1 • χ = χ
  rw [ha, pPrime_conj_smul]

/-- A stabilizing inner automorphism restricts to an inner automorphism of
the exact normalizer, and hence fixes every normalizer `3'`-character. -/
theorem specialLinearTwoFive_sylowThreeInner_smul_normalizer
    (a : SylowAutStabilizer specialLinearTwoFiveSylowThree)
    (g : SpecialLinearTwoFiveSylowThreeNormalizer)
    (ha : a.1 = MulAut.conj g.1)
    (χ :
      PPrimeIrreducibleCharacter
        SpecialLinearTwoFiveSylowThreeNormalizer 3) :
    a • χ = χ := by
  change
    (SylowAutStabilizer.normalizerRestrictionHom
      specialLinearTwoFiveSylowThree a) • χ = χ
  rw [
    specialLinearTwoFive_sylowThreeNormalizerRestriction_eq_inner
      a g ha,
    pPrime_conj_smul]

/-- In the outer normal form, the inner factor disappears from the
ambient character action. -/
theorem specialLinearTwoFive_sylowThreeOuterInner_smul_ambient
    (a : SylowAutStabilizer specialLinearTwoFiveSylowThree)
    (g : SpecialLinearTwoFiveSylowThreeNormalizer)
    (ha :
      a.1 =
        specialLinearTwoFiveSylowThreeOuterAutomorphism *
          MulAut.conj g.1)
    (r : SpecialLinearTwoFivePPrimeCharacterRow 3) :
    a • specialLinearTwoFivePPrimeCharacterEquiv 3 r =
      specialLinearTwoFivePPrimeCharacterEquiv 3
        (specialLinearTwoFiveThreeOuterPPrimeRow r) := by
  change
    a.1 • specialLinearTwoFivePPrimeCharacterEquiv 3 r =
      specialLinearTwoFivePPrimeCharacterEquiv 3
        (specialLinearTwoFiveThreeOuterPPrimeRow r)
  rw [ha, mul_smul, pPrime_conj_smul]
  exact
    specialLinearTwoFiveOuterAutomorphism_smul_pPrimeCharacter r

/-- In the outer normal form, the inner factor also disappears after
restriction to the exact normalizer. -/
theorem specialLinearTwoFive_sylowThreeOuterInner_smul_normalizer
    (a : SylowAutStabilizer specialLinearTwoFiveSylowThree)
    (g : SpecialLinearTwoFiveSylowThreeNormalizer)
    (ha :
      a.1 =
        specialLinearTwoFiveSylowThreeOuterAutomorphism *
          MulAut.conj g.1)
    (r : QuaternionGroupThreeCharacterRow) :
    a • specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv r =
      specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
        (quaternionGroupThreeOuterCharacterRow r) := by
  change
    (SylowAutStabilizer.normalizerRestrictionHom
      specialLinearTwoFiveSylowThree a) •
        specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv r =
      specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
        (quaternionGroupThreeOuterCharacterRow r)
  rw [
    specialLinearTwoFive_sylowThreeNormalizerRestriction_eq_outer_inner
      a g ha,
    mul_smul, pPrime_conj_smul]
  exact
    specialLinearTwoFiveSylowThreeOuterStabilizer_smul_normalizerCharacter r

/-- The explicit row matching is equivariant under every automorphism
stabilizing the chosen Sylow-three subgroup. -/
theorem specialLinearTwoFiveThreeCharacterRowEquiv_equivariant
    (a : SylowAutStabilizer specialLinearTwoFiveSylowThree)
    (r : SpecialLinearTwoFivePPrimeCharacterRow 3) :
    specialLinearTwoFiveThreeCharacterRowEquiv
        ((specialLinearTwoFivePPrimeCharacterEquiv 3).symm
          (a • specialLinearTwoFivePPrimeCharacterEquiv 3 r)) =
      specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv.symm
        (a •
          specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
            (specialLinearTwoFiveThreeCharacterRowEquiv r)) := by
  obtain ⟨g, hinner | houter⟩ :=
    specialLinearTwoFive_sylowThreeStabilizer_eq_inner_or_outer_inner a
  · have hamb :
        a • specialLinearTwoFivePPrimeCharacterEquiv 3 r =
          specialLinearTwoFivePPrimeCharacterEquiv 3 r :=
      specialLinearTwoFive_sylowThreeInner_smul_ambient
        a g.1 hinner _
    have hnormalizer :
        a •
            specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
              (specialLinearTwoFiveThreeCharacterRowEquiv r) =
          specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
            (specialLinearTwoFiveThreeCharacterRowEquiv r) :=
      specialLinearTwoFive_sylowThreeInner_smul_normalizer
        a g hinner _
    rw [hamb, hnormalizer,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  · have hamb :
        a • specialLinearTwoFivePPrimeCharacterEquiv 3 r =
          specialLinearTwoFivePPrimeCharacterEquiv 3
            (specialLinearTwoFiveThreeOuterPPrimeRow r) :=
      specialLinearTwoFive_sylowThreeOuterInner_smul_ambient
        a g houter r
    have hnormalizer :
        a •
            specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
              (specialLinearTwoFiveThreeCharacterRowEquiv r) =
          specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
            (quaternionGroupThreeOuterCharacterRow
              (specialLinearTwoFiveThreeCharacterRowEquiv r)) :=
      specialLinearTwoFive_sylowThreeOuterInner_smul_normalizer
        a g houter _
    rw [hamb, hnormalizer,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact specialLinearTwoFiveThreeCharacterRowEquiv_map_outer r

/-- The fully checked ordinary-character-table input at `p = 3`. -/
def specialLinearTwoFiveThreeCharacterTableCompletion :
    SpecialLinearTwoFiveThreeCharacterTableCompletion
      (SpecialLinearTwoFivePPrimeCharacterRow 3) where
  ambientEnumeration := specialLinearTwoFivePPrimeCharacterEquiv 3
  indexEquiv := specialLinearTwoFiveThreeCharacterRowEquiv
  indexEquivariance :=
    specialLinearTwoFiveThreeCharacterRowEquiv_equivariant

/-- The resulting explicit automorphism-equivariant McKay equivalence at
`p = 3`. -/
def specialLinearTwoFiveThreeEquivariantMcKayEquiv :
    EquivariantMcKayEquiv specialLinearTwoFiveSylowThree :=
  specialLinearTwoFiveThreeCharacterTableCompletion.toEquivariantMcKayEquiv

@[simp]
theorem specialLinearTwoFiveThreeEquivariantMcKayEquiv_apply
    (r : SpecialLinearTwoFivePPrimeCharacterRow 3) :
    specialLinearTwoFiveThreeEquivariantMcKayEquiv
        (specialLinearTwoFivePPrimeCharacterEquiv 3 r) =
      specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
        (specialLinearTwoFiveThreeCharacterRowEquiv r) :=
  specialLinearTwoFiveThreeCharacterTableCompletion
    |>.toEquivariantMcKayEquiv_apply_enumerated r

end InductiveMcKay
end McKayConjecture
