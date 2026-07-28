/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveFiveOuterActions

/-!
# The equivariant `5'`-character table of `SL(2, 𝔽₅)`

The explicit ambient and normalizer enumerations are matched row by row.
The stabilizer classification reduces equivariance to inner
automorphisms, which fix characters, and the diagonal outer
representative, whose row action was computed explicitly.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance factPrimeFiveForEquivariantTable :
    Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- A stabilizing inner automorphism fixes every ambient
`5'`-character. -/
theorem specialLinearTwoFive_sylowFiveInner_smul_ambient
    (a : SylowAutStabilizer specialLinearTwoFiveSylowFive)
    (g : SpecialLinearTwoFive)
    (ha : a.1 = MulAut.conj g)
    (χ : PPrimeIrreducibleCharacter SpecialLinearTwoFive 5) :
    a • χ = χ := by
  change a.1 • χ = χ
  rw [ha, pPrime_conj_smul]

/-- A stabilizing inner automorphism restricts to an inner automorphism
of the exact normalizer and fixes every normalizer `5'`-character. -/
theorem specialLinearTwoFive_sylowFiveInner_smul_normalizer
    (a : SylowAutStabilizer specialLinearTwoFiveSylowFive)
    (g : SylowNormalizer specialLinearTwoFiveSylowFive)
    (ha : a.1 = MulAut.conj g.1)
    (χ :
      PPrimeIrreducibleCharacter
        (SylowNormalizer specialLinearTwoFiveSylowFive) 5) :
    a • χ = χ := by
  change
    (SylowAutStabilizer.normalizerRestrictionHom
      specialLinearTwoFiveSylowFive a) • χ = χ
  rw [
    specialLinearTwoFive_sylowFiveNormalizerRestriction_eq_inner
      a g ha,
    pPrime_conj_smul]

/-- In the outer normal form, the inner factor disappears from the
ambient character action. -/
theorem specialLinearTwoFive_sylowFiveOuterInner_smul_ambient
    (a : SylowAutStabilizer specialLinearTwoFiveSylowFive)
    (g : SylowNormalizer specialLinearTwoFiveSylowFive)
    (ha :
      a.1 =
        specialLinearTwoFiveDiagonalOuterAutomorphism *
          MulAut.conj g.1)
    (r : SpecialLinearTwoFivePPrimeCharacterRow 5) :
    a • specialLinearTwoFivePPrimeCharacterEquiv 5 r =
      specialLinearTwoFivePPrimeCharacterEquiv 5
        (specialLinearTwoFiveFiveOuterPPrimeRow r) := by
  change
    a.1 • specialLinearTwoFivePPrimeCharacterEquiv 5 r =
      specialLinearTwoFivePPrimeCharacterEquiv 5
        (specialLinearTwoFiveFiveOuterPPrimeRow r)
  rw [ha, mul_smul, pPrime_conj_smul]
  exact
    specialLinearTwoFiveDiagonalOuterAutomorphism_smul_fivePPrimeCharacter r

/-- In the outer normal form, the inner factor also disappears after
restriction to the exact normalizer. -/
theorem specialLinearTwoFive_sylowFiveOuterInner_smul_normalizer
    (a : SylowAutStabilizer specialLinearTwoFiveSylowFive)
    (g : SylowNormalizer specialLinearTwoFiveSylowFive)
    (ha :
      a.1 =
        specialLinearTwoFiveDiagonalOuterAutomorphism *
          MulAut.conj g.1)
    (r : QuaternionGroupFive.CharacterRow) :
    a • specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv r =
      specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv
        (specialLinearTwoFiveFiveNormalizerOuterCharacterRow r) := by
  change
    (SylowAutStabilizer.normalizerRestrictionHom
      specialLinearTwoFiveSylowFive a) •
        specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv r =
      specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv
        (specialLinearTwoFiveFiveNormalizerOuterCharacterRow r)
  rw [
    specialLinearTwoFive_sylowFiveNormalizerRestriction_eq_outer_inner
      a g ha,
    mul_smul, pPrime_conj_smul]
  exact
    specialLinearTwoFiveSylowFiveOuterAutomorphism_smul_normalizerPPrime r

/-- The explicit row matching is equivariant under every automorphism
stabilizing the chosen Sylow-five subgroup. -/
theorem specialLinearTwoFiveFiveCharacterRowEquiv_equivariant
    (a : SylowAutStabilizer specialLinearTwoFiveSylowFive)
    (r : SpecialLinearTwoFivePPrimeCharacterRow 5) :
    specialLinearTwoFiveFiveCharacterRowEquiv
        ((specialLinearTwoFivePPrimeCharacterEquiv 5).symm
          (a • specialLinearTwoFivePPrimeCharacterEquiv 5 r)) =
      specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv.symm
        (a •
          specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv
            (specialLinearTwoFiveFiveCharacterRowEquiv r)) := by
  obtain ⟨g, hinner | houter⟩ :=
    specialLinearTwoFive_sylowFiveStabilizer_eq_inner_or_outer_inner a
  · have hamb :
        a • specialLinearTwoFivePPrimeCharacterEquiv 5 r =
          specialLinearTwoFivePPrimeCharacterEquiv 5 r :=
      specialLinearTwoFive_sylowFiveInner_smul_ambient
        a g.1 hinner _
    have hnormalizer :
        a •
            specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv
              (specialLinearTwoFiveFiveCharacterRowEquiv r) =
          specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv
            (specialLinearTwoFiveFiveCharacterRowEquiv r) :=
      specialLinearTwoFive_sylowFiveInner_smul_normalizer
        a g hinner _
    rw [hamb, hnormalizer,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  · have hamb :
        a • specialLinearTwoFivePPrimeCharacterEquiv 5 r =
          specialLinearTwoFivePPrimeCharacterEquiv 5
            (specialLinearTwoFiveFiveOuterPPrimeRow r) :=
      specialLinearTwoFive_sylowFiveOuterInner_smul_ambient
        a g houter r
    have hnormalizer :
        a •
            specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv
              (specialLinearTwoFiveFiveCharacterRowEquiv r) =
          specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv
            (specialLinearTwoFiveFiveNormalizerOuterCharacterRow
              (specialLinearTwoFiveFiveCharacterRowEquiv r)) :=
      specialLinearTwoFive_sylowFiveOuterInner_smul_normalizer
        a g houter _
    rw [hamb, hnormalizer,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact specialLinearTwoFiveFiveCharacterRowEquiv_map_outer r

/-- The fully checked ordinary-character-table input at `p = 5`. -/
def specialLinearTwoFiveFiveCharacterTableCompletion :
    SpecialLinearTwoFiveFiveCharacterTableCompletion
      (SpecialLinearTwoFivePPrimeCharacterRow 5) where
  ambientEnumeration := specialLinearTwoFivePPrimeCharacterEquiv 5
  indexEquiv := specialLinearTwoFiveFiveCharacterRowEquiv
  indexEquivariance :=
    specialLinearTwoFiveFiveCharacterRowEquiv_equivariant

/-- The resulting explicit automorphism-equivariant McKay equivalence at
`p = 5`. -/
def specialLinearTwoFiveFiveEquivariantMcKayEquiv :
    EquivariantMcKayEquiv specialLinearTwoFiveSylowFive :=
  specialLinearTwoFiveFiveCharacterTableCompletion.toEquivariantMcKayEquiv

@[simp]
theorem specialLinearTwoFiveFiveEquivariantMcKayEquiv_apply
    (r : SpecialLinearTwoFivePPrimeCharacterRow 5) :
    specialLinearTwoFiveFiveEquivariantMcKayEquiv
        (specialLinearTwoFivePPrimeCharacterEquiv 5 r) =
      specialLinearTwoFiveFiveNormalizerPPrimeCharacterEquiv
        (specialLinearTwoFiveFiveCharacterRowEquiv r) :=
  specialLinearTwoFiveFiveCharacterTableCompletion
    |>.toEquivariantMcKayEquiv_apply_enumerated r

end InductiveMcKay
end McKayConjecture
