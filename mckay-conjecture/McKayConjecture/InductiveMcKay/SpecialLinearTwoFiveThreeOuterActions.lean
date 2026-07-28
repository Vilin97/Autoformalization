/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InnerAutomorphism
import McKayConjecture.GroupTheory.SpecialLinearTwoFiveAutomorphisms
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveCharacterTable
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveThreeNormalizerTable
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveThreeRowEquiv

/-!
# The outer action on the two `3'`-character tables of `SL(2, 𝔽₅)`

The fixed outer automorphism interchanges the two faithful ambient rows.
On the generalized quaternion normalizer it inverts the order-four
generator, hence interchanges the two odd linear rows.  All four remaining
rows on each side are fixed.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance factPrimeThreeForOuterActions :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-- The transposition of the two golden-root indices. -/
def binaryIcosahedralSwapGoldenIndex : Fin 2 → Fin 2 :=
  Fin.cases 1 (fun _ : Fin 1 => 0)

@[simp]
theorem binaryIcosahedralSwapGoldenIndex_zero :
    binaryIcosahedralSwapGoldenIndex 0 = 1 :=
  rfl

@[simp]
theorem binaryIcosahedralSwapGoldenIndex_one :
    binaryIcosahedralSwapGoldenIndex 1 = 0 :=
  rfl

/-- Row permutation induced by the non-inner automorphism. -/
def specialLinearTwoFiveOuterCharacterRow :
    SpecialLinearTwoFiveCharacterRow →
      SpecialLinearTwoFiveCharacterRow
  | .trivial => .trivial
  | .faithful k =>
      .faithful (binaryIcosahedralSwapGoldenIndex k)
  | .symmetricSquare k =>
      .symmetricSquare (binaryIcosahedralSwapGoldenIndex k)
  | .symmetricCube => .symmetricCube
  | .tensor => .tensor
  | .symmetricFourthPower => .symmetricFourthPower
  | .symmetricFifthPower => .symmetricFifthPower

@[simp]
theorem specialLinearTwoFiveOuterCharacterRow_degree
    (r : SpecialLinearTwoFiveCharacterRow) :
    specialLinearTwoFiveCharacterRowDegree
        (specialLinearTwoFiveOuterCharacterRow r) =
      specialLinearTwoFiveCharacterRowDegree r := by
  rcases r with _ | k | k | _ | _ | _ | _ <;> rfl

/-- The induced permutation of the nine conjugacy classes. -/
def specialLinearTwoFiveOuterConjugacyClass :
    SpecialLinearTwoFiveConjugacyClass →
      SpecialLinearTwoFiveConjugacyClass
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 6
  | 6 => 5
  | 7 => 8
  | 8 => 7

/-- The explicit outer automorphism has the displayed class permutation. -/
theorem specialLinearTwoFiveOuterAutomorphism_representative_isConj
    (c : SpecialLinearTwoFiveConjugacyClass) :
    IsConj
      (specialLinearTwoFiveSylowThreeOuterAutomorphism.symm
        (specialLinearTwoFiveConjugacyRepresentative c))
      (specialLinearTwoFiveConjugacyRepresentative
        (specialLinearTwoFiveOuterConjugacyClass c)) := by
  apply
    (specialLinearTwoFiveAreConjugate_iff_isConj _ _).1
  fin_cases c <;> native_decide

/-- The symbolic table transforms by the outer row and class
permutations. -/
theorem specialLinearTwoFiveCharacterTableValue_outer
    (r : SpecialLinearTwoFiveCharacterRow)
    (c : SpecialLinearTwoFiveConjugacyClass) :
    specialLinearTwoFiveCharacterTableValue
        binaryIcosahedralGoldenRootPlus
        (specialLinearTwoFiveOuterCharacterRow r) c =
      specialLinearTwoFiveCharacterTableValue
        binaryIcosahedralGoldenRootPlus r
        (specialLinearTwoFiveOuterConjugacyClass c) := by
  have ht2 :
      binaryIcosahedralGoldenRootPlus ^ 2 =
        binaryIcosahedralGoldenRootPlus + 1 :=
    binaryIcosahedralGoldenRootPlus_sq
  have ht3 :
      binaryIcosahedralGoldenRootPlus ^ 3 =
        2 * binaryIcosahedralGoldenRootPlus + 1 := by
    linear_combination
      (binaryIcosahedralGoldenRootPlus + 1) * ht2
  have ht4 :
      binaryIcosahedralGoldenRootPlus ^ 4 =
        3 * binaryIcosahedralGoldenRootPlus + 2 := by
    linear_combination
      (binaryIcosahedralGoldenRootPlus ^ 2 +
        binaryIcosahedralGoldenRootPlus + 2) * ht2
  have ht5 :
      binaryIcosahedralGoldenRootPlus ^ 5 =
        5 * binaryIcosahedralGoldenRootPlus + 3 := by
    linear_combination
      (binaryIcosahedralGoldenRootPlus ^ 3 +
        binaryIcosahedralGoldenRootPlus ^ 2 +
          2 * binaryIcosahedralGoldenRootPlus + 3) * ht2
  rcases r with _ | k | k | _ | _ | _ | _
  · fin_cases c <;>
      rfl
  · fin_cases k <;> fin_cases c <;>
      simp [specialLinearTwoFiveCharacterTableValue,
        specialLinearTwoFiveOuterCharacterRow,
        specialLinearTwoFiveOuterConjugacyClass,
        binaryIcosahedralDefiningTrace,
        binaryIcosahedralGoldenRootChoice]
  · fin_cases k <;> fin_cases c <;>
      simp [specialLinearTwoFiveCharacterTableValue,
        specialLinearTwoFiveOuterCharacterRow,
        specialLinearTwoFiveOuterConjugacyClass,
        binaryIcosahedralSymmetricSquareValue,
        binaryIcosahedralDefiningTrace,
        binaryIcosahedralGoldenRootChoice]
  · fin_cases c <;>
      simp [specialLinearTwoFiveCharacterTableValue,
        specialLinearTwoFiveOuterCharacterRow,
        specialLinearTwoFiveOuterConjugacyClass,
        binaryIcosahedralSymmetricCubeValue,
        binaryIcosahedralDefiningTrace] <;>
      ring
    all_goals
      simp only [ht3, ht2]
      ring
  · fin_cases c <;>
      simp [specialLinearTwoFiveCharacterTableValue,
        specialLinearTwoFiveOuterCharacterRow,
        specialLinearTwoFiveOuterConjugacyClass,
        binaryIcosahedralDefiningTrace] <;>
      ring
  · fin_cases c <;>
      simp [specialLinearTwoFiveCharacterTableValue,
        specialLinearTwoFiveOuterCharacterRow,
        specialLinearTwoFiveOuterConjugacyClass,
        binaryIcosahedralSymmetricFourthPowerValue,
        binaryIcosahedralDefiningTrace] <;>
      ring
    all_goals
      simp only [ht4, ht3, ht2]
      ring
  · fin_cases c <;>
      simp [specialLinearTwoFiveCharacterTableValue,
        specialLinearTwoFiveOuterCharacterRow,
        specialLinearTwoFiveOuterConjugacyClass,
        binaryIcosahedralSymmetricFifthPowerValue,
        binaryIcosahedralDefiningTrace] <;>
      ring
    all_goals
      simp only [ht5, ht4, ht3, ht2]
      ring

/-- The non-inner automorphism acts on the realized ordinary table by the
explicit row permutation. -/
theorem specialLinearTwoFiveOuterAutomorphism_smul_irreducibleCharacter
    (r : SpecialLinearTwoFiveCharacterRow) :
    specialLinearTwoFiveSylowThreeOuterAutomorphism •
        specialLinearTwoFiveIrreducibleCharacter r =
      specialLinearTwoFiveIrreducibleCharacter
        (specialLinearTwoFiveOuterCharacterRow r) := by
  apply IrreducibleCharacter.ext
  funext g
  obtain ⟨c, hgc, _⟩ :=
    specialLinearTwoFive_existsUnique_conjugacyClass g
  have hsymm :
      IsConj
        (specialLinearTwoFiveSylowThreeOuterAutomorphism.symm g)
        (specialLinearTwoFiveConjugacyRepresentative
          (specialLinearTwoFiveOuterConjugacyClass c)) :=
    (specialLinearTwoFiveSylowThreeOuterAutomorphism.symm.toMonoidHom
      |>.map_isConj hgc).trans
        (specialLinearTwoFiveOuterAutomorphism_representative_isConj c)
  rw [IrreducibleCharacter.smul_values]
  calc
    (specialLinearTwoFiveIrreducibleCharacter r).values
          (specialLinearTwoFiveSylowThreeOuterAutomorphism.symm g) =
        (specialLinearTwoFiveIrreducibleCharacter r).values
          (specialLinearTwoFiveConjugacyRepresentative
            (specialLinearTwoFiveOuterConjugacyClass c)) :=
      IrreducibleCharacter.values_eq_of_isConj _ hsymm
    _ =
        specialLinearTwoFiveCharacterTableValue
          binaryIcosahedralGoldenRootPlus r
          (specialLinearTwoFiveOuterConjugacyClass c) :=
      specialLinearTwoFiveIrreducibleCharacter_values_representative _ _
    _ =
        specialLinearTwoFiveCharacterTableValue
          binaryIcosahedralGoldenRootPlus
          (specialLinearTwoFiveOuterCharacterRow r) c :=
      (specialLinearTwoFiveCharacterTableValue_outer r c).symm
    _ =
        (specialLinearTwoFiveIrreducibleCharacter
          (specialLinearTwoFiveOuterCharacterRow r)).values
            (specialLinearTwoFiveConjugacyRepresentative c) :=
      (specialLinearTwoFiveIrreducibleCharacter_values_representative _ _).symm
    _ =
        (specialLinearTwoFiveIrreducibleCharacter
          (specialLinearTwoFiveOuterCharacterRow r)).values g :=
      (IrreducibleCharacter.values_eq_of_isConj _ hgc).symm

/-- The outer row permutation preserves the `3'`-degree subtype. -/
def specialLinearTwoFiveThreeOuterPPrimeRow
    (r : SpecialLinearTwoFivePPrimeCharacterRow 3) :
    SpecialLinearTwoFivePPrimeCharacterRow 3 :=
  ⟨specialLinearTwoFiveOuterCharacterRow r.1, by
    rw [specialLinearTwoFiveOuterCharacterRow_degree]
    exact r.2⟩

@[simp]
theorem specialLinearTwoFiveOuterAutomorphism_smul_pPrimeCharacter
    (r : SpecialLinearTwoFivePPrimeCharacterRow 3) :
    specialLinearTwoFiveSylowThreeOuterAutomorphism •
        specialLinearTwoFivePPrimeCharacterEquiv 3 r =
      specialLinearTwoFivePPrimeCharacterEquiv 3
        (specialLinearTwoFiveThreeOuterPPrimeRow r) := by
  apply Subtype.ext
  exact
    specialLinearTwoFiveOuterAutomorphism_smul_irreducibleCharacter r.1

/-! ## The same outer action on the exact normalizer -/

/-- The row permutation induced on the generalized quaternion
normalizer. -/
def quaternionGroupThreeOuterCharacterRow :
    QuaternionGroupThreeCharacterRow →
      QuaternionGroupThreeCharacterRow
  | .linear j => .linear (-j)
  | .twoDimensional k => .twoDimensional k

/-- The chosen outer automorphism, as an element of the stabilizer of the
chosen Sylow-three subgroup. -/
def specialLinearTwoFiveSylowThreeOuterStabilizer :
    SylowAutStabilizer specialLinearTwoFiveSylowThree :=
  ⟨specialLinearTwoFiveSylowThreeOuterAutomorphism, by
    apply Sylow.ext
    change
      (specialLinearTwoFiveSylowThree :
          Subgroup SpecialLinearTwoFive).map
          specialLinearTwoFiveSylowThreeOuterAutomorphism =
        (specialLinearTwoFiveSylowThree :
          Subgroup SpecialLinearTwoFive)
    change
      (Subgroup.zpowers
        specialLinearTwoFive_orderThreeElement).map
          specialLinearTwoFiveSylowThreeOuterAutomorphism =
        Subgroup.zpowers
          specialLinearTwoFive_orderThreeElement
    rw [MonoidHom.map_zpowers]
    congr 1
    exact
      specialLinearTwoFiveSylowThreeOuterAutomorphism_orderThree⟩

@[simp]
theorem
    specialLinearTwoFiveSylowThreeOuterRestriction_symm_a
    (i : ZMod 6) :
    (SylowAutStabilizer.normalizerRestrictionHom
        specialLinearTwoFiveSylowThree
        specialLinearTwoFiveSylowThreeOuterStabilizer).symm
        (quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer
          (QuaternionGroup.a i)) =
      quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer
        (QuaternionGroup.a i) := by
  rw [
    quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer_apply_a]
  apply
    (SylowAutStabilizer.normalizerRestrictionHom
      specialLinearTwoFiveSylowThree
      specialLinearTwoFiveSylowThreeOuterStabilizer).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [SylowAutStabilizer.normalizerRestrictionHom_apply_coe]
  change
    (↑(specialLinearTwoFiveSylowThreeNormalizerA ^ i.val) :
        SpecialLinearTwoFive) =
      specialLinearTwoFiveSylowThreeOuterAutomorphism
        (↑(specialLinearTwoFiveSylowThreeNormalizerA ^ i.val) :
          SpecialLinearTwoFive)
  symm
  have hcoe :
      (↑(specialLinearTwoFiveSylowThreeNormalizerA ^ i.val) :
          SpecialLinearTwoFive) =
        specialLinearTwoFiveSylowThreeNormalizerA.1 ^ i.val :=
    rfl
  rw [hcoe, map_pow,
    specialLinearTwoFiveSylowThreeOuterAutomorphism_normalizerA]

@[simp]
theorem
    specialLinearTwoFiveSylowThreeOuterRestriction_symm_xa
    (i : ZMod 6) :
    (SylowAutStabilizer.normalizerRestrictionHom
        specialLinearTwoFiveSylowThree
        specialLinearTwoFiveSylowThreeOuterStabilizer).symm
        (quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer
          (QuaternionGroup.xa i)) =
      quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer
        (QuaternionGroup.xa (i + 3)) := by
  rw [
    quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer_apply_xa]
  apply
    (SylowAutStabilizer.normalizerRestrictionHom
      specialLinearTwoFiveSylowThree
      specialLinearTwoFiveSylowThreeOuterStabilizer).injective
  rw [MulEquiv.apply_symm_apply,
    quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer_apply_xa]
  apply Subtype.ext
  rw [SylowAutStabilizer.normalizerRestrictionHom_apply_coe]
  change
    (↑(specialLinearTwoFiveSylowThreeNormalizerX *
        specialLinearTwoFiveSylowThreeNormalizerA ^ i.val) :
      SpecialLinearTwoFive) =
      specialLinearTwoFiveSylowThreeOuterAutomorphism
        (↑(specialLinearTwoFiveSylowThreeNormalizerX *
            specialLinearTwoFiveSylowThreeNormalizerA ^ (i + 3).val) :
          SpecialLinearTwoFive)
  have hcoe (n : ℕ) :
      (↑(specialLinearTwoFiveSylowThreeNormalizerX *
          specialLinearTwoFiveSylowThreeNormalizerA ^ n) :
        SpecialLinearTwoFive) =
        specialLinearTwoFiveSylowThreeNormalizerX.1 *
          specialLinearTwoFiveSylowThreeNormalizerA.1 ^ n :=
    rfl
  rw [hcoe, hcoe, map_mul,
    specialLinearTwoFiveSylowThreeOuterAutomorphism_normalizerX,
    map_pow,
    specialLinearTwoFiveSylowThreeOuterAutomorphism_normalizerA]
  fin_cases i <;> native_decide

theorem quaternionGroupThreeOuterLinear_a_exponent :
    ∀ (j : ZMod 4) (i : ZMod 6),
      j * (2 * (i.val : ZMod 4)) =
        (-j) * (2 * (i.val : ZMod 4)) := by
  native_decide

theorem quaternionGroupThreeOuterLinear_xa_exponent :
    ∀ (j : ZMod 4) (i : ZMod 6),
      j * (1 + 2 * ((i + 3).val : ZMod 4)) =
        (-j) * (1 + 2 * (i.val : ZMod 4)) := by
  native_decide

/-- Values on the cyclic normalizer subgroup transform by negating the
linear-row index. -/
theorem quaternionGroupThreeOuterCharacterRow_values_a
    (r : QuaternionGroupThreeCharacterRow)
    (i : ZMod 6) :
    (quaternionGroupThreePPrimeCharacterEquiv r).1.values
        (QuaternionGroup.a i) =
      (quaternionGroupThreePPrimeCharacterEquiv
        (quaternionGroupThreeOuterCharacterRow r)).1.values
          (QuaternionGroup.a i) := by
  rcases r with j | k
  · change
      (quaternionGroupThreeLinearPPrimeCharacter j).1.values
          (QuaternionGroup.a i) =
        (quaternionGroupThreeLinearPPrimeCharacter (-j)).1.values
          (QuaternionGroup.a i)
    rw [quaternionGroupThreeLinearPPrimeCharacter_values_a,
      quaternionGroupThreeLinearPPrimeCharacter_values_a]
    exact congrArg
      (fun z : ZMod 4 => (ZMod.toCircle z : ℂ))
      (quaternionGroupThreeOuterLinear_a_exponent j i)
  · rfl

/-- On the noncyclic coset, inversion of the order-four generator shifts
the quaternion normal form by three. -/
theorem quaternionGroupThreeOuterCharacterRow_values_xa
    (r : QuaternionGroupThreeCharacterRow)
    (i : ZMod 6) :
    (quaternionGroupThreePPrimeCharacterEquiv r).1.values
        (QuaternionGroup.xa (i + 3)) =
      (quaternionGroupThreePPrimeCharacterEquiv
        (quaternionGroupThreeOuterCharacterRow r)).1.values
          (QuaternionGroup.xa i) := by
  rcases r with j | k
  · change
      (quaternionGroupThreeLinearPPrimeCharacter j).1.values
          (QuaternionGroup.xa (i + 3)) =
        (quaternionGroupThreeLinearPPrimeCharacter (-j)).1.values
          (QuaternionGroup.xa i)
    rw [quaternionGroupThreeLinearPPrimeCharacter_values_xa,
      quaternionGroupThreeLinearPPrimeCharacter_values_xa]
    exact congrArg
      (fun z : ZMod 4 => (ZMod.toCircle z : ℂ))
      (quaternionGroupThreeOuterLinear_xa_exponent j i)
  · change
      (quaternionGroupThreeTwoPPrimeCharacter k).1.values
          (QuaternionGroup.xa (i + 3)) =
        (quaternionGroupThreeTwoPPrimeCharacter k).1.values
          (QuaternionGroup.xa i)
    simp only [quaternionGroupThreeTwoPPrimeCharacter,
      quaternionGroupThreeTwoIrreducibleCharacter_values_xa]

/-- The restricted outer automorphism acts on the exact-normalizer table
by the displayed row permutation. -/
theorem
    specialLinearTwoFiveSylowThreeOuterStabilizer_smul_normalizerCharacter
    (r : QuaternionGroupThreeCharacterRow) :
    specialLinearTwoFiveSylowThreeOuterStabilizer •
        specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv r =
      specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv
        (quaternionGroupThreeOuterCharacterRow r) := by
  apply Subtype.ext
  apply IrreducibleCharacter.ext
  funext x
  obtain ⟨q, rfl⟩ :=
    quaternionGroupThreeEquivSpecialLinearTwoFiveSylowThreeNormalizer.surjective
      x
  rw [SylowAutStabilizer.smul_normalizer_pPrime_values]
  rcases q with i | i
  · rw [specialLinearTwoFiveSylowThreeOuterRestriction_symm_a,
      specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv_values,
      specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv_values]
    exact quaternionGroupThreeOuterCharacterRow_values_a r i
  · rw [specialLinearTwoFiveSylowThreeOuterRestriction_symm_xa,
      specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv_values,
      specialLinearTwoFiveThreeNormalizerPPrimeCharacterEquiv_values]
    exact quaternionGroupThreeOuterCharacterRow_values_xa r i

/-- The explicit ambient-to-normalizer row matching intertwines the two
outer permutations. -/
theorem specialLinearTwoFiveThreeCharacterRowEquiv_map_outer
    (r : SpecialLinearTwoFivePPrimeCharacterRow 3) :
    specialLinearTwoFiveThreeCharacterRowEquiv
        (specialLinearTwoFiveThreeOuterPPrimeRow r) =
      quaternionGroupThreeOuterCharacterRow
        (specialLinearTwoFiveThreeCharacterRowEquiv r) := by
  rcases r with ⟨r, hr⟩
  rcases r with _ | k | k | _ | _ | _ | _
  · rfl
  · fin_cases k <;> rfl
  · exfalso
    apply hr
    simp [specialLinearTwoFiveCharacterRowDegree]
  · rfl
  · rfl
  · rfl
  · exfalso
    apply hr
    simp [specialLinearTwoFiveCharacterRowDegree]

end InductiveMcKay
end McKayConjecture
