/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixUniversalCoverTwoNormalizerProduct
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# A direct-product model of the Sylow-two normalizer in `6.A₆`

The exact normalizer calculation gives

`N(P) = P ⊔ Z(6.A₆)`,

where `P` is generalized quaternion of order sixteen and the ambient center
is cyclic of order six.  Their intersection is the order-two center of `P`.
Consequently the order-two part of the ambient center is already contained
in `P`; adjoining only the central Sylow-three subgroup gives the whole
normalizer.

This file makes that observation precise.  It constructs the central
order-three complement inside the fixed normalizer and proves the concrete
group isomorphism

`Multiplicative (ZMod 3) × QuaternionGroup 4 ≃* N(P)`.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

local instance alternatingSixTwoNormalizerModelFactPrimeTwo :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

local instance alternatingSixTwoNormalizerModelFactPrimeThree :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-- The concrete order-forty-eight model of the fixed two-normalizer. -/
abbrev AlternatingSixTwoNormalizerModel :=
  Multiplicative (ZMod 3) × QuaternionGroup 4

/-- A fixed Sylow-three subgroup of the cyclic order-six ambient center. -/
def alternatingSixUniversalCoverCentralSylowThree :
    Sylow 3 (Subgroup.center AlternatingSixUniversalCover) :=
  Classical.choice Sylow.nonempty

/-- Inclusion of the central Sylow-three subgroup into the ambient cover. -/
def alternatingSixUniversalCoverCentralThreeHom :
    alternatingSixUniversalCoverCentralSylowThree →*
      AlternatingSixUniversalCover :=
  (Subgroup.center AlternatingSixUniversalCover).subtype.comp
    (alternatingSixUniversalCoverCentralSylowThree :
      Subgroup (Subgroup.center AlternatingSixUniversalCover)).subtype

/-- The central order-three subgroup, regarded as an ambient subgroup. -/
def alternatingSixUniversalCoverCentralThree :
    Subgroup AlternatingSixUniversalCover :=
  alternatingSixUniversalCoverCentralThreeHom.range

theorem alternatingSixUniversalCoverCentralThreeHom_injective :
    Function.Injective alternatingSixUniversalCoverCentralThreeHom :=
  Subtype.val_injective.comp Subtype.val_injective

/-- The chosen central Sylow-three subgroup has order three. -/
@[simp]
theorem natCard_alternatingSixUniversalCoverCentralSylowThree :
    Nat.card alternatingSixUniversalCoverCentralSylowThree = 3 := by
  have hfactor : Nat.factorization 6 3 = 1 := by
    conv_lhs =>
      rw [show 6 = 2 * 3 by norm_num]
    rw [Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.prime_two.factorization,
      Nat.prime_three.factorization]
    norm_num [Finsupp.single_apply]
  rw [Sylow.card_eq_multiplicity,
    alternatingSixHopfKernelHasOrderSix.center, hfactor]
  norm_num

/-- The ambient image of the chosen central Sylow-three subgroup has order
three. -/
@[simp]
theorem natCard_alternatingSixUniversalCoverCentralThree :
    Nat.card alternatingSixUniversalCoverCentralThree = 3 := by
  calc
    Nat.card alternatingSixUniversalCoverCentralThree =
        Nat.card alternatingSixUniversalCoverCentralSylowThree :=
      (Nat.card_congr
        (MonoidHom.ofInjective
          alternatingSixUniversalCoverCentralThreeHom_injective).toEquiv).symm
    _ = 3 :=
      natCard_alternatingSixUniversalCoverCentralSylowThree

/-- The chosen order-three subgroup is central in the ambient cover. -/
theorem alternatingSixUniversalCoverCentralThree_le_center :
    alternatingSixUniversalCoverCentralThree ≤
      Subgroup.center AlternatingSixUniversalCover := by
  rintro x ⟨y, rfl⟩
  exact y.1.2

private abbrev fixedSylowTwo :
    Subgroup AlternatingSixUniversalCover :=
  alternatingSixUniversalCoverSylow 2

private abbrev fixedSylowTwoNormalizer :
    Subgroup AlternatingSixUniversalCover :=
  Subgroup.normalizer
    (alternatingSixUniversalCoverSylow 2 :
      Set AlternatingSixUniversalCover)

/-- The fixed Sylow-two subgroup, regarded as a subgroup of its exact
normalizer. -/
def alternatingSixUniversalCoverSylowTwoInNormalizer :
    Subgroup fixedSylowTwoNormalizer :=
  fixedSylowTwo.subgroupOf fixedSylowTwoNormalizer

/-- The central order-three complement, regarded as a subgroup of the exact
normalizer. -/
def alternatingSixUniversalCoverCentralThreeInTwoNormalizer :
    Subgroup fixedSylowTwoNormalizer :=
  alternatingSixUniversalCoverCentralThree.subgroupOf
    fixedSylowTwoNormalizer

private theorem alternatingSixUniversalCoverCentralThree_le_twoNormalizer :
    alternatingSixUniversalCoverCentralThree ≤
      fixedSylowTwoNormalizer :=
  alternatingSixUniversalCoverCentralThree_le_center.trans
    (Subgroup.center_le_normalizer
      (alternatingSixUniversalCoverSylow 2 :
        Set AlternatingSixUniversalCover))

/-- The Sylow-two factor inside its normalizer has order sixteen. -/
@[simp]
theorem natCard_alternatingSixUniversalCoverSylowTwoInNormalizer :
    Nat.card alternatingSixUniversalCoverSylowTwoInNormalizer = 16 := by
  calc
    Nat.card alternatingSixUniversalCoverSylowTwoInNormalizer =
        Nat.card fixedSylowTwo :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          fixedSylowTwo.le_normalizer).toEquiv
    _ = 16 :=
      natCard_alternatingSixUniversalCoverSylowTwo_exact

/-- The central complement inside the normalizer has order three. -/
@[simp]
theorem natCard_alternatingSixUniversalCoverCentralThreeInTwoNormalizer :
    Nat.card alternatingSixUniversalCoverCentralThreeInTwoNormalizer = 3 := by
  calc
    Nat.card alternatingSixUniversalCoverCentralThreeInTwoNormalizer =
        Nat.card alternatingSixUniversalCoverCentralThree :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          alternatingSixUniversalCoverCentralThree_le_twoNormalizer).toEquiv
    _ = 3 :=
      natCard_alternatingSixUniversalCoverCentralThree

/-- The Sylow-two factor and central order-three factor are complementary
inside the exact normalizer. -/
theorem alternatingSixUniversalCoverTwoNormalizer_isComplement :
    alternatingSixUniversalCoverSylowTwoInNormalizer.IsComplement'
      alternatingSixUniversalCoverCentralThreeInTwoNormalizer := by
  apply Subgroup.isComplement'_of_coprime
  · rw [
      natCard_alternatingSixUniversalCoverSylowTwoInNormalizer,
      natCard_alternatingSixUniversalCoverCentralThreeInTwoNormalizer,
      natCard_normalizer_alternatingSixUniversalCoverSylowTwo]
  · rw [
      natCard_alternatingSixUniversalCoverSylowTwoInNormalizer,
      natCard_alternatingSixUniversalCoverCentralThreeInTwoNormalizer]
    norm_num

/-- Multiplication of the quaternion and central factors inside the fixed
normalizer. -/
def alternatingSixUniversalCoverTwoNormalizerProductHom :
    alternatingSixUniversalCoverSylowTwoInNormalizer ×
        alternatingSixUniversalCoverCentralThreeInTwoNormalizer →*
      fixedSylowTwoNormalizer where
  toFun x := x.1 * x.2
  map_one' := by simp
  map_mul' a b := by
    let ap : AlternatingSixUniversalCover := a.1
    let ak : AlternatingSixUniversalCover := a.2
    let bp : AlternatingSixUniversalCover := b.1
    let bk : AlternatingSixUniversalCover := b.2
    have hcentral :
        ak ∈ Subgroup.center AlternatingSixUniversalCover :=
      alternatingSixUniversalCoverCentralThree_le_center a.2.2
    have hcommAmbient :
        Commute ak bp :=
      (Subgroup.mem_center_iff.mp hcentral _).symm
    apply Subtype.ext
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    change ap * bp * (ak * bk) = ap * ak * (bp * bk)
    calc
      ap * bp * (ak * bk) = ap * (bp * ak) * bk := by group
      _ = ap * (ak * bp) * bk := by rw [← hcommAmbient.eq]
      _ = ap * ak * (bp * bk) := by group

/-- The two internal factors multiply uniquely to every element of the exact
normalizer. -/
theorem alternatingSixUniversalCoverTwoNormalizerProductHom_bijective :
    Function.Bijective
      alternatingSixUniversalCoverTwoNormalizerProductHom := by
  change
    Function.Bijective
      (fun x :
          alternatingSixUniversalCoverSylowTwoInNormalizer ×
            alternatingSixUniversalCoverCentralThreeInTwoNormalizer =>
        (x.1 : fixedSylowTwoNormalizer) *
          (x.2 : fixedSylowTwoNormalizer))
  exact alternatingSixUniversalCoverTwoNormalizer_isComplement

/-- Internal direct-product decomposition of the exact normalizer. -/
def alternatingSixUniversalCoverTwoNormalizerInternalProductEquiv :
    alternatingSixUniversalCoverSylowTwoInNormalizer ×
        alternatingSixUniversalCoverCentralThreeInTwoNormalizer ≃*
      fixedSylowTwoNormalizer :=
  MulEquiv.ofBijective
    alternatingSixUniversalCoverTwoNormalizerProductHom
    alternatingSixUniversalCoverTwoNormalizerProductHom_bijective

/-- Identify the central complement with the standard cyclic group of order
three. -/
def cyclicThreeEquivAlternatingSixUniversalCoverCentralThreeInTwoNormalizer :
    Multiplicative (ZMod 3) ≃*
      alternatingSixUniversalCoverCentralThreeInTwoNormalizer :=
  mulEquivOfPrimeCardEq (by simp)
    natCard_alternatingSixUniversalCoverCentralThreeInTwoNormalizer

/-- Identify the standard generalized quaternion group of order sixteen with
the Sylow-two factor inside its normalizer. -/
def quaternionFourEquivAlternatingSixUniversalCoverSylowTwoInNormalizer :
    QuaternionGroup 4 ≃*
      alternatingSixUniversalCoverSylowTwoInNormalizer :=
  (alternatingSixUniversalCoverSylowTwoEquivQuaternionFour
      (alternatingSixUniversalCoverSylow 2)).symm.trans
    (Subgroup.subgroupOfEquivOfLe fixedSylowTwo.le_normalizer).symm

/-- The concrete direct-product model is isomorphic to the exact normalizer
of the fixed Sylow-two subgroup. -/
def alternatingSixTwoNormalizerModelEquivUniversalCoverNormalizer :
    AlternatingSixTwoNormalizerModel ≃*
      fixedSylowTwoNormalizer :=
  (MulEquiv.prodCongr
      cyclicThreeEquivAlternatingSixUniversalCoverCentralThreeInTwoNormalizer
      quaternionFourEquivAlternatingSixUniversalCoverSylowTwoInNormalizer).trans
    ((MulEquiv.prodComm :
        alternatingSixUniversalCoverCentralThreeInTwoNormalizer ×
            alternatingSixUniversalCoverSylowTwoInNormalizer ≃*
          alternatingSixUniversalCoverSylowTwoInNormalizer ×
            alternatingSixUniversalCoverCentralThreeInTwoNormalizer).trans
      alternatingSixUniversalCoverTwoNormalizerInternalProductEquiv)

/-- The concrete two-normalizer model has order forty-eight. -/
@[simp]
theorem natCard_alternatingSixTwoNormalizerModel :
    Nat.card AlternatingSixTwoNormalizerModel = 48 := by
  calc
    Nat.card AlternatingSixTwoNormalizerModel =
        Nat.card fixedSylowTwoNormalizer :=
      Nat.card_congr
        alternatingSixTwoNormalizerModelEquivUniversalCoverNormalizer.toEquiv
    _ = 48 :=
      natCard_normalizer_alternatingSixUniversalCoverSylowTwo

end GroupTheory
end McKayConjecture
