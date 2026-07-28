/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SemidirectProduct
import McKayConjecture.GroupTheory.AlternatingSixSchurThreeNormalizerGenerator
import McKayConjecture.GroupTheory.AlternatingSixUniversalCoverThreeCentralizer
import McKayConjecture.Proof.Isomorphism

/-!
# The Sylow-three normalizer in `6.A₆` as `3^{1+2} ⋊ C₈`

Let `P` be the explicit exponent-three Heisenberg Sylow subgroup in the
presented sixfold cover.  The order-eight element constructed in
`AlternatingSixSchurThreeNormalizerGenerator` normalizes `P`.  Its
cyclic subgroup has order eight, is disjoint from `P`, and their orders
multiply to the order of the full normalizer.  Consequently they are
complementary and multiplication gives an exact semidirect-product
model of the full order-216 normalizer.

Unlike a quotient-only description, this identifies an actual
complement and its action:

`t x t⁻¹ = z y`, `t y t⁻¹ = x²`, and `t z t⁻¹ = z`.

Thus the model contains enough concrete data to enumerate ordinary
characters by the little-groups method.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

local instance alternatingSixSchurThreeNormalizerFactPrime :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-! ### The explicit order-eight complement -/

/-- The explicit lifted element normalizes the Heisenberg Sylow
subgroup. -/
theorem alternatingSixSchurThreeNormalizerElement_mem_normalizer :
    alternatingSixSchurThreeNormalizerElement ∈
      Subgroup.normalizer
        (alternatingSixSchurSylowThreeSubgroup :
          Set AlternatingSixSchurPresentedGroup) := by
  apply Subgroup.mem_normalizer_fintype
  intro g hg
  obtain ⟨q, rfl⟩ := hg
  change
    MulAut.conj alternatingSixSchurThreeNormalizerElement
        (alternatingSixSchurSylowThreeParameterizedElement q) ∈
      alternatingSixSchurSylowThreeSubgroup
  rw [alternatingSixSchurSylowThreeParameterizedElement,
    map_mul, map_mul, map_pow, map_pow, map_pow]
  simp only [MulAut.conj_apply]
  rw [
    alternatingSixSchurThreeNormalizerElement_conj_Z,
    alternatingSixSchurThreeNormalizerElement_conj_X,
    alternatingSixSchurThreeNormalizerElement_conj_Y]
  apply alternatingSixSchurSylowThreeSubgroup.mul_mem
  · apply alternatingSixSchurSylowThreeSubgroup.mul_mem
    · exact
        alternatingSixSchurSylowThreeSubgroup.pow_mem
          alternatingSixSchurSylowThreeZElement.property q.z.val
    · exact
        alternatingSixSchurSylowThreeSubgroup.pow_mem
          (alternatingSixSchurSylowThreeSubgroup.mul_mem
            alternatingSixSchurSylowThreeZElement.property
            alternatingSixSchurSylowThreeYElement.property)
          q.x.val
  · exact
      alternatingSixSchurSylowThreeSubgroup.pow_mem
        (alternatingSixSchurSylowThreeSubgroup.pow_mem
          alternatingSixSchurSylowThreeXElement.property 2)
        q.y.val

/-- The lifted element, regarded as an element of the exact Schur-cover
normalizer. -/
def alternatingSixSchurThreeNormalizerElementInNormalizer :
    Subgroup.normalizer
      (alternatingSixSchurSylowThreeSubgroup :
        Set AlternatingSixSchurPresentedGroup) :=
  ⟨alternatingSixSchurThreeNormalizerElement,
    alternatingSixSchurThreeNormalizerElement_mem_normalizer⟩

/-- The cyclic complement coordinates. -/
abbrev AlternatingSixThreeCyclicEight :=
  Multiplicative (ZMod 8)

/-- Powers of the explicit lift give a homomorphism from `C₈` into the
presented Schur cover. -/
def alternatingSixThreeCyclicEightToSchur :
    AlternatingSixThreeCyclicEight →*
      AlternatingSixSchurPresentedGroup where
  toFun i :=
    QuaternionGroup.zmodPower
      alternatingSixSchurThreeNormalizerElement
      alternatingSixSchurThreeNormalizerElement_pow_eight
      (Multiplicative.toAdd i)
  map_one' :=
    QuaternionGroup.zmodPower_zero
      alternatingSixSchurThreeNormalizerElement
      alternatingSixSchurThreeNormalizerElement_pow_eight
  map_mul' i j :=
    QuaternionGroup.zmodPower_add
      alternatingSixSchurThreeNormalizerElement
      alternatingSixSchurThreeNormalizerElement_pow_eight
      (Multiplicative.toAdd i)
      (Multiplicative.toAdd j)

/-- The cyclic-eight power map is injective. -/
theorem alternatingSixThreeCyclicEightToSchur_injective :
    Function.Injective alternatingSixThreeCyclicEightToSchur := by
  intro i j hij
  apply Multiplicative.toAdd.injective
  apply
    QuaternionGroup.zmodPower_injective_of_orderOf_eq
      alternatingSixSchurThreeNormalizerElement
      alternatingSixSchurThreeNormalizerElement_pow_eight
      orderOf_alternatingSixSchurThreeNormalizerElement
  exact hij

/-- Every cyclic-eight power lies in the exact Sylow normalizer. -/
theorem alternatingSixThreeCyclicEightToSchur_mem_normalizer
    (i : AlternatingSixThreeCyclicEight) :
    alternatingSixThreeCyclicEightToSchur i ∈
      Subgroup.normalizer
        (alternatingSixSchurSylowThreeSubgroup :
          Set AlternatingSixSchurPresentedGroup) := by
  exact
    (Subgroup.zpowers_le.mpr
      alternatingSixSchurThreeNormalizerElement_mem_normalizer)
      (QuaternionGroup.zmodPower_mem_zpowers
        alternatingSixSchurThreeNormalizerElement
        alternatingSixSchurThreeNormalizerElement_pow_eight
        (Multiplicative.toAdd i))

/-- The cyclic-eight power map with codomain restricted to the exact
normalizer. -/
def alternatingSixThreeCyclicEightToSchurNormalizer :
    AlternatingSixThreeCyclicEight →*
      Subgroup.normalizer
        (alternatingSixSchurSylowThreeSubgroup :
          Set AlternatingSixSchurPresentedGroup) :=
  alternatingSixThreeCyclicEightToSchur.codRestrict
    (Subgroup.normalizer
      (alternatingSixSchurSylowThreeSubgroup :
        Set AlternatingSixSchurPresentedGroup))
    alternatingSixThreeCyclicEightToSchur_mem_normalizer

theorem alternatingSixThreeCyclicEightToSchurNormalizer_injective :
    Function.Injective
      alternatingSixThreeCyclicEightToSchurNormalizer := by
  intro i j hij
  apply alternatingSixThreeCyclicEightToSchur_injective
  exact congrArg Subtype.val hij

/-! ### Cardinalities and complementary subgroups -/

/-- The exact normalizer of the explicit Schur-cover Sylow subgroup. -/
abbrev AlternatingSixSchurThreeNormalizer :=
  Subgroup.normalizer
    (alternatingSixSchurSylowThreeSubgroup :
      Set AlternatingSixSchurPresentedGroup)

/-- The Heisenberg Sylow subgroup, viewed inside its exact normalizer. -/
abbrev AlternatingSixSchurThreeSylowInNormalizer :
    Subgroup AlternatingSixSchurThreeNormalizer :=
  alternatingSixSchurSylowThreeSubgroup.subgroupOf
    AlternatingSixSchurThreeNormalizer

/-- The explicit cyclic-eight subgroup inside the exact normalizer. -/
abbrev AlternatingSixSchurThreeCyclicEightInNormalizer :
    Subgroup AlternatingSixSchurThreeNormalizer :=
  alternatingSixThreeCyclicEightToSchurNormalizer.range

local instance alternatingSixSchurThreeSylowInNormalizerNormal :
    AlternatingSixSchurThreeSylowInNormalizer.Normal :=
  Subgroup.normal_in_normalizer

/-- The explicit Schur-cover Sylow-three normalizer has order 216. -/
@[simp]
theorem natCard_alternatingSixSchurThreeNormalizer :
    Nat.card AlternatingSixSchurThreeNormalizer = 216 := by
  let transported :
      Sylow 3 AlternatingSixUniversalCover :=
    McKayConjecture.Sylow.transport
      alternatingSixSchurEquivUniversalCover
      alternatingSixSchurSylowThree
  calc
    Nat.card AlternatingSixSchurThreeNormalizer =
        Nat.card
          (SylowNormalizer transported) :=
      Nat.card_congr
        (McKayConjecture.Sylow.normalizerEquiv
          alternatingSixSchurEquivUniversalCover
          alternatingSixSchurSylowThree).toEquiv
    _ = 216 :=
      natCard_normalizer_sylowThree_alternatingSixUniversalCover
        transported

/-- The internal Heisenberg factor has order 27. -/
@[simp]
theorem natCard_alternatingSixSchurThreeSylowInNormalizer :
    Nat.card AlternatingSixSchurThreeSylowInNormalizer = 27 := by
  calc
    Nat.card AlternatingSixSchurThreeSylowInNormalizer =
        Nat.card alternatingSixSchurSylowThreeSubgroup :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          alternatingSixSchurSylowThreeSubgroup.le_normalizer).toEquiv
    _ = 27 :=
      natCard_alternatingSixSchurSylowThreeSubgroup

/-- The displayed complement has order eight. -/
@[simp]
theorem natCard_alternatingSixSchurThreeCyclicEightInNormalizer :
    Nat.card AlternatingSixSchurThreeCyclicEightInNormalizer = 8 := by
  calc
    Nat.card AlternatingSixSchurThreeCyclicEightInNormalizer =
        Nat.card AlternatingSixThreeCyclicEight :=
      Nat.card_congr
        (MonoidHom.ofInjective
          alternatingSixThreeCyclicEightToSchurNormalizer_injective).symm.toEquiv
    _ = 8 := by
      rw [Nat.card_eq_fintype_card,
        Fintype.card_multiplicative, ZMod.card]

/-- The explicit Heisenberg and cyclic-eight subgroups are complementary
inside the exact normalizer. -/
theorem alternatingSixSchurThreeSylow_isComplement'_cyclicEight :
    AlternatingSixSchurThreeSylowInNormalizer.IsComplement'
      AlternatingSixSchurThreeCyclicEightInNormalizer := by
  apply Subgroup.isComplement'_of_coprime
  · rw [natCard_alternatingSixSchurThreeSylowInNormalizer,
      natCard_alternatingSixSchurThreeCyclicEightInNormalizer,
      natCard_alternatingSixSchurThreeNormalizer]
  · rw [natCard_alternatingSixSchurThreeSylowInNormalizer,
      natCard_alternatingSixSchurThreeCyclicEightInNormalizer]
    norm_num

/-! ### The exact semidirect-product equivalence -/

/-- The internal conjugation action of the cyclic-eight complement on
the internal Heisenberg subgroup. -/
abbrev alternatingSixSchurThreeInternalCyclicEightAction :
    AlternatingSixSchurThreeCyclicEightInNormalizer →*
      MulAut AlternatingSixSchurThreeSylowInNormalizer :=
  AlternatingSixSchurThreeSylowInNormalizer.normalizerMonoidHom.comp
    (Subgroup.inclusion
      (AlternatingSixSchurThreeSylowInNormalizer.normalizer_eq_top ▸
        le_top))

/-- The exact internal semidirect-product model. -/
abbrev AlternatingSixSchurThreeNormalizerSemidirect :=
  AlternatingSixSchurThreeSylowInNormalizer ⋊[
    alternatingSixSchurThreeInternalCyclicEightAction]
      AlternatingSixSchurThreeCyclicEightInNormalizer

/-- Multiplication identifies the explicit internal semidirect product
with the full order-216 Schur-cover normalizer. -/
def alternatingSixSchurThreeNormalizerSemidirectEquiv :
    AlternatingSixSchurThreeNormalizerSemidirect ≃*
      AlternatingSixSchurThreeNormalizer :=
  SemidirectProduct.mulEquivSubgroup
    alternatingSixSchurThreeSylow_isComplement'_cyclicEight

/-- The normal factor in the model is the explicit exponent-three
Heisenberg group. -/
def alternatingSixSchurThreeInternalSylowEquiv :
    AlternatingSixSchurThreeSylowInNormalizer ≃*
      alternatingSixSchurSylowThreeSubgroup :=
  Subgroup.subgroupOfEquivOfLe
    alternatingSixSchurSylowThreeSubgroup.le_normalizer

/-- The acting factor in the model is concretely cyclic of order eight. -/
def alternatingSixSchurThreeInternalCyclicEightEquiv :
    AlternatingSixSchurThreeCyclicEightInNormalizer ≃*
      AlternatingSixThreeCyclicEight :=
  (MonoidHom.ofInjective
    alternatingSixThreeCyclicEightToSchurNormalizer_injective).symm

/-! ### A semidirect product on the concrete factor types -/

/-- The `C₈` action directly on the explicit Heisenberg subgroup. -/
def alternatingSixSchurThreeCyclicEightAction :
    AlternatingSixThreeCyclicEight →*
      MulAut alternatingSixSchurSylowThreeSubgroup :=
  alternatingSixSchurSylowThreeSubgroup.normalizerMonoidHom.comp
    alternatingSixThreeCyclicEightToSchurNormalizer

/-- The concrete-factor semidirect product `3^{1+2} ⋊ C₈`. -/
abbrev AlternatingSixThreeHeisenbergCyclicEightSemidirect :=
  alternatingSixSchurSylowThreeSubgroup ⋊[
    alternatingSixSchurThreeCyclicEightAction]
      AlternatingSixThreeCyclicEight

@[simp]
theorem alternatingSixSchurThreeCyclicEightAction_generator_Z :
    alternatingSixSchurThreeCyclicEightAction
        (Multiplicative.ofAdd 1)
        alternatingSixSchurSylowThreeZElement =
      alternatingSixSchurSylowThreeZElement := by
  apply Subtype.ext
  change
    QuaternionGroup.zmodPower
          alternatingSixSchurThreeNormalizerElement
          alternatingSixSchurThreeNormalizerElement_pow_eight
          ((1 : ℕ) : ZMod 8) *
        alternatingSixSchurSylowThreeZ *
      (QuaternionGroup.zmodPower
        alternatingSixSchurThreeNormalizerElement
        alternatingSixSchurThreeNormalizerElement_pow_eight
        ((1 : ℕ) : ZMod 8))⁻¹ =
      alternatingSixSchurSylowThreeZ
  rw [QuaternionGroup.zmodPower_natCast]
  exact alternatingSixSchurThreeNormalizerElement_conj_Z

@[simp]
theorem alternatingSixSchurThreeCyclicEightAction_generator_X :
    alternatingSixSchurThreeCyclicEightAction
        (Multiplicative.ofAdd 1)
        alternatingSixSchurSylowThreeXElement =
      alternatingSixSchurSylowThreeZElement *
        alternatingSixSchurSylowThreeYElement := by
  apply Subtype.ext
  change
    QuaternionGroup.zmodPower
          alternatingSixSchurThreeNormalizerElement
          alternatingSixSchurThreeNormalizerElement_pow_eight
          ((1 : ℕ) : ZMod 8) *
        alternatingSixSchurSylowThreeX *
      (QuaternionGroup.zmodPower
        alternatingSixSchurThreeNormalizerElement
        alternatingSixSchurThreeNormalizerElement_pow_eight
        ((1 : ℕ) : ZMod 8))⁻¹ =
      alternatingSixSchurSylowThreeZ *
        alternatingSixSchurSylowThreeY
  rw [QuaternionGroup.zmodPower_natCast]
  exact alternatingSixSchurThreeNormalizerElement_conj_X

@[simp]
theorem alternatingSixSchurThreeCyclicEightAction_generator_Y :
    alternatingSixSchurThreeCyclicEightAction
        (Multiplicative.ofAdd 1)
        alternatingSixSchurSylowThreeYElement =
      alternatingSixSchurSylowThreeXElement ^ 2 := by
  apply Subtype.ext
  change
    QuaternionGroup.zmodPower
          alternatingSixSchurThreeNormalizerElement
          alternatingSixSchurThreeNormalizerElement_pow_eight
          ((1 : ℕ) : ZMod 8) *
        alternatingSixSchurSylowThreeY *
      (QuaternionGroup.zmodPower
        alternatingSixSchurThreeNormalizerElement
        alternatingSixSchurThreeNormalizerElement_pow_eight
        ((1 : ℕ) : ZMod 8))⁻¹ =
      alternatingSixSchurSylowThreeX ^ 2
  rw [QuaternionGroup.zmodPower_natCast]
  exact alternatingSixSchurThreeNormalizerElement_conj_Y

/-- Transporting both factor types identifies the concrete-factor and
internal semidirect products. -/
def alternatingSixThreeHeisenbergCyclicEightEquivInternalSemidirect :
    AlternatingSixThreeHeisenbergCyclicEightSemidirect ≃*
      AlternatingSixSchurThreeNormalizerSemidirect :=
  SemidirectProduct.congr
    alternatingSixSchurThreeInternalSylowEquiv.symm
    alternatingSixSchurThreeInternalCyclicEightEquiv.symm
    (by
      intro i
      ext p
      rfl)

/-- The concrete-factor semidirect product is the exact Schur-cover
normalizer. -/
def alternatingSixThreeHeisenbergCyclicEightEquivSchurNormalizer :
    AlternatingSixThreeHeisenbergCyclicEightSemidirect ≃*
      AlternatingSixSchurThreeNormalizer :=
  alternatingSixThreeHeisenbergCyclicEightEquivInternalSemidirect.trans
    alternatingSixSchurThreeNormalizerSemidirectEquiv

@[simp]
theorem natCard_alternatingSixThreeHeisenbergCyclicEightSemidirect :
    Nat.card AlternatingSixThreeHeisenbergCyclicEightSemidirect = 216 := by
  calc
    Nat.card AlternatingSixThreeHeisenbergCyclicEightSemidirect =
        Nat.card AlternatingSixSchurThreeNormalizer :=
      Nat.card_congr
        alternatingSixThreeHeisenbergCyclicEightEquivSchurNormalizer.toEquiv
    _ = 216 :=
      natCard_alternatingSixSchurThreeNormalizer

end GroupTheory
end McKayConjecture
