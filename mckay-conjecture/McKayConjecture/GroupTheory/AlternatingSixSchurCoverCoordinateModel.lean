/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverEnumeration
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverThreeCycleLifts
import McKayConjecture.GroupTheory.QuaternionGroupHom

/-!
# Computable coordinates for the sixfold cover of `A₆`

The checked rewrite table has 360 noncentral states.  Its accumulated
central weight reduces to an exponent modulo six.  This file uses those two
coordinates to give the Schur cover a finite, computable group model.

The multiplication and inverse operations are evaluated by the checked
weighted rewrite table.  Their compatibility with the abstract presented
group is proved before the group laws are transferred back by injectivity.
This keeps later exhaustive conjugacy-class certificates independent of
quotient-group reduction.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- A normal-word state and an exponent of the central generator `k₀`. -/
@[ext]
structure AlternatingSixSchurCoordinates where
  state : Fin 360
  central : ZMod 6
deriving DecidableEq, Fintype

namespace AlternatingSixSchurCoordinates

/-- The integer exponent of `k₀` represented by a four-component rewrite
weight, reduced modulo six. -/
def weightExponent (weight : Fin 4 → ℤ) : ZMod 6 :=
  (weight 0 + 3 * weight 1 - weight 2 + weight 3 : ℤ)

@[simp]
theorem weightExponent_zero :
    weightExponent (fun _ ↦ 0) = 0 := by
  simp [weightExponent]

/-- The central element represented by an exponent modulo six. -/
def centralValue (n : ZMod 6) :
    AlternatingSixSchurPresentedGroup :=
  QuaternionGroup.zmodPower
    (alternatingSixSchurPresentedK 0)
    alternatingSixSchurPresentedK0_pow_six n

@[simp]
theorem centralValue_zero :
    centralValue 0 = 1 :=
  QuaternionGroup.zmodPower_zero _ _

@[simp]
theorem centralValue_add (m n : ZMod 6) :
    centralValue (m + n) =
      centralValue m * centralValue n :=
  QuaternionGroup.zmodPower_add _ _ m n

@[simp]
theorem centralValue_neg (n : ZMod 6) :
    centralValue (-n) = (centralValue n)⁻¹ :=
  QuaternionGroup.zmodPower_neg _ _ n

/-- The four-component central rewrite weight and its reduced exponent
represent the same element of the cover. -/
theorem schurWeight_eq_centralValue
    (weight : Fin 4 → ℤ) :
    alternatingSixSchurWeight weight =
      centralValue (weightExponent weight) := by
  rw [alternatingSixSchurWeight_eq_k0_zpow]
  symm
  exact
    QuaternionGroup.zmodPower_intCast
      (alternatingSixSchurPresentedK 0)
      alternatingSixSchurPresentedK0_pow_six
      (weight 0 + 3 * weight 1 - weight 2 + weight 3)

/-- Every reduced central value commutes with every element of the cover. -/
theorem centralValue_commute
    (n : ZMod 6) (g : AlternatingSixSchurPresentedGroup) :
    Commute (centralValue n) g := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective n
  rw [centralValue,
    QuaternionGroup.zmodPower_intCast]
  exact
    (Subgroup.mem_center_iff.mp
      ((Subgroup.center AlternatingSixSchurPresentedGroup).zpow_mem
        (alternatingSixSchurPresentedK_mem_center 0) z) g).symm

/-- The rewrite trace used to multiply two noncentral normal words. -/
def productTrace (left right : Fin 360) :
    AlternatingSixSchurWordTrace :=
  alternatingSixSchurTraceFrom
    { state := left, weight := fun _ ↦ 0 }
    (alternatingSixRewriteNormalWords right)

/-- The rewrite trace used to invert one noncentral normal word. -/
def inverseTrace (state : Fin 360) :
    AlternatingSixSchurWordTrace :=
  alternatingSixSchurTrace
    (alternatingSixRewriteInverseWord
      (alternatingSixRewriteNormalWords state))

instance : One AlternatingSixSchurCoordinates :=
  ⟨⟨0, 0⟩⟩

instance : Mul AlternatingSixSchurCoordinates where
  mul left right :=
    let trace := productTrace left.state right.state
    {
      state := trace.state
      central :=
        left.central + weightExponent trace.weight + right.central
    }

instance : Inv AlternatingSixSchurCoordinates where
  inv coordinate :=
    let trace := inverseTrace coordinate.state
    {
      state := trace.state
      central := weightExponent trace.weight - coordinate.central
    }

/-- Evaluation of the computable coordinates in the abstract presentation. -/
def evaluate (coordinate : AlternatingSixSchurCoordinates) :
    AlternatingSixSchurPresentedGroup :=
  alternatingSixSchurNormalElement coordinate.state *
    centralValue coordinate.central

/-- The coordinate carrier is canonically the previously proved
`Fin 360 × Fin 6` enumeration. -/
def structureEquiv :
    AlternatingSixSchurCoordinates ≃ (Fin 360 × ZMod 6) where
  toFun coordinate := (coordinate.state, coordinate.central)
  invFun coordinate :=
    { state := coordinate.1, central := coordinate.2 }
  left_inv coordinate := by cases coordinate; rfl
  right_inv coordinate := by cases coordinate; rfl

/-- Replace the central `ZMod 6` coordinate by its canonical `Fin 6`
representative. -/
def indexEquiv :
    AlternatingSixSchurCoordinates ≃ (Fin 360 × Fin 6) :=
  structureEquiv.trans
    (Equiv.prodCongr
      (Equiv.refl (Fin 360))
      (ZMod.finEquiv 6).symm)

@[simp]
theorem indexEquiv_apply_state
    (coordinate : AlternatingSixSchurCoordinates) :
    (indexEquiv coordinate).1 = coordinate.state :=
  rfl

@[simp]
theorem indexEquiv_apply_central
    (coordinate : AlternatingSixSchurCoordinates) :
    (indexEquiv coordinate).2.val = coordinate.central.val :=
  rfl

/-- Evaluation agrees with the exact normal-representative enumeration. -/
theorem evaluate_eq_normalRepresentative
    (coordinate : AlternatingSixSchurCoordinates) :
    evaluate coordinate =
      alternatingSixSchurNormalRepresentative
        (indexEquiv coordinate) := by
  rw [evaluate, alternatingSixSchurNormalRepresentative,
    indexEquiv_apply_state]
  congr 1

/-- Evaluation is a bijection before any group laws are placed on the
coordinate carrier. -/
theorem evaluate_bijective :
    Function.Bijective evaluate := by
  rw [show evaluate =
      alternatingSixSchurNormalRepresentative ∘ indexEquiv by
    funext coordinate
    exact evaluate_eq_normalRepresentative coordinate]
  exact
    alternatingSixSchurNormalRepresentative_bijective.comp
      indexEquiv.bijective

/-- The checked trace computes multiplication of two noncentral normal
words, including its central cocycle. -/
theorem normalElement_mul_normalElement
    (left right : Fin 360) :
    alternatingSixSchurNormalElement left *
        alternatingSixSchurNormalElement right =
      alternatingSixSchurNormalElement
          (productTrace left right).state *
        centralValue
          (weightExponent (productTrace left right).weight) := by
  have h :=
    alternatingSixSchurTraceFrom_sound
      ({ state := left, weight := fun _ ↦ 0 } :
        AlternatingSixSchurWordTrace)
      (alternatingSixRewriteNormalWords right)
  simpa [productTrace, alternatingSixSchurNormalElement,
    schurWeight_eq_centralValue] using h

/-- Coordinate multiplication is exactly multiplication in the presented
cover. -/
@[simp]
theorem evaluate_mul
    (left right : AlternatingSixSchurCoordinates) :
    evaluate (left * right) =
      evaluate left * evaluate right := by
  let trace := productTrace left.state right.state
  have htrace :
      alternatingSixSchurNormalElement left.state *
          alternatingSixSchurNormalElement right.state =
        alternatingSixSchurNormalElement trace.state *
          centralValue (weightExponent trace.weight) :=
    normalElement_mul_normalElement left.state right.state
  change
    alternatingSixSchurNormalElement trace.state *
        centralValue
          (left.central + weightExponent trace.weight + right.central) =
      (alternatingSixSchurNormalElement left.state *
          centralValue left.central) *
        (alternatingSixSchurNormalElement right.state *
          centralValue right.central)
  rw [centralValue_add, centralValue_add]
  calc
    alternatingSixSchurNormalElement trace.state *
          ((centralValue left.central *
              centralValue (weightExponent trace.weight)) *
            centralValue right.central) =
        alternatingSixSchurNormalElement trace.state *
          ((centralValue
              (weightExponent trace.weight) *
            centralValue left.central) *
            centralValue right.central) := by
              rw [(centralValue_commute left.central
                (centralValue
                  (weightExponent trace.weight))).eq]
    _ =
        (alternatingSixSchurNormalElement trace.state *
            centralValue (weightExponent trace.weight)) *
          (centralValue left.central *
            centralValue right.central) := by
              simp only [mul_assoc]
    _ =
        (alternatingSixSchurNormalElement left.state *
            alternatingSixSchurNormalElement right.state) *
          (centralValue left.central *
            centralValue right.central) := by
              rw [htrace]
    _ =
        (alternatingSixSchurNormalElement left.state *
            centralValue left.central) *
          (alternatingSixSchurNormalElement right.state *
            centralValue right.central) := by
              calc
                (alternatingSixSchurNormalElement left.state *
                      alternatingSixSchurNormalElement right.state) *
                    (centralValue left.central *
                      centralValue right.central) =
                    alternatingSixSchurNormalElement left.state *
                      (alternatingSixSchurNormalElement right.state *
                        centralValue left.central) *
                      centralValue right.central := by
                        simp only [mul_assoc]
                _ =
                    alternatingSixSchurNormalElement left.state *
                      (centralValue left.central *
                        alternatingSixSchurNormalElement right.state) *
                      centralValue right.central := by
                        rw [(centralValue_commute left.central
                          (alternatingSixSchurNormalElement
                            right.state)).eq]
                _ =
                    (alternatingSixSchurNormalElement left.state *
                        centralValue left.central) *
                      (alternatingSixSchurNormalElement right.state *
                        centralValue right.central) := by
                          simp only [mul_assoc]

/-- The inverse trace computes the inverse of a noncentral normal word. -/
theorem normalElement_inverse
    (state : Fin 360) :
    alternatingSixSchurNormalElement
          (inverseTrace state).state *
        centralValue
          (weightExponent (inverseTrace state).weight) =
      (alternatingSixSchurNormalElement state)⁻¹ := by
  have h :=
    alternatingSixSchurTrace_sound
      (alternatingSixRewriteInverseWord
        (alternatingSixRewriteNormalWords state))
  rw [alternatingSixSchurWord_inverse] at h
  simpa [inverseTrace, alternatingSixSchurNormalElement,
    schurWeight_eq_centralValue] using h.symm

/-- Coordinate inversion is exactly inversion in the presented cover. -/
@[simp]
theorem evaluate_inv
    (coordinate : AlternatingSixSchurCoordinates) :
    evaluate coordinate⁻¹ =
      (evaluate coordinate)⁻¹ := by
  let trace := inverseTrace coordinate.state
  have htrace :
      alternatingSixSchurNormalElement trace.state *
          centralValue (weightExponent trace.weight) =
        (alternatingSixSchurNormalElement coordinate.state)⁻¹ :=
    normalElement_inverse coordinate.state
  change
    alternatingSixSchurNormalElement trace.state *
        centralValue
          (weightExponent trace.weight - coordinate.central) =
      (alternatingSixSchurNormalElement coordinate.state *
        centralValue coordinate.central)⁻¹
  rw [sub_eq_add_neg, centralValue_add, centralValue_neg,
    mul_inv_rev]
  rw [← htrace]
  calc
    alternatingSixSchurNormalElement trace.state *
          (centralValue (weightExponent trace.weight) *
            (centralValue coordinate.central)⁻¹) =
        (alternatingSixSchurNormalElement trace.state *
            centralValue (weightExponent trace.weight)) *
          centralValue (-coordinate.central) := by
            rw [centralValue_neg]
            simp only [mul_assoc]
    _ =
        centralValue (-coordinate.central) *
          (alternatingSixSchurNormalElement trace.state *
            centralValue (weightExponent trace.weight)) := by
              exact
                (centralValue_commute (-coordinate.central)
                  (alternatingSixSchurNormalElement trace.state *
                    centralValue
                      (weightExponent trace.weight))).eq.symm
    _ =
        (centralValue coordinate.central)⁻¹ *
          (alternatingSixSchurNormalElement trace.state *
            centralValue (weightExponent trace.weight)) := by
              rw [centralValue_neg]

@[simp]
theorem evaluate_one :
    evaluate (1 : AlternatingSixSchurCoordinates) = 1 := by
  change
    alternatingSixSchurNormalElement 0 * centralValue 0 = 1
  rw [centralValue_zero]
  rfl

/-- The computable operations form a group because their evaluation in the
abstract cover is injective and preserves all three primitive operations. -/
instance : Group AlternatingSixSchurCoordinates where
  mul_assoc left middle right :=
    evaluate_bijective.injective (by
      simp only [evaluate_mul, mul_assoc])
  one_mul coordinate :=
    evaluate_bijective.injective (by
      simp only [evaluate_mul, evaluate_one, one_mul])
  mul_one coordinate :=
    evaluate_bijective.injective (by
      simp only [evaluate_mul, evaluate_one, mul_one])
  inv_mul_cancel coordinate :=
    evaluate_bijective.injective (by
      simp only [evaluate_mul, evaluate_inv, evaluate_one,
        inv_mul_cancel])

/-- Evaluation as a group homomorphism. -/
def evaluateHom :
    AlternatingSixSchurCoordinates →*
      AlternatingSixSchurPresentedGroup where
  toFun := evaluate
  map_one' := evaluate_one
  map_mul' := evaluate_mul

/-- The computable coordinate model is isomorphic to the Schur-cover
presentation. -/
def mulEquivPresentedGroup :
    AlternatingSixSchurCoordinates ≃*
      AlternatingSixSchurPresentedGroup :=
  MulEquiv.ofBijective evaluateHom evaluate_bijective

@[simp]
theorem mulEquivPresentedGroup_apply
    (coordinate : AlternatingSixSchurCoordinates) :
    mulEquivPresentedGroup coordinate =
      evaluate coordinate :=
  rfl

end AlternatingSixSchurCoordinates
end GroupTheory
end McKayConjecture
