/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.FiniteFiberSum
import McKayConjecture.Character.NormalizedCharacterCertificate
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyClassSizes

/-!
# Ambient character norms from the 31 conjugacy classes of `6.A₆`

The checked coordinate model partitions all 2160 elements into thirty-one
conjugacy classes.  This module rewrites an ambient representation's
unnormalized character self-pairing as the corresponding class-size weighted
sum.  Generated row certificates therefore need to evaluate only the
thirty-one canonical representatives.
-/

noncomputable section

open scoped BigOperators
open CategoryTheory

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- A representation character on the universal cover takes at a coordinate
the same value as at the checked representative carrying its class label. -/
theorem alternatingSixAmbient_character_coordinate_eq_representative
    (V : FDRep ℂ AlternatingSixUniversalCover)
    (x : AlternatingSixSchurCoordinates) :
    V.character
        (alternatingSixSchurCoordinatesEquivUniversalCover x) =
      V.character
        (alternatingSixSchurCoordinatesEquivUniversalCover
          (alternatingSixSchurClassRepresentative
            (alternatingSixSchurClassIndex x))) := by
  let c := alternatingSixSchurClassConjugator x
  let r :=
    alternatingSixSchurClassRepresentative
      (alternatingSixSchurClassIndex x)
  have hcoordinate : c * r * c⁻¹ = x :=
    alternatingSixSchurClassConjugator_spec x
  have hgroup :
      alternatingSixSchurCoordinatesEquivUniversalCover c *
            alternatingSixSchurCoordinatesEquivUniversalCover r *
          (alternatingSixSchurCoordinatesEquivUniversalCover c)⁻¹ =
        alternatingSixSchurCoordinatesEquivUniversalCover x := by
    simpa only [map_mul, map_inv] using
      congrArg
        alternatingSixSchurCoordinatesEquivUniversalCover
        hcoordinate
  rw [← hgroup]
  exact
    ClassFunction.conj_apply
      (ClassFunction.ofFDRep V)
      (alternatingSixSchurCoordinatesEquivUniversalCover r)
      (alternatingSixSchurCoordinatesEquivUniversalCover c)

/-- The unnormalized character self-pairing of a canonical-cover
representation is the checked class-size weighted sum over the thirty-one
coordinate representatives. -/
theorem alternatingSixAmbient_characterSelfPairingSum_eq_classSum
    (V : FDRep ℂ AlternatingSixUniversalCover) :
    characterSelfPairingSum V =
      ∑ i : Fin 31,
        (alternatingSixSchurClassSize i : ℂ) *
          (V.character
              (alternatingSixSchurCoordinatesEquivUniversalCover
                (alternatingSixSchurClassRepresentative i)) *
            V.character
              (alternatingSixSchurCoordinatesEquivUniversalCover
                (alternatingSixSchurClassRepresentative i))⁻¹) := by
  letI : Fintype AlternatingSixUniversalCover :=
    Fintype.ofFinite _
  let pairing :
      AlternatingSixSchurCoordinates → ℂ :=
    fun x ↦
      V.character
          (alternatingSixSchurCoordinatesEquivUniversalCover x) *
        V.character
          (alternatingSixSchurCoordinatesEquivUniversalCover x)⁻¹
  have pairing_constant
      (x : AlternatingSixSchurCoordinates) :
      pairing x =
        pairing
          (alternatingSixSchurClassRepresentative
            (alternatingSixSchurClassIndex x)) := by
    let c := alternatingSixSchurClassConjugator x
    let r :=
      alternatingSixSchurClassRepresentative
        (alternatingSixSchurClassIndex x)
    have hcoordinate : c * r * c⁻¹ = x :=
      alternatingSixSchurClassConjugator_spec x
    have hgroup :
        alternatingSixSchurCoordinatesEquivUniversalCover c *
              alternatingSixSchurCoordinatesEquivUniversalCover r *
            (alternatingSixSchurCoordinatesEquivUniversalCover c)⁻¹ =
          alternatingSixSchurCoordinatesEquivUniversalCover x := by
      simpa only [map_mul, map_inv] using
        congrArg
          alternatingSixSchurCoordinatesEquivUniversalCover
          hcoordinate
    have hcharacter :
        V.character
            (alternatingSixSchurCoordinatesEquivUniversalCover x) =
          V.character
            (alternatingSixSchurCoordinatesEquivUniversalCover r) := by
      rw [← hgroup]
      exact
        ClassFunction.conj_apply
          (ClassFunction.ofFDRep V)
          (alternatingSixSchurCoordinatesEquivUniversalCover r)
          (alternatingSixSchurCoordinatesEquivUniversalCover c)
    have hcharacter_inv :
        V.character
            (alternatingSixSchurCoordinatesEquivUniversalCover x)⁻¹ =
          V.character
            (alternatingSixSchurCoordinatesEquivUniversalCover r)⁻¹ := by
      have hinverse :
          (alternatingSixSchurCoordinatesEquivUniversalCover x)⁻¹ =
            alternatingSixSchurCoordinatesEquivUniversalCover c *
                (alternatingSixSchurCoordinatesEquivUniversalCover r)⁻¹ *
              (alternatingSixSchurCoordinatesEquivUniversalCover c)⁻¹ := by
        rw [← hgroup]
        group
      rw [hinverse]
      exact
        ClassFunction.conj_apply
          (ClassFunction.ofFDRep V)
          (alternatingSixSchurCoordinatesEquivUniversalCover r)⁻¹
          (alternatingSixSchurCoordinatesEquivUniversalCover c)
    exact congrArg₂ (· * ·) hcharacter hcharacter_inv
  unfold characterSelfPairingSum
  calc
    (∑ g : AlternatingSixUniversalCover,
        V.character g * V.character g⁻¹) =
        ∑ x : AlternatingSixSchurCoordinates, pairing x := by
      exact
        (Equiv.sum_comp
          alternatingSixSchurCoordinatesEquivUniversalCover.toEquiv
          (fun g : AlternatingSixUniversalCover ↦
            V.character g * V.character g⁻¹)).symm
    _ =
        ∑ i : Fin 31,
          Fintype.card (AlternatingSixSchurClassFiber i) •
            pairing (alternatingSixSchurClassRepresentative i) :=
      sum_eq_sum_card_fiber_nsmul
        alternatingSixSchurClassIndex
        alternatingSixSchurClassRepresentative
        pairing pairing_constant
    _ =
        ∑ i : Fin 31,
          alternatingSixSchurClassSize i •
            pairing (alternatingSixSchurClassRepresentative i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [alternatingSixSchurClassFiber_card]
    _ = _ := by
      simp only [nsmul_eq_mul, pairing]

end InductiveMcKay
end McKayConjecture
