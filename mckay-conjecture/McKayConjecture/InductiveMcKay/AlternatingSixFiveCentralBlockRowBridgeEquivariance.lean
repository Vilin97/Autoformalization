/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientPPrimeCharacterEnumeration
import McKayConjecture.InductiveMcKay.AlternatingSixFiveCentralCharacterMatching
import McKayConjecture.InductiveMcKay.AlternatingSixFiveConcreteFiniteTable

/-!
# Genuine stabilizer actions on the five-local row matching

A completed ambient ordinary table and the proved concrete normalizer table
transport the genuine Sylow-stabilizer actions to the two finite row types.
This file defines those transported actions and isolates the exact
equivariance proposition still required of the central-block-compatible row
matching.

The matching already preserves the exact complex central scalar.  That fact
does not by itself imply equivariance under the full stabilizer, so the
remaining obligation is kept as an explicit proposition.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixFiveCentralBlockBridgeFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- Before any automorphism calculation, the explicit matching already
identifies the scalar advertised by the ambient character at the canonical
central generator with the scalar computed in the concrete local model. -/
theorem alternatingSixFiveCentralBlockRowMatching_ambientCentralValue
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (r : AlternatingSixAmbientPPrimeRowIndex 5) :
    (alternatingSixAmbientPPrimeCharacterEquiv T 5 r).1.values
        alternatingSixAmbientCanonicalCentralGenerator =
      ((alternatingSixAmbientPPrimeCharacterEquiv T 5 r).1.degree : ℂ) *
        AlternatingSixFiveNormalizerSemidirectCharacterTable.centralScalar
          (alternatingSixAmbientFivePPrimeCentralBlockRowEquiv r) := by
  rw [
    alternatingSixAmbientPPrimeCharacterEquiv_values_centralGenerator,
    alternatingSixAmbientFivePPrimeCentralBlockRowEquiv_preserves_centralScalar
  ]

/-- The genuine Sylow-five stabilizer action transported to the arithmetic
ambient prime-to-five row subtype. -/
def alternatingSixFiveAmbientRowStabilizerAction
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 5))
    (r : AlternatingSixAmbientPPrimeRowIndex 5) :
    AlternatingSixAmbientPPrimeRowIndex 5 :=
  (alternatingSixAmbientPPrimeCharacterEquiv T 5).symm
    (a • alternatingSixAmbientPPrimeCharacterEquiv T 5 r)

@[simp]
theorem alternatingSixFiveAmbientRowStabilizerAction_character
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 5))
    (r : AlternatingSixAmbientPPrimeRowIndex 5) :
    alternatingSixAmbientPPrimeCharacterEquiv T 5
        (alternatingSixFiveAmbientRowStabilizerAction T a r) =
      a • alternatingSixAmbientPPrimeCharacterEquiv T 5 r :=
  (alternatingSixAmbientPPrimeCharacterEquiv T 5).apply_symm_apply _

@[simp]
theorem alternatingSixFiveAmbientRowStabilizerAction_one
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (r : AlternatingSixAmbientPPrimeRowIndex 5) :
    alternatingSixFiveAmbientRowStabilizerAction T 1 r = r := by
  apply (alternatingSixAmbientPPrimeCharacterEquiv T 5).injective
  simp

theorem alternatingSixFiveAmbientRowStabilizerAction_mul
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (a b :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 5))
    (r : AlternatingSixAmbientPPrimeRowIndex 5) :
    alternatingSixFiveAmbientRowStabilizerAction T (a * b) r =
      alternatingSixFiveAmbientRowStabilizerAction T a
        (alternatingSixFiveAmbientRowStabilizerAction T b r) := by
  apply (alternatingSixAmbientPPrimeCharacterEquiv T 5).injective
  simp [mul_smul]

/-- The genuine Sylow-five stabilizer action transported to the concrete
normalizer row type through the proved local character enumeration. -/
def alternatingSixFiveLocalRowStabilizerAction
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 5))
    (r : AlternatingSixFiveConcreteNormalizerRow) :
    AlternatingSixFiveConcreteNormalizerRow :=
  alternatingSixFiveActualNormalizerPPrimeCharacterEquiv.symm
    (a • alternatingSixFiveActualNormalizerPPrimeCharacterEquiv r)

@[simp]
theorem alternatingSixFiveLocalRowStabilizerAction_character
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 5))
    (r : AlternatingSixFiveConcreteNormalizerRow) :
    alternatingSixFiveActualNormalizerPPrimeCharacterEquiv
        (alternatingSixFiveLocalRowStabilizerAction a r) =
      a • alternatingSixFiveActualNormalizerPPrimeCharacterEquiv r :=
  alternatingSixFiveActualNormalizerPPrimeCharacterEquiv.apply_symm_apply _

@[simp]
theorem alternatingSixFiveLocalRowStabilizerAction_one
    (r : AlternatingSixFiveConcreteNormalizerRow) :
    alternatingSixFiveLocalRowStabilizerAction 1 r = r := by
  apply alternatingSixFiveActualNormalizerPPrimeCharacterEquiv.injective
  simp

theorem alternatingSixFiveLocalRowStabilizerAction_mul
    (a b :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 5))
    (r : AlternatingSixFiveConcreteNormalizerRow) :
    alternatingSixFiveLocalRowStabilizerAction (a * b) r =
      alternatingSixFiveLocalRowStabilizerAction a
        (alternatingSixFiveLocalRowStabilizerAction b r) := by
  apply alternatingSixFiveActualNormalizerPPrimeCharacterEquiv.injective
  simp [mul_smul]

/-- The exact full-stabilizer equivariance obligation for the explicit
central-block-compatible row matching.  The name denotes a proposition,
not a theorem established by the finite row order alone. -/
def AlternatingSixFiveCentralBlockRowMatchingEquivariant
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) : Prop :=
  ∀ (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 5))
    (r : AlternatingSixAmbientPPrimeRowIndex 5),
    alternatingSixAmbientFivePPrimeCentralBlockRowEquiv
        (alternatingSixFiveAmbientRowStabilizerAction T a r) =
      alternatingSixFiveLocalRowStabilizerAction a
        (alternatingSixAmbientFivePPrimeCentralBlockRowEquiv r)

/-- Package a completed ambient table and a proof of the exact transported
equivariance obligation into the concrete five-local finite-table
interface.  Projective factor-set compatibility remains separate. -/
def alternatingSixFiveCentralBlockConcreteCharacterTableCertificate
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (h : AlternatingSixFiveCentralBlockRowMatchingEquivariant T) :
    AlternatingSixFiveConcreteCharacterTableCertificate
      (AlternatingSixAmbientPPrimeRowIndex 5) where
  ambientEnumeration :=
    alternatingSixAmbientPPrimeCharacterEquiv T 5
  indexEquiv :=
    alternatingSixAmbientFivePPrimeCentralBlockRowEquiv
  indexEquivariance := by
    intro a r
    exact h a r

@[simp]
theorem
    alternatingSixFiveCentralBlockConcreteCharacterTableCertificate_ambientEnumeration
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (h : AlternatingSixFiveCentralBlockRowMatchingEquivariant T) :
    (alternatingSixFiveCentralBlockConcreteCharacterTableCertificate T h
        |>.ambientEnumeration) =
      alternatingSixAmbientPPrimeCharacterEquiv T 5 :=
  rfl

@[simp]
theorem
    alternatingSixFiveCentralBlockConcreteCharacterTableCertificate_indexEquiv
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (h : AlternatingSixFiveCentralBlockRowMatchingEquivariant T) :
    (alternatingSixFiveCentralBlockConcreteCharacterTableCertificate T h
        |>.indexEquiv) =
      alternatingSixAmbientFivePPrimeCentralBlockRowEquiv :=
  rfl

end InductiveMcKay
end McKayConjecture
