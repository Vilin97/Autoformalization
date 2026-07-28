/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixThreeDisplayedRowBridge
import McKayConjecture.InductiveMcKay.AlternatingSixThreeConcreteFiniteTable

/-!
# Genuine stabilizer actions on the displayed three-local row sets

Once an ambient ordinary character table is supplied, its table-induced
prime-to-three enumeration transports the genuine Sylow-stabilizer action
from ambient characters to the arithmetic ambient row subtype.  The proved
actual-normalizer enumeration similarly transports the genuine action on
local characters to the concrete local row type.

The two transported actions are defined and their action laws are proved
here.  Equivariance of the display-order bridge between them is isolated as
the remaining proposition `AlternatingSixThreeDisplayedOrderEquivariant`.
No proof of that proposition follows merely from the two row orders.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixThreeDisplayedRowBridgeFactPrime :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-- The actual Sylow-stabilizer transported to arithmetic ambient row
indices through a completed ambient character table. -/
def alternatingSixThreeAmbientRowStabilizerAction
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 3))
    (r : AlternatingSixAmbientPPrimeRowIndex 3) :
    AlternatingSixAmbientPPrimeRowIndex 3 :=
  (alternatingSixAmbientPPrimeCharacterEquiv T 3).symm
    (a • alternatingSixAmbientPPrimeCharacterEquiv T 3 r)

@[simp]
theorem alternatingSixThreeAmbientRowStabilizerAction_character
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 3))
    (r : AlternatingSixAmbientPPrimeRowIndex 3) :
    alternatingSixAmbientPPrimeCharacterEquiv T 3
        (alternatingSixThreeAmbientRowStabilizerAction T a r) =
      a • alternatingSixAmbientPPrimeCharacterEquiv T 3 r :=
  (alternatingSixAmbientPPrimeCharacterEquiv T 3).apply_symm_apply _

@[simp]
theorem alternatingSixThreeAmbientRowStabilizerAction_one
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (r : AlternatingSixAmbientPPrimeRowIndex 3) :
    alternatingSixThreeAmbientRowStabilizerAction T 1 r = r := by
  apply (alternatingSixAmbientPPrimeCharacterEquiv T 3).injective
  simp

theorem alternatingSixThreeAmbientRowStabilizerAction_mul
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (a b :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 3))
    (r : AlternatingSixAmbientPPrimeRowIndex 3) :
    alternatingSixThreeAmbientRowStabilizerAction T (a * b) r =
      alternatingSixThreeAmbientRowStabilizerAction T a
        (alternatingSixThreeAmbientRowStabilizerAction T b r) := by
  apply (alternatingSixAmbientPPrimeCharacterEquiv T 3).injective
  simp [mul_smul]

/-- The actual Sylow-stabilizer transported to concrete local row indices
through the proved actual-normalizer character enumeration. -/
def alternatingSixThreeLocalRowStabilizerAction
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 3))
    (r : AlternatingSixThreeConcreteNormalizerRow) :
    AlternatingSixThreeConcreteNormalizerRow :=
  AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv.symm
    (a •
      AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv
        r)

@[simp]
theorem alternatingSixThreeLocalRowStabilizerAction_character
    (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 3))
    (r : AlternatingSixThreeConcreteNormalizerRow) :
    AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv
        (alternatingSixThreeLocalRowStabilizerAction a r) =
      a •
        AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv
          r :=
  AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv.apply_symm_apply
    _

@[simp]
theorem alternatingSixThreeLocalRowStabilizerAction_one
    (r : AlternatingSixThreeConcreteNormalizerRow) :
    alternatingSixThreeLocalRowStabilizerAction 1 r = r := by
  apply
    AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv.injective
  simp

theorem alternatingSixThreeLocalRowStabilizerAction_mul
    (a b :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 3))
    (r : AlternatingSixThreeConcreteNormalizerRow) :
    alternatingSixThreeLocalRowStabilizerAction (a * b) r =
      alternatingSixThreeLocalRowStabilizerAction a
        (alternatingSixThreeLocalRowStabilizerAction b r) := by
  apply
    AlternatingSixThreeNormalizer.actualNormalizerPPrimeIrreducibleCharacterEquiv.injective
  simp [mul_smul]

/-- The precise genuine equivariance obligation for the explicit
display-order bridge.  This is deliberately a proposition, not an asserted
theorem: the current row-order data do not prove it. -/
def AlternatingSixThreeDisplayedOrderEquivariant
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate) : Prop :=
  ∀ (a :
      SylowAutStabilizer
        (alternatingSixUniversalCoverSylow 3))
    (r : AlternatingSixAmbientPPrimeRowIndex 3),
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv
        (alternatingSixThreeAmbientRowStabilizerAction T a r) =
      alternatingSixThreeLocalRowStabilizerAction a
        (alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv r)

/-- Package the completed ambient table and a proof of the exact transported
equivariance obligation into the existing concrete finite-table interface.

No degree-preservation or projective/factor compatibility is asserted. -/
def alternatingSixThreeDisplayedOrderConcreteCharacterTableCertificate
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (h : AlternatingSixThreeDisplayedOrderEquivariant T) :
    AlternatingSixThreeConcreteCharacterTableCertificate
      (AlternatingSixAmbientPPrimeRowIndex 3) where
  ambientEnumeration :=
    alternatingSixAmbientPPrimeCharacterEquiv T 3
  indexEquiv :=
    alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv
  indexEquivariance := by
    intro a r
    exact h a r

@[simp]
theorem alternatingSixThreeDisplayedOrderConcreteCharacterTableCertificate_ambientEnumeration
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (h : AlternatingSixThreeDisplayedOrderEquivariant T) :
    (alternatingSixThreeDisplayedOrderConcreteCharacterTableCertificate T h).ambientEnumeration =
      alternatingSixAmbientPPrimeCharacterEquiv T 3 :=
  rfl

@[simp]
theorem alternatingSixThreeDisplayedOrderConcreteCharacterTableCertificate_indexEquiv
    (T : AlternatingSixAmbientOrdinaryCharacterTableCertificate)
    (h : AlternatingSixThreeDisplayedOrderEquivariant T) :
    (alternatingSixThreeDisplayedOrderConcreteCharacterTableCertificate T h).indexEquiv =
      alternatingSixThreeDisplayedOrderAmbientLocalRowEquiv :=
  rfl

end InductiveMcKay
end McKayConjecture
