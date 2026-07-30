/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixAutomorphismStabilizerGeneration
import McKayConjecture.InductiveMcKay.AlternatingSixAmbientCompletedOrdinaryCharacterTable
import McKayConjecture.InductiveMcKay.AlternatingSixThreeCTblLibParameterizedFullEquivariance

/-!
# Ordering-safe CTblLib equivariance for `A₆`

The parameterized CTblLib APIs keep the semantic identification of display
positions with actual character rows explicit.  Their full-equivariance
theorems previously also required a Sylow-automorphism stabilizer generation
hypothesis.

That generation statement is now unconditional for `p = 2, 3, 5`.  The
wrappers in this file discharge it without changing the ordering-safe API:
the only remaining semantic proof input is the bundled set of four
generator-action bridges for the supplied row identification.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

/-! ### The prime `2` -/

namespace AlternatingSixTwoCTblLibRowIdentification

variable
  (identification : AlternatingSixTwoCTblLibRowIdentification)

/-- The bundled four semantic generator bridges imply full two-local
equivariance; stabilizer generation is unconditional. -/
theorem equivariant_of_generatorActionBridges
    (hBridges :
      identification.GeneratorActionBridges
        alternatingSixAmbientOrdinaryCharacterTableCertificate) :
    identification.Equivariant
      alternatingSixAmbientOrdinaryCharacterTableCertificate :=
  identification.equivariant_of_generatorActionBridges_of_generation
    alternatingSixAmbientOrdinaryCharacterTableCertificate
    hBridges alternatingSixTwoSylowAutStabilizerGeneration

/-- Construct the ordering-safe concrete two-local character-table
certificate from the supplied row identification and its four semantic
generator bridges. -/
def concreteCharacterTableCertificateOfGeneratorActionBridges
    (hBridges :
      identification.GeneratorActionBridges
        alternatingSixAmbientOrdinaryCharacterTableCertificate) :
    AlternatingSixTwoConcreteCharacterTableCertificate
      (AlternatingSixAmbientPPrimeRowIndex 2) :=
  identification.concreteCharacterTableCertificateOfGeneration
    alternatingSixAmbientOrdinaryCharacterTableCertificate
    hBridges alternatingSixTwoSylowAutStabilizerGeneration

end AlternatingSixTwoCTblLibRowIdentification

/-! ### The prime `3` -/

namespace AlternatingSixThreeCTblLibRowIdentification

variable
  (identification : AlternatingSixThreeCTblLibRowIdentification)

/-- The bundled four semantic generator bridges imply full three-local
equivariance; stabilizer generation is unconditional. -/
theorem equivariant_of_generatorActionBridges
    (hBridges :
      identification.GeneratorActionBridges
        alternatingSixAmbientOrdinaryCharacterTableCertificate) :
    identification.Equivariant
      alternatingSixAmbientOrdinaryCharacterTableCertificate :=
  identification.equivariant_of_generatorActionBridges_of_generation
    alternatingSixAmbientOrdinaryCharacterTableCertificate
    hBridges alternatingSixThreeSylowAutStabilizerGeneration

/-- Construct the ordering-safe concrete three-local character-table
certificate from the supplied row identification and its four semantic
generator bridges. -/
def concreteCharacterTableCertificateOfGeneratorActionBridges
    (hBridges :
      identification.GeneratorActionBridges
        alternatingSixAmbientOrdinaryCharacterTableCertificate) :
    AlternatingSixThreeConcreteCharacterTableCertificate
      (AlternatingSixAmbientPPrimeRowIndex 3) :=
  identification.concreteCharacterTableCertificateOfGeneration
    alternatingSixAmbientOrdinaryCharacterTableCertificate
    hBridges alternatingSixThreeSylowAutStabilizerGeneration

end AlternatingSixThreeCTblLibRowIdentification

/-! ### The prime `5` -/

namespace AlternatingSixFiveCTblLibRowIdentification

variable
  (identification : AlternatingSixFiveCTblLibRowIdentification)

/-- The bundled four semantic generator bridges imply full five-local
equivariance; stabilizer generation is unconditional. -/
theorem equivariant_of_generatorActionBridges
    (hBridges :
      identification.GeneratorActionBridges
        alternatingSixAmbientOrdinaryCharacterTableCertificate) :
    identification.Equivariant
      alternatingSixAmbientOrdinaryCharacterTableCertificate :=
  identification.equivariant_of_generatorActionBridges_of_generation
    alternatingSixAmbientOrdinaryCharacterTableCertificate
    hBridges alternatingSixFiveSylowAutStabilizerGeneration

/-- Construct the ordering-safe concrete five-local character-table
certificate from the supplied row identification and its four semantic
generator bridges. -/
def concreteCharacterTableCertificateOfGeneratorActionBridges
    (hBridges :
      identification.GeneratorActionBridges
        alternatingSixAmbientOrdinaryCharacterTableCertificate) :
    AlternatingSixFiveConcreteCharacterTableCertificate
      (AlternatingSixAmbientPPrimeRowIndex 5) :=
  identification.concreteCharacterTableCertificateOfGeneration
    alternatingSixAmbientOrdinaryCharacterTableCertificate
    hBridges alternatingSixFiveSylowAutStabilizerGeneration

end AlternatingSixFiveCTblLibRowIdentification

end InductiveMcKay
end McKayConjecture
