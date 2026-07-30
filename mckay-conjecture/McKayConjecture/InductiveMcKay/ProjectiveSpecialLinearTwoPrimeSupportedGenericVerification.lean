/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.ProjectiveSpecialLinearTwoGenericHopfKernelReduction
import McKayConjecture.InductiveMcKay.ProjectiveSpecialLinearTwoGenericVerificationReduction
import McKayConjecture.InductiveMcKay.ProjectiveSpecialLinearTwoPrimeSupportReduction

/-!
# Prime-supported generic PSL₂ verification

The generic PSL₂ reduction previously requested a local datum on a Sylow
subgroup of every `SL(2,q)` in the generic parameter branch.  That is
stronger than necessary: if `p` does not divide the simple target
`PSL(2,q)`, then the Sylow `p`-subgroup of the central cover `SL(2,q)` lies
in its center and carries the canonical local datum.

This file proves that the generic special-linear input is exactly
equivalent to its restriction to primes supported by the projective
target.  It then supplies assembly theorems whose only generic
character-theoretic premise is this supported restriction.

No generic local datum or Hopf-kernel calculation is asserted.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- The exact supported part of the generic special-linear local-data
input.  Parameters with `p ∤ |PSL(2,q)|` are deliberately omitted. -/
def ProjectiveSpecialLinearTwoPrimeSupportedGenericSpecialLinearLocalData
    (p : ℕ) : Prop :=
  ∀ a : ProjectiveSpecialLinearTwoGenericParameter,
    p ∣ Nat.card (projectiveSpecialLinearTwoRepresentative a.1) →
      ∃ P : Sylow p
          (projectiveSpecialLinearTwoSpecialLinearCover a.1),
        Nonempty (LocalInductiveMcKayData P)

namespace ProjectiveSpecialLinearTwoGenericSpecialLinearLocalData

/-- The unfiltered generic local-data input restricts to supported
projective targets. -/
theorem toPrimeSupported
    {p : ℕ}
    (h : ProjectiveSpecialLinearTwoGenericSpecialLinearLocalData p) :
    ProjectiveSpecialLinearTwoPrimeSupportedGenericSpecialLinearLocalData
      p :=
  fun a _ ↦ h a

end ProjectiveSpecialLinearTwoGenericSpecialLinearLocalData

namespace
    ProjectiveSpecialLinearTwoPrimeSupportedGenericSpecialLinearLocalData

/-- Adding the automatic central-Sylow cases recovers the formerly
unfiltered generic special-linear input. -/
theorem toFull
    {p : ℕ} [Fact p.Prime]
    (h :
      ProjectiveSpecialLinearTwoPrimeSupportedGenericSpecialLinearLocalData
        p) :
    ProjectiveSpecialLinearTwoGenericSpecialLinearLocalData p := by
  intro a
  by_cases hp :
      p ∣ Nat.card (projectiveSpecialLinearTwoRepresentative a.1)
  · exact h a hp
  · let P : Sylow p
        (projectiveSpecialLinearTwoSpecialLinearCover a.1) :=
      default
    exact
      ⟨P,
        LocalInductiveMcKayData.nonempty_of_sylow_le_center
          P
          (CentralExtension.sylow_le_center_of_prime_not_dvd_card
            (projectiveSpecialLinearTwoSpecialLinearCentralExtension a.1)
            P hp)⟩

end ProjectiveSpecialLinearTwoPrimeSupportedGenericSpecialLinearLocalData

/-- Exact prime-support reduction of the generic special-linear local-data
input. -/
theorem
    projectiveSpecialLinearTwoGenericSpecialLinearLocalData_iff_primeSupported
    (p : ℕ) [Fact p.Prime] :
    ProjectiveSpecialLinearTwoGenericSpecialLinearLocalData p ↔
      ProjectiveSpecialLinearTwoPrimeSupportedGenericSpecialLinearLocalData
        p :=
  ⟨ProjectiveSpecialLinearTwoGenericSpecialLinearLocalData.toPrimeSupported,
    ProjectiveSpecialLinearTwoPrimeSupportedGenericSpecialLinearLocalData.toFull⟩

/-- Generic central closedness and local data only at supported projective
targets discharge the complete generic representative branch. -/
theorem
    projectiveSpecialLinearTwoGenericVerification_of_supportedLocalData
    (p : ℕ) [Fact p.Prime]
    (hClosed :
      ProjectiveSpecialLinearTwoGenericCentrallyClosedResidual)
    (hLocal :
      ProjectiveSpecialLinearTwoPrimeSupportedGenericSpecialLinearLocalData
        p) :
    ProjectiveSpecialLinearTwoGenericRepresentativeVerification p :=
  projectiveSpecialLinearTwoGenericRepresentativeVerification_of_centrallyClosed_localData
    p hClosed hLocal.toFull

/-- With the closed order-four branch suppressed, the order-nine
verification, generic central closedness, and supported generic local data
supply the complete PSL₂ representative-family verification. -/
theorem
    projectiveSpecialLinearTwoFamilyVerification_of_orderNine_supportedGeneric
    (p : ℕ) [Fact p.Prime]
    (orderNine :
      ProjectiveSpecialLinearTwoOrderNineRepresentativeVerification p)
    (hClosed :
      ProjectiveSpecialLinearTwoGenericCentrallyClosedResidual)
    (hLocal :
      ProjectiveSpecialLinearTwoPrimeSupportedGenericSpecialLinearLocalData
        p) :
    ProjectiveSpecialLinearTwoRepresentativeFamilyVerification p :=
  projectiveSpecialLinearTwoRepresentativeFamilyVerification_of_orderNine_generic
    p orderNine hClosed hLocal.toFull

/-- The explicit generic Hopf-kernel computation, order-nine verification,
and supported generic local data are sufficient for the full PSL₂
representative family. -/
theorem
    projectiveSpecialLinearTwoFamilyVerification_of_orderNine_hopfKernel_supportedGeneric
    (p : ℕ) [Fact p.Prime]
    (orderNine :
      ProjectiveSpecialLinearTwoOrderNineRepresentativeVerification p)
    (hHopf :
      ProjectiveSpecialLinearTwoGenericHopfKernelTrivialResidual)
    (hLocal :
      ProjectiveSpecialLinearTwoPrimeSupportedGenericSpecialLinearLocalData
        p) :
    ProjectiveSpecialLinearTwoRepresentativeFamilyVerification p :=
  projectiveSpecialLinearTwoFamilyVerification_of_orderNine_supportedGeneric
    p orderNine
      (projectiveSpecialLinearTwoGenericCentrallyClosedResidual_of_hopfKernelTrivial
        hHopf)
      hLocal

/-- The same sharpened inputs give local data on every universal cover and
every Sylow subgroup of every member of the simple PSL₂ family. -/
theorem
    projectiveSpecialLinearTwoEveryCoverLocalData_of_orderNine_hopfKernel_supportedGeneric
    (p : ℕ) [Fact p.Prime]
    (orderNine :
      ProjectiveSpecialLinearTwoOrderNineRepresentativeVerification p)
    (hHopf :
      ProjectiveSpecialLinearTwoGenericHopfKernelTrivialResidual)
    (hLocal :
      ProjectiveSpecialLinearTwoPrimeSupportedGenericSpecialLinearLocalData
        p)
    (S : Type) [Group S] [Finite S]
    (hS : projectiveSpecialLinearTwoSimpleGroupFamily.Contains S)
    (V : Type) [Group V] [Finite V]
    (F : UniversalCentralExtension V S)
    (Q : Sylow p V) :
    Nonempty (LocalInductiveMcKayData Q) :=
  (projectiveSpecialLinearTwoFamilyVerification_of_orderNine_hopfKernel_supportedGeneric
    p orderNine hHopf hLocal).localData_on_every_universalCover
      S hS V F Q

end InductiveMcKay
end McKayConjecture
