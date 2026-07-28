/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Data.Nat.Prime.Factorial
import McKayConjecture.InductiveMcKay.UniversalCoverSimpleTargetPrimeSupport

/-!
# The prime-supported alternating-family residual

Mathlib supplies the concrete alternating groups and proves simplicity of
`A_m` for `m ≥ 5`.  This file removes all remaining classification
bookkeeping for that family.  For a prime `p` and `m ≥ 5`,

`p ∣ |A_m| ↔ p ≤ m`.

Consequently the alternating-family universal-cover obligation is exactly:
for every `m ≥ 5` with `p ≤ m`, construct local inductive-McKay data on one
Sylow subgroup of one universal cover of `A_m`.

This does not construct those character correspondences; it identifies
their precise kernel-checked parameter range and transports them to every
simple group isomorphic to an alternating group.
-/

noncomputable section

open scoped IsMulCommutative

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- For `m ≥ 5`, a prime divides the order of `A_m` exactly when it is at
most `m`. -/
theorem prime_dvd_natCard_alternatingGroup_iff_le
    {p m : ℕ} [Fact p.Prime]
    (hm : 5 ≤ m) :
    p ∣ Nat.card (alternatingGroup (Fin m)) ↔ p ≤ m := by
  letI : Nontrivial (Fin m) :=
    Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [nat_card_alternatingGroup, Nat.card_fin]
  have htwo : 2 ∣ m.factorial :=
    Nat.dvd_factorial (by omega) (by omega)
  constructor
  · intro hp
    have hfactorial : p ∣ m.factorial := by
      have :
          p ∣ m.factorial / 2 * 2 :=
        dvd_mul_of_dvd_left hp 2
      rwa [Nat.div_mul_cancel htwo] at this
    exact (Fact.out : p.Prime).dvd_factorial.mp hfactorial
  · intro hp
    rw [Nat.dvd_div_iff_mul_dvd htwo]
    have hpfactorial : p ∣ m.factorial :=
      (Fact.out : p.Prime).dvd_factorial.mpr hp
    by_cases hpTwo : p = 2
    · subst p
      simpa using
        (Nat.dvd_factorial (m := 4) (n := m)
          (by omega : 0 < 4) (by omega : 4 ≤ m))
    · exact
        Nat.Prime.dvd_mul_of_dvd_ne (Ne.symm hpTwo)
          Nat.prime_two (Fact.out : p.Prime)
          htwo hpfactorial

/-- Specialized parameterization for the representatives `A_{n+5}` used
by `alternatingSimpleGroupFamily`. -/
theorem prime_dvd_natCard_alternatingRepresentative_iff
    {p : ℕ} [Fact p.Prime]
    (n : ℕ) :
    p ∣
        Nat.card
          (alternatingGroup (Fin (n + 5))) ↔
      p ≤ n + 5 :=
  prime_dvd_natCard_alternatingGroup_iff_le (by omega)

/-- The representatives `A_{n+5}` are noncommutative. -/
theorem alternatingRepresentative_not_isMulCommutative
    (n : ℕ) :
    ¬IsMulCommutative
      (alternatingGroup (Fin (n + 5))) := by
  intro hcomm
  have hsmall :
      Nat.card (Fin (n + 5)) ≤ 3 :=
    alternatingGroup.isMulCommutative_iff_card_le_three.mp hcomm
  simp only [Nat.card_fin] at hsmall
  omega

/-- The exact character-theoretic residual for the alternating family at
`p`: one cover and one Sylow subgroup of `A_{n+5}` only when
`p ≤ n+5`. -/
def AlternatingUniversalCoverPrimeSupportedVerification
    (p : ℕ) : Prop :=
  ∀ n : ℕ,
    p ≤ n + 5 →
      ∃ (U : Type) (_ : Group U) (_ : Finite U)
          (_E :
            UniversalCentralExtension
              U (alternatingGroup (Fin (n + 5))))
          (P : Sylow p U),
        Nonempty (LocalInductiveMcKayData P)

namespace AlternatingUniversalCoverPrimeSupportedVerification

/-- Explicit verification on the representatives `A_{n+5}` transports to
the abstract alternating-family predicate. -/
theorem toFamily
    {p : ℕ} [Fact p.Prime]
    (h :
      AlternatingUniversalCoverPrimeSupportedVerification p) :
    PrimeSupportedOneUniversalCoverOneSylowFamilyVerification.{0}
      p alternatingSimpleGroupFamily := by
  intro S _ _ hmember _ _ hpS
  obtain ⟨n, ⟨e⟩⟩ := hmember
  have hpRepresentative :
      p ∣
        Nat.card
          (alternatingGroup (Fin (n + 5))) := by
    have hcard :
        Nat.card S =
          Nat.card
            (alternatingGroup (Fin (n + 5))) :=
      Nat.card_congr e.toEquiv
    exact hcard ▸ hpS
  obtain ⟨U, groupU, finiteU, E, P, hP⟩ :=
    h n
      ((prime_dvd_natCard_alternatingRepresentative_iff n).mp
        hpRepresentative)
  letI : Group U := groupU
  letI : Finite U := finiteU
  exact
    ⟨U, inferInstance, inferInstance, E.targetEquiv e.symm, P, hP⟩

end AlternatingUniversalCoverPrimeSupportedVerification

namespace PrimeSupportedOneUniversalCoverOneSylowFamilyVerification

/-- Conversely, prime-supported verification of the abstract alternating
family supplies the explicit `A_{n+5}` representatives. -/
theorem toAlternatingRepresentatives
    {p : ℕ} [Fact p.Prime]
    (h :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification.{0}
        p alternatingSimpleGroupFamily) :
    AlternatingUniversalCoverPrimeSupportedVerification p := by
  intro n hp
  exact
    h (alternatingGroup (Fin (n + 5)))
      ⟨n, ⟨MulEquiv.refl _⟩⟩
      (alternatingSimpleGroup_isSimpleGroup n)
      (alternatingRepresentative_not_isMulCommutative n)
      ((prime_dvd_natCard_alternatingRepresentative_iff n).mpr hp)

/-- The abstract alternating-family obligation is exactly the explicit
`A_{n+5}`, `p ≤ n+5` verification problem. -/
theorem iff_alternatingRepresentatives
    {p : ℕ} [Fact p.Prime] :
    PrimeSupportedOneUniversalCoverOneSylowFamilyVerification.{0}
        p alternatingSimpleGroupFamily ↔
      AlternatingUniversalCoverPrimeSupportedVerification p :=
  ⟨toAlternatingRepresentatives,
    AlternatingUniversalCoverPrimeSupportedVerification.toFamily⟩

end PrimeSupportedOneUniversalCoverOneSylowFamilyVerification

namespace CFSGFamilyCoverage

/-- A CFSG split using the concrete mathlib alternating family needs
alternating verification only for the explicit pairs `(n,p)` with
`p ≤ n+5`; the Lie-type and sporadic obligations retain the exact
prime-supported family interface. -/
theorem toUniversalCover_of_alternatingRepresentatives
    {p : ℕ} [Fact p.Prime]
    {lieType sporadic : FiniteGroupFamily.{0}}
    (coverage :
      CFSGFamilyCoverage
        alternatingSimpleGroupFamily lieType sporadic)
    (alternatingVerified :
      AlternatingUniversalCoverPrimeSupportedVerification p)
    (lieTypeVerified :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p lieType)
    (sporadicVerified :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p sporadic) :
    UniversalCoverInductiveMcKayHypothesis.{0} p :=
  coverage.toUniversalCover_of_primeSupported
    ⟨alternatingVerified.toFamily,
      lieTypeVerified, sporadicVerified⟩

/-- Quasisimple form of the explicit alternating-family reduction. -/
theorem toQuasisimple_of_alternatingRepresentatives
    {p : ℕ} [Fact p.Prime]
    {lieType sporadic : FiniteGroupFamily.{0}}
    (coverage :
      CFSGFamilyCoverage
        alternatingSimpleGroupFamily lieType sporadic)
    (alternatingVerified :
      AlternatingUniversalCoverPrimeSupportedVerification p)
    (lieTypeVerified :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p lieType)
    (sporadicVerified :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p sporadic) :
    QuasisimpleInductiveMcKayHypothesis.{0} p :=
  (coverage.toUniversalCover_of_alternatingRepresentatives
    alternatingVerified lieTypeVerified sporadicVerified).toQuasisimple

end CFSGFamilyCoverage

end InductiveMcKay
end McKayConjecture
