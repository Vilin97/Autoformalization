/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveProjectiveTables

/-!
# Removing `A₅` from the alternating universal-cover residual

The complete binary-icosahedral projective tables verify the universal
cover of `A₅` at every prime.  Consequently the remaining alternating
family input begins with `A₆`.

This file makes that removal exact in two equivalent forms:

* prime-supported family verification for alternating groups of degree at
  least six; and
* an explicit representative obligation indexed by `A_{n+5}` with
  `0 < n`.

Thus no verification of `A₅` remains hidden in the alternating-family
residual.  The first genuinely unproved representative is `A₆`.
-/

noncomputable section

open scoped IsMulCommutative

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- The exact remaining explicit alternating-family obligation after the
fully checked `A₅` case is removed. -/
def AlternatingBeyondFiveUniversalCoverPrimeSupportedVerification
    (p : ℕ) : Prop :=
  ∀ n : ℕ,
    0 < n →
      p ≤ n + 5 →
        ∃ (U : Type) (_ : Group U) (_ : Finite U)
            (_E :
              UniversalCentralExtension
                U (alternatingGroup (Fin (n + 5))))
            (P : Sylow p U),
          Nonempty (LocalInductiveMcKayData P)

namespace AlternatingBeyondFiveUniversalCoverPrimeSupportedVerification

/-- Explicit verification of `A_{n+5}` for `n > 0` transports to the
abstract family of alternating groups of degree at least six. -/
theorem toFamilyAtLeastSix
    {p : ℕ} [Fact p.Prime]
    (h :
      AlternatingBeyondFiveUniversalCoverPrimeSupportedVerification p) :
    PrimeSupportedOneUniversalCoverOneSylowFamilyVerification.{0}
      p (alternatingSimpleGroupFamilyAtLeast 6) := by
  intro S _ _ hmember _ _ hpS
  obtain ⟨n, hdegree, ⟨e⟩⟩ := hmember
  have hpRepresentative :
      p ∣ Nat.card (alternatingGroup (Fin (n + 5))) := by
    have hcard :
        Nat.card S =
          Nat.card (alternatingGroup (Fin (n + 5))) :=
      Nat.card_congr e.toEquiv
    exact hcard ▸ hpS
  obtain ⟨U, groupU, finiteU, E, P, hP⟩ :=
    h n (by omega)
      ((prime_dvd_natCard_alternatingRepresentative_iff n).mp
        hpRepresentative)
  letI : Group U := groupU
  letI : Finite U := finiteU
  exact
    ⟨U, inferInstance, inferInstance, E.targetEquiv e.symm, P, hP⟩

end AlternatingBeyondFiveUniversalCoverPrimeSupportedVerification

namespace PrimeSupportedOneUniversalCoverOneSylowFamilyVerification

/-- Verification of the degree-at-least-six family supplies the explicit
remaining representatives. -/
theorem toAlternatingBeyondFiveRepresentatives
    {p : ℕ} [Fact p.Prime]
    (h :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification.{0}
        p (alternatingSimpleGroupFamilyAtLeast 6)) :
    AlternatingBeyondFiveUniversalCoverPrimeSupportedVerification p := by
  intro n hn hp
  exact
    h (alternatingGroup (Fin (n + 5)))
      ⟨n, by omega, ⟨MulEquiv.refl _⟩⟩
      (alternatingSimpleGroup_isSimpleGroup n)
      (alternatingRepresentative_not_isMulCommutative n)
      ((prime_dvd_natCard_alternatingRepresentative_iff n).mpr hp)

/-- The completed `A₅` tables extend verification from alternating groups
of degree at least six to the whole alternating family. -/
theorem of_alternatingAtLeastSix
    {p : ℕ} [Fact p.Prime]
    (h :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification.{0}
        p (alternatingSimpleGroupFamilyAtLeast 6)) :
    PrimeSupportedOneUniversalCoverOneSylowFamilyVerification.{0}
      p alternatingSimpleGroupFamily := by
  intro S _ _ hmember hsimple hnoncomm hpS
  obtain ⟨n, ⟨e⟩⟩ := hmember
  by_cases hn : n = 0
  · subst n
    apply alternatingFiveFamilyVerification p
    · exact
        (alternatingFiveSimpleGroupFamily_contains_iff S).2
          (by simpa using (show Nonempty (S ≃* alternatingGroup (Fin 5)) from ⟨e⟩))
    · exact hsimple
    · exact hnoncomm
  · exact
      h S ⟨n, by omega, ⟨e⟩⟩
        hsimple hnoncomm hpS

/-- Conversely, full alternating-family verification restricts to degrees
at least six. -/
theorem toAlternatingAtLeastSix
    {p : ℕ}
    (h :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification.{0}
        p alternatingSimpleGroupFamily) :
    PrimeSupportedOneUniversalCoverOneSylowFamilyVerification.{0}
      p (alternatingSimpleGroupFamilyAtLeast 6) := by
  intro S _ _ hmember hsimple hnoncomm hpS
  obtain ⟨n, _, hS⟩ := hmember
  exact h S ⟨n, hS⟩ hsimple hnoncomm hpS

/-- Removing the completely verified `A₅` case is an exact reduction of
the prime-supported alternating-family obligation. -/
theorem primeSupportedAlternatingFamilyVerification_iff_atLeastSix
    {p : ℕ} [Fact p.Prime] :
    PrimeSupportedOneUniversalCoverOneSylowFamilyVerification.{0}
        p alternatingSimpleGroupFamily ↔
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification.{0}
        p (alternatingSimpleGroupFamilyAtLeast 6) :=
  ⟨toAlternatingAtLeastSix, of_alternatingAtLeastSix⟩

/-- The family residual and the explicit `A_{n+5}`, `n > 0`, residual are
equivalent. -/
theorem primeSupportedAlternatingFamilyVerification_iff_beyondFive
    {p : ℕ} [Fact p.Prime] :
    PrimeSupportedOneUniversalCoverOneSylowFamilyVerification.{0}
        p alternatingSimpleGroupFamily ↔
      AlternatingBeyondFiveUniversalCoverPrimeSupportedVerification p := by
  rw [primeSupportedAlternatingFamilyVerification_iff_atLeastSix]
  exact
    ⟨toAlternatingBeyondFiveRepresentatives,
      AlternatingBeyondFiveUniversalCoverPrimeSupportedVerification.toFamilyAtLeastSix⟩

end PrimeSupportedOneUniversalCoverOneSylowFamilyVerification

/-- Verification only for alternating simple groups of degree at least
six recovers the full one-cover/one-Sylow alternating-family input. -/
theorem alternatingSimpleGroupFamily_verification_of_atLeastSix
    {p : ℕ} [Fact p.Prime]
    (h :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification.{0}
        p (alternatingSimpleGroupFamilyAtLeast 6)) :
    OneUniversalCoverOneSylowFamilyVerification.{0}
      p alternatingSimpleGroupFamily :=
  h.of_alternatingAtLeastSix.toFull

end InductiveMcKay
end McKayConjecture
