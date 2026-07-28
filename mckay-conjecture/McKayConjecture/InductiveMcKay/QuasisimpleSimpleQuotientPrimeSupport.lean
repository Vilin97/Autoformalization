/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.CentralExtensionPrimeSupport
import McKayConjecture.InductiveMcKay.QuasisimpleStructuralResidual

/-!
# Prime support in the simple quotient of a quasisimple group

For a finite quasisimple group `U`, the quotient `U / Z(U)` is nonabelian
simple.  A prime that occurs only in the center of `U` has a central Sylow
subgroup and therefore contributes no classification-dependent local McKay
case.  This file makes the sharper cutoff exact:

* the full quasisimple hypothesis is equivalent to verification only when
  `p ∣ |U / Z(U)|`; and
* after combining this cutoff with the elementary residual profile, the
  only remaining cases simultaneously have prime support in the simple
  quotient and every structural obstruction recorded in
  `QuasisimpleLocalResidualProfile`.

Thus primes occurring only in a Schur multiplier are discharged
constructively rather than being left in the family verification.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- One-Sylow verification restricted to primes occurring in the
nonabelian simple central quotient of a quasisimple group. -/
def SimpleQuotientRelevantQuasisimpleOneSylowHypothesis
    (p : ℕ) : Prop :=
  ∀ (U : Type u) [Group U] [Finite U],
    IsQuasisimple U →
      p ∣ Nat.card (U ⧸ Subgroup.center U) →
        ∃ P : Sylow p U,
          Nonempty (LocalInductiveMcKayData P)

namespace SimpleQuotientRelevantQuasisimpleOneSylowHypothesis

/-- Verification at primes supported by the simple quotient implies the
full quasisimple hypothesis.  At every other prime, the Sylow subgroup lies
in the central kernel of the canonical quotient map. -/
theorem toQuasisimple
    {p : ℕ} [Fact p.Prime]
    (h :
      SimpleQuotientRelevantQuasisimpleOneSylowHypothesis.{u} p) :
    QuasisimpleInductiveMcKayHypothesis.{u} p := by
  apply QuasisimpleInductiveMcKayHypothesis.of_one_sylow
  intro U _ _ hU
  by_cases hp :
      p ∣ Nat.card (U ⧸ Subgroup.center U)
  · exact h U hU hp
  · let P : Sylow p U := default
    exact
      ⟨P,
        LocalInductiveMcKayData.nonempty_of_sylow_le_center
          P
          (CentralExtension.sylow_le_center_of_prime_not_dvd_card
            (centralQuotientExtension U) P hp)⟩

end SimpleQuotientRelevantQuasisimpleOneSylowHypothesis

namespace QuasisimpleInductiveMcKayHypothesis

/-- The full quasisimple hypothesis supplies the simple-quotient-supported
one-Sylow verification. -/
theorem toSimpleQuotientRelevantOneSylow
    {p : ℕ}
    (h : QuasisimpleInductiveMcKayHypothesis.{u} p) :
    SimpleQuotientRelevantQuasisimpleOneSylowHypothesis.{u} p := by
  intro U _ _ hU _
  let P : Sylow p U := default
  exact ⟨P, h U hU P⟩

/-- Exact prime-support reduction: the quasisimple input only needs
verification at primes dividing the nonabelian simple central quotient. -/
theorem iff_simpleQuotientRelevantOneSylow
    {p : ℕ} [Fact p.Prime] :
    QuasisimpleInductiveMcKayHypothesis.{u} p ↔
      SimpleQuotientRelevantQuasisimpleOneSylowHypothesis.{u} p :=
  ⟨toSimpleQuotientRelevantOneSylow,
    SimpleQuotientRelevantQuasisimpleOneSylowHypothesis.toQuasisimple⟩

end QuasisimpleInductiveMcKayHypothesis

/-! ### Combined prime-support and structural residual -/

/-- The strongest residual interface currently available without invoking
classification or constructing a nontrivial character correspondence.

For one selected Sylow subgroup of each quasisimple group, local data are
required only when the prime occurs in the simple central quotient and the
selected subgroup satisfies the complete elementary residual profile.
-/
def SimpleQuotientStructuralResidualHypothesis
    (p : ℕ) : Prop :=
  ∀ (U : Type u) [Group U] [Finite U],
    IsQuasisimple U →
      ∃ P : Sylow p U,
        p ∣ Nat.card (U ⧸ Subgroup.center U) →
          QuasisimpleLocalResidualProfile p U P →
            Nonempty (LocalInductiveMcKayData P)

namespace SimpleQuotientStructuralResidualHypothesis

/-- The combined prime-support/structural residual implies the full
quasisimple input. -/
theorem toQuasisimple
    {p : ℕ} [Fact p.Prime]
    (h : SimpleQuotientStructuralResidualHypothesis.{u} p) :
    QuasisimpleInductiveMcKayHypothesis.{u} p := by
  apply QuasisimpleInductiveMcKayHypothesis.of_one_sylow
  intro U _ _ hU
  obtain ⟨P, hP⟩ := h U hU
  by_cases hquotient :
      p ∣ Nat.card (U ⧸ Subgroup.center U)
  · by_cases hnormal : (P : Subgroup U).Normal
    · exact
        ⟨P,
          LocalInductiveMcKayData.nonempty_of_normal_sylow
            P hnormal⟩
    · have hambient : p ∣ Nat.card U :=
        hquotient.trans
          (Subgroup.card_quotient_dvd_card
            (Subgroup.center U))
      exact
        ⟨P,
          hP hquotient
            (quasisimpleLocalResidualProfile
              hU P hambient hnormal)⟩
  · exact
      ⟨P,
        LocalInductiveMcKayData.nonempty_of_sylow_le_center
          P
          (CentralExtension.sylow_le_center_of_prime_not_dvd_card
            (centralQuotientExtension U) P hquotient)⟩

end SimpleQuotientStructuralResidualHypothesis

namespace QuasisimpleInductiveMcKayHypothesis

/-- Full local data imply the combined residual verification. -/
theorem toSimpleQuotientStructuralResidual
    {p : ℕ}
    (h : QuasisimpleInductiveMcKayHypothesis.{u} p) :
    SimpleQuotientStructuralResidualHypothesis.{u} p := by
  intro U _ _ hU
  let P : Sylow p U := default
  exact ⟨P, fun _ _ ↦ h U hU P⟩

/-- Exact combined residual formulation of the quasisimple input. -/
theorem iff_simpleQuotientStructuralResidual
    {p : ℕ} [Fact p.Prime] :
    QuasisimpleInductiveMcKayHypothesis.{u} p ↔
      SimpleQuotientStructuralResidualHypothesis.{u} p :=
  ⟨toSimpleQuotientStructuralResidual,
    SimpleQuotientStructuralResidualHypothesis.toQuasisimple⟩

end QuasisimpleInductiveMcKayHypothesis

end InductiveMcKay
end McKayConjecture
