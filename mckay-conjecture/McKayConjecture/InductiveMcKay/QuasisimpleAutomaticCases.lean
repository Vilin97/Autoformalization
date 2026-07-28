/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.QuasisimpleFamilyReduction

/-!
# Automatic cases in the quasisimple verification

The classification-dependent input in the inductive McKay reduction only
needs attention when the prime divides the group order and a Sylow subgroup
is not normal.  This file makes that elementary reduction precise.

* If `p ∤ |G|`, every Sylow `p`-subgroup is trivial.
* A normal (in particular, central or unique) Sylow subgroup has the
  canonical full-local datum from `TrivialLocal`.
* Consequently the quasisimple hypothesis is equivalent to verification at
  one possibly nonnormal Sylow subgroup of each quasisimple group whose order
  is divisible by `p`.

No classification coverage or local correspondence in the remaining cases
is asserted here.
-/

noncomputable section

universe u w

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

namespace LocalInductiveMcKayData

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ}

/-- A Sylow subgroup for a prime not dividing the group order is trivial. -/
theorem sylow_eq_bot_of_prime_not_dvd_card
    [Fact p.Prime]
    (P : Sylow p G)
    (hp : ¬p ∣ Nat.card G) :
    (P : Subgroup G) = ⊥ := by
  apply Subgroup.card_eq_one.mp
  rw [P.card_eq_multiplicity,
    Nat.factorization_eq_zero_of_not_dvd hp, pow_zero]

/-- A normal Sylow subgroup has the canonical full local datum. -/
theorem nonempty_of_normal_sylow
    (P : Sylow p G)
    (hP : (P : Subgroup G).Normal) :
    Nonempty (LocalInductiveMcKayData P) := by
  letI : (P : Subgroup G).Normal := hP
  exact ⟨LocalInductiveMcKayData.of_normal_sylow P⟩

/-- If the prime does not divide the group order, the trivial Sylow subgroup
has the canonical full local datum. -/
theorem nonempty_of_prime_not_dvd_card
    [Fact p.Prime]
    (P : Sylow p G)
    (hp : ¬p ∣ Nat.card G) :
    Nonempty (LocalInductiveMcKayData P) := by
  have hP :
      (P : Subgroup G) = ⊥ :=
    sylow_eq_bot_of_prime_not_dvd_card P hp
  have hnormal : (P : Subgroup G).Normal := by
    rw [hP]
    infer_instance
  exact nonempty_of_normal_sylow P hnormal

/-- Uniqueness of the Sylow subgroup makes it normal, hence automatic. -/
theorem nonempty_of_subsingleton_sylow
    (P : Sylow p G)
    [Subsingleton (Sylow p G)] :
    Nonempty (LocalInductiveMcKayData P) :=
  nonempty_of_normal_sylow P (Sylow.normal_of_subsingleton P)

end LocalInductiveMcKayData

/-! ### The exact residual one-Sylow obligation -/

/-- The residual quasisimple verification after removing the elementary
automatic cases.

Only groups whose order is divisible by `p` are presented.  For each such
quasisimple group one may choose a single Sylow subgroup; a local datum is
required only if that chosen Sylow subgroup is not normal.
-/
def RelevantQuasisimpleOneSylowHypothesis
    (p : ℕ) : Prop :=
  ∀ (U : Type u) [Group U] [Finite U],
    IsQuasisimple U →
      p ∣ Nat.card U →
        ∃ P : Sylow p U,
          (¬(P : Subgroup U).Normal) →
            Nonempty (LocalInductiveMcKayData P)

namespace RelevantQuasisimpleOneSylowHypothesis

/-- The residual one-Sylow verification implies the full quasisimple input.
The missing-order case has a trivial Sylow, and the normal-Sylow case uses
the canonical full-local datum. -/
theorem toQuasisimple
    {p : ℕ} [Fact p.Prime]
    (h : RelevantQuasisimpleOneSylowHypothesis.{u} p) :
    QuasisimpleInductiveMcKayHypothesis.{u} p := by
  apply QuasisimpleInductiveMcKayHypothesis.of_one_sylow
  intro U _ _ hU
  by_cases hp : p ∣ Nat.card U
  · obtain ⟨P, hP⟩ := h U hU hp
    refine ⟨P, ?_⟩
    by_cases hnormal : (P : Subgroup U).Normal
    · exact
        LocalInductiveMcKayData.nonempty_of_normal_sylow
          P hnormal
    · exact hP hnormal
  · let P : Sylow p U := default
    exact
      ⟨P,
        LocalInductiveMcKayData.nonempty_of_prime_not_dvd_card
          P hp⟩

end RelevantQuasisimpleOneSylowHypothesis

namespace QuasisimpleInductiveMcKayHypothesis

/-- The full quasisimple hypothesis supplies the residual verification by
choosing an arbitrary Sylow subgroup. -/
theorem toRelevantOneSylow
    {p : ℕ}
    (h : QuasisimpleInductiveMcKayHypothesis.{u} p) :
    RelevantQuasisimpleOneSylowHypothesis.{u} p := by
  intro U _ _ hU _
  let P : Sylow p U := default
  exact ⟨P, fun _ ↦ h U hU P⟩

/-- Exact elementary reduction of the quasisimple input: it remains to
verify one nonnormal Sylow subgroup only for quasisimple groups whose order
is divisible by `p`. -/
theorem iff_relevantOneSylow
    {p : ℕ} [Fact p.Prime] :
    QuasisimpleInductiveMcKayHypothesis.{u} p ↔
      RelevantQuasisimpleOneSylowHypothesis.{u} p :=
  ⟨toRelevantOneSylow,
    RelevantQuasisimpleOneSylowHypothesis.toQuasisimple⟩

/-! ### Isomorphism representatives with automatic cases removed -/

/-- For a covering family of quasisimple isomorphism representatives, it
suffices to verify one possibly nonnormal Sylow only on representatives
whose order is divisible by `p`.

The coverage premise is deliberately explicit; no classification theorem is
asserted.
-/
theorem of_relevant_isomorphism_representatives
    {p : ℕ} [Fact p.Prime]
    {ι : Type w}
    (F : ι → Type u)
    [groupF : ∀ i, Group (F i)]
    [finiteF : ∀ i, Finite (F i)]
    (coverage :
      ∀ (U : Type u) [Group U] [Finite U],
        IsQuasisimple U →
          ∃ i : ι, Nonempty (U ≃* F i))
    (verified :
      ∀ i : ι, IsQuasisimple (F i) →
        p ∣ Nat.card (F i) →
          ∃ P : Sylow p (F i),
            (¬(P : Subgroup (F i)).Normal) →
              Nonempty (LocalInductiveMcKayData P)) :
    QuasisimpleInductiveMcKayHypothesis.{u} p := by
  apply RelevantQuasisimpleOneSylowHypothesis.toQuasisimple
  intro U _ _ hU hp
  obtain ⟨i, ⟨e⟩⟩ := coverage U hU
  have hFi : IsQuasisimple (F i) :=
    IsQuasisimple.of_mulEquiv e hU
  have hpFi : p ∣ Nat.card (F i) := by
    rwa [← Nat.card_congr e.toEquiv]
  obtain ⟨Q, hQ⟩ := verified i hFi hpFi
  refine ⟨Sylow.transport e.symm Q, ?_⟩
  intro htransportNotNormal
  have hQnotNormal : ¬(Q : Subgroup (F i)).Normal := by
    intro hQnormal
    apply htransportNotNormal
    rw [McKayConjecture.Sylow.coe_transport]
    exact hQnormal.map e.symm.toMonoidHom e.symm.surjective
  obtain ⟨dQ⟩ := hQ hQnotNormal
  exact
    ⟨LocalInductiveMcKayData.transport e.symm Q dQ⟩

end QuasisimpleInductiveMcKayHypothesis

/-! ### Explicit finite carriers with automatic cases removed -/

namespace FiniteGroupEnumeration

/-- The residual verification task on the canonical carrier `Carrier n`.
It is vacuous unless `p ∣ n`, and only a chosen nonnormal Sylow requires a
local datum. -/
def RelevantOneSylowVerified
    (p n : ℕ) (groupStructure : Group (Carrier n)) : Prop :=
  letI : Group (Carrier n) := groupStructure
  IsQuasisimple (Carrier n) →
    p ∣ n →
      ∃ P : Sylow p (Carrier n),
        (¬(P : Subgroup (Carrier n)).Normal) →
          Nonempty (LocalInductiveMcKayData P)

end FiniteGroupEnumeration

namespace QuasisimpleInductiveMcKayHypothesis

/-- Universe-zero verification reduces to the finite multiplication tables
whose carrier size is divisible by `p`, with only one nonnormal Sylow case
left on each quasisimple table. -/
theorem of_finiteGroupEnumeration_relevant
    {p : ℕ} [Fact p.Prime]
    (verified :
      ∀ (n : ℕ)
        (groupStructure :
          Group (FiniteGroupEnumeration.Carrier n)),
        FiniteGroupEnumeration.RelevantOneSylowVerified
          p n groupStructure) :
    QuasisimpleInductiveMcKayHypothesis.{0} p := by
  apply RelevantQuasisimpleOneSylowHypothesis.toQuasisimple
  intro U groupU finiteU hU hp
  letI : Fintype U := Fintype.ofFinite U
  let e₀ :
      U ≃
        FiniteGroupEnumeration.Carrier
          (Fintype.card U) :=
    (Fintype.equivFin U).trans
      (FiniteGroupEnumeration.carrierEquivFin
        (Fintype.card U)).symm
  let groupStructure :
      Group
        (FiniteGroupEnumeration.Carrier
          (Fintype.card U)) :=
    e₀.symm.group
  letI :
      Group
        (FiniteGroupEnumeration.Carrier
          (Fintype.card U)) :=
    groupStructure
  let e :
      U ≃*
        FiniteGroupEnumeration.Carrier
          (Fintype.card U) :=
    (e₀.symm.mulEquiv).symm
  have hCarrier :
      IsQuasisimple
        (FiniteGroupEnumeration.Carrier
          (Fintype.card U)) :=
    IsQuasisimple.of_mulEquiv e hU
  have hpCarrier : p ∣ Fintype.card U := by
    simpa only [Nat.card_eq_fintype_card] using hp
  obtain ⟨Q, hQ⟩ :=
    verified (Fintype.card U) groupStructure
      hCarrier hpCarrier
  refine ⟨Sylow.transport e.symm Q, ?_⟩
  intro htransportNotNormal
  have hQnotNormal :
      ¬(Q : Subgroup
        (FiniteGroupEnumeration.Carrier
          (Fintype.card U))).Normal := by
    intro hQnormal
    apply htransportNotNormal
    rw [McKayConjecture.Sylow.coe_transport]
    exact hQnormal.map e.symm.toMonoidHom e.symm.surjective
  obtain ⟨dQ⟩ := hQ hQnotNormal
  exact
    ⟨by
      simpa using
        LocalInductiveMcKayData.transport
          e.symm Q dQ⟩

end QuasisimpleInductiveMcKayHypothesis

end InductiveMcKay
end McKayConjecture
