/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.ElementaryLocalAutomaticCases
import McKayConjecture.InductiveMcKay.QuasisimpleAutomaticCases

/-!
# Structural residual in the quasisimple verification

This file sharpens `RelevantQuasisimpleOneSylowHypothesis` by collecting
every elementary obstruction currently available before the
classification-dependent character correspondence is constructed.

For a selected Sylow subgroup `P` in a finite quasisimple group, the actual
residual case has all of the following properties:

* `p` divides the group order and `P` is nontrivial;
* `P` is neither normal nor central, and its normalizer is proper;
* the ambient group is not solvable, nilpotent, a `p`-group, or a Z-group;
* the ambient order is not squarefree;
* neither the full automorphism group nor the Sylow-stabilizing
  automorphism group is subsingleton; and
* if `p` is the least prime divisor of the group order, `P` is not cyclic.

The resulting structural residual hypothesis is proved equivalent to the
original quasisimple hypothesis.  In particular, for `p = 2`, every
remaining Sylow subgroup is automatically noncyclic.

No assertion is made for a self-normalizing Sylow subgroup or a cyclic
Sylow subgroup away from the least prime: neither condition constructs the
required character bijection or the character-triple witnesses.
-/

noncomputable section

universe u w

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- If a Sylow subgroup is not central, its stabilizer in the full
automorphism group cannot be subsingleton: conjugation by its own elements
already supplies nontrivial Sylow-stabilizing automorphisms. -/
theorem not_subsingleton_sylowAutStabilizer_of_not_le_center
    {p : ℕ}
    {U : Type u} [Group U]
    (P : Sylow p U)
    (hP : ¬(P : Subgroup U) ≤ Subgroup.center U) :
    ¬Subsingleton (SylowAutStabilizer P) := by
  intro hAut
  letI : Subsingleton (SylowAutStabilizer P) := hAut
  apply hP
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  let a : SylowAutStabilizer P :=
    ⟨MulAut.conj x, by
      rw [SylowAutStabilizer.mem_iff]
      exact
        (Sylow.smul_eq_iff_mem_normalizer.mpr
          (P.le_normalizer hx))⟩
  have ha : a = 1 :=
    Subsingleton.elim _ _
  have hvalue :=
    congrArg
      (fun e : SylowAutStabilizer P ↦ e.1 g) ha
  have hone :
      (1 : SylowAutStabilizer P).1 g = g := rfl
  have hconj :
      x * g * x⁻¹ = g := by
    simpa only [a, MulAut.conj_apply] using
      hvalue.trans hone
  symm
  calc
    x * g = (x * g * x⁻¹) * x := by
      simp [mul_assoc]
    _ = g * x := by rw [hconj]

/-- The elementary structural facts satisfied by a genuinely residual
quasisimple local-verification case. -/
structure QuasisimpleLocalResidualProfile
    (p : ℕ)
    (U : Type u) [Group U] [Finite U]
    (P : Sylow p U) : Prop where
  /-- The fixed prime occurs in the group order. -/
  prime_dvd_card : p ∣ Nat.card U
  /-- The selected Sylow subgroup is nontrivial. -/
  sylow_ne_bot : (P : Subgroup U) ≠ ⊥
  /-- The normal-Sylow case has already been removed. -/
  sylow_not_normal : ¬(P : Subgroup U).Normal
  /-- In a quasisimple group this is equivalent to nonnormality. -/
  sylow_not_le_center :
    ¬(P : Subgroup U) ≤ Subgroup.center U
  /-- Thus the Sylow normalizer is a proper subgroup. -/
  sylow_normalizer_lt_top :
    Subgroup.normalizer (P : Set U) < ⊤
  /-- Burnside transfer forbids the Sylow normalizer from centralizing the
  Sylow subgroup. -/
  sylow_normalizer_not_le_centralizer :
    ¬Subgroup.normalizer (P : Set U) ≤
      Subgroup.centralizer (P : Set U)
  /-- A nontrivial perfect group is not solvable. -/
  ambient_not_solvable : ¬Group.IsSolvable U
  /-- In particular it is not nilpotent. -/
  ambient_not_nilpotent : ¬Group.IsNilpotent U
  /-- Its order is not a power of the fixed prime. -/
  ambient_not_pGroup : ¬IsPGroup p U
  /-- It cannot have every Sylow subgroup cyclic. -/
  ambient_not_zGroup : ¬IsZGroup U
  /-- Consequently its order is not squarefree. -/
  ambient_card_not_squarefree : ¬Squarefree (Nat.card U)
  /-- Its full automorphism group does not collapse to a singleton. -/
  ambient_mulAut_not_subsingleton :
    ¬Subsingleton (MulAut U)
  /-- Nor does the actual Sylow-stabilizing automorphism group collapse:
  inner automorphisms from the noncentral Sylow subgroup survive. -/
  sylowAutStabilizer_not_subsingleton :
    ¬Subsingleton (SylowAutStabilizer P)
  /-- At the least prime divisor, Burnside transfer rules out a cyclic
  Sylow subgroup. -/
  smallest_prime_sylow_not_cyclic :
    (Nat.card U).minFac = p → ¬IsCyclic P

namespace QuasisimpleLocalResidualProfile

variable {U : Type u} [Group U] [Finite U]

/-- The least-prime field of the profile, specialized to `p = 2`. -/
theorem sylow_two_not_isCyclic
    {P : Sylow 2 U}
    (h : QuasisimpleLocalResidualProfile 2 U P) :
    ¬IsCyclic P :=
  h.smallest_prime_sylow_not_cyclic
    ((Nat.minFac_eq_two_iff (Nat.card U)).mpr
      h.prime_dvd_card)

end QuasisimpleLocalResidualProfile

/-- Every nonnormal Sylow subgroup at a prime dividing the order of a
finite quasisimple group has the full residual profile. -/
theorem quasisimpleLocalResidualProfile
    {p : ℕ} [Fact p.Prime]
    {U : Type u} [Group U] [Finite U]
    (hU : IsQuasisimple U)
    (P : Sylow p U)
    (hp : p ∣ Nat.card U)
    (hPnormal : ¬(P : Subgroup U).Normal) :
    QuasisimpleLocalResidualProfile p U P where
  prime_dvd_card := hp
  sylow_ne_bot := P.ne_bot_of_dvd_card hp
  sylow_not_normal := hPnormal
  sylow_not_le_center := by
    intro hcentral
    exact hPnormal
      ((hU.sylow_normal_iff_le_center P).mpr hcentral)
  sylow_normalizer_lt_top := by
    rw [lt_top_iff_ne_top]
    intro htop
    exact hPnormal
      (Subgroup.normalizer_eq_top_iff.mp htop)
  sylow_normalizer_not_le_centralizer :=
    hU.sylow_normalizer_not_le_centralizer P hp
  ambient_not_solvable := hU.not_isSolvable
  ambient_not_nilpotent := hU.not_isNilpotent
  ambient_not_pGroup := hU.not_isPGroup
  ambient_not_zGroup := hU.not_isZGroup
  ambient_card_not_squarefree := hU.not_squarefree_card
  ambient_mulAut_not_subsingleton :=
    hU.not_subsingleton_mulAut
  sylowAutStabilizer_not_subsingleton :=
    not_subsingleton_sylowAutStabilizer_of_not_le_center
      P (by
        intro hcentral
        exact hPnormal
          ((hU.sylow_normal_iff_le_center P).mpr hcentral))
  smallest_prime_sylow_not_cyclic :=
    hU.sylow_not_isCyclic_of_minFac_eq P

/-- The exact residual quasisimple verification after all elementary
structural filters in `QuasisimpleLocalResidualProfile` are removed.

For each quasisimple group one may choose a single Sylow subgroup.  Local
data are requested only if that choice satisfies the residual profile.
-/
def StructurallyRelevantQuasisimpleOneSylowHypothesis
    (p : ℕ) : Prop :=
  ∀ (U : Type u) [Group U] [Finite U],
    IsQuasisimple U →
      ∃ P : Sylow p U,
        QuasisimpleLocalResidualProfile p U P →
          Nonempty (LocalInductiveMcKayData P)

namespace StructurallyRelevantQuasisimpleOneSylowHypothesis

/-- The structurally filtered residual verification implies the complete
quasisimple input.  Order-prime, normal-Sylow, and all profile fields are
discharged by proved elementary lemmas. -/
theorem toQuasisimple
    {p : ℕ} [Fact p.Prime]
    (h :
      StructurallyRelevantQuasisimpleOneSylowHypothesis.{u} p) :
    QuasisimpleInductiveMcKayHypothesis.{u} p := by
  apply QuasisimpleInductiveMcKayHypothesis.of_one_sylow
  intro U _ _ hU
  obtain ⟨P, hP⟩ := h U hU
  refine ⟨P, ?_⟩
  by_cases hp : p ∣ Nat.card U
  · by_cases hnormal : (P : Subgroup U).Normal
    · exact
        LocalInductiveMcKayData.nonempty_of_normal_sylow
          P hnormal
    · exact
        hP
          (quasisimpleLocalResidualProfile
            hU P hp hnormal)
  · exact
      LocalInductiveMcKayData.nonempty_of_prime_not_dvd_card
        P hp

end StructurallyRelevantQuasisimpleOneSylowHypothesis

namespace QuasisimpleInductiveMcKayHypothesis

/-- The full quasisimple hypothesis supplies the structurally filtered
one-Sylow verification. -/
theorem toStructurallyRelevantOneSylow
    {p : ℕ}
    (h : QuasisimpleInductiveMcKayHypothesis.{u} p) :
    StructurallyRelevantQuasisimpleOneSylowHypothesis.{u} p := by
  intro U _ _ hU
  let P : Sylow p U := default
  exact ⟨P, fun _ ↦ h U hU P⟩

/-- The profile is an exact elementary reduction, not an additional
assumption: verifying precisely its remaining cases is equivalent to the
full quasisimple input. -/
theorem iff_structurallyRelevantOneSylow
    {p : ℕ} [Fact p.Prime] :
    QuasisimpleInductiveMcKayHypothesis.{u} p ↔
      StructurallyRelevantQuasisimpleOneSylowHypothesis.{u} p :=
  ⟨toStructurallyRelevantOneSylow,
    StructurallyRelevantQuasisimpleOneSylowHypothesis.toQuasisimple⟩

/-! ### Isomorphism representatives with structural filters -/

/-- For a covering family of quasisimple isomorphism representatives, it
suffices to construct local data for one Sylow subgroup only when its
proved residual profile is present. -/
theorem of_structural_isomorphism_representatives
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
        ∃ P : Sylow p (F i),
          QuasisimpleLocalResidualProfile p (F i) P →
            Nonempty (LocalInductiveMcKayData P)) :
    QuasisimpleInductiveMcKayHypothesis.{u} p := by
  apply
    StructurallyRelevantQuasisimpleOneSylowHypothesis.toQuasisimple
  intro U _ _ hU
  obtain ⟨i, ⟨e⟩⟩ := coverage U hU
  have hFi : IsQuasisimple (F i) :=
    IsQuasisimple.of_mulEquiv e hU
  obtain ⟨Q, hQ⟩ := verified i hFi
  refine ⟨Sylow.transport e.symm Q, ?_⟩
  intro hprofile
  have hpFi : p ∣ Nat.card (F i) := by
    have hcard :
        Nat.card U = Nat.card (F i) :=
      Nat.card_congr e.toEquiv
    exact hcard ▸ hprofile.prime_dvd_card
  have hQnotNormal :
      ¬(Q : Subgroup (F i)).Normal := by
    intro hQnormal
    apply hprofile.sylow_not_normal
    rw [McKayConjecture.Sylow.coe_transport]
    exact
      hQnormal.map e.symm.toMonoidHom
        e.symm.surjective
  obtain ⟨dQ⟩ :=
    hQ
      (quasisimpleLocalResidualProfile
        hFi Q hpFi hQnotNormal)
  exact
    ⟨LocalInductiveMcKayData.transport
      e.symm Q dQ⟩

end QuasisimpleInductiveMcKayHypothesis

/-! ### Explicit finite carriers with structural filters -/

namespace FiniteGroupEnumeration

/-- The structurally filtered residual task on a canonical finite carrier.
Solvable, nilpotent, prime-power, Z-group, squarefree-order, and the other
excluded cases make the profile unavailable and require no local datum. -/
def StructuralResidualVerified
    (p n : ℕ)
    (groupStructure : Group (Carrier n)) : Prop :=
  letI : Group (Carrier n) := groupStructure
  IsQuasisimple (Carrier n) →
    ∃ P : Sylow p (Carrier n),
      QuasisimpleLocalResidualProfile p (Carrier n) P →
        Nonempty (LocalInductiveMcKayData P)

end FiniteGroupEnumeration

namespace QuasisimpleInductiveMcKayHypothesis

/-- In universe zero, the full quasisimple hypothesis follows from
checking only structurally residual multiplication tables on the canonical
finite carriers. -/
theorem of_finiteGroupEnumeration_structural
    {p : ℕ} [Fact p.Prime]
    (verified :
      ∀ (n : ℕ)
        (groupStructure :
          Group (FiniteGroupEnumeration.Carrier n)),
        FiniteGroupEnumeration.StructuralResidualVerified
          p n groupStructure) :
    QuasisimpleInductiveMcKayHypothesis.{0} p := by
  apply
    StructurallyRelevantQuasisimpleOneSylowHypothesis.toQuasisimple
  intro U groupU finiteU hU
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
  obtain ⟨Q, hQ⟩ :=
    verified (Fintype.card U) groupStructure
      hCarrier
  refine ⟨Sylow.transport e.symm Q, ?_⟩
  intro hprofile
  have hpCarrier :
      p ∣
        Nat.card
          (FiniteGroupEnumeration.Carrier
            (Fintype.card U)) := by
    have hcard :
        Nat.card U =
          Nat.card
            (FiniteGroupEnumeration.Carrier
              (Fintype.card U)) :=
      Nat.card_congr e.toEquiv
    exact hcard ▸ hprofile.prime_dvd_card
  have hQnotNormal :
      ¬(Q : Subgroup
        (FiniteGroupEnumeration.Carrier
          (Fintype.card U))).Normal := by
    intro hQnormal
    apply hprofile.sylow_not_normal
    rw [McKayConjecture.Sylow.coe_transport]
    exact
      hQnormal.map e.symm.toMonoidHom
        e.symm.surjective
  obtain ⟨dQ⟩ :=
    hQ
      (quasisimpleLocalResidualProfile
        hCarrier Q hpCarrier hQnotNormal)
  exact
    ⟨by
      simpa using
        LocalInductiveMcKayData.transport
          e.symm Q dQ⟩

end QuasisimpleInductiveMcKayHypothesis

end InductiveMcKay
end McKayConjecture
