/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Group.Ext
import Mathlib.Algebra.Group.TransferInstance
import McKayConjecture.InductiveMcKay.EquivariantTransport
import McKayConjecture.InductiveMcKay.QuasisimpleHypothesis
import McKayConjecture.InductiveMcKay.TrivialLocal

/-!
# Family-by-family verification of the quasisimple input

This file separates reusable bookkeeping from the classification-dependent
part of the quasisimple inductive-McKay hypothesis.

* local data for one Sylow subgroup transports to every Sylow subgroup;
* a central Sylow subgroup has the canonical trivial local datum;
* verification transports from one group in each isomorphism class;
* a quasisimple group is equivalently a perfect central cover of its
  nonabelian simple central quotient; and
* in universe zero, every finite group can be placed on a canonical carrier
  of cardinality `n`, while the possible group structures at each fixed
  `n` form a finite type.

The final finite-carrier bridge therefore asks for one noncentral Sylow
verification per quasisimple group structure on each finite carrier.  It
does not assert classification coverage or the existence of any local
correspondence.
-/

noncomputable section

open scoped IsMulCommutative

universe u w

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-! ### One Sylow subgroup suffices -/

namespace LocalInductiveMcKayData

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- Full local data at one Sylow subgroup transports to every other Sylow
subgroup, since finite-group Sylow subgroups form one conjugacy orbit. -/
theorem nonempty_of_one_sylow
    (P₀ : Sylow p G)
    (h₀ : Nonempty (LocalInductiveMcKayData P₀))
    (P : Sylow p G) :
    Nonempty (LocalInductiveMcKayData P) := by
  obtain ⟨g, hg⟩ :=
    MulAction.exists_smul_eq G P₀ P
  obtain ⟨d₀⟩ := h₀
  have htransport :
      Sylow.transport (MulAut.conj g) P₀ = P := by
    simpa only [Sylow.transport_conj] using hg
  exact
    ⟨htransport ▸
      LocalInductiveMcKayData.transport
        (MulAut.conj g) P₀ d₀⟩

omit [Fact p.Prime] in
/-- A Sylow subgroup contained in the center is normal, so its normalizer is
the whole group and the canonical trivial local datum applies. -/
theorem nonempty_of_sylow_le_center
    (P : Sylow p G)
    (hP : (P : Subgroup G) ≤ Subgroup.center G) :
    Nonempty (LocalInductiveMcKayData P) := by
  letI : (P : Subgroup G).Normal := by
    refine ⟨?_⟩
    intro x hx g
    have hcomm :
        g * x = x * g :=
      Subgroup.mem_center_iff.mp (hP hx) g
    rw [hcomm]
    simpa using hx
  exact ⟨LocalInductiveMcKayData.of_normal_sylow P⟩

end LocalInductiveMcKayData

namespace QuasisimpleInductiveMcKayHypothesis

/-- To verify the quasisimple hypothesis, it is enough to construct full
local data at one Sylow subgroup of each quasisimple group. -/
theorem of_one_sylow
    {p : ℕ} [Fact p.Prime]
    (h :
      ∀ (U : Type u) [Group U] [Finite U],
        IsQuasisimple U →
          ∃ P : Sylow p U,
            Nonempty (LocalInductiveMcKayData P)) :
    QuasisimpleInductiveMcKayHypothesis.{u} p := by
  intro U _ _ hU P
  obtain ⟨P₀, hP₀⟩ := h U hU
  exact
    LocalInductiveMcKayData.nonempty_of_one_sylow
      P₀ hP₀ P

/-- It is enough to handle one Sylow subgroup per quasisimple group only
when that selected Sylow is noncentral.  The central case is automatic. -/
theorem of_one_noncentral_sylow
    {p : ℕ} [Fact p.Prime]
    (h :
      ∀ (U : Type u) [Group U] [Finite U],
        IsQuasisimple U →
          ∃ P : Sylow p U,
            (¬(P : Subgroup U) ≤ Subgroup.center U) →
              Nonempty (LocalInductiveMcKayData P)) :
    QuasisimpleInductiveMcKayHypothesis.{u} p := by
  apply of_one_sylow
  intro U _ _ hU
  obtain ⟨P, hP⟩ := h U hU
  refine ⟨P, ?_⟩
  by_cases hcentral :
      (P : Subgroup U) ≤ Subgroup.center U
  · exact
      LocalInductiveMcKayData.nonempty_of_sylow_le_center
        P hcentral
  · exact hP hcentral

/-! ### Isomorphism representatives -/

/-- A covering family of group isomorphism representatives reduces the
quasisimple input to one Sylow verification on each covered representative.

The coverage argument remains an explicit hypothesis: this theorem does not
assert a classification of finite quasisimple groups. -/
theorem of_isomorphism_representatives
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
          Nonempty (LocalInductiveMcKayData P)) :
    QuasisimpleInductiveMcKayHypothesis.{u} p := by
  apply of_one_sylow
  intro U _ _ hU
  obtain ⟨i, ⟨e⟩⟩ := coverage U hU
  have hFi : IsQuasisimple (F i) :=
    IsQuasisimple.of_mulEquiv e hU
  obtain ⟨Q, ⟨dQ⟩⟩ := verified i hFi
  exact
    ⟨Sylow.transport e.symm Q,
      ⟨LocalInductiveMcKayData.transport
        e.symm Q dQ⟩⟩

end QuasisimpleInductiveMcKayHypothesis

/-! ### Reindexing by perfect central covers -/

/-- The quotient map to the central quotient is a central extension. -/
def centralQuotientExtension
    (U : Type u) [Group U] :
    CentralExtension U (U ⧸ Subgroup.center U) where
  projection := QuotientGroup.mk' (Subgroup.center U)
  surjective :=
    QuotientGroup.mk'_surjective (Subgroup.center U)
  ker_le_center := by
    rw [QuotientGroup.ker_mk']

/-- The central quotient of a quasisimple group is nonabelian. -/
theorem quasisimple_centralQuotient_not_isMulCommutative
    {U : Type u} [Group U]
    (hU : IsQuasisimple U) :
    ¬IsMulCommutative (U ⧸ Subgroup.center U) := by
  letI : Group.IsPerfect U := hU.isPerfect
  letI : IsSimpleGroup (U ⧸ Subgroup.center U) :=
    hU.isSimpleGroup_quotient
  exact
    Group.IsPerfect.not_isMulCommutative
      (U ⧸ Subgroup.center U)

/-- Family-oriented form of the quasisimple input: for each nonabelian
finite simple group and each finite perfect central cover, verify one Sylow
subgroup of the cover. -/
def PerfectCentralCoverOneSylowHypothesis
    (p : ℕ) : Prop :=
  ∀ (S : Type u) [Group S] [Finite S],
    IsSimpleGroup S →
      ¬IsMulCommutative S →
        ∀ (U : Type u) [Group U] [Finite U],
          CentralExtension U S →
            Group.IsPerfect U →
              ∃ P : Sylow p U,
                Nonempty (LocalInductiveMcKayData P)

namespace PerfectCentralCoverOneSylowHypothesis

/-- Perfect-central-cover verification implies the quasisimple hypothesis
by using the canonical central quotient of each quasisimple group. -/
theorem toQuasisimple
    {p : ℕ} [Fact p.Prime]
    (h : PerfectCentralCoverOneSylowHypothesis.{u} p) :
    QuasisimpleInductiveMcKayHypothesis.{u} p := by
  apply QuasisimpleInductiveMcKayHypothesis.of_one_sylow
  intro U _ _ hU
  exact
    h (U ⧸ Subgroup.center U)
      hU.isSimpleGroup_quotient
      (quasisimple_centralQuotient_not_isMulCommutative hU)
      U (centralQuotientExtension U) hU.isPerfect

end PerfectCentralCoverOneSylowHypothesis

namespace QuasisimpleInductiveMcKayHypothesis

/-- Conversely, the quasisimple hypothesis verifies one Sylow subgroup of
every finite perfect central cover of a nonabelian simple group. -/
theorem toPerfectCentralCoverOneSylow
    {p : ℕ}
    (h : QuasisimpleInductiveMcKayHypothesis.{u} p) :
    PerfectCentralCoverOneSylowHypothesis.{u} p := by
  intro S _ _ hS hnoncomm U _ _ E hperfect
  let hU : IsQuasisimple U :=
    E.source_isQuasisimple hperfect hS hnoncomm
  let P : Sylow p U := default
  exact ⟨P, h U hU P⟩

/-- Thus the quasisimple input is exactly one-Sylow verification over all
finite perfect central covers of nonabelian finite simple groups.  Restricting
this further to universal covers would additionally require a descent theorem
through their central quotients, which is not assumed here. -/
theorem iff_perfectCentralCoverOneSylow
    {p : ℕ} [Fact p.Prime] :
    QuasisimpleInductiveMcKayHypothesis.{u} p ↔
      PerfectCentralCoverOneSylowHypothesis.{u} p :=
  ⟨toPerfectCentralCoverOneSylow,
    PerfectCentralCoverOneSylowHypothesis.toQuasisimple⟩

end QuasisimpleInductiveMcKayHypothesis

/-! ### Explicit finite carriers in universe zero -/

namespace FiniteGroupEnumeration

/-- A wrapper around `Fin n` with no pre-existing multiplication instance,
so arbitrary group structures can be transported onto it without instance
conflicts. -/
structure Carrier (n : ℕ) where
  val : Fin n
deriving Fintype, DecidableEq

/-- The canonical finite carrier has exactly the elements of `Fin n`. -/
def carrierEquivFin (n : ℕ) :
    Carrier n ≃ Fin n where
  toFun := Carrier.val
  invFun i := ⟨i⟩
  left_inv x := by cases x; rfl
  right_inv _ := rfl

@[simp]
theorem card_carrier (n : ℕ) :
    Fintype.card (Carrier n) = n := by
  rw [Fintype.card_congr (carrierEquivFin n)]
  exact Fintype.card_fin n

/-- Remember only the multiplication table of a group structure. -/
def groupMultiplication (α : Type) :
    Group α → (α → α → α) :=
  fun groupStructure => groupStructure.mul

/-- The multiplication table determines the complete `Group` structure;
the remaining data and laws are proof-irrelevant or forced by it. -/
theorem groupMultiplication_injective (α : Type) :
    Function.Injective (groupMultiplication α) := by
  intro g h hmul
  exact Group.ext hmul

/-- There are only finitely many group structures on a finite carrier. -/
theorem groupStructures_finite
    (α : Type) [Finite α] :
    Finite (Group α) :=
  Finite.of_injective
    (groupMultiplication α)
    (groupMultiplication_injective α)

/-- At each fixed order `n`, all group multiplication tables form an
actual finite enumeration type. -/
noncomputable instance groupStructuresFintype (n : ℕ) :
    Fintype (Group (Carrier n)) := by
  letI : Finite (Group (Carrier n)) :=
    groupStructures_finite (Carrier n)
  exact Fintype.ofFinite _

/-- Explicit one-Sylow verification for a group structure on the canonical
carrier. -/
def OneSylowVerified
    (p n : ℕ) (groupStructure : Group (Carrier n)) : Prop :=
  letI : Group (Carrier n) := groupStructure
  IsQuasisimple (Carrier n) →
    ∃ P : Sylow p (Carrier n),
      Nonempty (LocalInductiveMcKayData P)

/-- The narrower verification task in which only a selected noncentral
Sylow subgroup needs a supplied local datum. -/
def OneNoncentralSylowVerified
    (p n : ℕ) (groupStructure : Group (Carrier n)) : Prop :=
  letI : Group (Carrier n) := groupStructure
  IsQuasisimple (Carrier n) →
    ∃ P : Sylow p (Carrier n),
      (¬(P : Subgroup (Carrier n)) ≤
          Subgroup.center (Carrier n)) →
        Nonempty (LocalInductiveMcKayData P)

end FiniteGroupEnumeration

namespace QuasisimpleInductiveMcKayHypothesis

/-- Universe-zero quasisimple verification reduces to the explicit finite
carrier slices.  At each `n`, the quantified group structures form the
finite type constructed above, and only one Sylow subgroup is checked. -/
theorem of_finiteGroupEnumeration
    {p : ℕ} [Fact p.Prime]
    (verified :
      ∀ (n : ℕ)
        (groupStructure :
          Group (FiniteGroupEnumeration.Carrier n)),
        FiniteGroupEnumeration.OneSylowVerified
          p n groupStructure) :
    QuasisimpleInductiveMcKayHypothesis.{0} p := by
  intro U groupU finiteU hU P
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
    verified (Fintype.card U) groupStructure hCarrier
  have hAtTransportedSylow :
      Nonempty
        (LocalInductiveMcKayData
          (Sylow.transport e P)) :=
    LocalInductiveMcKayData.nonempty_of_one_sylow
      Q hQ (Sylow.transport e P)
  obtain ⟨d⟩ := hAtTransportedSylow
  exact
    ⟨by
      simpa using
        LocalInductiveMcKayData.transport
          e.symm (Sylow.transport e P) d⟩

/-- Strongest finite-carrier bridge: central Sylow subgroups are discharged
automatically, so the family-by-family input supplies local data only for
one selected noncentral Sylow subgroup of each quasisimple multiplication
table. -/
theorem of_finiteGroupEnumeration_noncentral
    {p : ℕ} [Fact p.Prime]
    (verified :
      ∀ (n : ℕ)
        (groupStructure :
          Group (FiniteGroupEnumeration.Carrier n)),
        FiniteGroupEnumeration.OneNoncentralSylowVerified
          p n groupStructure) :
    QuasisimpleInductiveMcKayHypothesis.{0} p := by
  apply of_finiteGroupEnumeration
  intro n groupStructure
  letI : Group (FiniteGroupEnumeration.Carrier n) :=
    groupStructure
  intro hU
  obtain ⟨P, hP⟩ := verified n groupStructure hU
  refine ⟨P, ?_⟩
  by_cases hcentral :
      (P : Subgroup (FiniteGroupEnumeration.Carrier n)) ≤
        Subgroup.center
          (FiniteGroupEnumeration.Carrier n)
  · exact
      LocalInductiveMcKayData.nonempty_of_sylow_le_center
        P hcentral
  · exact hP hcentral

end QuasisimpleInductiveMcKayHypothesis

end InductiveMcKay
end McKayConjecture
