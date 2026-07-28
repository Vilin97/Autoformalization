/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import McKayConjecture.GroupTheory.UniversalCentralExtensionSourceEquiv
import McKayConjecture.GroupTheory.UniversalCentralExtensionTargetEquiv
import McKayConjecture.InductiveMcKay.QuasisimpleFamilyReduction
import McKayConjecture.InductiveMcKay.UniversalCoverQuasisimpleDescent

/-!
# Family coverage for the universal-cover input

This file isolates the two logically independent classification-dependent
inputs in the quasisimple part of the McKay reduction:

1. **coverage:** every nonabelian finite simple group belongs to one of the
   chosen families;
2. **verification:** for each member of each family, one chosen universal
   cover has local inductive-McKay data at one chosen Sylow subgroup.

The second input is deliberately weaker than the public universal-cover
hypothesis.  Sources of two universal central extensions of the same target
are canonically isomorphic, and Sylow subgroups form one conjugacy orbit.
Consequently one cover and one Sylow subgroup really do suffice.

No classification theorem is asserted here.  In particular, the three
predicates in `CFSGFamilyCoverage` must eventually be instantiated by
kernel-checked definitions of the alternating, finite-Lie-type, and sporadic
families, and its coverage proof is precisely the CFSG dependency.
-/

noncomputable section

open scoped IsMulCommutative

universe u w

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-! ### Abstract finite-group families -/

/-- An isomorphism-invariant family predicate may be packaged as a
predicate on a finite group together with its concrete group and finiteness
instances.  Isomorphism invariance is not built into this wrapper: a
classification implementation should prove it for its concrete predicates.
-/
structure FiniteGroupFamily where
  member :
    ∀ (S : Type u), Group S → Finite S → Prop

namespace FiniteGroupFamily

/-- Membership in a finite-group family using the ambient instances. -/
def Contains
    (family : FiniteGroupFamily.{u})
    (S : Type u) [Group S] [Finite S] : Prop :=
  family.member S inferInstance inferInstance

/-- A family is stable under replacing a finite group by an isomorphic
group.  This is a separately checkable requirement for concrete family
predicates, rather than an unproved field hidden in `Contains`. -/
def IsIsomorphismInvariant
    (family : FiniteGroupFamily.{u}) : Prop :=
  ∀ (S T : Type u) [Group S] [Finite S]
      [Group T] [Finite T],
    Nonempty (S ≃* T) →
      (family.Contains S ↔ family.Contains T)

end FiniteGroupFamily

/-- An indexed collection of family predicates covers the nonabelian finite
simple groups.  This proposition contains classification only; it contains
no character theory and no local McKay datum. -/
def NonabelianFiniteSimpleFamilyCoverage
    {ι : Type w}
    (family : ι → FiniteGroupFamily.{u}) : Prop :=
  ∀ (S : Type u) [Group S] [Finite S],
    IsSimpleGroup S →
      ¬IsMulCommutative S →
        ∃ i : ι, (family i).Contains S

/-! ### Isomorphism representatives of simple groups -/

/-- A family of concrete groups contains an isomorphism representative of
every nonabelian finite simple group.  Unlike
`NonabelianFiniteSimpleFamilyCoverage`, this interface is suitable for a
classification encoded by explicit group constructions. -/
def NonabelianFiniteSimpleRepresentativeCoverage
    {ι : Type w}
    (representative : ι → Type u)
    [groupRepresentative :
      ∀ i, Group (representative i)]
    [_finiteRepresentative :
      ∀ i, Finite (representative i)] : Prop :=
  ∀ (S : Type u) [Group S] [Finite S],
    IsSimpleGroup S →
      ¬IsMulCommutative S →
        ∃ i : ι,
          Nonempty (S ≃* representative i)

/-- Character-theoretic verification on one universal cover and one Sylow
subgroup for each nonabelian simple representative. -/
def OneUniversalCoverOneSylowRepresentativeVerification
    (p : ℕ)
    {ι : Type w}
    (representative : ι → Type u)
    [groupRepresentative :
      ∀ i, Group (representative i)]
    [_finiteRepresentative :
      ∀ i, Finite (representative i)] : Prop :=
  ∀ i : ι,
    IsSimpleGroup (representative i) →
      ¬IsMulCommutative (representative i) →
        ∃ (U : Type u) (_ : Group U) (_ : Finite U)
            (_E :
              UniversalCentralExtension
                U (representative i))
            (P : Sylow p U),
          Nonempty (LocalInductiveMcKayData P)

/-! ### One chosen universal cover and one chosen Sylow subgroup -/

/-- For every simple group in `family`, there is one finite universal cover
and one Sylow subgroup of that cover carrying full local inductive-McKay
data.

This is the exact family-verification obligation left to character theory.
It does not quantify over all universal covers or all Sylow subgroups. -/
def OneUniversalCoverOneSylowFamilyVerification
    (p : ℕ)
    (family : FiniteGroupFamily.{u}) : Prop :=
  ∀ (S : Type u) [Group S] [Finite S],
    family.Contains S →
      IsSimpleGroup S →
        ¬IsMulCommutative S →
          ∃ (U : Type u) (_ : Group U) (_ : Finite U)
              (_E : UniversalCentralExtension U S)
              (P : Sylow p U),
            Nonempty (LocalInductiveMcKayData P)

namespace OneUniversalCoverOneSylowFamilyVerification

/-- Verification on one chosen universal cover and one chosen Sylow
subgroup transports to every universal cover and every Sylow subgroup of
the same simple target. -/
theorem localData_on_every_universalCover
    {p : ℕ} [Fact p.Prime]
    {family : FiniteGroupFamily.{u}}
    (verified :
      OneUniversalCoverOneSylowFamilyVerification p family)
    (S : Type u) [Group S] [Finite S]
    (hmember : family.Contains S)
    (hs : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S)
    (V : Type u) [Group V] [Finite V]
    (F : UniversalCentralExtension V S)
    (Q : Sylow p V) :
    Nonempty (LocalInductiveMcKayData Q) := by
  obtain ⟨U, groupU, finiteU, E, P, ⟨d⟩⟩ :=
    verified S hmember hs hnoncomm
  letI : Group U := groupU
  letI : Finite U := finiteU
  let e : U ≃* V :=
    E.sourceEquiv F
  let R : Sylow p V :=
    Sylow.transport e P
  have hR :
      Nonempty (LocalInductiveMcKayData R) :=
    ⟨LocalInductiveMcKayData.transport e P d⟩
  exact
    LocalInductiveMcKayData.nonempty_of_one_sylow
      R hR Q

end OneUniversalCoverOneSylowFamilyVerification

namespace UniversalCoverInductiveMcKayHypothesis

/-- Family coverage together with one-cover/one-Sylow verification for each
family implies the exact universal-cover hypothesis. -/
theorem of_familyCoverage
    {p : ℕ} [Fact p.Prime]
    {ι : Type w}
    {family : ι → FiniteGroupFamily.{u}}
    (coverage :
      NonabelianFiniteSimpleFamilyCoverage family)
    (verified :
      ∀ i : ι,
        OneUniversalCoverOneSylowFamilyVerification
          p (family i)) :
    UniversalCoverInductiveMcKayHypothesis.{u} p := by
  intro S _ _ hs hnoncomm U _ _ E P
  obtain ⟨i, hi⟩ :=
    coverage S hs hnoncomm
  exact
    (verified i).localData_on_every_universalCover
      S hi hs hnoncomm U E P

/-- A classification by concrete simple-group representatives reduces the
universal-cover hypothesis to one chosen universal cover and one Sylow
subgroup for each representative.

Both transports are genuine: `targetEquiv` moves the arbitrary universal
cover along the classified target isomorphism, and `sourceEquiv` then
identifies its source with the chosen verified universal cover. -/
theorem of_isomorphismRepresentatives
    {p : ℕ} [Fact p.Prime]
    {ι : Type w}
    (representative : ι → Type u)
    [groupRepresentative :
      ∀ i, Group (representative i)]
    [_finiteRepresentative :
      ∀ i, Finite (representative i)]
    (coverage :
      NonabelianFiniteSimpleRepresentativeCoverage
        representative)
    (verified :
      OneUniversalCoverOneSylowRepresentativeVerification
        p representative) :
    UniversalCoverInductiveMcKayHypothesis.{u} p := by
  intro S _ _ hs hnoncomm V _ _ F Q
  obtain ⟨i, ⟨e⟩⟩ :=
    coverage S hs hnoncomm
  have hsRepresentative :
      IsSimpleGroup (representative i) :=
    e.isSimpleGroup_congr.mp hs
  have hnoncommRepresentative :
      ¬IsMulCommutative (representative i) := by
    intro hcomm
    letI : IsMulCommutative (representative i) :=
      hcomm
    apply hnoncomm
    exact
      IsMulCommutative.of_comm fun x y ↦ by
        apply e.injective
        simpa using mul_comm' (e x) (e y)
  obtain ⟨U, groupU, finiteU, E, P, ⟨d⟩⟩ :=
    verified i hsRepresentative hnoncommRepresentative
  letI : Group U := groupU
  letI : Finite U := finiteU
  let F' :
      UniversalCentralExtension
        V (representative i) :=
    F.targetEquiv e
  let sourceEquiv : U ≃* V :=
    E.sourceEquiv F'
  let R : Sylow p V :=
    Sylow.transport sourceEquiv P
  have hR :
      Nonempty (LocalInductiveMcKayData R) :=
    ⟨LocalInductiveMcKayData.transport
      sourceEquiv P d⟩
  exact
    LocalInductiveMcKayData.nonempty_of_one_sylow
      R hR Q

end UniversalCoverInductiveMcKayHypothesis

namespace QuasisimpleInductiveMcKayHypothesis

/-- The corresponding family-cover bridge to the stronger quasisimple
hypothesis.  Descent from universal covers to arbitrary perfect central
covers is already kernel-checked in
`UniversalCoverQuasisimpleDescent`. -/
theorem of_universalCoverFamilyCoverage
    {p : ℕ} [Fact p.Prime]
    {ι : Type w}
    {family : ι → FiniteGroupFamily.{u}}
    (coverage :
      NonabelianFiniteSimpleFamilyCoverage family)
    (verified :
      ∀ i : ι,
        OneUniversalCoverOneSylowFamilyVerification
          p (family i)) :
    QuasisimpleInductiveMcKayHypothesis.{u} p :=
  (UniversalCoverInductiveMcKayHypothesis.of_familyCoverage
    coverage verified).toQuasisimple

/-- Concrete simple-group representatives likewise suffice for the
quasisimple input: only one chosen universal cover and one chosen Sylow
subgroup are verified on each representative. -/
theorem of_universalCoverIsomorphismRepresentatives
    {p : ℕ} [Fact p.Prime]
    {ι : Type w}
    (representative : ι → Type u)
    [groupRepresentative :
      ∀ i, Group (representative i)]
    [_finiteRepresentative :
      ∀ i, Finite (representative i)]
    (coverage :
      NonabelianFiniteSimpleRepresentativeCoverage
        representative)
    (verified :
      OneUniversalCoverOneSylowRepresentativeVerification
        p representative) :
    QuasisimpleInductiveMcKayHypothesis.{u} p :=
  (UniversalCoverInductiveMcKayHypothesis.of_isomorphismRepresentatives
    representative coverage verified).toQuasisimple

end QuasisimpleInductiveMcKayHypothesis

/-! ### The three CFSG families -/

/-- The concrete alternating-family predicate available from mathlib:
`S` is isomorphic to `Aₙ` for some `n ≥ 5`. -/
def IsAlternatingSimpleGroup
    (S : Type u) [Group S] [Finite S] : Prop :=
  ∃ n : ℕ,
    Nonempty
      (S ≃*
        alternatingGroup (Fin (n + 5)))

/-- The alternating groups form a concrete `FiniteGroupFamily`.  This is
the one CFSG family for which the pinned mathlib already provides the
underlying finite groups and their simplicity theorem. -/
def alternatingSimpleGroupFamily :
    FiniteGroupFamily.{u} where
  member S groupS finiteS :=
    @IsAlternatingSimpleGroup S groupS finiteS

@[simp]
theorem alternatingSimpleGroupFamily_contains_iff
    (S : Type u) [Group S] [Finite S] :
    alternatingSimpleGroupFamily.Contains S ↔
      IsAlternatingSimpleGroup S :=
  Iff.rfl

/-- The concrete alternating-family predicate is invariant under group
isomorphism. -/
theorem alternatingSimpleGroupFamily_isIsomorphismInvariant :
    alternatingSimpleGroupFamily.IsIsomorphismInvariant := by
  intro S T _ _ _ _ ⟨e⟩
  constructor
  · rintro ⟨n, ⟨f⟩⟩
    exact ⟨n, ⟨e.symm.trans f⟩⟩
  · rintro ⟨n, ⟨f⟩⟩
    exact ⟨n, ⟨e.trans f⟩⟩

/-- Mathlib proves simplicity of every representative in the concrete
alternating family. -/
theorem alternatingSimpleGroup_isSimpleGroup
    (n : ℕ) :
    IsSimpleGroup
      (alternatingGroup (Fin (n + 5))) :=
  alternatingGroup.isSimpleGroup (by simp)

/-- The three top-level families in the classification of finite simple
groups.  This tag supplies bookkeeping only; it asserts no classification
fact. -/
inductive CFSGFamilyTag
  | alternating
  | lieType
  | sporadic

/-- Classification coverage for explicit alternating, finite-Lie-type, and
sporadic predicates.  Its proof is the exact kernel-checked CFSG fact still
needed by this development. -/
def CFSGFamilyCoverage
    (alternating lieType sporadic :
      FiniteGroupFamily.{u}) : Prop :=
  ∀ (S : Type u) [Group S] [Finite S],
    IsSimpleGroup S →
      ¬IsMulCommutative S →
        alternating.Contains S ∨
          lieType.Contains S ∨
            sporadic.Contains S

/-- The three independent character-theoretic verification obligations.
Each conjunct asks for only one universal cover and one Sylow subgroup per
simple group in that family. -/
def CFSGFamilyVerification
    (p : ℕ)
    (alternating lieType sporadic :
      FiniteGroupFamily.{u}) : Prop :=
  OneUniversalCoverOneSylowFamilyVerification p alternating ∧
    OneUniversalCoverOneSylowFamilyVerification p lieType ∧
      OneUniversalCoverOneSylowFamilyVerification p sporadic

namespace CFSGFamilyCoverage

/-- The three-way CFSG interface implies the exact universal-cover input
once its three independent family verifications are supplied. -/
theorem toUniversalCover
    {p : ℕ} [Fact p.Prime]
    {alternating lieType sporadic :
      FiniteGroupFamily.{u}}
    (coverage :
      CFSGFamilyCoverage alternating lieType sporadic)
    (verified :
      CFSGFamilyVerification
        p alternating lieType sporadic) :
    UniversalCoverInductiveMcKayHypothesis.{u} p := by
  intro S _ _ hs hnoncomm U _ _ E P
  rcases coverage S hs hnoncomm with
    halternating | hlieType | hsporadic
  · exact
      verified.1.localData_on_every_universalCover
        S halternating hs hnoncomm U E P
  · exact
      verified.2.1.localData_on_every_universalCover
        S hlieType hs hnoncomm U E P
  · exact
      verified.2.2.localData_on_every_universalCover
        S hsporadic hs hnoncomm U E P

/-- The three-way CFSG interface also implies the quasisimple hypothesis
used by the current final reduction. -/
theorem toQuasisimple
    {p : ℕ} [Fact p.Prime]
    {alternating lieType sporadic :
      FiniteGroupFamily.{u}}
    (coverage :
      CFSGFamilyCoverage alternating lieType sporadic)
    (verified :
      CFSGFamilyVerification
        p alternating lieType sporadic) :
    QuasisimpleInductiveMcKayHypothesis.{u} p :=
  (coverage.toUniversalCover verified).toQuasisimple

end CFSGFamilyCoverage

end InductiveMcKay
end McKayConjecture
