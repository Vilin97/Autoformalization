/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.CentralExtensionPrimeSupport
import McKayConjecture.GroupTheory.FiniteUniversalCentralExtension
import McKayConjecture.InductiveMcKay.UniversalCoverFamilyReduction

/-!
# Prime-supported universal-cover verification

The universal-cover input does not require character theory at primes that
occur only in a covering kernel.  If `U → S` is a universal central
extension and `p ∤ |S|`, every Sylow `p`-subgroup of `U` is central and the
canonical full local datum applies.  Conversely, when `p ∣ |S|`, every
Sylow `p`-subgroup of `U` is noncentral and nonnormal.

This file packages the resulting exact reduction in three forms:

* one chosen universal cover and one Sylow subgroup for every relevant
  nonabelian finite simple group;
* prime-supported verification for an abstract family; and
* prime-supported verification for concrete isomorphism representatives.

The corresponding interfaces are equivalent to their unfiltered versions,
because finite universal central extensions exist and sources over a fixed
simple target are canonically isomorphic.
-/

noncomputable section

open scoped IsMulCommutative

universe u w

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-! ### The exact global target-prime residual -/

/-- For every nonabelian finite simple group whose order is divisible by
`p`, one chosen finite universal cover and one chosen Sylow subgroup carry
full local inductive-McKay data. -/
def SimpleTargetPrimeSupportedUniversalCoverVerification
    (p : ℕ) : Prop :=
  ∀ (S : Type u) [Group S] [Finite S],
    IsSimpleGroup S →
      ¬IsMulCommutative S →
        p ∣ Nat.card S →
          ∃ (U : Type u) (_ : Group U) (_ : Finite U)
              (_E : UniversalCentralExtension U S)
              (P : Sylow p U),
            Nonempty (LocalInductiveMcKayData P)

namespace SimpleTargetPrimeSupportedUniversalCoverVerification

/-- Prime-supported one-cover/one-Sylow verification implies local data on
every universal cover and every Sylow subgroup. -/
theorem toUniversalCover
    {p : ℕ} [Fact p.Prime]
    (h :
      SimpleTargetPrimeSupportedUniversalCoverVerification.{u} p) :
    UniversalCoverInductiveMcKayHypothesis.{u} p := by
  intro S _ _ hS hnoncomm U _ _ E P
  by_cases hp : p ∣ Nat.card S
  · obtain ⟨V, groupV, finiteV, F, Q, ⟨dQ⟩⟩ :=
      h S hS hnoncomm hp
    letI : Group V := groupV
    letI : Finite V := finiteV
    let e : V ≃* U :=
      F.sourceEquiv E
    let R : Sylow p U :=
      Sylow.transport e Q
    have hR :
        Nonempty (LocalInductiveMcKayData R) :=
      ⟨LocalInductiveMcKayData.transport e Q dQ⟩
    exact
      LocalInductiveMcKayData.nonempty_of_one_sylow
        R hR P
  · exact
      LocalInductiveMcKayData.nonempty_of_sylow_le_center
        P
        (CentralExtension.sylow_le_center_of_prime_not_dvd_card
          E.toCentralExtension P hp)

end SimpleTargetPrimeSupportedUniversalCoverVerification

namespace UniversalCoverInductiveMcKayHypothesis

/-- The full universal-cover hypothesis supplies prime-supported
one-cover/one-Sylow verification. -/
theorem toSimpleTargetPrimeSupportedVerification
    {p : ℕ}
    (h : UniversalCoverInductiveMcKayHypothesis.{u} p) :
    SimpleTargetPrimeSupportedUniversalCoverVerification.{u} p := by
  intro S _ _ hS hnoncomm _
  obtain ⟨U, groupU, finiteU, ⟨E⟩⟩ :=
    finite_universalCentralExtension_exists_of_isSimpleGroup
      hS hnoncomm
  letI : Group U := groupU
  letI : Finite U := finiteU
  let P : Sylow p U := default
  exact
    ⟨U, inferInstance, inferInstance, E, P,
      h S hS hnoncomm U E P⟩

/-- Exact global reduction of the universal-cover input to primes occurring
in the underlying simple target. -/
theorem iff_simpleTargetPrimeSupportedVerification
    {p : ℕ} [Fact p.Prime] :
    UniversalCoverInductiveMcKayHypothesis.{u} p ↔
      SimpleTargetPrimeSupportedUniversalCoverVerification.{u} p :=
  ⟨toSimpleTargetPrimeSupportedVerification,
    SimpleTargetPrimeSupportedUniversalCoverVerification.toUniversalCover⟩

end UniversalCoverInductiveMcKayHypothesis

/-! ### Abstract finite-group families -/

/-- Prime-supported character-theoretic verification for one abstract
family of nonabelian finite simple groups. -/
def PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
    (p : ℕ)
    (family : FiniteGroupFamily.{u}) : Prop :=
  ∀ (S : Type u) [Group S] [Finite S],
    family.Contains S →
      IsSimpleGroup S →
        ¬IsMulCommutative S →
          p ∣ Nat.card S →
            ∃ (U : Type u) (_ : Group U) (_ : Finite U)
                (_E : UniversalCentralExtension U S)
                (P : Sylow p U),
              Nonempty (LocalInductiveMcKayData P)

namespace PrimeSupportedOneUniversalCoverOneSylowFamilyVerification

/-- Adding the automatic target-prime-absent cases recovers the ordinary
one-cover/one-Sylow family verification. -/
theorem toFull
    {p : ℕ} [Fact p.Prime]
    {family : FiniteGroupFamily.{u}}
    (h :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p family) :
    OneUniversalCoverOneSylowFamilyVerification p family := by
  intro S _ _ hmember hS hnoncomm
  by_cases hp : p ∣ Nat.card S
  · exact h S hmember hS hnoncomm hp
  · obtain ⟨U, groupU, finiteU, ⟨E⟩⟩ :=
      finite_universalCentralExtension_exists_of_isSimpleGroup
        hS hnoncomm
    letI : Group U := groupU
    letI : Finite U := finiteU
    let P : Sylow p U := default
    exact
      ⟨U, inferInstance, inferInstance, E, P,
        LocalInductiveMcKayData.nonempty_of_sylow_le_center
          P
          (CentralExtension.sylow_le_center_of_prime_not_dvd_card
            E.toCentralExtension P hp)⟩

end PrimeSupportedOneUniversalCoverOneSylowFamilyVerification

namespace OneUniversalCoverOneSylowFamilyVerification

/-- Forgetting the target-prime filter gives the prime-supported family
verification. -/
theorem toPrimeSupported
    {p : ℕ}
    {family : FiniteGroupFamily.{u}}
    (h : OneUniversalCoverOneSylowFamilyVerification p family) :
    PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
      p family := by
  intro S _ _ hmember hS hnoncomm _
  exact h S hmember hS hnoncomm

/-- The prime-supported and unfiltered family obligations are equivalent. -/
theorem iff_primeSupported
    {p : ℕ} [Fact p.Prime]
    {family : FiniteGroupFamily.{u}} :
    OneUniversalCoverOneSylowFamilyVerification p family ↔
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p family :=
  ⟨toPrimeSupported,
    PrimeSupportedOneUniversalCoverOneSylowFamilyVerification.toFull⟩

end OneUniversalCoverOneSylowFamilyVerification

namespace UniversalCoverInductiveMcKayHypothesis

/-- Family coverage plus verification only at primes dividing each simple
target implies the universal-cover hypothesis. -/
theorem of_primeSupportedFamilyCoverage
    {p : ℕ} [Fact p.Prime]
    {ι : Type w}
    {family : ι → FiniteGroupFamily.{u}}
    (coverage :
      NonabelianFiniteSimpleFamilyCoverage family)
    (verified :
      ∀ i : ι,
        PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
          p (family i)) :
    UniversalCoverInductiveMcKayHypothesis.{u} p :=
  UniversalCoverInductiveMcKayHypothesis.of_familyCoverage
    coverage (fun i ↦ (verified i).toFull)

end UniversalCoverInductiveMcKayHypothesis

namespace QuasisimpleInductiveMcKayHypothesis

/-- Prime-supported family verification also implies the quasisimple input
after the already formalized universal-cover descent. -/
theorem of_primeSupportedUniversalCoverFamilyCoverage
    {p : ℕ} [Fact p.Prime]
    {ι : Type w}
    {family : ι → FiniteGroupFamily.{u}}
    (coverage :
      NonabelianFiniteSimpleFamilyCoverage family)
    (verified :
      ∀ i : ι,
        PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
          p (family i)) :
    QuasisimpleInductiveMcKayHypothesis.{u} p :=
  (UniversalCoverInductiveMcKayHypothesis.of_primeSupportedFamilyCoverage
    coverage verified).toQuasisimple

end QuasisimpleInductiveMcKayHypothesis

/-! ### Concrete simple-group representatives -/

/-- Prime-supported one-cover/one-Sylow verification for concrete simple
group representatives. -/
def PrimeSupportedOneUniversalCoverOneSylowRepresentativeVerification
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
        p ∣ Nat.card (representative i) →
          ∃ (U : Type u) (_ : Group U) (_ : Finite U)
              (_E :
                UniversalCentralExtension
                  U (representative i))
              (P : Sylow p U),
            Nonempty (LocalInductiveMcKayData P)

namespace PrimeSupportedOneUniversalCoverOneSylowRepresentativeVerification

/-- Adding automatic target-prime-absent cases recovers the unfiltered
representative verification. -/
theorem toFull
    {p : ℕ} [Fact p.Prime]
    {ι : Type w}
    {representative : ι → Type u}
    [groupRepresentative :
      ∀ i, Group (representative i)]
    [_finiteRepresentative :
      ∀ i, Finite (representative i)]
    (h :
      PrimeSupportedOneUniversalCoverOneSylowRepresentativeVerification
        p representative) :
    OneUniversalCoverOneSylowRepresentativeVerification
      p representative := by
  intro i hS hnoncomm
  by_cases hp : p ∣ Nat.card (representative i)
  · exact h i hS hnoncomm hp
  · obtain ⟨U, groupU, finiteU, ⟨E⟩⟩ :=
      finite_universalCentralExtension_exists_of_isSimpleGroup
        hS hnoncomm
    letI : Group U := groupU
    letI : Finite U := finiteU
    let P : Sylow p U := default
    exact
      ⟨U, inferInstance, inferInstance, E, P,
        LocalInductiveMcKayData.nonempty_of_sylow_le_center
          P
          (CentralExtension.sylow_le_center_of_prime_not_dvd_card
            E.toCentralExtension P hp)⟩

end PrimeSupportedOneUniversalCoverOneSylowRepresentativeVerification

namespace OneUniversalCoverOneSylowRepresentativeVerification

/-- The unfiltered representative obligation implies its prime-supported
restriction. -/
theorem toPrimeSupported
    {p : ℕ}
    {ι : Type w}
    {representative : ι → Type u}
    [groupRepresentative :
      ∀ i, Group (representative i)]
    [_finiteRepresentative :
      ∀ i, Finite (representative i)]
    (h :
      OneUniversalCoverOneSylowRepresentativeVerification
        p representative) :
    PrimeSupportedOneUniversalCoverOneSylowRepresentativeVerification
      p representative := by
  intro i hS hnoncomm _
  exact h i hS hnoncomm

/-- Exact prime-support reduction for concrete simple representatives. -/
theorem iff_primeSupported
    {p : ℕ} [Fact p.Prime]
    {ι : Type w}
    {representative : ι → Type u}
    [groupRepresentative :
      ∀ i, Group (representative i)]
    [_finiteRepresentative :
      ∀ i, Finite (representative i)] :
    OneUniversalCoverOneSylowRepresentativeVerification
        p representative ↔
      PrimeSupportedOneUniversalCoverOneSylowRepresentativeVerification
        p representative :=
  ⟨toPrimeSupported,
    PrimeSupportedOneUniversalCoverOneSylowRepresentativeVerification.toFull⟩

end OneUniversalCoverOneSylowRepresentativeVerification

namespace UniversalCoverInductiveMcKayHypothesis

/-- Concrete classification representatives need character-theoretic
verification only when `p` divides the representative simple-group order. -/
theorem of_primeSupportedIsomorphismRepresentatives
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
      PrimeSupportedOneUniversalCoverOneSylowRepresentativeVerification
        p representative) :
    UniversalCoverInductiveMcKayHypothesis.{u} p :=
  UniversalCoverInductiveMcKayHypothesis.of_isomorphismRepresentatives
    representative coverage verified.toFull

end UniversalCoverInductiveMcKayHypothesis

/-! ### The three classification families -/

/-- The three CFSG-family verification obligations after removing all
primes absent from the corresponding simple target. -/
def PrimeSupportedCFSGFamilyVerification
    (p : ℕ)
    (alternating lieType sporadic :
      FiniteGroupFamily.{u}) : Prop :=
  PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
      p alternating ∧
    PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p lieType ∧
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p sporadic

namespace PrimeSupportedCFSGFamilyVerification

/-- Prime-supported CFSG-family verification recovers the unfiltered
three-family obligation. -/
theorem toFull
    {p : ℕ} [Fact p.Prime]
    {alternating lieType sporadic :
      FiniteGroupFamily.{u}}
    (h :
      PrimeSupportedCFSGFamilyVerification
        p alternating lieType sporadic) :
    CFSGFamilyVerification p alternating lieType sporadic :=
  ⟨h.1.toFull, h.2.1.toFull, h.2.2.toFull⟩

end PrimeSupportedCFSGFamilyVerification

namespace CFSGFamilyVerification

/-- The ordinary three-family verification restricts to the exact
prime-supported residual. -/
theorem toPrimeSupported
    {p : ℕ}
    {alternating lieType sporadic :
      FiniteGroupFamily.{u}}
    (h : CFSGFamilyVerification p alternating lieType sporadic) :
    PrimeSupportedCFSGFamilyVerification
      p alternating lieType sporadic :=
  ⟨h.1.toPrimeSupported,
    h.2.1.toPrimeSupported,
    h.2.2.toPrimeSupported⟩

/-- Exact prime-support reduction of the three CFSG-family obligations. -/
theorem iff_primeSupported
    {p : ℕ} [Fact p.Prime]
    {alternating lieType sporadic :
      FiniteGroupFamily.{u}} :
    CFSGFamilyVerification p alternating lieType sporadic ↔
      PrimeSupportedCFSGFamilyVerification
        p alternating lieType sporadic :=
  ⟨toPrimeSupported,
    PrimeSupportedCFSGFamilyVerification.toFull⟩

end CFSGFamilyVerification

namespace CFSGFamilyCoverage

/-- CFSG coverage plus character theory only at primes occurring in each
simple target implies the universal-cover input. -/
theorem toUniversalCover_of_primeSupported
    {p : ℕ} [Fact p.Prime]
    {alternating lieType sporadic :
      FiniteGroupFamily.{u}}
    (coverage :
      CFSGFamilyCoverage alternating lieType sporadic)
    (verified :
      PrimeSupportedCFSGFamilyVerification
        p alternating lieType sporadic) :
    UniversalCoverInductiveMcKayHypothesis.{u} p :=
  coverage.toUniversalCover verified.toFull

/-- The same prime-supported CFSG interface implies the quasisimple input. -/
theorem toQuasisimple_of_primeSupported
    {p : ℕ} [Fact p.Prime]
    {alternating lieType sporadic :
      FiniteGroupFamily.{u}}
    (coverage :
      CFSGFamilyCoverage alternating lieType sporadic)
    (verified :
      PrimeSupportedCFSGFamilyVerification
        p alternating lieType sporadic) :
    QuasisimpleInductiveMcKayHypothesis.{u} p :=
  (coverage.toUniversalCover_of_primeSupported verified).toQuasisimple

end CFSGFamilyCoverage

end InductiveMcKay
end McKayConjecture
