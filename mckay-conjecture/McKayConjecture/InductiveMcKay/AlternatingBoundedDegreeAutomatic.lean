/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingUniversalCoverPrimeSupport
import McKayConjecture.InductiveMcKay.UniversalCoverAutomaticFamilies

/-!
# Automatic bounded-degree alternating families

For a fixed prime `p`, the alternating targets of degree strictly below
`p` have order prime to `p`.  Their universal-cover local data are therefore
canonical: every Sylow `p`-subgroup of the cover lies in its center.

This file packages that observation at the family level.  It gives:

* unconditional verification of all alternating simple groups of degree at
  most `m` whenever `m < p`;
* the concrete `A₅` case for every prime `p > 5`; and
* an exact family-level reduction of the full alternating obligation to
  alternating groups of degree at least `p`.

No local data are constructed here for `A_m` when `p ≤ m`; that is the
first genuinely character-theoretic alternating-family boundary.
-/

noncomputable section

open scoped IsMulCommutative

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory
open PrimeSupportedOneUniversalCoverOneSylowFamilyVerification

/-- `S` is isomorphic to an alternating simple group `A_{n+5}` whose
degree is at most `m`. -/
def IsAlternatingSimpleGroupUpTo
    (m : ℕ) (S : Type) [Group S] [Finite S] : Prop :=
  ∃ n : ℕ,
    n + 5 ≤ m ∧
      Nonempty
        (S ≃* alternatingGroup (Fin (n + 5)))

/-- The concrete family of alternating simple groups of degree at most
`m`. -/
def alternatingSimpleGroupFamilyUpTo
    (m : ℕ) : FiniteGroupFamily.{0} where
  member S groupS finiteS :=
    @IsAlternatingSimpleGroupUpTo m S groupS finiteS

@[simp]
theorem alternatingSimpleGroupFamilyUpTo_contains_iff
    (m : ℕ) (S : Type) [Group S] [Finite S] :
    (alternatingSimpleGroupFamilyUpTo m).Contains S ↔
      IsAlternatingSimpleGroupUpTo m S :=
  Iff.rfl

/-- Bounded-degree alternating-family membership is invariant under group
isomorphism. -/
theorem alternatingSimpleGroupFamilyUpTo_isIsomorphismInvariant
    (m : ℕ) :
    (alternatingSimpleGroupFamilyUpTo m).IsIsomorphismInvariant := by
  intro S T _ _ _ _ ⟨e⟩
  constructor
  · rintro ⟨n, hn, ⟨f⟩⟩
    exact ⟨n, hn, ⟨e.symm.trans f⟩⟩
  · rintro ⟨n, hn, ⟨f⟩⟩
    exact ⟨n, hn, ⟨e.trans f⟩⟩

/-- `S` is isomorphic to an alternating simple group `A_{n+5}` whose
degree is at least `m`. -/
def IsAlternatingSimpleGroupAtLeast
    (m : ℕ) (S : Type) [Group S] [Finite S] : Prop :=
  ∃ n : ℕ,
    m ≤ n + 5 ∧
      Nonempty
        (S ≃* alternatingGroup (Fin (n + 5)))

/-- The concrete family of alternating simple groups of degree at least
`m`. -/
def alternatingSimpleGroupFamilyAtLeast
    (m : ℕ) : FiniteGroupFamily.{0} where
  member S groupS finiteS :=
    @IsAlternatingSimpleGroupAtLeast m S groupS finiteS

@[simp]
theorem alternatingSimpleGroupFamilyAtLeast_contains_iff
    (m : ℕ) (S : Type) [Group S] [Finite S] :
    (alternatingSimpleGroupFamilyAtLeast m).Contains S ↔
      IsAlternatingSimpleGroupAtLeast m S :=
  Iff.rfl

/-- The degree-at-least family is invariant under group isomorphism. -/
theorem alternatingSimpleGroupFamilyAtLeast_isIsomorphismInvariant
    (m : ℕ) :
    (alternatingSimpleGroupFamilyAtLeast m).IsIsomorphismInvariant := by
  intro S T _ _ _ _ ⟨e⟩
  constructor
  · rintro ⟨n, hn, ⟨f⟩⟩
    exact ⟨n, hn, ⟨e.symm.trans f⟩⟩
  · rintro ⟨n, hn, ⟨f⟩⟩
    exact ⟨n, hn, ⟨e.trans f⟩⟩

/-- If `m < p`, no nonabelian simple member of the bounded alternating
family has order divisible by `p`. -/
theorem alternatingSimpleGroupFamilyUpTo_hasNoPrimeSupportedMembers
    {p m : ℕ} [Fact p.Prime]
    (hmp : m < p) :
    (alternatingSimpleGroupFamilyUpTo m)
      |>.HasNoPrimeSupportedNonabelianSimpleMembers p := by
  intro S _ _ hmember _ _ hp
  obtain ⟨n, hdegree, ⟨e⟩⟩ := hmember
  have hpRepresentative :
      p ∣ Nat.card (alternatingGroup (Fin (n + 5))) := by
    have hcard :
        Nat.card S =
          Nat.card (alternatingGroup (Fin (n + 5))) :=
      Nat.card_congr e.toEquiv
    exact hcard ▸ hp
  have hpDegree : p ≤ n + 5 :=
    (prime_dvd_natCard_alternatingRepresentative_iff n).mp
      hpRepresentative
  omega

/-- The exact prime-supported obligation for bounded-degree alternating
groups is vacuous when the bound is below `p`. -/
theorem alternatingSimpleGroupFamilyUpTo_primeSupportedVerification
    {p m : ℕ} [Fact p.Prime]
    (hmp : m < p) :
    PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
      p (alternatingSimpleGroupFamilyUpTo m) :=
  of_noPrimeSupportedNonabelianSimpleMembers
    (alternatingSimpleGroupFamilyUpTo_hasNoPrimeSupportedMembers hmp)

/-- Full universal-cover verification for every bounded-degree
alternating simple group when `m < p`.  In the prime-absent case,
`toFull` chooses a finite universal cover and constructs its canonical
central-Sylow local datum. -/
theorem alternatingSimpleGroupFamilyUpTo_verification
    {p m : ℕ} [Fact p.Prime]
    (hmp : m < p) :
    OneUniversalCoverOneSylowFamilyVerification
      p (alternatingSimpleGroupFamilyUpTo m) :=
  (alternatingSimpleGroupFamilyUpTo_primeSupportedVerification hmp).toFull

/-! ### The first concrete simple group -/

/-- The `A₅` family, expressed as the bounded alternating family at
degree five. -/
abbrev alternatingFiveSimpleGroupFamily :
    FiniteGroupFamily.{0} :=
  alternatingSimpleGroupFamilyUpTo 5

/-- Membership in the bounded family at degree five is exactly
isomorphism to `A₅`. -/
theorem alternatingFiveSimpleGroupFamily_contains_iff
    (S : Type) [Group S] [Finite S] :
    alternatingFiveSimpleGroupFamily.Contains S ↔
      Nonempty (S ≃* alternatingGroup (Fin 5)) := by
  constructor
  · rintro ⟨n, hn, hS⟩
    have hnZero : n = 0 := by omega
    subst n
    simpa using hS
  · intro hS
    exact ⟨0, by omega, by simpa using hS⟩

/-- The `A₅` universal-cover family is completely verified at every prime
strictly greater than five. -/
theorem alternatingFiveSimpleGroupFamily_verification
    {p : ℕ} [Fact p.Prime]
    (hfive : 5 < p) :
    OneUniversalCoverOneSylowFamilyVerification
      p alternatingFiveSimpleGroupFamily :=
  alternatingSimpleGroupFamilyUpTo_verification hfive

/-! ### Exact residual alternating family -/

/-- Prime-supported verification of the full alternating family restricts
to the concrete family of degrees at least `p`. -/
theorem PrimeSupportedOneUniversalCoverOneSylowFamilyVerification.toAlternatingAtLeastPrime
    {p : ℕ} [Fact p.Prime]
    (h :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p alternatingSimpleGroupFamily.{0}) :
    PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
      p (alternatingSimpleGroupFamilyAtLeast p) := by
  intro S _ _ hmember hsimple hnoncomm hp
  obtain ⟨n, _, hS⟩ := hmember
  exact h S ⟨n, hS⟩ hsimple hnoncomm hp

/-- Conversely, at a prime-supported alternating target the order formula
forces the degree to be at least `p`, so verification of that residual
family suffices for the whole alternating family. -/
theorem PrimeSupportedOneUniversalCoverOneSylowFamilyVerification.of_alternatingAtLeastPrime
    {p : ℕ} [Fact p.Prime]
    (h :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p (alternatingSimpleGroupFamilyAtLeast p)) :
    PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
      p alternatingSimpleGroupFamily.{0} := by
  intro S _ _ hmember hsimple hnoncomm hp
  obtain ⟨n, ⟨e⟩⟩ := hmember
  have hpRepresentative :
      p ∣ Nat.card (alternatingGroup (Fin (n + 5))) := by
    have hcard :
        Nat.card S =
          Nat.card (alternatingGroup (Fin (n + 5))) :=
      Nat.card_congr e.toEquiv
    exact hcard ▸ hp
  have hpDegree : p ≤ n + 5 :=
    (prime_dvd_natCard_alternatingRepresentative_iff n).mp
      hpRepresentative
  exact h S ⟨n, hpDegree, ⟨e⟩⟩ hsimple hnoncomm hp

/-- The exact prime-supported alternating-family obligation is equivalent
to verification of alternating groups whose degree is at least `p`. -/
theorem primeSupportedAlternatingFamilyVerification_iff_atLeastPrime
    {p : ℕ} [Fact p.Prime] :
    PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p alternatingSimpleGroupFamily.{0} ↔
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p (alternatingSimpleGroupFamilyAtLeast p) :=
  ⟨fun h ↦ h.toAlternatingAtLeastPrime,
    fun h ↦ h.of_alternatingAtLeastPrime⟩

/-- Verification only on alternating groups of degree at least `p`
constructs the full one-cover/one-Sylow verification for every alternating
simple group. -/
theorem alternatingSimpleGroupFamily_verification_of_atLeastPrime
    {p : ℕ} [Fact p.Prime]
    (h :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p (alternatingSimpleGroupFamilyAtLeast p)) :
    OneUniversalCoverOneSylowFamilyVerification
      p alternatingSimpleGroupFamily.{0} :=
  h.of_alternatingAtLeastPrime.toFull

end InductiveMcKay
end McKayConjecture
