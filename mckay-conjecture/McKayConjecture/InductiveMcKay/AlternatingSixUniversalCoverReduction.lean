/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSylowFiveNormalizer
import McKayConjecture.InductiveMcKay.AlternatingBeyondFiveUniversalCover

/-!
# Isolating the `A₆` universal-cover obligation

The completed `A₅` computation leaves alternating groups of degree at least
six.  This file separates the first remaining group, `A₆`, from degrees at
least seven and fixes all non-character-theoretic choices for that case.

For `A₆`, verification on an arbitrary universal cover and arbitrary Sylow
subgroup is equivalent to full local data on one fixed Sylow subgroup of the
canonical finite free-presentation cover.  Since `|A₆| = 360`, this datum is
automatic away from `p = 2, 3, 5`.  Thus the first alternating case requires
exactly three local character-theoretic computations, one at each of those
primes.

No Schur-multiplier value, concrete `6.A₆` model, or character table is
asserted here.
-/

noncomputable section

open scoped IsMulCommutative

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-! ### The exact `A₆` family -/

/-- A finite group is in the `A₆` family when it is isomorphic to the
concrete six-point alternating group. -/
def IsAlternatingSixSimpleGroup
    (S : Type) [Group S] [Finite S] : Prop :=
  Nonempty (S ≃* AlternatingSix)

/-- The single-isomorphism-class family consisting of `A₆`. -/
def alternatingSixSimpleGroupFamily :
    FiniteGroupFamily.{0} where
  member S groupS finiteS :=
    @IsAlternatingSixSimpleGroup S groupS finiteS

@[simp]
theorem alternatingSixSimpleGroupFamily_contains_iff
    (S : Type) [Group S] [Finite S] :
    alternatingSixSimpleGroupFamily.Contains S ↔
      Nonempty (S ≃* AlternatingSix) :=
  Iff.rfl

/-- The exact `A₆` family is invariant under group isomorphism. -/
theorem alternatingSixSimpleGroupFamily_isIsomorphismInvariant :
    alternatingSixSimpleGroupFamily.IsIsomorphismInvariant := by
  intro S T _ _ _ _ ⟨e⟩
  constructor
  · rintro ⟨f⟩
    exact ⟨e.symm.trans f⟩
  · rintro ⟨f⟩
    exact ⟨e.trans f⟩

/-! ### One fixed cover and one fixed Sylow subgroup -/

/-- The remaining local datum at `p` on the fixed canonical universal cover
of `A₆`. -/
def AlternatingSixCanonicalCoverVerification
    (p : ℕ) : Prop :=
  Nonempty
    (LocalInductiveMcKayData
      (alternatingSixUniversalCoverSylow p))

namespace AlternatingSixCanonicalCoverVerification

/-- Local data on the fixed canonical cover supply the ordinary one-cover,
one-Sylow verification for the `A₆` isomorphism class. -/
theorem toFamily
    {p : ℕ}
    (h : AlternatingSixCanonicalCoverVerification p) :
    OneUniversalCoverOneSylowFamilyVerification
      p alternatingSixSimpleGroupFamily := by
  intro S _ _ hmember _ _
  obtain ⟨e⟩ := hmember
  exact
    ⟨AlternatingSixUniversalCover,
      inferInstance, inferInstance,
      alternatingSixUniversalCentralExtension.targetEquiv e.symm,
      alternatingSixUniversalCoverSylow p, h⟩

/-- Local data on the fixed canonical cover also supply the
prime-supported family interface. -/
theorem toPrimeSupportedFamily
    {p : ℕ}
    (h : AlternatingSixCanonicalCoverVerification p) :
    PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
      p alternatingSixSimpleGroupFamily :=
  h.toFamily.toPrimeSupported

/-- At a prime not dividing `|A₆|`, the fixed Sylow subgroup lies in the
central kernel and has canonical local data. -/
theorem of_prime_not_dvd_order
    {p : ℕ} [Fact p.Prime]
    (hp : ¬p ∣ Nat.card AlternatingSix) :
    AlternatingSixCanonicalCoverVerification p :=
  LocalInductiveMcKayData.nonempty_of_sylow_le_center
    (alternatingSixUniversalCoverSylow p)
    (CentralExtension.sylow_le_center_of_prime_not_dvd_card
      alternatingSixUniversalCentralExtension.toCentralExtension
      (alternatingSixUniversalCoverSylow p) hp)

/-- Consequently the fixed-cover datum is automatic away from the three
primes dividing `360`. -/
theorem of_not_two_three_five
    {p : ℕ} [Fact p.Prime]
    (hpTwo : p ≠ 2)
    (hpThree : p ≠ 3)
    (hpFive : p ≠ 5) :
    AlternatingSixCanonicalCoverVerification p := by
  apply of_prime_not_dvd_order
  intro hp
  rcases
      prime_dvd_natCard_alternatingSix_iff.mp hp with
    h | h | h
  · exact hpTwo h
  · exact hpThree h
  · exact hpFive h

end AlternatingSixCanonicalCoverVerification

namespace OneUniversalCoverOneSylowFamilyVerification

/-- Conversely, any one-cover verification of the `A₆` family transports
back to the fixed free-presentation cover and fixed Sylow subgroup. -/
theorem toAlternatingSixCanonicalCover
    {p : ℕ} [Fact p.Prime]
    (h :
      OneUniversalCoverOneSylowFamilyVerification
        p alternatingSixSimpleGroupFamily) :
    AlternatingSixCanonicalCoverVerification p :=
  h.localData_on_every_universalCover
    AlternatingSix ⟨MulEquiv.refl _⟩
    (inferInstance : IsSimpleGroup AlternatingSix)
    alternatingSix_not_isMulCommutative
    AlternatingSixUniversalCover
    alternatingSixUniversalCentralExtension
    (alternatingSixUniversalCoverSylow p)

/-- The ordinary `A₆` family obligation is exactly local data on the fixed
cover and fixed Sylow subgroup. -/
theorem alternatingSixFamilyVerification_iff_canonicalCover
    {p : ℕ} [Fact p.Prime] :
    OneUniversalCoverOneSylowFamilyVerification
        p alternatingSixSimpleGroupFamily ↔
      AlternatingSixCanonicalCoverVerification p :=
  ⟨toAlternatingSixCanonicalCover,
    AlternatingSixCanonicalCoverVerification.toFamily⟩

end OneUniversalCoverOneSylowFamilyVerification

namespace PrimeSupportedOneUniversalCoverOneSylowFamilyVerification

/-- The prime-supported `A₆` family obligation is also equivalent to the
fixed-cover datum.  For primes absent from `|A₆|`, both sides are automatic. -/
theorem alternatingSixFamilyVerification_iff_canonicalCover
    {p : ℕ} [Fact p.Prime] :
    PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p alternatingSixSimpleGroupFamily ↔
      AlternatingSixCanonicalCoverVerification p := by
  constructor
  · intro h
    exact h.toFull.toAlternatingSixCanonicalCover
  · exact
      AlternatingSixCanonicalCoverVerification.toPrimeSupportedFamily

end PrimeSupportedOneUniversalCoverOneSylowFamilyVerification

/-! ### The three exceptional primes -/

/-- The exact three fixed-cover local computations left for `A₆`. -/
structure AlternatingSixExceptionalPrimeLocalData : Prop where
  /-- Full local data on a fixed Sylow `2`-subgroup of the canonical cover. -/
  atTwo : AlternatingSixCanonicalCoverVerification 2
  /-- Full local data on a fixed Sylow `3`-subgroup of the canonical cover. -/
  atThree : AlternatingSixCanonicalCoverVerification 3
  /-- Full local data on a fixed Sylow `5`-subgroup of the canonical cover. -/
  atFive : AlternatingSixCanonicalCoverVerification 5

namespace AlternatingSixExceptionalPrimeLocalData

/-- Bundling the three fixed-cover data is equivalent to verifying the
prime-supported `A₆` family separately at `2`, `3`, and `5`. -/
theorem iff_primeSupportedFamilyVerifications :
    AlternatingSixExceptionalPrimeLocalData ↔
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
          2 alternatingSixSimpleGroupFamily ∧
        PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
            3 alternatingSixSimpleGroupFamily ∧
          PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
            5 alternatingSixSimpleGroupFamily := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  constructor
  · intro d
    exact
      ⟨d.atTwo.toPrimeSupportedFamily,
        d.atThree.toPrimeSupportedFamily,
        d.atFive.toPrimeSupportedFamily⟩
  · rintro ⟨hTwo, hThree, hFive⟩
    exact
      ⟨hTwo.toFull.toAlternatingSixCanonicalCover,
        hThree.toFull.toAlternatingSixCanonicalCover,
        hFive.toFull.toAlternatingSixCanonicalCover⟩

/-- The three exceptional computations give fixed-cover local data at every
prime; all other primes use the central-Sylow construction. -/
theorem canonicalCoverVerification
    (d : AlternatingSixExceptionalPrimeLocalData)
    (p : ℕ) [Fact p.Prime] :
    AlternatingSixCanonicalCoverVerification p := by
  by_cases hpTwo : p = 2
  · subst p
    exact d.atTwo
  by_cases hpThree : p = 3
  · subst p
    exact d.atThree
  by_cases hpFive : p = 5
  · subst p
    exact d.atFive
  exact
    AlternatingSixCanonicalCoverVerification.of_not_two_three_five
      hpTwo hpThree hpFive

/-- The three computations verify the `A₆` family at every prime. -/
theorem familyVerification
    (d : AlternatingSixExceptionalPrimeLocalData)
    (p : ℕ) [Fact p.Prime] :
    OneUniversalCoverOneSylowFamilyVerification
      p alternatingSixSimpleGroupFamily :=
  (d.canonicalCoverVerification p).toFamily

/-- The three computations give local data on every finite universal cover
of `A₆` and every Sylow subgroup. -/
theorem localData_on_every_universalCover
    (d : AlternatingSixExceptionalPrimeLocalData)
    (p : ℕ) [Fact p.Prime]
    (U : Type) [Group U] [Finite U]
    (E : UniversalCentralExtension U AlternatingSix)
    (P : Sylow p U) :
    Nonempty (LocalInductiveMcKayData P) :=
  (d.familyVerification p).localData_on_every_universalCover
    AlternatingSix ⟨MulEquiv.refl _⟩
    (inferInstance : IsSimpleGroup AlternatingSix)
    alternatingSix_not_isMulCommutative
    U E P

end AlternatingSixExceptionalPrimeLocalData

/-! ### Splitting the residual alternating family at degree six -/

namespace PrimeSupportedOneUniversalCoverOneSylowFamilyVerification

/-- Restriction of the degree-at-least-six obligation to `A₆`. -/
theorem toAlternatingSix
    {p : ℕ}
    (h :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p (alternatingSimpleGroupFamilyAtLeast 6)) :
    PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
      p alternatingSixSimpleGroupFamily := by
  intro S _ _ ⟨e⟩ hsimple hnoncomm hp
  exact
    h S ⟨1, by omega, by simpa [AlternatingSix] using
      (show Nonempty (S ≃* AlternatingSix) from ⟨e⟩)⟩
      hsimple hnoncomm hp

/-- Restriction of the degree-at-least-six obligation to degrees at least
seven. -/
theorem toAlternatingAtLeastSeven
    {p : ℕ}
    (h :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p (alternatingSimpleGroupFamilyAtLeast 6)) :
    PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
      p (alternatingSimpleGroupFamilyAtLeast 7) := by
  intro S _ _ ⟨n, hn, hS⟩ hsimple hnoncomm hp
  exact h S ⟨n, by omega, hS⟩ hsimple hnoncomm hp

/-- Verification of `A₆` and of all alternating groups of degree at least
seven reconstructs the degree-at-least-six obligation. -/
theorem of_alternatingSix_and_atLeastSeven
    {p : ℕ}
    (hSix :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p alternatingSixSimpleGroupFamily)
    (hSeven :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p (alternatingSimpleGroupFamilyAtLeast 7)) :
    PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
      p (alternatingSimpleGroupFamilyAtLeast 6) := by
  intro S _ _ ⟨n, hn, hS⟩ hsimple hnoncomm hp
  by_cases hnOne : n = 1
  · subst n
    exact
      hSix S (by simpa [AlternatingSix] using hS)
        hsimple hnoncomm hp
  · exact
      hSeven S ⟨n, by omega, hS⟩
        hsimple hnoncomm hp

/-- Exact next-case split: after the completed `A₅` case, the remaining
alternating input is one fixed-cover `A₆` datum plus the family of degrees
at least seven. -/
theorem alternatingAtLeastSixVerification_iff_canonicalSix_and_atLeastSeven
    {p : ℕ} [Fact p.Prime] :
    PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p (alternatingSimpleGroupFamilyAtLeast 6) ↔
      AlternatingSixCanonicalCoverVerification p ∧
        PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
          p (alternatingSimpleGroupFamilyAtLeast 7) := by
  constructor
  · intro h
    exact
      ⟨(alternatingSixFamilyVerification_iff_canonicalCover).mp
          h.toAlternatingSix,
        h.toAlternatingAtLeastSeven⟩
  · rintro ⟨hSix, hSeven⟩
    exact
      of_alternatingSix_and_atLeastSeven
        ((alternatingSixFamilyVerification_iff_canonicalCover).mpr hSix)
        hSeven

end PrimeSupportedOneUniversalCoverOneSylowFamilyVerification

/-- With the completed `A₅` tables already installed, a fixed-cover `A₆`
datum and verification in degrees at least seven give the full alternating
family input at the chosen prime. -/
theorem alternatingSimpleGroupFamily_verification_of_canonicalSix_and_atLeastSeven
    {p : ℕ} [Fact p.Prime]
    (hSix : AlternatingSixCanonicalCoverVerification p)
    (hSeven :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p (alternatingSimpleGroupFamilyAtLeast 7)) :
    OneUniversalCoverOneSylowFamilyVerification.{0}
      p alternatingSimpleGroupFamily := by
  have hAtLeastSix :
      PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
        p (alternatingSimpleGroupFamilyAtLeast 6) :=
    hSix.toPrimeSupportedFamily
      |>.of_alternatingSix_and_atLeastSeven hSeven
  exact hAtLeastSix.of_alternatingAtLeastSix.toFull

end InductiveMcKay
end McKayConjecture
