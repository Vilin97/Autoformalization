/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import McKayConjecture.InductiveMcKay.UniversalCoverSimpleTargetPrimeSupport

/-!
# Automatic universal-cover family verification

The first character-theoretic input in the CFSG branch is
`PrimeSupportedOneUniversalCoverOneSylowFamilyVerification`.  This file
records two ways in which that family obligation is genuinely vacuous:

* every simple member of the family is commutative; or
* the chosen prime divides the order of no nonabelian simple member.

The first criterion gives unconditional verification of the family.  The
second criterion gives prime-supported verification and hence, using the
already formalized central-Sylow construction, full verification.

Two concrete families are discharged unconditionally: finite solvable
groups and groups with cyclic quotient by their center.  Neither result
asserts any classification or character correspondence for a nonabelian
simple target.
-/

noncomputable section

open scoped IsMulCommutative

universe u

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

namespace FiniteGroupFamily

/-- Every simple member of `family` is commutative. -/
def OnlyCommutativeSimpleMembers
    (family : FiniteGroupFamily.{u}) : Prop :=
  ∀ (S : Type u) [Group S] [Finite S],
    family.Contains S →
      IsSimpleGroup S →
        IsMulCommutative S

/-- No nonabelian simple member of `family` has order divisible by `p`. -/
def HasNoPrimeSupportedNonabelianSimpleMembers
    (p : ℕ) (family : FiniteGroupFamily.{u}) : Prop :=
  ∀ (S : Type u) [Group S] [Finite S],
    family.Contains S →
      IsSimpleGroup S →
        ¬IsMulCommutative S →
          ¬p ∣ Nat.card S

end FiniteGroupFamily

namespace OneUniversalCoverOneSylowFamilyVerification

/-- A family whose simple members are all commutative has no nonabelian
simple target, so its universal-cover verification is unconditional. -/
theorem of_onlyCommutativeSimpleMembers
    {p : ℕ} {family : FiniteGroupFamily.{u}}
    (h : family.OnlyCommutativeSimpleMembers) :
    OneUniversalCoverOneSylowFamilyVerification p family := by
  intro S _ _ hmember hsimple hnoncomm
  exact (hnoncomm (h S hmember hsimple)).elim

end OneUniversalCoverOneSylowFamilyVerification

namespace PrimeSupportedOneUniversalCoverOneSylowFamilyVerification

/-- If no nonabelian simple member has `p` in its order, the exact
prime-supported family obligation is vacuous. -/
theorem of_noPrimeSupportedNonabelianSimpleMembers
    {p : ℕ} {family : FiniteGroupFamily.{u}}
    (h : family.HasNoPrimeSupportedNonabelianSimpleMembers p) :
    PrimeSupportedOneUniversalCoverOneSylowFamilyVerification
      p family := by
  intro S _ _ hmember hsimple hnoncomm hp
  exact (h S hmember hsimple hnoncomm hp).elim

end PrimeSupportedOneUniversalCoverOneSylowFamilyVerification

/-! ### Concrete automatic families -/

/-- The family of finite solvable groups. -/
def solvableFiniteGroupFamily :
    FiniteGroupFamily.{u} where
  member S groupS _ :=
    @Group.IsSolvable S groupS

@[simp]
theorem solvableFiniteGroupFamily_contains_iff
    (S : Type u) [Group S] [Finite S] :
    solvableFiniteGroupFamily.Contains S ↔
      Group.IsSolvable S :=
  Iff.rfl

/-- A finite simple solvable group is commutative. -/
theorem solvableFiniteGroupFamily_onlyCommutativeSimpleMembers :
    solvableFiniteGroupFamily.OnlyCommutativeSimpleMembers := by
  intro S _ _ hsolvable hsimple
  letI : IsSimpleGroup S := hsimple
  exact
    IsMulCommutative.of_comm
      (IsSimpleGroup.comm_iff_isSolvable.mpr hsolvable)

/-- The solvable family has unconditional one-cover/one-Sylow
verification, because it contains no nonabelian simple target. -/
theorem solvableFiniteGroupFamily_verification
    (p : ℕ) :
    OneUniversalCoverOneSylowFamilyVerification
      p solvableFiniteGroupFamily :=
  OneUniversalCoverOneSylowFamilyVerification.of_onlyCommutativeSimpleMembers
    solvableFiniteGroupFamily_onlyCommutativeSimpleMembers

/-- A finite group has cyclic quotient by its center. -/
def HasCyclicCentralQuotient
    (S : Type u) [Group S] [Finite S] : Prop :=
  IsCyclic (S ⧸ Subgroup.center S)

/-- The family of finite groups whose quotient by the center is cyclic. -/
def cyclicCentralQuotientFiniteGroupFamily :
    FiniteGroupFamily.{u} where
  member S groupS finiteS :=
    @HasCyclicCentralQuotient S groupS finiteS

@[simp]
theorem cyclicCentralQuotientFiniteGroupFamily_contains_iff
    (S : Type u) [Group S] [Finite S] :
    cyclicCentralQuotientFiniteGroupFamily.Contains S ↔
      IsCyclic (S ⧸ Subgroup.center S) :=
  Iff.rfl

/-- A group with cyclic quotient by its center is commutative. -/
theorem cyclicCentralQuotientFiniteGroupFamily_onlyCommutativeSimpleMembers :
    cyclicCentralQuotientFiniteGroupFamily.OnlyCommutativeSimpleMembers := by
  intro S _ _ hcyclic _
  letI : IsCyclic (S ⧸ Subgroup.center S) := hcyclic
  exact isMulCommutative_of_isCyclic_quotient_center_self S

/-- The cyclic-central-quotient family has unconditional
one-cover/one-Sylow verification. -/
theorem cyclicCentralQuotientFiniteGroupFamily_verification
    (p : ℕ) :
    OneUniversalCoverOneSylowFamilyVerification
      p cyclicCentralQuotientFiniteGroupFamily :=
  OneUniversalCoverOneSylowFamilyVerification.of_onlyCommutativeSimpleMembers
    cyclicCentralQuotientFiniteGroupFamily_onlyCommutativeSimpleMembers

end InductiveMcKay
end McKayConjecture
