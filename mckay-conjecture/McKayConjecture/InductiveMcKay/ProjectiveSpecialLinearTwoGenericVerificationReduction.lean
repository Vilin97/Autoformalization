/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.ProjectiveSpecialLinearTwoOrderFourAlternatingFive

/-!
# Three-branch verification reduction for the simple PSL₂ family

The representative-level local-data obligation splits exhaustively into
field orders four, nine, and the generic branch.  On the generic branch,
central closedness of `SL(2,q)` upgrades the special-linear quotient map to
a universal central extension.  Consequently one local datum on one Sylow
subgroup of that special-linear cover suffices.

The two exceptional branches remain explicit inputs.  In particular, this
file does not assert the missing identifications with `A₅` and `A₆`, generic
central closedness, or any local inductive-McKay datum.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-! ### The three representative-level branches -/

/-- Representative verification restricted to the field-order-four
branch. -/
def ProjectiveSpecialLinearTwoOrderFourRepresentativeVerification
    (p : ℕ) : Prop :=
  ∀ a : ProjectiveSpecialLinearTwoOrderFourParameter,
    ProjectiveSpecialLinearTwoRepresentativeVerification p a.1

/-- Representative verification restricted to the field-order-nine
branch. -/
def ProjectiveSpecialLinearTwoOrderNineRepresentativeVerification
    (p : ℕ) : Prop :=
  ∀ a : ProjectiveSpecialLinearTwoOrderNineParameter,
    ProjectiveSpecialLinearTwoRepresentativeVerification p a.1

/-- Representative verification restricted to the generic branch. -/
def ProjectiveSpecialLinearTwoGenericRepresentativeVerification
    (p : ℕ) : Prop :=
  ∀ a : ProjectiveSpecialLinearTwoGenericParameter,
    ProjectiveSpecialLinearTwoRepresentativeVerification p a.1

/-- The full representative-family obligation is exactly the conjunction
of its two exceptional branches and its generic branch. -/
theorem
    projectiveSpecialLinearTwoRepresentativeFamilyVerification_iff_branches
    (p : ℕ) :
    ProjectiveSpecialLinearTwoRepresentativeFamilyVerification p ↔
      ProjectiveSpecialLinearTwoOrderFourRepresentativeVerification p ∧
        ProjectiveSpecialLinearTwoOrderNineRepresentativeVerification p ∧
          ProjectiveSpecialLinearTwoGenericRepresentativeVerification p := by
  constructor
  · intro verified
    exact
      ⟨fun a ↦ verified a.1,
        fun a ↦ verified a.1,
        fun a ↦ verified a.1⟩
  · rintro ⟨orderFour, orderNine, generic⟩ a
    rcases projectiveSpecialLinearTwoParameter_trichotomy a with
      hFour | hNine | hGeneric
    · exact orderFour ⟨a, hFour⟩
    · exact orderNine ⟨a, hNine⟩
    · exact generic ⟨a, hGeneric⟩

/-! ### Discharging the generic branch on the special-linear cover -/

/-- The explicit remaining character-theoretic input on the generic
branch: one Sylow subgroup of `SL(2,q)` carrying local inductive-McKay
data, for every generic parameter. -/
def ProjectiveSpecialLinearTwoGenericSpecialLinearLocalData
    (p : ℕ) : Prop :=
  ∀ a : ProjectiveSpecialLinearTwoGenericParameter,
    ∃ P : Sylow p
        (projectiveSpecialLinearTwoSpecialLinearCover a.1),
      Nonempty (LocalInductiveMcKayData P)

/-- Generic central closedness and the explicit special-linear local-data
input supply representative verification throughout the generic branch. -/
theorem
    projectiveSpecialLinearTwoGenericRepresentativeVerification_of_centrallyClosed_localData
    (p : ℕ)
    (hClosed :
      ProjectiveSpecialLinearTwoGenericCentrallyClosedResidual)
    (hLocal :
      ProjectiveSpecialLinearTwoGenericSpecialLinearLocalData p) :
    ProjectiveSpecialLinearTwoGenericRepresentativeVerification p := by
  intro a
  obtain ⟨P, hP⟩ := hLocal a
  exact
    ⟨projectiveSpecialLinearTwoSpecialLinearCover a.1,
      inferInstance,
      projectiveSpecialLinearTwoSpecialLinearCover_finite a.1,
      hClosed.universalCentralExtension a,
      P,
      hP⟩

/-- Assembly of the complete representative-family verification from the
two explicit exceptional inputs and the generic cover/local-data inputs. -/
theorem
    projectiveSpecialLinearTwoRepresentativeFamilyVerification_of_branches
    (p : ℕ)
    (orderFour :
      ProjectiveSpecialLinearTwoOrderFourRepresentativeVerification p)
    (orderNine :
      ProjectiveSpecialLinearTwoOrderNineRepresentativeVerification p)
    (hClosed :
      ProjectiveSpecialLinearTwoGenericCentrallyClosedResidual)
    (hLocal :
      ProjectiveSpecialLinearTwoGenericSpecialLinearLocalData p) :
    ProjectiveSpecialLinearTwoRepresentativeFamilyVerification p :=
  (projectiveSpecialLinearTwoRepresentativeFamilyVerification_iff_branches
    p).2
      ⟨orderFour, orderNine,
        projectiveSpecialLinearTwoGenericRepresentativeVerification_of_centrallyClosed_localData
          p hClosed hLocal⟩

/-- The field-order-four branch is already closed by the faithful
five-point action and the completed `A₅` family verification.  Thus only
the order-nine branch and the two generic inputs remain. -/
theorem
    projectiveSpecialLinearTwoRepresentativeFamilyVerification_of_orderNine_generic
    (p : ℕ) [Fact p.Prime]
    (orderNine :
      ProjectiveSpecialLinearTwoOrderNineRepresentativeVerification p)
    (hClosed :
      ProjectiveSpecialLinearTwoGenericCentrallyClosedResidual)
    (hLocal :
      ProjectiveSpecialLinearTwoGenericSpecialLinearLocalData p) :
    ProjectiveSpecialLinearTwoRepresentativeFamilyVerification p :=
  projectiveSpecialLinearTwoRepresentativeFamilyVerification_of_branches
    p
    (projectiveSpecialLinearTwoOrderFourRepresentativeVerification p)
    orderNine hClosed hLocal

/-- Once the three branches are discharged, the existing family transport
supplies local data on every universal cover and every Sylow subgroup of
every isomorphic PSL₂ family member. -/
theorem
    projectiveSpecialLinearTwoLocalData_on_every_universalCover_of_branches
    (p : ℕ) [Fact p.Prime]
    (orderFour :
      ProjectiveSpecialLinearTwoOrderFourRepresentativeVerification p)
    (orderNine :
      ProjectiveSpecialLinearTwoOrderNineRepresentativeVerification p)
    (hClosed :
      ProjectiveSpecialLinearTwoGenericCentrallyClosedResidual)
    (hLocal :
      ProjectiveSpecialLinearTwoGenericSpecialLinearLocalData p)
    (S : Type) [Group S] [Finite S]
    (hS : projectiveSpecialLinearTwoSimpleGroupFamily.Contains S)
    (V : Type) [Group V] [Finite V]
    (F : UniversalCentralExtension V S)
    (Q : Sylow p V) :
    Nonempty (LocalInductiveMcKayData Q) :=
  (projectiveSpecialLinearTwoRepresentativeFamilyVerification_of_branches
    p orderFour orderNine hClosed hLocal).localData_on_every_universalCover
      S hS V F Q

/-- With the order-four branch discharged by `A₅`, the order-nine and
generic inputs supply local data on every universal cover and Sylow
subgroup in the simple `PSL₂` family. -/
theorem
    projectiveSpecialLinearTwoLocalData_on_every_universalCover_of_orderNine_generic
    (p : ℕ) [Fact p.Prime]
    (orderNine :
      ProjectiveSpecialLinearTwoOrderNineRepresentativeVerification p)
    (hClosed :
      ProjectiveSpecialLinearTwoGenericCentrallyClosedResidual)
    (hLocal :
      ProjectiveSpecialLinearTwoGenericSpecialLinearLocalData p)
    (S : Type) [Group S] [Finite S]
    (hS : projectiveSpecialLinearTwoSimpleGroupFamily.Contains S)
    (V : Type) [Group V] [Finite V]
    (F : UniversalCentralExtension V S)
    (Q : Sylow p V) :
    Nonempty (LocalInductiveMcKayData Q) :=
  (projectiveSpecialLinearTwoRepresentativeFamilyVerification_of_orderNine_generic
    p orderNine hClosed hLocal).localData_on_every_universalCover
      S hS V F Q

end InductiveMcKay
end McKayConjecture
