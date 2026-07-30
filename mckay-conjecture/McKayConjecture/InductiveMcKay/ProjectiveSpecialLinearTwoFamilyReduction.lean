/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.ProjectiveSpecialLinearTwoSimpleFamily

/-!
# Universal-cover reduction for the simple PSL₂ family

This file supplies the semantic layer between the concrete representatives

`PSL(2, GaloisField p n)`

and the abstract one-universal-cover/one-Sylow family interface.  It proves
that every member of the isomorphism-closed family is simple and
noncommutative, and isolates the remaining character-theoretic obligation
as an explicit predicate on each parameter.

No local inductive-McKay datum is asserted here.  The only result is a
transport theorem: if such data are supplied for one cover and one Sylow
subgroup of every canonical representative, then they supply the
corresponding family verification.
-/

noncomputable section

open scoped IsMulCommutative

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-! ### Semantic properties of arbitrary family members -/

/-- Every member of the simple PSL₂ family is simple. -/
theorem projectiveSpecialLinearTwoSimpleGroupFamily_member_isSimpleGroup
    (S : Type) [Group S] [Finite S]
    (hS : projectiveSpecialLinearTwoSimpleGroupFamily.Contains S) :
    IsSimpleGroup S := by
  obtain ⟨a, ⟨e⟩⟩ := hS
  letI :
      IsSimpleGroup (projectiveSpecialLinearTwoRepresentative a) :=
    projectiveSpecialLinearTwoRepresentative_isSimpleGroup a
  exact e.isSimpleGroup

/-- Every member of the simple PSL₂ family is perfect.  This intermediate
transport lemma makes the proof of noncommutativity independent of a
pointwise calculation with the chosen isomorphism. -/
theorem projectiveSpecialLinearTwoSimpleGroupFamily_member_isPerfect
    (S : Type) [Group S] [Finite S]
    (hS : projectiveSpecialLinearTwoSimpleGroupFamily.Contains S) :
    Group.IsPerfect S := by
  obtain ⟨a, ⟨e⟩⟩ := hS
  letI :
      Group.IsPerfect
        (projectiveSpecialLinearTwoRepresentative a) :=
    projectiveSpecialLinearTwoRepresentative_isPerfect a
  exact
    Group.IsPerfect.ofSurjective
      (f := e.symm.toMonoidHom) e.symm.surjective

/-- Every member of the simple PSL₂ family is noncommutative. -/
theorem
    projectiveSpecialLinearTwoSimpleGroupFamily_member_not_isMulCommutative
    (S : Type) [Group S] [Finite S]
    (hS : projectiveSpecialLinearTwoSimpleGroupFamily.Contains S) :
    ¬IsMulCommutative S := by
  letI : IsSimpleGroup S :=
    projectiveSpecialLinearTwoSimpleGroupFamily_member_isSimpleGroup S hS
  letI : Group.IsPerfect S :=
    projectiveSpecialLinearTwoSimpleGroupFamily_member_isPerfect S hS
  exact Group.IsPerfect.not_isMulCommutative S

/-! ### The explicit representative-level verification obligation -/

/-- The local character-theoretic obligation for one canonical
`PSL(2, p^n)` representative: exhibit one finite universal cover, one Sylow
`p`-subgroup of that cover, and local inductive-McKay data on it.

This is deliberately a predicate rather than an asserted theorem. -/
def ProjectiveSpecialLinearTwoRepresentativeVerification
    (p : ℕ)
    (a : ProjectiveSpecialLinearTwoSimpleParameter) : Prop :=
  ∃ (U : Type) (_ : Group U) (_ : Finite U)
      (_E :
        UniversalCentralExtension
          U (projectiveSpecialLinearTwoRepresentative a))
      (P : Sylow p U),
    Nonempty (LocalInductiveMcKayData P)

/-- The universal closure of the explicit representative-level obligation
over all simple PSL₂ parameters. -/
def ProjectiveSpecialLinearTwoRepresentativeFamilyVerification
    (p : ℕ) : Prop :=
  ∀ a : ProjectiveSpecialLinearTwoSimpleParameter,
    ProjectiveSpecialLinearTwoRepresentativeVerification p a

namespace ProjectiveSpecialLinearTwoRepresentativeFamilyVerification

/-- Verification on one cover and one Sylow subgroup of every canonical
representative transports along the target isomorphism to the entire
isomorphism-closed simple PSL₂ family. -/
theorem toFamily
    {p : ℕ}
    (verified :
      ProjectiveSpecialLinearTwoRepresentativeFamilyVerification p) :
    OneUniversalCoverOneSylowFamilyVerification
      p projectiveSpecialLinearTwoSimpleGroupFamily := by
  intro S _ _ hS _ _
  obtain ⟨a, ⟨e⟩⟩ := hS
  obtain ⟨U, groupU, finiteU, E, P, hP⟩ :=
    verified a
  letI : Group U := groupU
  letI : Finite U := finiteU
  exact
    ⟨U, inferInstance, inferInstance,
      E.targetEquiv e.symm, P, hP⟩

/-- Consequently the representative verification supplies local data on
every universal cover and every Sylow subgroup of every family member.

The source equivalence and Sylow transport are provided by
`OneUniversalCoverOneSylowFamilyVerification.localData_on_every_universalCover`;
the theorem above supplies its target-isomorphism transport step. -/
theorem localData_on_every_universalCover
    {p : ℕ} [Fact p.Prime]
    (verified :
      ProjectiveSpecialLinearTwoRepresentativeFamilyVerification p)
    (S : Type) [Group S] [Finite S]
    (hS : projectiveSpecialLinearTwoSimpleGroupFamily.Contains S)
    (V : Type) [Group V] [Finite V]
    (F : UniversalCentralExtension V S)
    (Q : Sylow p V) :
    Nonempty (LocalInductiveMcKayData Q) :=
  verified.toFamily.localData_on_every_universalCover
    S hS
    (projectiveSpecialLinearTwoSimpleGroupFamily_member_isSimpleGroup S hS)
    (projectiveSpecialLinearTwoSimpleGroupFamily_member_not_isMulCommutative
      S hS)
    V F Q

end ProjectiveSpecialLinearTwoRepresentativeFamilyVerification

end InductiveMcKay
end McKayConjecture
