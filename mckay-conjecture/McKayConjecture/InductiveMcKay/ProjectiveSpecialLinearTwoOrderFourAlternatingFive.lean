/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import McKayConjecture.InductiveMcKay.AlternatingBoundedDegreeAutomatic
import McKayConjecture.InductiveMcKay.ProjectiveSpecialLinearTwoExceptionalCoverSplit
import McKayConjecture.InductiveMcKay.SpecialLinearTwoFiveProjectiveTables

/-!
# The exceptional isomorphism `PSL(2, 𝔽₄) ≃ A₅`

The projective special linear group over the canonical field of order four
acts faithfully on its projective line, which has five points.  Since the
group is perfect, the sign of this permutation action is trivial, so the
action lands in `A₅`.  The source and target both have order sixty; the
faithful homomorphism is therefore an isomorphism.

The final theorem transports this canonical isomorphism to every parameter
in the field-order-four branch and closes the corresponding residual
predicate from the exceptional-cover split.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory
open scoped LinearAlgebra.Projectivization

local instance projectiveSpecialLinearTwoOrderFourFactPrime :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-! ### Canonical field-order-four objects -/

/-- The canonical parameter for the field of order four. -/
def projectiveSpecialLinearTwoOrderFourCanonicalParameter :
    ProjectiveSpecialLinearTwoSimpleParameter where
  characteristic := 2
  degree := 2
  characteristic_prime := Nat.prime_two
  degree_ne_zero := by norm_num
  four_le_card := by norm_num

/-- The canonical finite field of order four. -/
abbrev ProjectiveSpecialLinearTwoOrderFourField : Type :=
  GaloisField 2 2

/-- The projective line on which `PSL(2, 𝔽₄)` acts faithfully. -/
abbrev ProjectiveSpecialLinearTwoOrderFourProjectiveLine : Type :=
  ℙ ProjectiveSpecialLinearTwoOrderFourField
    (Fin 2 → ProjectiveSpecialLinearTwoOrderFourField)

/-- The projective line over the canonical field of order four has five
points. -/
theorem natCard_projectiveSpecialLinearTwoOrderFourProjectiveLine :
    Nat.card ProjectiveSpecialLinearTwoOrderFourProjectiveLine = 5 := by
  calc
    Nat.card ProjectiveSpecialLinearTwoOrderFourProjectiveLine =
        Nat.card ProjectiveSpecialLinearTwoOrderFourField + 1 :=
      Projectivization.card_of_finrank_two
        ProjectiveSpecialLinearTwoOrderFourField
        (Fin 2 → ProjectiveSpecialLinearTwoOrderFourField) (by simp)
    _ = 5 := by
      rw [GaloisField.card 2 2 (by norm_num)]
      norm_num

/-- A fixed identification of the five-point projective line with
`Fin 5`. -/
def projectiveSpecialLinearTwoOrderFourProjectiveLineEquiv :
    ProjectiveSpecialLinearTwoOrderFourProjectiveLine ≃ Fin 5 :=
  Finite.equivFinOfCardEq
    natCard_projectiveSpecialLinearTwoOrderFourProjectiveLine

/-! ### The faithful even permutation action -/

/-- The faithful projective-line action, transported to five letters. -/
def projectiveSpecialLinearTwoOrderFourPermutationHom :
    Matrix.ProjectiveSpecialLinearGroup
        (Fin 2) ProjectiveSpecialLinearTwoOrderFourField →*
      Equiv.Perm (Fin 5) where
  toFun g :=
    projectiveSpecialLinearTwoOrderFourProjectiveLineEquiv.permCongr
      (Projectivization.PSLAction.toPermHom g)
  map_one' := by
    rw [map_one]
    exact
      projectiveSpecialLinearTwoOrderFourProjectiveLineEquiv.permCongr_refl
  map_mul' := by
    intro g h
    simp

/-- Transporting the faithful projective-line action to `Fin 5` preserves
faithfulness. -/
theorem projectiveSpecialLinearTwoOrderFourPermutationHom_injective :
    Function.Injective
      projectiveSpecialLinearTwoOrderFourPermutationHom := by
  intro g h hgh
  apply Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective
  apply Equiv.ext
  intro x
  apply projectiveSpecialLinearTwoOrderFourProjectiveLineEquiv.injective
  have hx :=
    Equiv.congr_fun hgh
      (projectiveSpecialLinearTwoOrderFourProjectiveLineEquiv x)
  change
    projectiveSpecialLinearTwoOrderFourProjectiveLineEquiv.permCongr
        (Projectivization.PSLAction.toPermHom g)
        (projectiveSpecialLinearTwoOrderFourProjectiveLineEquiv x) =
      projectiveSpecialLinearTwoOrderFourProjectiveLineEquiv.permCongr
        (Projectivization.PSLAction.toPermHom h)
        (projectiveSpecialLinearTwoOrderFourProjectiveLineEquiv x)
    at hx
  simpa only [
    Equiv.permCongr_apply,
    Equiv.symm_apply_apply
  ] using hx

local instance projectiveSpecialLinearTwoOrderFourIsPerfect :
    Group.IsPerfect
      (Matrix.ProjectiveSpecialLinearGroup
        (Fin 2) ProjectiveSpecialLinearTwoOrderFourField) :=
  projectiveSpecialLinearTwoRepresentative_isPerfect
    projectiveSpecialLinearTwoOrderFourCanonicalParameter

/-- Every permutation in the projective-line image is even.  This is the
only place perfectness is used in the exceptional isomorphism. -/
theorem projectiveSpecialLinearTwoOrderFourPermutationHom_mem_alternating
    (g :
      Matrix.ProjectiveSpecialLinearGroup
        (Fin 2) ProjectiveSpecialLinearTwoOrderFourField) :
    projectiveSpecialLinearTwoOrderFourPermutationHom g ∈
      alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  let signAction :
      Matrix.ProjectiveSpecialLinearGroup
          (Fin 2) ProjectiveSpecialLinearTwoOrderFourField →*
        ℤˣ :=
    Equiv.Perm.sign.comp
      projectiveSpecialLinearTwoOrderFourPermutationHom
  have hCommutator :
      commutator
          (Matrix.ProjectiveSpecialLinearGroup
            (Fin 2) ProjectiveSpecialLinearTwoOrderFourField) ≤
        signAction.ker :=
    Abelianization.commutator_subset_ker signAction
  have hg : g ∈ signAction.ker := by
    rw [Group.IsPerfect.commutator_eq_top] at hCommutator
    exact hCommutator (Subgroup.mem_top g)
  exact MonoidHom.mem_ker.mp hg

/-- The faithful projective-line action with codomain restricted to
`A₅`. -/
def projectiveSpecialLinearTwoOrderFourToAlternatingFive :
    Matrix.ProjectiveSpecialLinearGroup
        (Fin 2) ProjectiveSpecialLinearTwoOrderFourField →*
      alternatingGroup (Fin 5) :=
  projectiveSpecialLinearTwoOrderFourPermutationHom.codRestrict
    (alternatingGroup (Fin 5))
    projectiveSpecialLinearTwoOrderFourPermutationHom_mem_alternating

theorem projectiveSpecialLinearTwoOrderFourToAlternatingFive_injective :
    Function.Injective
      projectiveSpecialLinearTwoOrderFourToAlternatingFive := by
  intro g h hgh
  apply
    projectiveSpecialLinearTwoOrderFourPermutationHom_injective
  exact congrArg Subtype.val hgh

/-! ### Equal orders and the exceptional isomorphism -/

theorem natCard_projectiveSpecialLinearTwoOrderFour :
    Nat.card
        (Matrix.ProjectiveSpecialLinearGroup
          (Fin 2) ProjectiveSpecialLinearTwoOrderFourField) =
      60 := by
  change
    Nat.card
        (projectiveSpecialLinearTwoRepresentative
          projectiveSpecialLinearTwoOrderFourCanonicalParameter) =
      60
  rw [
    natCard_projectiveSpecialLinearTwoRepresentative_of_characteristic_two
      projectiveSpecialLinearTwoOrderFourCanonicalParameter rfl
  ]
  norm_num [projectiveSpecialLinearTwoOrderFourCanonicalParameter]

theorem natCard_alternatingGroup_fin_five :
    Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- The exceptional group isomorphism obtained from the faithful even
five-point action. -/
def projectiveSpecialLinearTwoOrderFourMulEquivAlternatingFive :
    Matrix.ProjectiveSpecialLinearGroup
        (Fin 2) ProjectiveSpecialLinearTwoOrderFourField ≃*
      alternatingGroup (Fin 5) :=
  MulEquiv.ofBijective
    projectiveSpecialLinearTwoOrderFourToAlternatingFive
    (projectiveSpecialLinearTwoOrderFourToAlternatingFive_injective
      |>.bijective_of_nat_card_le (by
        rw [natCard_projectiveSpecialLinearTwoOrderFour,
          natCard_alternatingGroup_fin_five]))

/-! ### Every field-order-four parameter -/

/-- Every parameter of field order four is the canonical `(2,2)`
parameter. -/
theorem projectiveSpecialLinearTwoOrderFourParameter_eq_canonical
    (a : ProjectiveSpecialLinearTwoOrderFourParameter) :
    a.1 = projectiveSpecialLinearTwoOrderFourCanonicalParameter := by
  rcases
      (isProjectiveSpecialLinearTwoOrderFourParameter_iff a.1).mp a.2 with
    ⟨hCharacteristic, hDegree⟩
  cases a with
  | mk a ha =>
    cases a with
    | mk characteristic degree hPrime hDegreeNe hFour =>
      simp only at hCharacteristic hDegree
      subst characteristic
      subst degree
      rfl

/-- Every representative in the field-order-four branch is isomorphic to
`A₅`. -/
theorem
    projectiveSpecialLinearTwoOrderFourRepresentative_mulEquiv_alternatingFive
    (a : ProjectiveSpecialLinearTwoOrderFourParameter) :
    Nonempty
      (projectiveSpecialLinearTwoRepresentative a.1 ≃*
        alternatingGroup (Fin 5)) := by
  rw [projectiveSpecialLinearTwoOrderFourParameter_eq_canonical a]
  exact
    ⟨projectiveSpecialLinearTwoOrderFourMulEquivAlternatingFive⟩

/-- The closed `A₅` family verification discharges every representative in
the field-order-four branch, at every prime. -/
theorem projectiveSpecialLinearTwoOrderFourRepresentativeVerification
    (p : ℕ) [Fact p.Prime] :
    ∀ a : ProjectiveSpecialLinearTwoOrderFourParameter,
      ProjectiveSpecialLinearTwoRepresentativeVerification p a.1 := by
  intro a
  letI :
      Finite (projectiveSpecialLinearTwoRepresentative a.1) :=
    projectiveSpecialLinearTwoRepresentative_finite a.1
  exact
    alternatingFiveFamilyVerification p
      (projectiveSpecialLinearTwoRepresentative a.1)
      ((alternatingFiveSimpleGroupFamily_contains_iff
        (projectiveSpecialLinearTwoRepresentative a.1)).2
          (projectiveSpecialLinearTwoOrderFourRepresentative_mulEquiv_alternatingFive
            a))
      (projectiveSpecialLinearTwoRepresentative_isSimpleGroup a.1)
      (projectiveSpecialLinearTwoRepresentative_not_isMulCommutative a.1)

/-- The order-four exceptional residual from the cover split is closed. -/
theorem projectiveSpecialLinearTwoOrderFourAlternatingFiveResidual :
    ProjectiveSpecialLinearTwoOrderFourAlternatingFiveResidual :=
  projectiveSpecialLinearTwoOrderFourRepresentative_mulEquiv_alternatingFive

end InductiveMcKay
end McKayConjecture
