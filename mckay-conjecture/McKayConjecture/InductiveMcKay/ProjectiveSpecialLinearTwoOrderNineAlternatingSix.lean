/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixRewriteNormalForm
import McKayConjecture.InductiveMcKay.ProjectiveSpecialLinearTwoExceptionalCoverSplit
import McKayConjecture.InductiveMcKay.ProjectiveSpecialLinearTwoOrderNineMatrixGenerators

/-!
# The exceptional isomorphism `PSL(2, 𝔽₉) ≃ A₆`

The explicit projective generators constructed in
`ProjectiveSpecialLinearTwoOrderNineMatrixGenerators` satisfy the four
standard relators

`a² = b⁴ = (ab)⁵ = (ab²)⁵ = 1`.

They therefore define a homomorphism from the certified four-relator
presentation of `A₆` to `PSL(2, 𝔽₉)`.  The second generator has nontrivial
image, so simplicity of `A₆` makes this homomorphism injective.  Both
groups have order `360`, and the homomorphism is consequently an
isomorphism.

The final theorem observes that every parameter in the field-order-nine
branch is definitionally the canonical `(3,2)` parameter and closes the
exceptional residual predicate.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-! ### Descent through the certified presentation of `A₆` -/

/-- The assignment of the two presentation generators to the explicit
projective matrices. -/
def projectiveSpecialLinearTwoOrderNinePresentationGenerator
    (i : Fin 2) :
    Matrix.ProjectiveSpecialLinearGroup
      (Fin 2) ProjectiveSpecialLinearTwoOrderNineField :=
  if i = 0 then
    projectiveSpecialLinearTwoOrderNineProjectiveA
  else
    projectiveSpecialLinearTwoOrderNineProjectiveB

/-- The explicit projective matrices kill all four defining relators of
the standard presentation of `A₆`. -/
theorem
    projectiveSpecialLinearTwoOrderNinePresentationGenerator_kills_relators :
    ∀ r ∈ alternatingSixPresentationRelators,
      FreeGroup.lift
        projectiveSpecialLinearTwoOrderNinePresentationGenerator r = 1 := by
  intro r hr
  simp only [alternatingSixPresentationRelators, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa [alternatingSixPresentationRelatorA,
      alternatingSixPresentationGenerator,
      projectiveSpecialLinearTwoOrderNinePresentationGenerator] using
        projectiveSpecialLinearTwoOrderNineProjective_relations.1
  · simpa [alternatingSixPresentationRelatorB,
      alternatingSixPresentationGenerator,
      projectiveSpecialLinearTwoOrderNinePresentationGenerator] using
        projectiveSpecialLinearTwoOrderNineProjective_relations.2.1
  · simpa [alternatingSixPresentationRelatorAB,
      alternatingSixPresentationGenerator,
      projectiveSpecialLinearTwoOrderNinePresentationGenerator] using
        projectiveSpecialLinearTwoOrderNineProjective_relations.2.2.1
  · simpa [alternatingSixPresentationRelatorABSq,
      alternatingSixPresentationGenerator,
      projectiveSpecialLinearTwoOrderNinePresentationGenerator] using
        projectiveSpecialLinearTwoOrderNineProjective_relations.2.2.2

/-- The homomorphism from the certified four-relator presentation to
`PSL(2, 𝔽₉)`. -/
def alternatingSixPresentedGroupToProjectiveSpecialLinearTwoOrderNine :
    AlternatingSixPresentedGroup →*
      Matrix.ProjectiveSpecialLinearGroup
        (Fin 2) ProjectiveSpecialLinearTwoOrderNineField :=
  PresentedGroup.toGroup
    projectiveSpecialLinearTwoOrderNinePresentationGenerator_kills_relators

@[simp]
theorem
    alternatingSixPresentedGroupToProjectiveSpecialLinearTwoOrderNine_a :
    alternatingSixPresentedGroupToProjectiveSpecialLinearTwoOrderNine
        alternatingSixPresentedA =
      projectiveSpecialLinearTwoOrderNineProjectiveA := by
  simp [alternatingSixPresentedGroupToProjectiveSpecialLinearTwoOrderNine,
    alternatingSixPresentedA,
    projectiveSpecialLinearTwoOrderNinePresentationGenerator]

@[simp]
theorem
    alternatingSixPresentedGroupToProjectiveSpecialLinearTwoOrderNine_b :
    alternatingSixPresentedGroupToProjectiveSpecialLinearTwoOrderNine
        alternatingSixPresentedB =
      projectiveSpecialLinearTwoOrderNineProjectiveB := by
  simp [alternatingSixPresentedGroupToProjectiveSpecialLinearTwoOrderNine,
    alternatingSixPresentedB,
    projectiveSpecialLinearTwoOrderNinePresentationGenerator]

/-- The homomorphism from concrete `A₆` to `PSL(2, 𝔽₉)` obtained through
the certified presentation equivalence. -/
def alternatingSixToProjectiveSpecialLinearTwoOrderNine :
    AlternatingSix →*
      Matrix.ProjectiveSpecialLinearGroup
        (Fin 2) ProjectiveSpecialLinearTwoOrderNineField :=
  alternatingSixPresentedGroupToProjectiveSpecialLinearTwoOrderNine.comp
    alternatingSixPresentedGroupEquivAlternatingSix.symm.toMonoidHom

@[simp]
theorem alternatingSixToProjectiveSpecialLinearTwoOrderNine_b :
    alternatingSixToProjectiveSpecialLinearTwoOrderNine
        alternatingSixPresentationB =
      projectiveSpecialLinearTwoOrderNineProjectiveB := by
  change
    alternatingSixPresentedGroupToProjectiveSpecialLinearTwoOrderNine
        (alternatingSixPresentedGroupEquivAlternatingSix.symm
          alternatingSixPresentationB) =
      projectiveSpecialLinearTwoOrderNineProjectiveB
  rw [show
      alternatingSixPresentedGroupEquivAlternatingSix.symm
          alternatingSixPresentationB =
        alternatingSixPresentedB by
      apply alternatingSixPresentedGroupEquivAlternatingSix.injective
      simp [alternatingSixPresentedGroupEquivAlternatingSix]]
  exact
    alternatingSixPresentedGroupToProjectiveSpecialLinearTwoOrderNine_b

/-- The homomorphism from `A₆` is injective.  No separate generation
calculation is needed: its kernel is normal, simplicity leaves only
`⊥` and `⊤`, and the nontrivial image of `b` excludes `⊤`. -/
theorem alternatingSixToProjectiveSpecialLinearTwoOrderNine_injective :
    Function.Injective
      alternatingSixToProjectiveSpecialLinearTwoOrderNine := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases
      alternatingSixToProjectiveSpecialLinearTwoOrderNine.normal_ker
        |>.eq_bot_or_eq_top with
    hKernel | hKernel
  · exact hKernel
  · exfalso
    have hB :
        alternatingSixPresentationB ∈
          alternatingSixToProjectiveSpecialLinearTwoOrderNine.ker := by
      rw [hKernel]
      exact Subgroup.mem_top _
    have hBOne := MonoidHom.mem_ker.mp hB
    rw [alternatingSixToProjectiveSpecialLinearTwoOrderNine_b] at hBOne
    exact
      projectiveSpecialLinearTwoOrderNineProjectiveB_ne_one hBOne

/-! ### Equal orders and the exceptional isomorphism -/

/-- The canonical parameter for the field-order-nine branch. -/
def projectiveSpecialLinearTwoOrderNineCanonicalParameter :
    ProjectiveSpecialLinearTwoSimpleParameter where
  characteristic := 3
  degree := 2
  characteristic_prime := Nat.prime_three
  degree_ne_zero := by norm_num
  four_le_card := by norm_num

/-- The canonical projective special-linear group over the field of order
nine has order `360`. -/
theorem natCard_projectiveSpecialLinearTwoOrderNine :
    Nat.card
        (Matrix.ProjectiveSpecialLinearGroup
          (Fin 2) ProjectiveSpecialLinearTwoOrderNineField) =
      360 := by
  change
    Nat.card
        (projectiveSpecialLinearTwoRepresentative
          projectiveSpecialLinearTwoOrderNineCanonicalParameter) =
      360
  rw [
    natCard_projectiveSpecialLinearTwoRepresentative_of_characteristic_ne_two
      projectiveSpecialLinearTwoOrderNineCanonicalParameter
      (by
        norm_num [
          projectiveSpecialLinearTwoOrderNineCanonicalParameter])
  ]
  norm_num [projectiveSpecialLinearTwoOrderNineCanonicalParameter]

/-- The injective homomorphism from `A₆` is bijective because source and
target both have order `360`. -/
theorem alternatingSixToProjectiveSpecialLinearTwoOrderNine_bijective :
    Function.Bijective
      alternatingSixToProjectiveSpecialLinearTwoOrderNine :=
  alternatingSixToProjectiveSpecialLinearTwoOrderNine_injective
    |>.bijective_of_nat_card_le (by
      rw [natCard_alternatingSix,
        natCard_projectiveSpecialLinearTwoOrderNine])

/-- The canonical exceptional isomorphism, oriented from
`PSL(2, 𝔽₉)` to `A₆`. -/
def projectiveSpecialLinearTwoOrderNineMulEquivAlternatingSix :
    Matrix.ProjectiveSpecialLinearGroup
        (Fin 2) ProjectiveSpecialLinearTwoOrderNineField ≃*
      AlternatingSix :=
  (MulEquiv.ofBijective
      alternatingSixToProjectiveSpecialLinearTwoOrderNine
      alternatingSixToProjectiveSpecialLinearTwoOrderNine_bijective).symm

/-! ### Every field-order-nine parameter -/

/-- Every parameter of field order nine is the canonical `(3,2)`
parameter. -/
theorem projectiveSpecialLinearTwoOrderNineParameter_eq_canonical
    (a : ProjectiveSpecialLinearTwoOrderNineParameter) :
    a.1 = projectiveSpecialLinearTwoOrderNineCanonicalParameter := by
  rcases
      (isProjectiveSpecialLinearTwoOrderNineParameter_iff a.1).mp a.2 with
    ⟨hCharacteristic, hDegree⟩
  cases a with
  | mk a ha =>
    cases a with
    | mk characteristic degree hPrime hDegreeNe hFour =>
      simp only at hCharacteristic hDegree
      subst characteristic
      subst degree
      rfl

/-- Every representative in the field-order-nine branch is isomorphic to
`A₆`. -/
theorem
    projectiveSpecialLinearTwoOrderNineRepresentative_mulEquiv_alternatingSix
    (a : ProjectiveSpecialLinearTwoOrderNineParameter) :
    Nonempty
      (projectiveSpecialLinearTwoRepresentative a.1 ≃*
        alternatingGroup (Fin 6)) := by
  rw [projectiveSpecialLinearTwoOrderNineParameter_eq_canonical a]
  exact
    ⟨projectiveSpecialLinearTwoOrderNineMulEquivAlternatingSix⟩

/-- The order-nine exceptional residual from the cover split is closed. -/
theorem projectiveSpecialLinearTwoOrderNineAlternatingSixResidual :
    ProjectiveSpecialLinearTwoOrderNineAlternatingSixResidual :=
  projectiveSpecialLinearTwoOrderNineRepresentative_mulEquiv_alternatingSix

end InductiveMcKay
end McKayConjecture
