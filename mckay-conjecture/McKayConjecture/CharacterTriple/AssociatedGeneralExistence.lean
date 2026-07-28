/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedExistence
import McKayConjecture.CharacterTriple.ProjectiveIntertwiner
import McKayConjecture.CharacterTriple.ProjectiveLinearLift

/-!
# Associated projective representations for arbitrary character triples

For a finite character triple `(A, X, χ)`, this file constructs a normalized
projective representation of `A` associated with `χ`.

The construction starts with the projective-linear conjugation action supplied
by intertwining operators.  A normalized section of `A ⧸ X` is then used to
choose the lift on every coset in such a way that multiplication by `X` is
literal on both sides.  The resulting operators differ from the initial lift
only by nonzero scalars, so rescaling supplies their factor set.
-/

noncomputable section

open CategoryTheory

universe u

namespace McKayConjecture
namespace CharacterTriple
namespace AssociatedGeneralExistence

variable {A : Type u} [Finite A] [Group A] (T : CharacterTriple A)

/-- Invariance of the character under the ambient conjugation action. -/
theorem conjugationInvariant :
    IsInvariant
      (MulAut.conjNormal : A →* MulAut T.normalSubgroup) T.character :=
  T.invariant_conjNormal

/-- The chosen realization as an honest action of the normal subgroup. -/
abbrev realizationAction :
    T.normalSubgroup →*
      (T.character.realization ≃ₗ[ℂ] T.character.realization) :=
  AssociatedExistence.realizationAction T.character

/-- A normalized intertwiner implementing conjugation by an ambient element. -/
abbrev ambientIntertwiner (a : A) :
    T.character.realization ≃ₗ[ℂ] T.character.realization :=
  AssociatedExistence.intertwiner
    (MulAut.conjNormal : A →* MulAut T.normalSubgroup)
    T.character (conjugationInvariant T) a

@[simp]
theorem ambientIntertwiner_one :
    ambientIntertwiner T 1 = 1 :=
  AssociatedExistence.intertwiner_one
    (MulAut.conjNormal : A →* MulAut T.normalSubgroup)
    T.character (conjugationInvariant T)

/-- Ambient intertwiners implement the conjugation action on the chosen
realization. -/
theorem ambientIntertwiner_mul_realizationAction
    (a : A) (x : T.normalSubgroup) :
    ambientIntertwiner T a * realizationAction T x =
      realizationAction T (MulAut.conjNormal a x) *
        ambientIntertwiner T a :=
  AssociatedExistence.intertwiner_mul_rho
    (MulAut.conjNormal : A →* MulAut T.normalSubgroup)
    T.character (conjugationInvariant T) a x

/-- The initial projective lift furnished by arbitrary normalized
intertwiners. -/
def intertwinerProjectiveRepresentation :
    ProjectiveRepresentation ℂ A T.character.realization where
  operator := ambientIntertwiner T
  factor :=
    AssociatedExistence.intertwinerFactor
      (MulAut.conjNormal : A →* MulAut T.normalSubgroup)
      T.character (conjugationInvariant T)
  map_mul :=
    AssociatedExistence.intertwiner_mul
      (MulAut.conjNormal : A →* MulAut T.normalSubgroup)
      T.character (conjugationInvariant T)

/-- The genuine projective-linear conjugation action underlying the initial
intertwiner lift. -/
def projectiveLinearConjugationAction :
    A →* ProjectiveLinearGroup ℂ T.character.realization :=
  (intertwinerProjectiveRepresentation T).toProjectiveLinearGroup

/-- The canonical representative lift of the projective-linear conjugation
action.  The coset-normalized lift below is a scalar modification of this
projective action. -/
def canonicalProjectiveLinearLift :
    ProjectiveRepresentation ℂ A T.character.realization :=
  ProjectiveRepresentation.ofProjectiveLinearGroup
    (projectiveLinearConjugationAction T)

/-- A section of the quotient map which sends the identity coset to the
identity element. -/
def quotientRepresentative (q : A ⧸ T.normalSubgroup) : A := by
  classical
  exact if hq : q = 1 then 1
    else
      Classical.choose
        (QuotientGroup.mk'_surjective T.normalSubgroup q)

@[simp]
theorem quotientRepresentative_one :
    quotientRepresentative T 1 = 1 := by
  simp [quotientRepresentative]

@[simp]
theorem mk_quotientRepresentative (q : A ⧸ T.normalSubgroup) :
    QuotientGroup.mk' T.normalSubgroup
      (quotientRepresentative T q) = q := by
  classical
  by_cases hq : q = 1
  · subst q
    simp
  · simp only [quotientRepresentative, hq, ↓reduceDIte]
    exact Classical.choose_spec
      (QuotientGroup.mk'_surjective T.normalSubgroup q)

/-- The normal component in the decomposition
`a = normalPart(a) * representative(aX)`. -/
def normalPart (a : A) : T.normalSubgroup :=
  ⟨a * (quotientRepresentative T
      (QuotientGroup.mk' T.normalSubgroup a))⁻¹, by
    apply (QuotientGroup.eq_one_iff
      (a * (quotientRepresentative T
        (QuotientGroup.mk' T.normalSubgroup a))⁻¹)).mp
    change QuotientGroup.mk' T.normalSubgroup
      (a * (quotientRepresentative T
        (QuotientGroup.mk' T.normalSubgroup a))⁻¹) = 1
    rw [map_mul, map_inv, mk_quotientRepresentative T]
    simp⟩

@[simp]
theorem normalPart_coe (a : A) :
    (normalPart T a : A) =
      a * (quotientRepresentative T
        (QuotientGroup.mk' T.normalSubgroup a))⁻¹ :=
  rfl

theorem normalPart_mul_representative (a : A) :
    (normalPart T a : A) *
        quotientRepresentative T
          (QuotientGroup.mk' T.normalSubgroup a) = a := by
  simp [normalPart, mul_assoc]

@[simp]
theorem normalPart_normal (x : T.normalSubgroup) :
    normalPart T (x : A) = x := by
  have hx :
      QuotientGroup.mk' T.normalSubgroup (x : A) = 1 :=
    (QuotientGroup.eq_one_iff (x : A)).2 x.property
  apply Subtype.ext
  simp [normalPart, hx]

theorem quotient_mk_normal_mul (x : T.normalSubgroup) (a : A) :
    QuotientGroup.mk' T.normalSubgroup ((x : A) * a) =
      QuotientGroup.mk' T.normalSubgroup a := by
  have hx : QuotientGroup.mk' T.normalSubgroup (x : A) = 1 :=
    (QuotientGroup.eq_one_iff (x : A)).2 x.property
  rw [map_mul, hx, one_mul]

theorem normalPart_normal_mul (x : T.normalSubgroup) (a : A) :
    normalPart T ((x : A) * a) = x * normalPart T a := by
  apply Subtype.ext
  simp only [normalPart_coe, Subgroup.coe_mul]
  rw [quotient_mk_normal_mul T x a]
  simp only [mul_assoc]

/-- The coset-normalized operator:
`P(a) = ρ(normalPart(a)) I(representative(aX))`. -/
def projectiveOperator (a : A) :
    T.character.realization ≃ₗ[ℂ] T.character.realization :=
  realizationAction T (normalPart T a) *
    ambientIntertwiner T
      (quotientRepresentative T
        (QuotientGroup.mk' T.normalSubgroup a))

@[simp]
theorem projectiveOperator_normal (x : T.normalSubgroup) :
    projectiveOperator T (x : A) = realizationAction T x := by
  have hx :
      QuotientGroup.mk' T.normalSubgroup (x : A) = 1 :=
    (QuotientGroup.eq_one_iff (x : A)).2 x.property
  simp [projectiveOperator, hx]

@[simp]
theorem projectiveOperator_one :
    projectiveOperator T 1 = 1 := by
  simpa using
    projectiveOperator_normal T (1 : T.normalSubgroup)

theorem projectiveOperator_normal_mul
    (x : T.normalSubgroup) (a : A) :
    projectiveOperator T ((x : A) * a) =
      realizationAction T x * projectiveOperator T a := by
  rw [projectiveOperator, projectiveOperator,
    normalPart_normal_mul T, map_mul, quotient_mk_normal_mul T]
  simp only [mul_assoc]

/-- The normal component followed by the selected representative induces the
same conjugation automorphism as the original ambient element. -/
theorem normalPart_mul_conjugate_representative
    (a : A) (x : T.normalSubgroup) :
    normalPart T a *
        MulAut.conjNormal
          (quotientRepresentative T
            (QuotientGroup.mk' T.normalSubgroup a)) x =
      MulAut.conjNormal a x * normalPart T a := by
  let n := normalPart T a
  let s :=
    quotientRepresentative T
      (QuotientGroup.mk' T.normalSubgroup a)
  have ha : (n : A) * s = a :=
    normalPart_mul_representative T a
  apply Subtype.ext
  change (n : A) * (s * (x : A) * s⁻¹) =
    (a * (x : A) * a⁻¹) * (n : A)
  calc
    (n : A) * (s * (x : A) * s⁻¹) =
        ((n : A) * s) * (x : A) * ((n : A) * s)⁻¹ * (n : A) := by
      group
    _ = (a * (x : A) * a⁻¹) * (n : A) := by rw [ha]

/-- Every coset-normalized operator implements conjugation by its ambient
group element. -/
theorem projectiveOperator_mul_realizationAction
    (a : A) (x : T.normalSubgroup) :
    projectiveOperator T a * realizationAction T x =
      realizationAction T (MulAut.conjNormal a x) *
        projectiveOperator T a := by
  let s :=
    quotientRepresentative T
      (QuotientGroup.mk' T.normalSubgroup a)
  let n := normalPart T a
  change
    (realizationAction T n * ambientIntertwiner T s) *
        realizationAction T x =
      realizationAction T (MulAut.conjNormal a x) *
        (realizationAction T n * ambientIntertwiner T s)
  calc
    (realizationAction T n * ambientIntertwiner T s) *
          realizationAction T x =
        realizationAction T n *
          (ambientIntertwiner T s * realizationAction T x) := by
            rw [mul_assoc]
    _ = realizationAction T n *
          (realizationAction T (MulAut.conjNormal s x) *
            ambientIntertwiner T s) := by
          rw [ambientIntertwiner_mul_realizationAction]
    _ = (realizationAction T n *
          realizationAction T (MulAut.conjNormal s x)) *
            ambientIntertwiner T s := by rw [mul_assoc]
    _ = realizationAction T
          (n * MulAut.conjNormal s x) *
            ambientIntertwiner T s := by rw [map_mul]
    _ = realizationAction T (MulAut.conjNormal a x) *
          (realizationAction T n * ambientIntertwiner T s) := by
        rw [normalPart_mul_conjugate_representative T]
        rw [map_mul, mul_assoc]

/-- Right multiplication by a normal element is literal for the
coset-normalized operators. -/
theorem projectiveOperator_mul_normal
    (a : A) (x : T.normalSubgroup) :
    projectiveOperator T (a * (x : A)) =
      projectiveOperator T a * realizationAction T x := by
  let y : T.normalSubgroup := MulAut.conjNormal a x
  have hay : a * (x : A) = (y : A) * a := by
    change a * (x : A) = (a * (x : A) * a⁻¹) * a
    group
  rw [hay, projectiveOperator_normal_mul T]
  exact (projectiveOperator_mul_realizationAction T a x).symm

/-- The quotient of a coset-normalized operator by the initial ambient
intertwiner. -/
def operatorComparison (a : A) :
    T.character.realization ≃ₗ[ℂ] T.character.realization :=
  (ambientIntertwiner T a)⁻¹ * projectiveOperator T a

/-- The comparison operator commutes with the normal-subgroup action. -/
theorem operatorComparison_mul_realizationAction
    (a : A) (x : T.normalSubgroup) :
    operatorComparison T a * realizationAction T x =
      realizationAction T x * operatorComparison T a := by
  let I := ambientIntertwiner T a
  let P := projectiveOperator T a
  have hI :
      I * realizationAction T x =
        realizationAction T (MulAut.conjNormal a x) * I :=
    ambientIntertwiner_mul_realizationAction T a x
  have hP :
      P * realizationAction T x =
        realizationAction T (MulAut.conjNormal a x) * P :=
    projectiveOperator_mul_realizationAction T a x
  have hIinv :
      I⁻¹ * realizationAction T (MulAut.conjNormal a x) =
        realizationAction T x * I⁻¹ := by
    apply mul_left_cancel (a := I)
    calc
      I * (I⁻¹ * realizationAction T (MulAut.conjNormal a x)) =
          realizationAction T (MulAut.conjNormal a x) := by simp
      _ = (I * realizationAction T x) * I⁻¹ := by
            rw [hI]
            simp
      _ = I * (realizationAction T x * I⁻¹) := by rw [mul_assoc]
  change (I⁻¹ * P) * realizationAction T x =
    realizationAction T x * (I⁻¹ * P)
  calc
    (I⁻¹ * P) * realizationAction T x =
        I⁻¹ * (P * realizationAction T x) := by rw [mul_assoc]
    _ = I⁻¹ *
        (realizationAction T (MulAut.conjNormal a x) * P) := by rw [hP]
    _ = (I⁻¹ * realizationAction T (MulAut.conjNormal a x)) * P := by
          rw [mul_assoc]
    _ = (realizationAction T x * I⁻¹) * P := by rw [hIinv]
    _ = realizationAction T x * (I⁻¹ * P) := by rw [mul_assoc]

/-- The same comparison, packaged as a projective intertwiner of the honest
normal-subgroup action with itself. -/
def operatorComparisonIntertwiningMap (a : A) :
    ProjectiveRepresentation.IntertwiningMap
      (ProjectiveRepresentation.ofLinearAction (realizationAction T))
      (ProjectiveRepresentation.ofLinearAction (realizationAction T)) where
  toLinearMap := (operatorComparison T a).toLinearMap
  intertwines := by
    intro x
    apply LinearMap.ext
    intro z
    exact DFunLike.congr_fun
      (operatorComparison_mul_realizationAction T a x) z

/-- The comparison as an endomorphism of the irreducible realization. -/
def operatorComparisonEndomorphism (a : A) :
    T.character.realization ⟶ T.character.realization :=
  ⟨InducedCategory.homMk
      (ModuleCat.ofHom
        (operatorComparisonIntertwiningMap T a).toLinearMap),
    fun x ↦ by
      ext z
      exact DFunLike.congr_fun
        (operatorComparison_mul_realizationAction T a x) z⟩

@[simp]
theorem operatorComparisonEndomorphism_apply
    (a : A) (z : T.character.realization) :
    operatorComparisonEndomorphism T a z =
      operatorComparison T a z :=
  rfl

/-- Schur's lemma makes each comparison a nonzero scalar. -/
theorem operatorComparison_isScalar (a : A) :
    ∃ c : ℂˣ,
      operatorComparison T a =
        scalarLinearEquiv ℂ T.character.realization c := by
  let f := operatorComparisonEndomorphism T a
  obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id ℂ f
  have hpoint : ∀ z : T.character.realization,
      c • z = operatorComparison T a z := by
    intro z
    have hz := ConcreteCategory.congr_hom hc z
    change c • z = operatorComparison T a z at hz
    exact hz
  have hc0 : c ≠ 0 := by
    intro hc0
    obtain ⟨z : T.character.realization, hz⟩ :=
      exists_ne (0 : T.character.realization)
    have hcomparison_zero : operatorComparison T a z = 0 := by
      rw [← hpoint z, hc0, zero_smul]
    exact hz ((operatorComparison T a).injective
      (by simpa using hcomparison_zero))
  refine ⟨Units.mk0 c hc0, ?_⟩
  ext z
  exact hpoint z |>.symm

/-- The scalar cochain which changes the initial intertwiner lift into the
coset-normalized lift. -/
def normalizationScalar (a : A) : ℂˣ :=
  Classical.choose (operatorComparison_isScalar T a)

theorem operatorComparison_eq_scalar (a : A) :
    operatorComparison T a =
      scalarLinearEquiv ℂ T.character.realization
        (normalizationScalar T a) :=
  Classical.choose_spec (operatorComparison_isScalar T a)

/-- The coset-normalized operator is exactly the scalar modification selected
by `normalizationScalar`. -/
theorem projectiveOperator_eq_scalar_mul_intertwiner (a : A) :
    projectiveOperator T a =
      scalarLinearEquiv ℂ T.character.realization
          (normalizationScalar T a) *
        ambientIntertwiner T a := by
  let I := ambientIntertwiner T a
  let P := projectiveOperator T a
  have hcomparison := operatorComparison_eq_scalar T a
  change I⁻¹ * P =
    scalarLinearEquiv ℂ T.character.realization
      (normalizationScalar T a) at hcomparison
  calc
    P = I * (I⁻¹ * P) := by simp
    _ = I * scalarLinearEquiv ℂ T.character.realization
        (normalizationScalar T a) := by rw [hcomparison]
    _ = scalarLinearEquiv ℂ T.character.realization
          (normalizationScalar T a) * I :=
      (scalarLinearEquiv_comm ℂ T.character.realization
        (normalizationScalar T a) I).symm

/-- The arbitrary-triple projective representation with exact
normal-subgroup multiplication laws. -/
def projectiveRepresentation :
    ProjectiveRepresentation ℂ A T.character.realization :=
  (intertwinerProjectiveRepresentation T).rescale
    (normalizationScalar T)

@[simp]
theorem projectiveRepresentation_operator (a : A) :
    (projectiveRepresentation T).operator a =
      projectiveOperator T a := by
  rw [projectiveRepresentation,
    ProjectiveRepresentation.rescale_operator]
  exact (projectiveOperator_eq_scalar_mul_intertwiner T a).symm

/-- The arbitrary-triple lift is normalized. -/
theorem projectiveRepresentation_isNormalized :
    (projectiveRepresentation T).IsNormalized := by
  rw [ProjectiveRepresentation.IsNormalized,
    projectiveRepresentation_operator]
  exact projectiveOperator_one T

/-- The normalized lift and the canonical projective-linear lift represent
the same genuine action in the projective linear group. -/
theorem projectiveRepresentation_toProjectiveLinearGroup :
    (projectiveRepresentation T).toProjectiveLinearGroup =
      projectiveLinearConjugationAction T := by
  ext a
  change
    ProjectiveLinearGroup.mk ℂ T.character.realization
        (scalarLinearEquiv ℂ T.character.realization
          (normalizationScalar T a) * ambientIntertwiner T a) =
      ProjectiveLinearGroup.mk ℂ T.character.realization
        (ambientIntertwiner T a)
  rw [map_mul, ProjectiveLinearGroup.mk_scalar, one_mul]

/-- The restriction action, with domain exactly the normal subgroup stored
in the character triple. -/
abbrev restriction :
    T.normalSubgroup →*
      (T.character.realization ≃ₗ[ℂ] T.character.realization) :=
  realizationAction T

/-- The constructed representation is associated with the arbitrary
character triple. -/
def associated :
    AssociatedProjectiveRepresentation T T.character.realization
      (projectiveRepresentation T) where
  restriction := restriction T
  restriction_apply := by
    intro x
    rw [projectiveRepresentation_operator,
      projectiveOperator_normal]
  restriction_simple := by
    change Simple T.character.realization
    infer_instance
  restriction_character := by
    funext x
    change T.character.realization.character x =
      T.character.values x
    exact congrFun T.character.realization_character x
  normal_mul := by
    intro x a
    rw [projectiveRepresentation_operator,
      projectiveRepresentation_operator,
      projectiveRepresentation_operator,
      projectiveOperator_normal,
      projectiveOperator_normal_mul]
  mul_normal := by
    intro a x
    rw [projectiveRepresentation_operator,
      projectiveRepresentation_operator,
      projectiveRepresentation_operator,
      projectiveOperator_normal,
      projectiveOperator_mul_normal]

/-- Every finite character triple has a normalized associated projective
representation on the chosen realization of its character. -/
theorem exists_normalized_associated :
    ∃ P : ProjectiveRepresentation ℂ A T.character.realization,
      P.IsNormalized ∧
        Nonempty (AssociatedProjectiveRepresentation
          T T.character.realization P) :=
  ⟨projectiveRepresentation T,
    projectiveRepresentation_isNormalized T,
    ⟨associated T⟩⟩

end AssociatedGeneralExistence

/-- Public existence theorem for an arbitrary finite character triple. -/
theorem exists_normalized_associated
    {A : Type u} [Finite A] [Group A] (T : CharacterTriple A) :
    ∃ P : ProjectiveRepresentation ℂ A T.character.realization,
      P.IsNormalized ∧
        Nonempty (AssociatedProjectiveRepresentation
          T T.character.realization P) :=
  AssociatedGeneralExistence.exists_normalized_associated T

end CharacterTriple
end McKayConjecture
