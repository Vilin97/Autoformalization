/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralUnit
import McKayConjecture.Character.ExtensionLinearTwist
import McKayConjecture.CharacterTriple.AssociatedExistence

/-!
# Projective semidirect representations from a common central cover

Let `L → Γ` cover an action group, and suppose `L` acts by conjugation
inside an overgroup `Ω` containing the normal group `X`.  If the cover
kernel is central in `Ω`, a normalized section `Γ → L` turns an honest
extension character on `Ω` into an associated projective representation
of `X ⋊ Γ`.  Its factor is exactly the central scalar of the section
defect.

The construction is designed so that the same section can be used for an
ambient group and a local subgroup.  Equality of normalized character
values on the common kernel then makes the two factor sets literally
equal.
-/

noncomputable section

open CategoryTheory

universe u v w x

namespace McKayConjecture
namespace CharacterTriple
namespace CommonCentralCoverSemidirectProjective

variable {X : Type u} {Γ : Type v} {L : Type w} {Ω : Type x}
variable [Group X] [Finite X] [Group Γ] [Finite Γ]
variable [Group L] [Finite L] [Group Ω] [Finite Ω]

variable (φ : Γ →* MulAut X)
variable (χ : IrreducibleCharacter X)
variable (hχ : IsInvariant φ χ)
variable (cover : L →* Γ)
variable (cover_surjective : Function.Surjective cover)
variable (normalEmbedding : X →* Ω)
variable (coverEmbedding : L →* Ω)
variable
  (cover_conjugates :
    ∀ (l : L) (g : X),
      normalEmbedding (φ (cover l) g) =
        coverEmbedding l * normalEmbedding g *
          (coverEmbedding l)⁻¹)
variable (extensionCharacter : IrreducibleCharacter Ω)
variable
  (extendsNormal :
    IrreducibleCharacter.IsExtensionAlong
      normalEmbedding χ extensionCharacter)
variable
  (kernel_central :
    ∀ l : L, l ∈ cover.ker →
      coverEmbedding l ∈ Subgroup.center Ω)

/-- A normalized set-theoretic section of the covering map. -/
def normalizedSection (a : Γ) : L := by
  classical
  exact
    if ha : a = 1 then 1
    else Classical.choose (cover_surjective a)

@[simp]
theorem normalizedSection_one :
    normalizedSection cover cover_surjective 1 = 1 := by
  simp [normalizedSection]

@[simp]
theorem cover_normalizedSection (a : Γ) :
    cover (normalizedSection cover cover_surjective a) = a := by
  by_cases ha : a = 1
  · subst a
    simp
  · rw [normalizedSection, dif_neg ha]
    exact Classical.choose_spec (cover_surjective a)

/-- The central defect of the normalized section. -/
def sectionDefect (a b : Γ) : L :=
  normalizedSection cover cover_surjective a *
    normalizedSection cover cover_surjective b *
      (normalizedSection cover cover_surjective (a * b))⁻¹

theorem sectionDefect_mem_ker (a b : Γ) :
    sectionDefect cover cover_surjective a b ∈ cover.ker := by
  rw [MonoidHom.mem_ker]
  simp [sectionDefect]

/-- The overgroup word attached to a semidirect-product element. -/
def word (z : X ⋊[φ] Γ) : Ω :=
  normalEmbedding z.left *
    coverEmbedding
      (normalizedSection cover cover_surjective z.right)

include kernel_central
/-- The section defect, embedded in the overgroup, is central. -/
theorem embeddedSectionDefect_mem_center (a b : Γ) :
    coverEmbedding
        (sectionDefect cover cover_surjective a b) ∈
      Subgroup.center Ω :=
  kernel_central
    (sectionDefect cover cover_surjective a b)
    (sectionDefect_mem_ker cover cover_surjective a b)

include cover_conjugates kernel_central
/-- Multiplication of overgroup words differs from the selected word by
the embedded central section defect. -/
theorem word_mul (z t : X ⋊[φ] Γ) :
    word φ cover cover_surjective normalEmbedding coverEmbedding z *
        word φ cover cover_surjective normalEmbedding coverEmbedding t =
      coverEmbedding
          (sectionDefect cover cover_surjective z.right t.right) *
        word φ cover cover_surjective normalEmbedding coverEmbedding
          (z * t) := by
  let sz := normalizedSection cover cover_surjective z.right
  let st := normalizedSection cover cover_surjective t.right
  let szt := normalizedSection cover cover_surjective (z.right * t.right)
  have haction :
      normalEmbedding (φ z.right t.left) =
        coverEmbedding sz * normalEmbedding t.left *
          (coverEmbedding sz)⁻¹ := by
    simpa only [sz, cover_normalizedSection] using
      cover_conjugates sz t.left
  have hcentral :
      coverEmbedding (sectionDefect cover cover_surjective
          z.right t.right) ∈ Subgroup.center Ω :=
    embeddedSectionDefect_mem_center
      (cover := cover) (cover_surjective := cover_surjective)
      (coverEmbedding := coverEmbedding)
      (kernel_central := kernel_central) z.right t.right
  have hcomm :
      coverEmbedding
            (sectionDefect cover cover_surjective z.right t.right) *
          normalEmbedding
            (z.left * φ z.right t.left) =
        normalEmbedding
            (z.left * φ z.right t.left) *
          coverEmbedding
            (sectionDefect cover cover_surjective z.right t.right) :=
    (Subgroup.mem_center_iff.mp hcentral _).symm
  have hsection :
      coverEmbedding (sz * st) =
        coverEmbedding
            (sectionDefect cover cover_surjective
              z.right t.right) *
          coverEmbedding szt := by
    rw [← map_mul]
    congr 1
    simp only [sectionDefect, sz, st, szt]
    group
  calc
    word φ cover cover_surjective normalEmbedding coverEmbedding z *
          word φ cover cover_surjective normalEmbedding coverEmbedding t =
        normalEmbedding
            (z.left * φ z.right t.left) *
          coverEmbedding (sz * st) := by
      simp only [word, map_mul]
      rw [haction]
      dsimp only [sz, st]
      group
    _ =
        normalEmbedding
            (z.left * φ z.right t.left) *
          (coverEmbedding
              (sectionDefect cover cover_surjective
                z.right t.right) *
            coverEmbedding szt) := by rw [hsection]
    _ =
        coverEmbedding
            (sectionDefect cover cover_surjective
              z.right t.right) *
          (normalEmbedding
              (z.left * φ z.right t.left) *
            coverEmbedding szt) := by
      rw [← mul_assoc, ← hcomm, mul_assoc]
    _ =
        coverEmbedding
            (sectionDefect cover cover_surjective
              z.right t.right) *
          word φ cover cover_surjective normalEmbedding coverEmbedding
            (z * t) := by
      simp only [word, SemidirectProduct.mul_left,
        SemidirectProduct.mul_right, map_mul, sz, st, szt]

/-- The associated projective representation obtained from the extension
character and the common central cover. -/
def projectiveRepresentation :
    ProjectiveRepresentation ℂ (X ⋊[φ] Γ)
      extensionCharacter.realization where
  operator z :=
    AssociatedExistence.realizationAction extensionCharacter
      (word φ cover cover_surjective
        normalEmbedding coverEmbedding z)
  factor z t :=
    extensionCharacter.centralUnit
      (coverEmbedding
        (sectionDefect cover cover_surjective z.right t.right))
      (embeddedSectionDefect_mem_center
        (cover := cover) (cover_surjective := cover_surjective)
        (coverEmbedding := coverEmbedding)
        (kernel_central := kernel_central) z.right t.right)
  map_mul z t := by
    change
      AssociatedExistence.realizationAction extensionCharacter
            (word φ cover cover_surjective
              normalEmbedding coverEmbedding z) *
          AssociatedExistence.realizationAction extensionCharacter
            (word φ cover cover_surjective
              normalEmbedding coverEmbedding t) =
        scalarLinearEquiv ℂ extensionCharacter.realization
            (extensionCharacter.centralUnit
              (coverEmbedding
                (sectionDefect cover cover_surjective
                  z.right t.right))
              (embeddedSectionDefect_mem_center
                (cover := cover)
                (cover_surjective := cover_surjective)
                (coverEmbedding := coverEmbedding)
                (kernel_central := kernel_central)
                z.right t.right)) *
          AssociatedExistence.realizationAction extensionCharacter
            (word φ cover cover_surjective
              normalEmbedding coverEmbedding (z * t))
    rw [← map_mul,
      word_mul (φ := φ) (cover := cover)
        (cover_surjective := cover_surjective)
        (normalEmbedding := normalEmbedding)
        (coverEmbedding := coverEmbedding)
        (cover_conjugates := cover_conjugates)
        (kernel_central := kernel_central) z t,
      map_mul,
      extensionCharacter.realizationAction_eq_centralUnit]

@[simp]
theorem projectiveRepresentation_operator
    (z : X ⋊[φ] Γ) :
    (projectiveRepresentation
      (φ := φ) (cover := cover)
      (cover_surjective := cover_surjective)
      (normalEmbedding := normalEmbedding)
      (coverEmbedding := coverEmbedding)
      (cover_conjugates := cover_conjugates)
      (extensionCharacter := extensionCharacter)
      (kernel_central := kernel_central)).operator z =
      AssociatedExistence.realizationAction extensionCharacter
        (word φ cover cover_surjective
          normalEmbedding coverEmbedding z) :=
  rfl

@[simp]
theorem projectiveRepresentation_factor
    (z t : X ⋊[φ] Γ) :
    (projectiveRepresentation
      (φ := φ) (cover := cover)
      (cover_surjective := cover_surjective)
      (normalEmbedding := normalEmbedding)
      (coverEmbedding := coverEmbedding)
      (cover_conjugates := cover_conjugates)
      (extensionCharacter := extensionCharacter)
      (kernel_central := kernel_central)).factor z t =
      extensionCharacter.centralUnit
        (coverEmbedding
          (sectionDefect cover cover_surjective z.right t.right))
        (embeddedSectionDefect_mem_center
          (cover := cover) (cover_surjective := cover_surjective)
          (coverEmbedding := coverEmbedding)
          (kernel_central := kernel_central) z.right t.right) :=
  rfl

/-- The common-cover projective representation is associated with the
canonical semidirect character triple. -/
def associated :
    AssociatedProjectiveRepresentation
      (ofSemidirect φ χ hχ)
      extensionCharacter.realization
      (projectiveRepresentation
        (φ := φ) (cover := cover)
        (cover_surjective := cover_surjective)
        (normalEmbedding := normalEmbedding)
        (coverEmbedding := coverEmbedding)
        (cover_conjugates := cover_conjugates)
        (extensionCharacter := extensionCharacter)
        (kernel_central := kernel_central)) := by
  let rhoX : Representation ℂ X χ.realization :=
    χ.realization.ρ
  let res :
      Representation ℂ X extensionCharacter.realization :=
    extensionCharacter.realization.ρ.comp normalEmbedding
  letI : Representation.IsIrreducible rhoX :=
    CliffordRestriction.isIrreducible_of_simple χ.realization
  have hchar : res.character = rhoX.character := by
    funext g
    calc
      res.character g =
          extensionCharacter.realization.character
            (normalEmbedding g) := rfl
      _ = extensionCharacter.values (normalEmbedding g) :=
        congrFun extensionCharacter.realization_character _
      _ = χ.values g := extendsNormal g
      _ = χ.realization.character g :=
        (congrFun χ.realization_character g).symm
      _ = rhoX.character g := rfl
  let Phi :=
    Classical.choice
      (IrreducibleCharacter.Representation.nonempty_equiv_of_character_eq_irreducible
        rhoX res hchar)
  letI : Representation.IsIrreducible res :=
    IrreducibleCharacter.Representation.IsIrreducible.of_equiv Phi
  refine
    { restriction :=
        (AssociatedExistence.realizationAction extensionCharacter).comp
          (normalEmbedding.comp
            (AssociatedExistence.tripleNormalEquiv
              φ χ hχ).toMonoidHom)
      restriction_apply := ?_
      restriction_simple := ?_
      restriction_character := ?_
      normal_mul := ?_
      mul_normal := ?_ }
  · intro x
    rw [AssociatedExistence.coe_eq_inl_tripleNormalEquiv]
    change
      AssociatedExistence.realizationAction extensionCharacter
          (normalEmbedding
            (AssociatedExistence.tripleNormalEquiv φ χ hχ x)) =
        AssociatedExistence.realizationAction extensionCharacter
          (word φ cover cover_surjective normalEmbedding coverEmbedding
            (SemidirectProduct.inl
              (AssociatedExistence.tripleNormalEquiv φ χ hχ x)))
    simp [word]
  · let E :
        FDRep ℂ X ≌
          FDRep ℂ (ofSemidirect φ χ hχ).normalSubgroup :=
      Action.resEquiv
        (FGModuleCat ℂ)
        (AssociatedExistence.tripleNormalEquiv φ χ hχ)
    have hsimpleRes : Simple (FDRep.of res) :=
      RepresentationTheory.simple_fdRep_of_isIrreducible res
    change Simple (E.functor.obj (FDRep.of res))
    exact CategoryTheory.simple_obj E.functor (FDRep.of res)
  · funext x
    change
      extensionCharacter.realization.character
          (normalEmbedding
            (AssociatedExistence.tripleNormalEquiv φ χ hχ x)) =
        χ.values
          (AssociatedExistence.tripleNormalEquiv φ χ hχ x)
    rw [extensionCharacter.realization_character]
    exact extendsNormal _
  · intro x a
    rw [AssociatedExistence.coe_eq_inl_tripleNormalEquiv]
    simp only [projectiveRepresentation_operator]
    rw [show
      word φ cover cover_surjective normalEmbedding coverEmbedding
          (SemidirectProduct.inl
            (AssociatedExistence.tripleNormalEquiv φ χ hχ x)) =
        normalEmbedding
          (AssociatedExistence.tripleNormalEquiv φ χ hχ x) by
      simp [word]]
    change
      AssociatedExistence.realizationAction extensionCharacter
          (word φ cover cover_surjective normalEmbedding coverEmbedding
            (SemidirectProduct.inl
                (AssociatedExistence.tripleNormalEquiv
                  φ χ hχ x) * a)) =
        AssociatedExistence.realizationAction extensionCharacter
              (normalEmbedding
                (AssociatedExistence.tripleNormalEquiv
                  φ χ hχ x)) *
          AssociatedExistence.realizationAction extensionCharacter
            (word φ cover cover_surjective
              normalEmbedding coverEmbedding a)
    rw [← map_mul]
    apply congrArg
      (AssociatedExistence.realizationAction extensionCharacter)
    simp [word, mul_assoc]
  · intro a x
    rw [AssociatedExistence.coe_eq_inl_tripleNormalEquiv]
    simp only [projectiveRepresentation_operator]
    let y :=
      AssociatedExistence.tripleNormalEquiv φ χ hχ x
    rw [show
      word φ cover cover_surjective normalEmbedding coverEmbedding
          (SemidirectProduct.inl y) =
        normalEmbedding y by
      simp [word]]
    change
      AssociatedExistence.realizationAction extensionCharacter
          (word φ cover cover_surjective normalEmbedding coverEmbedding
            (a * SemidirectProduct.inl y)) =
        AssociatedExistence.realizationAction extensionCharacter
            (word φ cover cover_surjective
              normalEmbedding coverEmbedding a) *
          AssociatedExistence.realizationAction extensionCharacter
            (normalEmbedding y)
    rw [← map_mul]
    apply congrArg
      (AssociatedExistence.realizationAction extensionCharacter)
    have ha :
        normalEmbedding (φ a.right y) =
          coverEmbedding
              (normalizedSection cover cover_surjective a.right) *
            normalEmbedding y *
              (coverEmbedding
                (normalizedSection cover cover_surjective a.right))⁻¹ := by
      simpa only [cover_normalizedSection] using
        cover_conjugates
          (normalizedSection cover cover_surjective a.right) y
    simp only [word, SemidirectProduct.mul_left,
      SemidirectProduct.mul_right,
      SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, normalizedSection_one,
      map_one, mul_one]
    rw [map_mul, ha]
    group

end CommonCentralCoverSemidirectProjective
end CharacterTriple
end McKayConjecture
