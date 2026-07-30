/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GoodElementTwoGeneratorExtension
import McKayConjecture.Character.NavarroLocalGlobalExtension
import McKayConjecture.CharacterTriple.FactorSetAbelianSylowGluing
import McKayConjecture.CharacterTriple.ProjectiveObstructionExtension

/-!
# Navarro local--global extension for abelian outer quotients

For a finite character triple `T = (G, N, θ)` with abelian outer quotient,
extension of `θ` is detected on the full preimages of the Sylow subgroups of
`G / N`.

The proof uses the canonical associated projective representation.  On a
Sylow preimage its quotient factor set is literally the pullback of the
ambient quotient factor set through the canonical quotient equivalence.
Thus a local ordinary extension supplies a splitting of the corresponding
Sylow-restricted factor-set extension.  The elementary abelian Sylow gluing
theorem then supplies a global splitting, hence a global ordinary extension.
-/

noncomputable section

open scoped IsMulCommutative

namespace McKayConjecture
namespace CharacterTriple

open GroupTheory

variable {G : Type} [Group G] [Finite G]

/-- The canonical quotient equivalence for a full preimage, with its source
written using the normal subgroup field of the restricted character triple.
This wrapper keeps dependent quotient instances aligned definitionally. -/
def restrictToPreimageQuotientEquiv
    (T : CharacterTriple G)
    (R : Subgroup (G ⧸ T.normalSubgroup)) :
    let H :=
      quotientSubgroupPreimage T.normalSubgroup R
    let hNH :
        T.normalSubgroup ≤ H :=
      normal_le_quotientSubgroupPreimage
        T.normalSubgroup R
    H ⧸ (T.restrictTo H hNH).normalSubgroup ≃* R := by
  dsimp
  exact
    quotientSubgroupPreimageQuotientEquiv
      T.normalSubgroup R

@[simp]
theorem restrictToPreimageQuotientEquiv_mk
    (T : CharacterTriple G)
    (R : Subgroup (G ⧸ T.normalSubgroup))
    (x :
      quotientSubgroupPreimage T.normalSubgroup R) :
    restrictToPreimageQuotientEquiv T R
        (QuotientGroup.mk'
          ((T.restrictTo
            (quotientSubgroupPreimage T.normalSubgroup R)
            (normal_le_quotientSubgroupPreimage
              T.normalSubgroup R)).normalSubgroup) x) =
      quotientSubgroupPreimageProjection
        T.normalSubgroup R x := by
  rfl

namespace AssociatedProjectiveRepresentation

variable {T : CharacterTriple G}
variable {V : Type}
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ G V}

/-- On the full preimage of a quotient subgroup, restricting an associated
lift and then descending its factor is the same as pulling the ambient
quotient factor back through the canonical preimage-quotient equivalence. -/
theorem restrictTo_quotientFactorSet_eq_comap_preimageQuotientEquiv
    (A : AssociatedProjectiveRepresentation T V P)
    (R : Subgroup (G ⧸ T.normalSubgroup)) :
    let H :=
      quotientSubgroupPreimage T.normalSubgroup R
    let hNH :
        T.normalSubgroup ≤ H :=
      normal_le_quotientSubgroupPreimage
        T.normalSubgroup R
    let e :=
      restrictToPreimageQuotientEquiv T R
    (A.restrictTo H hNH).quotientFactorSet =
      A.quotientFactorSet.comap
        ((R.subtype).comp e.toMonoidHom) := by
  dsimp only
  apply FactorSet.ext
  intro q r
  induction q using QuotientGroup.induction_on with
  | H x =>
      induction r using QuotientGroup.induction_on with
      | H y =>
          change
            (A.restrictTo
                (quotientSubgroupPreimage T.normalSubgroup R)
                (normal_le_quotientSubgroupPreimage
                  T.normalSubgroup R)).quotientFactorSet
                  (QuotientGroup.mk'
                    ((T.restrictTo
                      (quotientSubgroupPreimage
                        T.normalSubgroup R)
                      (normal_le_quotientSubgroupPreimage
                        T.normalSubgroup R)).normalSubgroup) x)
                  (QuotientGroup.mk'
                    ((T.restrictTo
                      (quotientSubgroupPreimage
                        T.normalSubgroup R)
                      (normal_le_quotientSubgroupPreimage
                        T.normalSubgroup R)).normalSubgroup) y) =
              _
          simp only [quotientFactorSet_mk,
            ProjectiveRepresentation.comap_factor]
          change
            P.factor (x : G) (y : G) =
              A.quotientFactorSet
                (((R.subtype).comp
                  (quotientSubgroupPreimageQuotientEquiv
                    T.normalSubgroup R).toMonoidHom)
                  (QuotientGroup.mk'
                    (T.normalSubgroup.subgroupOf
                      (quotientSubgroupPreimage
                        T.normalSubgroup R)) x))
                (((R.subtype).comp
                  (quotientSubgroupPreimageQuotientEquiv
                    T.normalSubgroup R).toMonoidHom)
                  (QuotientGroup.mk'
                    (T.normalSubgroup.subgroupOf
                      (quotientSubgroupPreimage
                        T.normalSubgroup R)) y))
          simp only [MonoidHom.comp_apply]
          exact A.quotientFactorSet_mk (x : G) (y : G) |>.symm

end AssociatedProjectiveRepresentation

namespace FactorSet

open AssociatedProjectiveRepresentation

/-- The quotient factor of a restricted associated lift, transported back
along the canonical quotient-preimage equivalence, is the literal Sylow
restriction of the ambient quotient factor. -/
theorem restrictedAssociatedFactor_comap_preimageQuotientEquiv_symm
    (T : CharacterTriple G)
    (R : Subgroup (G ⧸ T.normalSubgroup)) :
    let A := AssociatedGeneralExistence.associated T
    let H :=
      quotientSubgroupPreimage T.normalSubgroup R
    let hNH :
        T.normalSubgroup ≤ H :=
      normal_le_quotientSubgroupPreimage
        T.normalSubgroup R
    let e :=
      restrictToPreimageQuotientEquiv T R
    ((A.restrictTo H hNH).quotientFactorSet.comap
        e.symm.toMonoidHom) =
      A.quotientFactorSet.comap R.subtype := by
  dsimp only
  rw [
    restrictTo_quotientFactorSet_eq_comap_preimageQuotientEquiv]
  apply FactorSet.ext
  intro q r
  change
    (AssociatedGeneralExistence.associated T).quotientFactorSet
        (R.subtype
          ((quotientSubgroupPreimageQuotientEquiv
            T.normalSubgroup R)
            ((quotientSubgroupPreimageQuotientEquiv
              T.normalSubgroup R).symm q)))
        (R.subtype
          ((quotientSubgroupPreimageQuotientEquiv
            T.normalSubgroup R)
            ((quotientSubgroupPreimageQuotientEquiv
              T.normalSubgroup R).symm r))) =
      (AssociatedGeneralExistence.associated T).quotientFactorSet
        (R.subtype q) (R.subtype r)
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

end FactorSet

/-- An ordinary extension on a full quotient-subgroup preimage splits the
restriction of the canonical ambient obstruction factor to that quotient
subgroup. -/
theorem exists_canonicalAssociatedFactor_section_of_preimageExtension
    (T : CharacterTriple G)
    (R : Subgroup (G ⧸ T.normalSubgroup))
    (hlocal :
      let H :=
        quotientSubgroupPreimage T.normalSubgroup R
      let hNH :
          T.normalSubgroup ≤ H :=
        normal_le_quotientSubgroupPreimage
          T.normalSubgroup R
      (T.restrictTo H hNH).HasExtension) :
    let A := AssociatedGeneralExistence.associated T
    let alphaR :=
      A.quotientFactorSet.comap R.subtype
    let halphaR : alphaR.IsNormalized :=
      A.quotientFactorSet.comap_isNormalized
        R.subtype A.quotientFactorSet_isNormalized
    ∃ s :
        R →*
          FactorSet.CentralExtensionGroup alphaR halphaR,
      (FactorSet.CentralExtensionGroup.projection
          alphaR halphaR).comp s =
        MonoidHom.id R := by
  dsimp only at hlocal ⊢
  let A := AssociatedGeneralExistence.associated T
  let H :=
    quotientSubgroupPreimage T.normalSubgroup R
  let hNH :
      T.normalSubgroup ≤ H :=
    normal_le_quotientSubgroupPreimage
      T.normalSubgroup R
  let TR := T.restrictTo H hNH
  let AR := A.restrictTo H hNH
  let e := restrictToPreimageQuotientEquiv T R
  let alphaR :=
    A.quotientFactorSet.comap R.subtype
  let halphaR : alphaR.IsNormalized :=
    A.quotientFactorSet.comap_isNormalized
      R.subtype A.quotientFactorSet_isNormalized
  have hzero :
      letI :=
        trivialMulDistribMulAction
          (H ⧸ TR.normalSubgroup) ℂˣ
      TR.projectiveObstructionClass = 0 :=
    TR.projectiveObstructionClass_eq_zero_iff_exists_extension.mpr
      hlocal
  have hclass :
      letI :=
        trivialMulDistribMulAction
          (H ⧸ TR.normalSubgroup) ℂˣ
      AR.quotientFactorSet.h2Class = 0 :=
    AR.quotientFactorSet_h2Class_eq_projectiveObstructionClass.trans
      hzero
  have hcoh :
      AR.quotientFactorSet.Cohomologous
        (FactorSet.one :
          FactorSet (H ⧸ TR.normalSubgroup) ℂˣ) :=
    FactorSet.cohomologous_of_h2Class_eq
      (hclass.trans FactorSet.h2Class_one.symm)
  have hcomap :=
    FactorSet.comap_cohomologous
      hcoh e.symm.toMonoidHom
  have hleft :
      AR.quotientFactorSet.comap e.symm.toMonoidHom =
        alphaR :=
    FactorSet.restrictedAssociatedFactor_comap_preimageQuotientEquiv_symm
      T R
  have hright :
      (FactorSet.one :
          FactorSet (H ⧸ TR.normalSubgroup) ℂˣ).comap
            e.symm.toMonoidHom =
        (FactorSet.one : FactorSet R ℂˣ) := by
    apply FactorSet.ext
    intro q r
    rfl
  rw [hleft, hright] at hcomap
  exact
    (FactorSet.CentralExtensionGroup.cohomologous_one_iff_exists_section
        alphaR halphaR).mp hcomap

/-- A global extension restricts irreducibly to every full quotient-subgroup
preimage.  This direction does not require commutativity of the quotient. -/
theorem extendsToQuotientSylowPreimage_of_hasExtension
    (T : CharacterTriple G)
    (hglobal : T.HasExtension)
    {r : ℕ} [Fact r.Prime]
    (R : Sylow r (G ⧸ T.normalSubgroup)) :
    T.ExtendsToQuotientSylowPreimage R := by
  obtain ⟨psi, hpsi⟩ := hglobal
  let H :=
    quotientSubgroupPreimage T.normalSubgroup
      (R : Subgroup (G ⧸ T.normalSubgroup))
  let hNH :
      T.normalSubgroup ≤ H :=
    normal_le_quotientSubgroupPreimage
      T.normalSubgroup
      (R : Subgroup (G ⧸ T.normalSubgroup))
  let TR := T.restrictTo H hNH
  have hpsi' :
      IrreducibleCharacter.IsExtensionAlong
        (H.subtype.comp TR.normalSubgroup.subtype)
        TR.character psi := by
    intro x
    change
      psi.values (((x : TR.normalSubgroup) : H) : G) =
        T.character.values
          (T.normalSubgroupInEquiv H hNH x)
    rw [← normalSubgroupInEquiv_apply_coe T H hNH x]
    exact hpsi (T.normalSubgroupInEquiv H hNH x)
  obtain ⟨eta, heta, _⟩ :=
    IrreducibleCharacter.IsExtensionAlong.exists_intermediate
      hpsi'
  exact ⟨eta, heta⟩

/-- For an abelian outer quotient, extension on every full Sylow preimage
implies a global extension.  The proof glues splittings of the canonical
associated quotient factor set. -/
theorem hasExtension_of_quotientSylowPreimageExtensions_of_commutator_le
    (T : CharacterTriple G)
    (hcomm :
      _root_.commutator G ≤ T.normalSubgroup)
    (hlocal :
      ∀ (r : ℕ) (hr : r.Prime),
        letI : Fact r.Prime := ⟨hr⟩
        ∀ R : Sylow r (G ⧸ T.normalSubgroup),
          T.ExtendsToQuotientSylowPreimage R) :
    T.HasExtension := by
  letI : IsMulCommutative (G ⧸ T.normalSubgroup) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
      hcomm
  letI : CommGroup (G ⧸ T.normalSubgroup) := inferInstance
  let A := AssociatedGeneralExistence.associated T
  let alpha := A.quotientFactorSet
  let halpha : alpha.IsNormalized :=
    A.quotientFactorSet_isNormalized
  have hsylow :
      FactorSet.HasSylowRestrictionSections
        alpha halpha := by
    intro r hr
    letI : Fact r.Prime := ⟨hr⟩
    intro R
    have hlocalR :
        let H :=
          quotientSubgroupPreimage T.normalSubgroup
            (R : Subgroup (G ⧸ T.normalSubgroup))
        let hNH :
            T.normalSubgroup ≤ H :=
          normal_le_quotientSubgroupPreimage
            T.normalSubgroup
            (R : Subgroup (G ⧸ T.normalSubgroup))
        (T.restrictTo H hNH).HasExtension := by
      simpa only [ExtendsToQuotientSylowPreimage, HasExtension] using
        hlocal r hr R
    exact
      exists_canonicalAssociatedFactor_section_of_preimageExtension
        T (R : Subgroup (G ⧸ T.normalSubgroup)) hlocalR
  obtain ⟨c, _, hc⟩ :=
    FactorSet.exists_normalized_gauge_eq_one_of_hasSylowRestrictionSections
      alpha halpha hsylow
  have hcoh :
      alpha.Cohomologous
        (FactorSet.one :
          FactorSet (G ⧸ T.normalSubgroup) ℂˣ) :=
    ⟨c, hc.symm⟩
  have hclass :
      letI :=
        trivialMulDistribMulAction
          (G ⧸ T.normalSubgroup) ℂˣ
      alpha.h2Class = 0 :=
    (FactorSet.h2Class_eq_of_cohomologous hcoh).trans
      FactorSet.h2Class_one
  have hzero :
      letI :=
        trivialMulDistribMulAction
          (G ⧸ T.normalSubgroup) ℂˣ
      T.projectiveObstructionClass = 0 := by
    exact hclass
  exact
    T.exists_extension_of_projectiveObstructionClass_eq_zero
      hzero

/-- Navarro's Sylow-preimage local--global extension conclusion for character
triples with abelian outer quotient. -/
theorem navarroSylowPreimageExtensionConclusion_of_commutator_le
    (T : CharacterTriple G)
    (hcomm :
      _root_.commutator G ≤ T.normalSubgroup) :
    NavarroSylowPreimageExtensionConclusion T := by
  constructor
  · intro hglobal r hr
    letI : Fact r.Prime := ⟨hr⟩
    exact T.extendsToQuotientSylowPreimage_of_hasExtension hglobal
  · exact
      T.hasExtension_of_quotientSylowPreimageExtensions_of_commutator_le
        hcomm

end CharacterTriple
end McKayConjecture
