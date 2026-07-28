/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordOrbit
import McKayConjecture.Character.CyclicExtensionConstruction

/-!
# Exhaustivity of the Clifford correspondence

This file completes the Clifford correspondence.  Maschke semisimplicity is
applied to the induction of the fixed normal-subgroup constituent to its
inertia group.  A simple summand detected by Frobenius reciprocity supplies
the inverse constituent.
-/

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra

namespace McKayConjecture
namespace CliffordEquivalence

open CliffordCorrespondence

variable {G : Type} [Group G] [Fintype G]
variable (N : Subgroup G) [N.Normal]
variable (θ : IrreducibleCharacter N)

/-- Every irreducible ambient character lying over `θ` has a simple
inertia-group constituent which itself lies over `θ`. -/
theorem exists_inertia_constituent
    (χ : IrreducibleCharacter G)
    (hχ : LiesOverAlong N.subtype θ χ) :
    ∃ ψ : IrreducibleCharactersOverInertia N θ,
      ∃ f :
        ψ.1.realization ⟶
          FDRep.resSubgroup
            (IrreducibleCharacter.inertia N θ)
            χ.realization,
        f ≠ 0 := by
  let I := IrreducibleCharacter.inertia N θ
  let W := FDRep.resSubgroup I χ.realization
  obtain ⟨fN, hfN⟩ :=
    (liesOverAlong_iff_exists_nonzero N.subtype θ χ).mp hχ
  let fI :
      θ.realization ⟶
        FDRep.res (inertiaInclusion N θ) W :=
    fN ≫ (resInertiaResIsoResNormal N θ χ.realization).inv
  have hfI : fI ≠ 0 := by
    intro hzero
    apply hfN
    have hrecover :
        fI ≫ (resInertiaResIsoResNormal N θ χ.realization).hom =
          fN := by
      simp [fI]
    rw [← hrecover, hzero]
    simp
  let A := FDRep.ind (inertiaInclusion N θ) θ.realization
  let F : A ⟶ W :=
    (fdRepInductionRestrictionHomEquiv
      (inertiaInclusion N θ) θ.realization W).symm fI
  have hF : F ≠ 0 := by
    intro hzero
    apply hfI
    apply
      (fdRepInductionRestrictionHomEquiv
        (inertiaInclusion N θ) θ.realization W).symm.injective
    simpa [F, hzero]
  let FIntertwining :
      Representation.IntertwiningMap A.ρ W.ρ :=
    ((FDRep.forget₂HomLinearEquiv A W).symm F).hom
  let FModule :
      Representation.asModule A.ρ →ₗ[ℂ[I]]
        Representation.asModule W.ρ :=
    Representation.IntertwiningMap.equivLinearMapAsModule
      A.ρ W.ρ FIntertwining
  have hFModule : FModule ≠ 0 := by
    intro hzero
    apply hF
    apply (FDRep.forget₂HomLinearEquiv A W).symm.injective
    apply Rep.Hom.ext
    apply
      (Representation.IntertwiningMap.equivLinearMapAsModule
        A.ρ W.ρ).injective
    exact hzero
  letI :
      IsSemisimpleModule ℂ[I]
        (Representation.asModule A.ρ) := by
    infer_instance
  obtain ⟨S, hSsimple, hSmap⟩ :=
    LinearMap.exists_ne_zero_of_sSup_eq_top hFModule
      {S : Submodule ℂ[I] (Representation.asModule A.ρ) |
        IsSimpleModule ℂ[I] S}
      (IsSemisimpleModule.sSup_simples_eq_top
        ℂ[I] (Representation.asModule A.ρ))
  letI : IsSimpleModule ℂ[I] S := hSsimple
  letI : Nontrivial S :=
    IsSimpleModule.nontrivial ℂ[I] S
  obtain ⟨projection, hprojection⟩ :=
    IsSemisimpleModule.extension_property
      S.subtype S.subtype_injective
      (LinearMap.id : S →ₗ[ℂ[I]] S)
  have hprojection_ne : projection ≠ 0 := by
    obtain ⟨s, hs⟩ := exists_ne (0 : S)
    intro hzero
    have happ := LinearMap.congr_fun hprojection s
    rw [hzero] at happ
    change 0 = s at happ
    exact hs happ.symm
  letI : Module.Finite ℂ S :=
    Module.Finite.of_injective
      (S.subtype.restrictScalars ℂ)
      S.subtype_injective
  let ρS :=
    Representation.ofModule' (k := ℂ) (G := I) S
  have hρS_asAlgebraHom :
      ρS.asAlgebraHom = Algebra.lsmul ℂ ℂ S := by
    dsimp [ρS, Representation.asAlgebraHom,
      Representation.ofModule']
    exact
      (MonoidAlgebra.lift ℂ (Module.End ℂ S) I).apply_symm_apply _
  haveI : Representation.IsIrreducible ρS := by
    rw [Representation.irreducible_iff_isSimpleModule_asModule]
    exact IsSimpleModule.congr (by
      let e :
          Representation.asModule ρS ≃ₗ[ℂ[I]] S :=
        { toFun := fun x => x
          invFun := fun x => x
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun r x => by
            change
              ρS.asAlgebraHom r (show S from x) =
                r • (show S from x)
            rw [hρS_asAlgebraHom]
            rfl }
      exact e)
  let VS : FDRep ℂ I := FDRep.of ρS
  letI : Simple VS :=
    RepresentationTheory.simple_fdRep_of_isIrreducible ρS
  let moduleEquiv :
      Representation.asModule ρS ≃ₗ[ℂ[I]] S :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        change
          ρS.asAlgebraHom r (show S from x) =
            r • (show S from x)
        rw [hρS_asAlgebraHom]
        rfl }
  let inclusionModule :
      Representation.asModule ρS →ₗ[ℂ[I]]
        Representation.asModule A.ρ :=
    S.subtype.comp moduleEquiv.toLinearMap
  let inclusionIntertwining :
      Representation.IntertwiningMap ρS A.ρ :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      ρS A.ρ).symm inclusionModule
  let detectedIntertwining :
      Representation.IntertwiningMap ρS W.ρ :=
    FIntertwining.comp inclusionIntertwining
  have hdetectedIntertwining : detectedIntertwining ≠ 0 := by
    intro hzero
    apply hSmap
    have hzeroModule :
        FModule.comp inclusionModule = 0 := by
      apply
        (Representation.IntertwiningMap.equivLinearMapAsModule
          ρS W.ρ).symm.injective
      exact hzero
    ext s
    have happ :=
      LinearMap.congr_fun hzeroModule (moduleEquiv.symm s)
    simpa [inclusionModule] using happ
  let detectedRepHom :
      (Rep.of ρS ⟶ Rep.of W.ρ) :=
    (Rep.homLinearEquiv (Rep.of ρS) (Rep.of W.ρ)).symm
      detectedIntertwining
  let detectedHom : VS ⟶ W :=
    FDRep.forget₂HomLinearEquiv VS W detectedRepHom
  have hdetectedHom : detectedHom ≠ 0 := by
    intro hzero
    apply hdetectedIntertwining
    apply
      (Rep.homLinearEquiv (Rep.of ρS) (Rep.of W.ρ)).symm.injective
    apply (FDRep.forget₂HomLinearEquiv VS W).injective
    exact hzero
  let projectionModule :
      Representation.asModule A.ρ →ₗ[ℂ[I]]
        Representation.asModule ρS :=
    moduleEquiv.symm.toLinearMap.comp projection
  let projectionIntertwining :
      Representation.IntertwiningMap A.ρ ρS :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      A.ρ ρS).symm projectionModule
  have hprojectionIntertwining : projectionIntertwining ≠ 0 := by
    intro hzero
    apply hprojection_ne
    have hzeroModule : projectionModule = 0 := by
      apply
        (Representation.IntertwiningMap.equivLinearMapAsModule
          A.ρ ρS).symm.injective
      exact hzero
    ext a
    have happ := LinearMap.congr_fun hzeroModule a
    have ha : projection a = 0 := by
      apply moduleEquiv.symm.injective
      simpa [projectionModule] using happ
    exact congrArg Subtype.val ha
  let projectionRepHom :
      (Rep.of A.ρ ⟶ Rep.of ρS) :=
    (Rep.homLinearEquiv (Rep.of A.ρ) (Rep.of ρS)).symm
      projectionIntertwining
  let projectionHom : A ⟶ VS :=
    FDRep.forget₂HomLinearEquiv A VS projectionRepHom
  have hprojectionHom : projectionHom ≠ 0 := by
    intro hzero
    apply hprojectionIntertwining
    apply
      (Rep.homLinearEquiv (Rep.of A.ρ) (Rep.of ρS)).symm.injective
    apply (FDRep.forget₂HomLinearEquiv A VS).injective
    exact hzero
  let constituentVS :
      θ.realization ⟶
        FDRep.res (inertiaInclusion N θ) VS :=
    fdRepInductionRestrictionHomEquiv
      (inertiaInclusion N θ) θ.realization VS projectionHom
  have hconstituentVS : constituentVS ≠ 0 := by
    intro hzero
    apply hprojectionHom
    apply
      (fdRepInductionRestrictionHomEquiv
        (inertiaInclusion N θ) θ.realization VS).injective
    simpa [constituentVS, hzero]
  let ψ₀ : IrreducibleCharacter I :=
    IrreducibleCharacter.ofSimple VS
  let realizationIso : ψ₀.realization ≅ VS := by
    apply Classical.choice
    apply FDRep.nonempty_iso_of_character_eq
    rw [ψ₀.realization_character]
    rfl
  let constituentChosen :
      θ.realization ⟶
        FDRep.res (inertiaInclusion N θ) ψ₀.realization :=
    constituentVS ≫
      (FDRep.resFunctor (k := ℂ)
        (inertiaInclusion N θ)).map realizationIso.inv
  have hconstituentChosen : constituentChosen ≠ 0 := by
    intro hzero
    apply hconstituentVS
    have hrecover :
        constituentChosen ≫
            (FDRep.resFunctor (k := ℂ)
              (inertiaInclusion N θ)).map realizationIso.hom =
          constituentVS := by
      simp [constituentChosen]
    rw [← hrecover, hzero]
    simp
  have hψ₀ : LiesOverAlong (inertiaInclusion N θ) θ ψ₀ :=
    (liesOverAlong_iff_exists_nonzero
      (inertiaInclusion N θ) θ ψ₀).mpr
      ⟨constituentChosen, hconstituentChosen⟩
  let detectedChosen : ψ₀.realization ⟶ W :=
    realizationIso.hom ≫ detectedHom
  have hdetectedChosen : detectedChosen ≠ 0 := by
    intro hzero
    apply hdetectedHom
    have h :=
      congrArg (fun z => realizationIso.inv ≫ z) hzero
    simpa [detectedChosen, Category.assoc] using h
  exact
    ⟨⟨ψ₀, hψ₀⟩, detectedChosen, hdetectedChosen⟩

/-- Every irreducible character in the orbit block is induced from the
inertia group. -/
theorem induceOverInertiaOrbit_surjective :
    Function.Surjective (induceOverInertiaOrbit N θ) := by
  intro χ
  have hθ : LiesOverAlong N.subtype θ χ.1 :=
    (liesOverOrbit_iff_liesOver N θ χ.1).mp χ.2
  obtain ⟨ψ, f, hf⟩ :=
    exists_inertia_constituent N θ χ.1 hθ
  let inducedToχ :
      inertiaInduction N θ ψ.1.realization ⟶ χ.1.realization :=
    (inertiaInductionHomEquiv
      N θ ψ.1.realization χ.1.realization).symm f
  have hinducedToχ : inducedToχ ≠ 0 := by
    intro hzero
    apply hf
    apply
      (inertiaInductionHomEquiv
        N θ ψ.1.realization χ.1.realization).symm.injective
    simpa [inducedToχ, hzero]
  letI : Simple (inertiaInduction N θ ψ.1.realization) :=
    inertiaInduction_simple N θ ψ.1 ψ.2
  letI : IsIso inducedToχ :=
    (CategoryTheory.isIso_iff_nonzero inducedToχ).2 hinducedToχ
  refine ⟨ψ, ?_⟩
  apply Subtype.ext
  apply IrreducibleCharacter.ext
  funext g
  change
    (inertiaInduction N θ ψ.1.realization).character g =
      χ.1.values g
  rw [← χ.1.realization_character]
  exact congrFun (FDRep.char_iso (asIso inducedToχ)) g

/-- The ordinary Clifford correspondence as an equivalence of finite sets
of irreducible characters. -/
def cliffordCorrespondenceEquiv :
    IrreducibleCharactersOverInertia N θ ≃
      IrreducibleCharactersOverOrbit N θ :=
  Equiv.ofBijective
    (induceOverInertiaOrbit N θ)
    ⟨induceOverInertiaOrbit_injective N θ,
      induceOverInertiaOrbit_surjective N θ⟩

end CliffordEquivalence
end McKayConjecture
