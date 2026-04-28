import Aristotle.GrothendieckVanishing.main.PresheafFilteredColimitCore

/-!
  # Degree-one and higher filtered-colimit comparisons

  This file contains the degree-`1` and higher comparison arguments showing that
  sheaf cohomology commutes with filtered colimits on Noetherian spaces, building
  on the presheaf-boundary and successor-stage infrastructure in
  `PresheafFilteredColimitCore`.
-/

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

/-- The global-sections functor used in the degree-`1` filtered-colimit boundary
construction. -/
private noncomputable def sheafH_filtered_colimit_h1_sectionsFunctor
    {X : TopCat.{u}} :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)

/-- The stagewise top-sections map from the injective replacement to its quotient in the
degree-`1` filtered-colimit comparison. -/
private noncomputable def sheafH_filtered_colimit_h1_gTopNat
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    [Zero (TopCat.Sheaf AddCommGrpCat.{u} X)] :
    (sheafH_filtered_colimit_succ_Inj Y' ⋙ sheafH_filtered_colimit_h1_sectionsFunctor) ⟶
      (sheafH_filtered_colimit_succ_quotient Y' ⋙ sheafH_filtered_colimit_h1_sectionsFunctor) :=
  { app := fun j =>
      ((cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j)).val.app (op ⊤))
    naturality := fun j j' f => by
      have hπ :
          cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫
              (sheafH_filtered_colimit_succ_quotient Y').map f =
            ((sheafH_filtered_colimit_succ_Inj Y').map f) ≫
              cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j') := by
        dsimp [sheafH_filtered_colimit_succ_quotient]
        exact cokernel.π_desc _ _ _
      exact congrArg
        (fun α :
          ((sheafH_filtered_colimit_succ_Inj Y').obj j) ⟶
            (sheafH_filtered_colimit_succ_quotient Y').obj j' =>
          α.val.app (op ⊤)) hπ.symm }

/-- The functor of stagewise cokernels of the top-sections maps used in the degree-`1`
filtered-colimit boundary construction. -/
private noncomputable def sheafH_filtered_colimit_h1_cokernelFunctor
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    [Zero (TopCat.Sheaf AddCommGrpCat.{u} X)] :
    J' ⥤ AddCommGrpCat.{u} :=
  { obj := fun j => cokernel ((sheafH_filtered_colimit_h1_gTopNat Y').app j)
    map := fun {j j'} f =>
      cokernel.map
        ((sheafH_filtered_colimit_h1_gTopNat Y').app j)
        ((sheafH_filtered_colimit_h1_gTopNat Y').app j')
        (((sheafH_filtered_colimit_succ_Inj Y').map f).val.app (op ⊤))
        (((sheafH_filtered_colimit_succ_quotient Y').map f).val.app (op ⊤))
        (by
          simpa [sheafH_filtered_colimit_h1_sectionsFunctor] using
            ((sheafH_filtered_colimit_h1_gTopNat Y').naturality f).symm)
    map_id := fun j => by
      apply (cancel_epi (cokernel.π ((sheafH_filtered_colimit_h1_gTopNat Y').app j))).mp
      rw [cokernel.π_desc]
      have hq' :
          (sheafH_filtered_colimit_succ_quotient Y').map (𝟙 j) =
            𝟙 ((sheafH_filtered_colimit_succ_quotient Y').obj j) := by
        simp [sheafH_filtered_colimit_succ_quotient, cokernel.map]
      have hq :
          ((sheafH_filtered_colimit_succ_quotient Y').map (𝟙 j)).val.app (op ⊤) =
            𝟙 (((sheafH_filtered_colimit_succ_quotient Y').obj j).val.obj (op ⊤)) := by
        rw [hq']
        rfl
      rw [hq]
      exact Category.id_comp
        (cokernel.π ((sheafH_filtered_colimit_h1_gTopNat Y').app j))
    map_comp := fun {j j' j''} f g => by
      apply (cancel_epi (cokernel.π ((sheafH_filtered_colimit_h1_gTopNat Y').app j))).mp
      rw [cokernel.π_desc, ← Category.assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc]
      have hq' :
          (sheafH_filtered_colimit_succ_quotient Y').map (f ≫ g) =
            (sheafH_filtered_colimit_succ_quotient Y').map f ≫
              (sheafH_filtered_colimit_succ_quotient Y').map g := by
        simp [sheafH_filtered_colimit_succ_quotient, cokernel.map, Functor.map_comp]
      have hq :
          ((sheafH_filtered_colimit_succ_quotient Y').map (f ≫ g)).val.app (op ⊤) =
            ((sheafH_filtered_colimit_succ_quotient Y').map f).val.app (op ⊤) ≫
              ((sheafH_filtered_colimit_succ_quotient Y').map g).val.app (op ⊤) := by
        rw [hq']
        rfl
      rw [hq]
      simp [Category.assoc] }

/-- Evaluation at each diagram object identifies the stagewise cokernel functor with the
cokernel of `sheafH_filtered_colimit_h1_gTopNat`. -/
private noncomputable def sheafH_filtered_colimit_h1_cokernelFunctorIso
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    [Zero (TopCat.Sheaf AddCommGrpCat.{u} X)] :
    sheafH_filtered_colimit_h1_cokernelFunctor Y' ≅
      cokernel (sheafH_filtered_colimit_h1_gTopNat Y') :=
  NatIso.ofComponents
    (fun j =>
      (PreservesCokernel.iso
        ((CategoryTheory.evaluation J' AddCommGrpCat.{u}).obj j)
        (sheafH_filtered_colimit_h1_gTopNat Y')).symm)
    (fun {j j'} f => by
      let e_j :=
        PreservesCokernel.iso
          ((CategoryTheory.evaluation J' AddCommGrpCat.{u}).obj j)
          (sheafH_filtered_colimit_h1_gTopNat Y')
      let e_j' :=
        PreservesCokernel.iso
          ((CategoryTheory.evaluation J' AddCommGrpCat.{u}).obj j')
          (sheafH_filtered_colimit_h1_gTopNat Y')
      apply (cancel_epi
        (cokernel.π ((sheafH_filtered_colimit_h1_gTopNat Y').app j))).mp
      have hπj :
          cokernel.π ((sheafH_filtered_colimit_h1_gTopNat Y').app j) ≫
              e_j.inv =
            (cokernel.π (sheafH_filtered_colimit_h1_gTopNat Y')).app j := by
        symm
        exact (Iso.eq_comp_inv e_j).2 (by
          simpa using (PreservesCokernel.π_iso_hom
          ((CategoryTheory.evaluation J' AddCommGrpCat.{u}).obj j)
          (sheafH_filtered_colimit_h1_gTopNat Y')))
      have hπj' :
          cokernel.π ((sheafH_filtered_colimit_h1_gTopNat Y').app j') ≫
              e_j'.inv =
            (cokernel.π (sheafH_filtered_colimit_h1_gTopNat Y')).app j' := by
        symm
        exact (Iso.eq_comp_inv e_j').2 (by
          simpa using (PreservesCokernel.π_iso_hom
          ((CategoryTheory.evaluation J' AddCommGrpCat.{u}).obj j')
          (sheafH_filtered_colimit_h1_gTopNat Y')))
      change cokernel.π ((sheafH_filtered_colimit_h1_gTopNat Y').app j) ≫
          (sheafH_filtered_colimit_h1_cokernelFunctor Y').map f ≫ e_j'.inv =
        cokernel.π ((sheafH_filtered_colimit_h1_gTopNat Y').app j) ≫
          e_j.inv ≫
            (cokernel (sheafH_filtered_colimit_h1_gTopNat Y')).map f
      dsimp [sheafH_filtered_colimit_h1_cokernelFunctor]
      rw [show cokernel.π ((sheafH_filtered_colimit_h1_gTopNat Y').app j) ≫
            cokernel.map ((sheafH_filtered_colimit_h1_gTopNat Y').app j)
              ((sheafH_filtered_colimit_h1_gTopNat Y').app j')
              (((sheafH_filtered_colimit_succ_Inj Y').map f).val.app (op ⊤))
              (((sheafH_filtered_colimit_succ_quotient Y').map f).val.app (op ⊤))
              (by
                simpa [sheafH_filtered_colimit_h1_sectionsFunctor] using
                  ((sheafH_filtered_colimit_h1_gTopNat Y').naturality f).symm) ≫
            e_j'.inv =
          (cokernel.π ((sheafH_filtered_colimit_h1_gTopNat Y').app j) ≫
              cokernel.map ((sheafH_filtered_colimit_h1_gTopNat Y').app j)
                ((sheafH_filtered_colimit_h1_gTopNat Y').app j')
                (((sheafH_filtered_colimit_succ_Inj Y').map f).val.app (op ⊤))
                (((sheafH_filtered_colimit_succ_quotient Y').map f).val.app (op ⊤))
                (by
                  simpa [sheafH_filtered_colimit_h1_sectionsFunctor] using
                    ((sheafH_filtered_colimit_h1_gTopNat Y').naturality f).symm)) ≫
            e_j'.inv by
          simp [Category.assoc]]
      rw [cokernel.π_desc, Category.assoc, hπj']
      have hπj_assoc :
          cokernel.π ((sheafH_filtered_colimit_h1_gTopNat Y').app j) ≫
              e_j.inv ≫ (cokernel (sheafH_filtered_colimit_h1_gTopNat Y')).map f =
            (cokernel.π (sheafH_filtered_colimit_h1_gTopNat Y')).app j ≫
              (cokernel (sheafH_filtered_colimit_h1_gTopNat Y')).map f := by
        rw [← Category.assoc, hπj]
      rw [hπj_assoc]
      simpa [Category.assoc] using
        (cokernel.π (sheafH_filtered_colimit_h1_gTopNat Y')).naturality f)

/-- The stagewise identification of `H¹` with the cokernel of top sections for the
injective-replacement short exact sequence used in the filtered-colimit comparison. -/
private noncomputable def sheafH_filtered_colimit_h1_stageNatIso
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    [Zero (TopCat.Sheaf AddCommGrpCat.{u} X)]
    (h_mid : ∀ j, Subsingleton (Sheaf.H ((sheafH_filtered_colimit_succ_Inj Y').obj j) 1)) :
    sheafH_filtered_colimit_h1_cokernelFunctor Y' ≅
      Y' ⋙ sheafCohomologyFunctor X 1 :=
  NatIso.ofComponents
    (fun j => by
      simpa using
        (sheafH1_cokernel_iso_of_subsingleton_middle
          (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Y') j) (h_mid j)))
    (fun {j j'} f => by
      ext y
      simpa [sheafCohomologyFunctor_map_apply] using congrArg
        (fun m => AddCommGrpCat.Hom.hom m y)
        (sheafH1_cokernel_iso_of_subsingleton_middle_natural
          (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Y') j)
          (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Y') j')
          (sheafH_filtered_colimit_succ_stage_map_hom (Y' := Y') f)
          (h_mid j) (h_mid j')))

private theorem sheafH_filtered_colimit_h1_boundary_square
    {X : TopCat.{u}} {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) [Zero (TopCat.Sheaf AddCommGrpCat.{u} X)]
    (c' : Cocone Y') (hc' : IsColimit c')
    (hc_sections_inj : IsColimit ((sheafH_filtered_colimit_h1_sectionsFunctor (X := X)).mapCocone
      (sheafH_filtered_colimit_succ_injCocone Y')))
    (hc_sections_q : IsColimit ((sheafH_filtered_colimit_h1_sectionsFunctor (X := X)).mapCocone
      (sheafH_filtered_colimit_succ_quotientCocone Y' c' hc'))) :
    (colim (J := J') (C := AddCommGrpCat.{u})).map
        (sheafH_filtered_colimit_h1_gTopNat Y') ≫
      ((colimit.isColimit (sheafH_filtered_colimit_succ_quotient Y' ⋙
          sheafH_filtered_colimit_h1_sectionsFunctor (X := X))).coconePointUniqueUpToIso
        hc_sections_q).hom =
    ((colimit.isColimit (sheafH_filtered_colimit_succ_Inj Y' ⋙
          sheafH_filtered_colimit_h1_sectionsFunctor (X := X))).coconePointUniqueUpToIso
        hc_sections_inj).hom ≫
      (sheafH_filtered_colimit_h1_sectionsFunctor (X := X)).map
        (cokernel.π (sheafH_filtered_colimit_succ_iota Y' c' hc')) := by
  let sectionsFunctor := sheafH_filtered_colimit_h1_sectionsFunctor (X := X)
  let qCocone := sheafH_filtered_colimit_succ_quotientCocone Y' c' hc'
  let ι' := sheafH_filtered_colimit_succ_iota Y' c' hc'
  let eInj := (colimit.isColimit
    (sheafH_filtered_colimit_succ_Inj Y' ⋙ sectionsFunctor)).coconePointUniqueUpToIso
      hc_sections_inj
  let eQ := (colimit.isColimit
    (sheafH_filtered_colimit_succ_quotient Y' ⋙ sectionsFunctor)).coconePointUniqueUpToIso
      hc_sections_q
  change
    (colim (J := J') (C := AddCommGrpCat.{u})).map
        (sheafH_filtered_colimit_h1_gTopNat Y') ≫ eQ.hom =
      eInj.hom ≫ sectionsFunctor.map (cokernel.π ι')
  apply colimit.hom_ext
  intro j
  have hQj : colimit.ι (sheafH_filtered_colimit_succ_quotient Y' ⋙ sectionsFunctor) j ≫
      eQ.hom = (sectionsFunctor.mapCocone qCocone).ι.app j := by
    simp [eQ, qCocone, sectionsFunctor]
  have hInjj : colimit.ι (sheafH_filtered_colimit_succ_Inj Y' ⋙ sectionsFunctor) j ≫
      eInj.hom =
        (sectionsFunctor.mapCocone (sheafH_filtered_colimit_succ_injCocone Y')).ι.app j := by
    simp [eInj, sectionsFunctor]
  have hInjj_assoc : colimit.ι (sheafH_filtered_colimit_succ_Inj Y' ⋙ sectionsFunctor) j ≫
      eInj.hom ≫ sectionsFunctor.map (cokernel.π ι') =
        (sectionsFunctor.mapCocone (sheafH_filtered_colimit_succ_injCocone Y')).ι.app j ≫
          sectionsFunctor.map (cokernel.π ι') := by
    simpa [Category.assoc] using congrArg (fun t => t ≫ sectionsFunctor.map (cokernel.π ι')) hInjj
  rw [colimit.ι_map_assoc, hQj, hInjj_assoc]
  change ((cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j)).val.app (op ⊤)) ≫
      ((qCocone.ι.app j).val.app (op ⊤)) =
    ((sheafH_filtered_colimit_succ_injCocone Y').ι.app j).val.app (op ⊤) ≫
      ((cokernel.π ι').val.app (op ⊤))
  exact (congrArg
    (fun β :
      ((sheafH_filtered_colimit_succ_Inj Y').obj j) ⟶ qCocone.pt =>
        β.val.app (op ⊤))
    (cokernel.π_desc _ _ _))

private noncomputable def sheafH_filtered_colimit_h1_global_cokernel_iso
    {X : TopCat.{u}} {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) [Zero (TopCat.Sheaf AddCommGrpCat.{u} X)]
    (c' : Cocone Y') (hc' : IsColimit c')
    (h_colim : Subsingleton (Sheaf.H (sheafH_filtered_colimit_succ_injCocone Y').pt 1)) :
    cokernel ((sheafH_filtered_colimit_h1_sectionsFunctor (X := X)).map
      (cokernel.π (sheafH_filtered_colimit_succ_iota Y' c' hc'))) ≅
        AddCommGrpCat.of (Sheaf.H c'.pt 1) := by
  let sectionsFunctor := sheafH_filtered_colimit_h1_sectionsFunctor (X := X)
  let qCocone := sheafH_filtered_colimit_succ_quotientCocone Y' c' hc'
  let ι' := sheafH_filtered_colimit_succ_iota Y' c' hc'
  change cokernel (sectionsFunctor.map (cokernel.π ι')) ≅
    AddCommGrpCat.of (Sheaf.H c'.pt 1)
  simpa [sectionsFunctor] using
    (sheafH1_cokernel_iso_of_subsingleton_middle
      (sheafH_filtered_colimit_succ_shortExact Y' c' hc') h_colim)

/-- The degree-`1` filtered-colimit comparison isomorphism, obtained by identifying `H¹`
with the cokernel of top sections for the injective-replacement short exact sequence. -/
private noncomputable def sheafH_filtered_colimit_comparison_one_iso
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Ysh : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (csh : Cocone Ysh) (hcsh : IsColimit csh) :
    colimit (Ysh ⋙ sheafCohomologyFunctor X 1) ≅
      AddCommGrpCat.of (Sheaf.H csh.pt 1) := by
  letI : Zero (TopCat.Sheaf AddCommGrpCat.{u} X) := Limits.HasZeroObject.zero' _
  let Inj := sheafH_filtered_colimit_succ_Inj Ysh
  let qCocone := sheafH_filtered_colimit_succ_quotientCocone Ysh csh hcsh
  let sectionsFunctor := sheafH_filtered_colimit_h1_sectionsFunctor (X := X)
  let ι' := sheafH_filtered_colimit_succ_iota Ysh csh hcsh
  have hqColim : IsColimit qCocone :=
    sheafH_filtered_colimit_succ_quotientCocone_isColimit Ysh csh hcsh
  have hInj : ∀ j, Injective (Inj.obj j) := by
    intro j
    let ffData := MorphismProperty.functorialFactorizationData
      (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X))
      (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X)).rlp
    change Injective (ffData.Z.obj (Arrow.mk (0 : Ysh.obj j ⟶ 0)))
    exact IsGrothendieckAbelian.instInjectiveZMonomorphismsRlpMonoMapFactorizationDataRlpOfNatHom
  have h_mid : ∀ j, Subsingleton (Sheaf.H (Inj.obj j) 1) := by
    intro j
    letI : Injective (Inj.obj j) := hInj j
    exact sheafH_subsingleton_of_injective (Inj.obj j) 0
  have h_colim : Subsingleton (Sheaf.H (sheafH_filtered_colimit_succ_injCocone Ysh).pt 1) := by
    simpa using
      (sheafH_filtered_colimit_succ_inj_subsingleton
        (X := X) (Y' := Ysh) 0 hInj)
  haveI := createsFilteredColimit Inj
  have hc_psh_inj :
      IsColimit ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone
        (sheafH_filtered_colimit_succ_injCocone Ysh)) :=
    isColimitOfPreserves (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (colimit.isColimit Inj)
  have hc_sections_inj :
      IsColimit (sectionsFunctor.mapCocone (sheafH_filtered_colimit_succ_injCocone Ysh)) :=
    isColimitOfPreserves
      ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) hc_psh_inj
  haveI := createsFilteredColimit (sheafH_filtered_colimit_succ_quotient Ysh)
  have hc_psh_q :
      IsColimit ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone
        qCocone) :=
    isColimitOfPreserves (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      hqColim
  have hc_sections_q : IsColimit (sectionsFunctor.mapCocone qCocone) :=
    isColimitOfPreserves
      ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) hc_psh_q
  let eInj :
      colimit (Inj ⋙ sectionsFunctor) ≅
        sectionsFunctor.obj (sheafH_filtered_colimit_succ_injCocone Ysh).pt :=
    (colimit.isColimit (Inj ⋙ sectionsFunctor)).coconePointUniqueUpToIso hc_sections_inj
  let eQ :
      colimit (sheafH_filtered_colimit_succ_quotient Ysh ⋙ sectionsFunctor) ≅
        sectionsFunctor.obj qCocone.pt :=
    (colimit.isColimit (sheafH_filtered_colimit_succ_quotient Ysh ⋙ sectionsFunctor)).coconePointUniqueUpToIso hc_sections_q
  have hsq :
      (colim (J := J') (C := AddCommGrpCat.{u})).map
          (sheafH_filtered_colimit_h1_gTopNat Ysh) ≫
        eQ.hom =
      eInj.hom ≫ sectionsFunctor.map (cokernel.π ι') := by
    simpa [Inj, qCocone, sectionsFunctor, ι', eInj, eQ] using
      (sheafH_filtered_colimit_h1_boundary_square (Y' := Ysh) (c' := csh) (hc' := hcsh)
        (hc_sections_inj := hc_sections_inj) (hc_sections_q := hc_sections_q))
  let globalIso :
      cokernel (sectionsFunctor.map (cokernel.π ι')) ≅ AddCommGrpCat.of (Sheaf.H csh.pt 1) := by
    simpa [sectionsFunctor, ι'] using
      (sheafH_filtered_colimit_h1_global_cokernel_iso (Y' := Ysh) (c' := csh) (hc' := hcsh) h_colim)
  exact
    (HasColimit.isoOfNatIso (sheafH_filtered_colimit_h1_stageNatIso Ysh h_mid)).symm ≪≫
      HasColimit.isoOfNatIso (sheafH_filtered_colimit_h1_cokernelFunctorIso Ysh) ≪≫
      PreservesCokernel.iso (colim (J := J') (C := AddCommGrpCat.{u}))
        (sheafH_filtered_colimit_h1_gTopNat Ysh) ≪≫
      (cokernel.mapIso (f := (colim (J := J') (C := AddCommGrpCat.{u})).map
          (sheafH_filtered_colimit_h1_gTopNat Ysh))
        (sectionsFunctor.map (cokernel.π ι')) eInj eQ hsq) ≪≫
      globalIso

@[simp] theorem sheafH_filtered_colimit_comparison_one_iso_hom
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Ysh : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (csh : Cocone Ysh) (hcsh : IsColimit csh) :
    (sheafH_filtered_colimit_comparison_one_iso
      (Ysh := Ysh) (csh := csh) (hcsh := hcsh)).hom =
      sheafH_filtered_colimit_comparison Ysh 1 csh := by
  letI : Zero (TopCat.Sheaf AddCommGrpCat.{u} X) := Limits.HasZeroObject.zero' _
  let Inj := sheafH_filtered_colimit_succ_Inj Ysh
  let qCocone := sheafH_filtered_colimit_succ_quotientCocone Ysh csh hcsh
  let sectionsFunctor := sheafH_filtered_colimit_h1_sectionsFunctor (X := X)
  let ι' := sheafH_filtered_colimit_succ_iota Ysh csh hcsh
  have hqColim : IsColimit qCocone :=
    sheafH_filtered_colimit_succ_quotientCocone_isColimit Ysh csh hcsh
  have hInj : ∀ j, Injective (Inj.obj j) := by
    intro j
    let ffData := MorphismProperty.functorialFactorizationData
      (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X))
      (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X)).rlp
    change Injective (ffData.Z.obj (Arrow.mk (0 : Ysh.obj j ⟶ 0)))
    exact IsGrothendieckAbelian.instInjectiveZMonomorphismsRlpMonoMapFactorizationDataRlpOfNatHom
  have h_mid : ∀ j, Subsingleton (Sheaf.H (Inj.obj j) 1) := by
    intro j
    letI : Injective (Inj.obj j) := hInj j
    exact sheafH_subsingleton_of_injective (Inj.obj j) 0
  have h_colim : Subsingleton (Sheaf.H (sheafH_filtered_colimit_succ_injCocone Ysh).pt 1) := by
    simpa using
      (sheafH_filtered_colimit_succ_inj_subsingleton
        (X := X) (Y' := Ysh) 0 hInj)
  haveI := createsFilteredColimit Inj
  have hc_psh_inj :
      IsColimit ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone
        (sheafH_filtered_colimit_succ_injCocone Ysh)) :=
    isColimitOfPreserves (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (colimit.isColimit Inj)
  have hc_sections_inj :
      IsColimit (sectionsFunctor.mapCocone (sheafH_filtered_colimit_succ_injCocone Ysh)) :=
    isColimitOfPreserves
      ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) hc_psh_inj
  haveI := createsFilteredColimit (sheafH_filtered_colimit_succ_quotient Ysh)
  have hc_psh_q :
      IsColimit ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone
        qCocone) :=
    isColimitOfPreserves (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      hqColim
  have hc_sections_q : IsColimit (sectionsFunctor.mapCocone qCocone) :=
    isColimitOfPreserves
      ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) hc_psh_q
  let eInj :
      colimit (Inj ⋙ sectionsFunctor) ≅
        sectionsFunctor.obj (sheafH_filtered_colimit_succ_injCocone Ysh).pt :=
    (colimit.isColimit (Inj ⋙ sectionsFunctor)).coconePointUniqueUpToIso hc_sections_inj
  let eQ :
      colimit (sheafH_filtered_colimit_succ_quotient Ysh ⋙ sectionsFunctor) ≅
        sectionsFunctor.obj qCocone.pt :=
    (colimit.isColimit (sheafH_filtered_colimit_succ_quotient Ysh ⋙ sectionsFunctor)).coconePointUniqueUpToIso hc_sections_q
  let α := sheafH_filtered_colimit_h1_gTopNat Ysh
  let stageIso :
      sheafH_filtered_colimit_h1_cokernelFunctor Ysh ≅
        Ysh ⋙ sheafCohomologyFunctor X 1 :=
    sheafH_filtered_colimit_h1_stageNatIso Ysh h_mid
  let functorCokIso :
      sheafH_filtered_colimit_h1_cokernelFunctor Ysh ≅ cokernel α :=
    sheafH_filtered_colimit_h1_cokernelFunctorIso Ysh
  let colimCokIso :
      colimit (cokernel α) ≅
        cokernel ((colim (J := J') (C := AddCommGrpCat.{u})).map α) :=
    PreservesCokernel.iso (colim (J := J') (C := AddCommGrpCat.{u})) α
  let mapIso :
      cokernel ((colim (J := J') (C := AddCommGrpCat.{u})).map α) ≅
        cokernel (sectionsFunctor.map (cokernel.π ι')) :=
    cokernel.mapIso (f := (colim (J := J') (C := AddCommGrpCat.{u})).map α)
      (sectionsFunctor.map (cokernel.π ι')) eInj eQ (by
      simpa [α, Inj, qCocone, sectionsFunctor, ι', eInj, eQ] using
        (sheafH_filtered_colimit_h1_boundary_square (Y' := Ysh) (c' := csh) (hc' := hcsh)
          (hc_sections_inj := hc_sections_inj) (hc_sections_q := hc_sections_q)))
  let globalIso :
      cokernel (sectionsFunctor.map (cokernel.π ι')) ≅ AddCommGrpCat.of (Sheaf.H csh.pt 1) := by
    simpa [sectionsFunctor, ι'] using
      (sheafH_filtered_colimit_h1_global_cokernel_iso (Y' := Ysh) (c' := csh) (hc' := hcsh) h_colim)
  let comparisonOne :=
    (HasColimit.isoOfNatIso stageIso).symm ≪≫
      HasColimit.isoOfNatIso functorCokIso ≪≫
      colimCokIso ≪≫ mapIso ≪≫ globalIso
  change comparisonOne.hom = sheafH_filtered_colimit_comparison Ysh 1 csh
  apply colimit.hom_ext
  intro j
  let stageShort := sheafH_filtered_colimit_succ_stage_shortExact (Y' := Ysh) j
  let stageIsoH1 :=
    sheafH1_cokernel_iso_of_subsingleton_middle stageShort (h_mid j)
  let stageHom := sheafH_filtered_colimit_succ_stage_hom Ysh csh hcsh j
  let stageCokMap :
      cokernel (α.app j) ⟶
        cokernel (sectionsFunctor.map (cokernel.π ι')) :=
    cokernel.map
      (α.app j)
      (sectionsFunctor.map (cokernel.π ι'))
      (((sheafH_filtered_colimit_succ_injCocone Ysh).ι.app j).val.app (op ⊤))
      ((qCocone.ι.app j).val.app (op ⊤))
      (by
        simpa [sectionsFunctor, sheafH_filtered_colimit_h1_gTopNat,
          sheafH_filtered_colimit_succ_shortComplex] using
          congrArg
            (fun β :
              ((sheafH_filtered_colimit_succ_Inj Ysh).obj j) ⟶
                (sheafH_filtered_colimit_succ_shortComplex Ysh csh hcsh).X₃ =>
              β.val.app (op ⊤))
            stageHom.comm₂₃.symm)
  have hstage_cok :
      (functorCokIso.hom.app j) ≫
          colimit.ι (cokernel α) j ≫
          colimCokIso.hom ≫
          mapIso.hom =
        stageCokMap := by
    let e_j := PreservesCokernel.iso
      ((CategoryTheory.evaluation J' AddCommGrpCat.{u}).obj j) α
    apply (cancel_epi (cokernel.π (α.app j))).mp
    change cokernel.π (α.app j) ≫
        (functorCokIso.hom.app j) ≫
          colimit.ι (cokernel α) j ≫
          colimCokIso.hom ≫
          mapIso.hom =
      cokernel.π (α.app j) ≫ stageCokMap
    have hfunctorCok :
        cokernel.π (α.app j) ≫ functorCokIso.hom.app j =
          (cokernel.π α).app j := by
      change cokernel.π (α.app j) ≫ e_j.inv = (cokernel.π α).app j
      symm
      exact (Iso.eq_comp_inv e_j).2 (by
        simpa using
          (PreservesCokernel.π_iso_hom
            ((CategoryTheory.evaluation J' AddCommGrpCat.{u}).obj j) α))
    calc
      cokernel.π (α.app j) ≫
          functorCokIso.hom.app j ≫
            colimit.ι (cokernel α) j ≫ colimCokIso.hom ≫ mapIso.hom =
        (cokernel.π α).app j ≫
          colimit.ι (cokernel α) j ≫ colimCokIso.hom ≫ mapIso.hom := by
            simpa [Category.assoc] using
              congrArg
                (fun t => t ≫ colimit.ι (cokernel α) j ≫ colimCokIso.hom ≫ mapIso.hom)
                hfunctorCok
      _ = colimit.ι (sheafH_filtered_colimit_succ_quotient Ysh ⋙ sectionsFunctor) j ≫
          cokernel.π (colim.map α) ≫ mapIso.hom := by
            rw [← colimit.ι_map_assoc, PreservesCokernel.π_iso_hom_assoc]
      _ = colimit.ι (sheafH_filtered_colimit_succ_quotient Ysh ⋙ sectionsFunctor) j ≫
          eQ.hom ≫ cokernel.π (sectionsFunctor.map (cokernel.π ι')) := by
            simpa [Category.assoc] using
              congrArg
                (fun t =>
                  colimit.ι (sheafH_filtered_colimit_succ_quotient Ysh ⋙ sectionsFunctor) j ≫ t)
                (cokernel.π_desc _ _ _)
      _ = (sectionsFunctor.mapCocone qCocone).ι.app j ≫
          cokernel.π (sectionsFunctor.map (cokernel.π ι')) := by
            rw [colimit.comp_coconePointUniqueUpToIso_hom_assoc]
      _ = cokernel.π (α.app j) ≫ stageCokMap :=
        (cokernel.π_desc _ _ _).symm
  have hnat :
      stageCokMap ≫ globalIso.hom =
        stageIsoH1.hom ≫ (sheafCohomologyFunctor X 1).map (csh.ι.app j) := by
    simpa [stageShort, stageIsoH1, globalIso, stageCokMap, stageHom, sectionsFunctor,
      sheafH_filtered_colimit_h1_global_cokernel_iso,
      sheafH_filtered_colimit_h1_gTopNat, sheafH_filtered_colimit_succ_shortComplex] using
      (sheafH1_cokernel_iso_of_subsingleton_middle_natural
        stageShort
        (sheafH_filtered_colimit_succ_shortExact Ysh csh hcsh)
        stageHom
        (h_mid j) h_colim)
  dsimp [comparisonOne]
  rw [HasColimit.isoOfNatIso_ι_inv_assoc, HasColimit.isoOfNatIso_ι_hom_assoc,
    colimit_ι_sheafH_filtered_colimit_comparison]
  simpa [stageIso, stageIsoH1] using
    calc
      stageIsoH1.inv ≫
          functorCokIso.hom.app j ≫
            colimit.ι (cokernel α) j ≫
              colimCokIso.hom ≫ mapIso.hom ≫ globalIso.hom =
        stageIsoH1.inv ≫ stageCokMap ≫ globalIso.hom := by
          simpa [Category.assoc] using
            congrArg (fun t => stageIsoH1.inv ≫ t ≫ globalIso.hom) hstage_cok
      _ = stageIsoH1.inv ≫
          (stageIsoH1.hom ≫ (sheafCohomologyFunctor X 1).map (csh.ι.app j)) := by
            rw [hnat]
      _ = (sheafCohomologyFunctor X 1).map (csh.ι.app j) := by simp

/-- The degree-`0` filtered-colimit comparison isomorphism, obtained from global sections. -/
private noncomputable def sheafH_filtered_colimit_comparison_zero_iso
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Ysh : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (csh : Cocone Ysh) (hcsh : IsColimit csh) :
    colimit (Ysh ⋙ sheafCohomologyFunctor X 0) ≅ AddCommGrpCat.of (Sheaf.H csh.pt 0) := by
  let sectionsFunctor := sheafH_filtered_colimit_h1_sectionsFunctor (X := X)
  let h0Iso :
      Ysh ⋙ sheafCohomologyFunctor X 0 ≅ Ysh ⋙ sectionsFunctor :=
    Functor.isoWhiskerLeft Ysh (sheafH0NatIsoSections (X := X))
  haveI : CreatesColimit Ysh
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    createsFilteredColimit Ysh
  have hc_psh :
      IsColimit ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone
        csh) :=
    isColimitOfPreserves (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      hcsh
  have hc_sections : IsColimit (sectionsFunctor.mapCocone csh) := by
    simpa [sectionsFunctor] using
      (isColimitOfPreserves
        ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) hc_psh)
  exact
    HasColimit.isoOfNatIso h0Iso ≪≫
      (colimit.isColimit (Ysh ⋙ sectionsFunctor)).coconePointUniqueUpToIso hc_sections ≪≫
      ((sheafH0EquivSections csh.pt).toAddCommGrpIso).symm

@[simp] theorem sheafH_filtered_colimit_comparison_zero_iso_hom
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Ysh : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (csh : Cocone Ysh) (hcsh : IsColimit csh) :
    (sheafH_filtered_colimit_comparison_zero_iso
      (Ysh := Ysh) (csh := csh) (hcsh := hcsh)).hom =
      sheafH_filtered_colimit_comparison Ysh 0 csh := by
  let sectionsFunctor := sheafH_filtered_colimit_h1_sectionsFunctor (X := X)
  let h0Iso :
      Ysh ⋙ sheafCohomologyFunctor X 0 ≅ Ysh ⋙ sectionsFunctor :=
    Functor.isoWhiskerLeft Ysh (sheafH0NatIsoSections (X := X))
  haveI : CreatesColimit Ysh
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    createsFilteredColimit Ysh
  have hc_psh :
      IsColimit ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone
        csh) :=
    isColimitOfPreserves (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      hcsh
  have hc_sections : IsColimit (sectionsFunctor.mapCocone csh) := by
    simpa [sectionsFunctor] using
      (isColimitOfPreserves
        ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) hc_psh)
  apply colimit.hom_ext
  intro j
  simp only [sheafH_filtered_colimit_comparison_zero_iso, Iso.trans_hom]
  rw [HasColimit.isoOfNatIso_ι_hom_assoc, colimit.comp_coconePointUniqueUpToIso_hom_assoc,
    colimit_ι_sheafH_filtered_colimit_comparison]
  ext x
  change (sheafH0EquivSections csh.pt).symm
      (ConcreteCategory.hom ((csh.ι.app j).val.app (op ⊤))
        (sheafH0EquivSections (Ysh.obj j) x)) =
    ConcreteCategory.hom ((sheafCohomologyFunctor X 0).map (csh.ι.app j)) x
  apply (sheafH0EquivSections csh.pt).injective
  simpa [sheafCohomologyFunctor_map_apply] using
    (sheafH0EquivSections_natural (f := csh.ι.app j) (x := x)).symm

private theorem sheafH_filtered_colimit_comparison_isIso_zero
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Ysh : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (csh : Cocone Ysh) (hcsh : IsColimit csh) :
    IsIso (sheafH_filtered_colimit_comparison Ysh 0 csh) := by
  rw [← sheafH_filtered_colimit_comparison_zero_iso_hom
    (Ysh := Ysh) (csh := csh) (hcsh := hcsh)]
  infer_instance

private theorem sheafH_filtered_colimit_comparison_isIso_one
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Ysh : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (csh : Cocone Ysh) (hcsh : IsColimit csh) :
    IsIso (sheafH_filtered_colimit_comparison Ysh 1 csh) := by
  rw [← sheafH_filtered_colimit_comparison_one_iso_hom
    (Ysh := Ysh) (csh := csh) (hcsh := hcsh)]
  infer_instance

private theorem sheafH_filtered_colimit_comparison_isIso_succ_succ
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Ysh : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (csh : Cocone Ysh) (hcsh : IsColimit csh)
    (m : ℕ)
    (ih :
      ∀ {J'' : Type u} [SmallCategory J''] [IsFiltered J'']
        (Ysh : J'' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
        (csh : Cocone Ysh) (_ : IsColimit csh),
        IsIso (sheafH_filtered_colimit_comparison Ysh (m + 1) csh)) :
    IsIso (sheafH_filtered_colimit_comparison Ysh (m + 1 + 1) csh) := by
  letI : Zero (TopCat.Sheaf AddCommGrpCat.{u} X) := Limits.HasZeroObject.zero' _
  let Inj := sheafH_filtered_colimit_succ_Inj Ysh
  let injCocone := sheafH_filtered_colimit_succ_injCocone Ysh
  let qCocone := sheafH_filtered_colimit_succ_quotientCocone Ysh csh hcsh
  have hqColim : IsColimit qCocone :=
    sheafH_filtered_colimit_succ_quotientCocone_isColimit Ysh csh hcsh
  have h_quot :
      IsIso
        (sheafH_filtered_colimit_comparison
          (sheafH_filtered_colimit_succ_quotient Ysh) (m + 1) qCocone) := by
    exact ih
      (Ysh := sheafH_filtered_colimit_succ_quotient Ysh) (csh := qCocone) hqColim
  letI :
      IsIso
        (sheafH_filtered_colimit_comparison
          (sheafH_filtered_colimit_succ_quotient Ysh) (m + 1) qCocone) := h_quot
  have hInj : ∀ j, Injective (Inj.obj j) := by
    intro j
    let fac :=
      IsGrothendieckAbelian.monoMapFactorizationDataRlp
        (C := TopCat.Sheaf AddCommGrpCat.{u} X) (0 : Ysh.obj j ⟶ 0)
    change Injective fac.Z
    simpa only [injective_iff_rlp_monomorphisms_zero,
      (isZero_zero (TopCat.Sheaf AddCommGrpCat.{u} X)).eq_of_tgt fac.p 0] using fac.hp
  have h_mid_n : ∀ j, Subsingleton (Sheaf.H (Inj.obj j) (m + 1)) := by
    intro j
    letI : Injective (Inj.obj j) := hInj j
    exact sheafH_subsingleton_of_injective (Inj.obj j) m
  have h_mid_succ : ∀ j, Subsingleton (Sheaf.H (Inj.obj j) (m + 2)) := by
    intro j
    letI : Injective (Inj.obj j) := hInj j
    exact sheafH_subsingleton_of_injective (Inj.obj j) (m + 1)
  have hFlasqueInj : IsFlasqueSheaf injCocone.pt := fun i => by
    simpa using
      (isFlasque_filtered_colimit
        (F := Inj)
        (hFlasque := fun j => by
          letI : Injective (Inj.obj j) := hInj j
          exact fun {_ _} i => (isFlasque_of_injective (Inj.obj j)) i)
        (c := injCocone)
        (hc := colimit.isColimit Inj)) i
  have h_colim_n : Subsingleton (Sheaf.H injCocone.pt (m + 1)) := by
    simpa using sheafH_subsingleton_of_flasque X injCocone.pt hFlasqueInj m
  have h_colim_succ : Subsingleton (Sheaf.H injCocone.pt (m + 2)) := by
    simpa using sheafH_subsingleton_of_flasque X injCocone.pt hFlasqueInj (m + 1)
  let domainIso :=
    sheafH_filtered_colimit_succ_shiftDomainIso Ysh (m + 1) h_mid_n h_mid_succ
  let codomainIso :=
    sheafH_filtered_colimit_succ_shiftCodomainIso
      Ysh csh hcsh (m + 1) h_colim_n h_colim_succ
  have hcompat :
      domainIso.hom ≫ sheafH_filtered_colimit_comparison Ysh (m + 1 + 1) csh =
        sheafH_filtered_colimit_comparison
            (sheafH_filtered_colimit_succ_quotient Ysh) (m + 1) qCocone ≫
          codomainIso.hom := by
    simpa [domainIso, codomainIso, qCocone] using
      sheafH_filtered_colimit_comparison_succ_compatibility
        (Ysh := Ysh) (csh := csh) (hcsh := hcsh) (n := m + 1)
        h_mid_n h_mid_succ h_colim_n h_colim_succ
  have hrewrite :
      sheafH_filtered_colimit_comparison Ysh (m + 1 + 1) csh =
        domainIso.inv ≫
          sheafH_filtered_colimit_comparison
            (sheafH_filtered_colimit_succ_quotient Ysh) (m + 1) qCocone ≫
          codomainIso.hom := by
    calc
      sheafH_filtered_colimit_comparison Ysh (m + 1 + 1) csh
          = 𝟙 _ ≫ sheafH_filtered_colimit_comparison Ysh (m + 1 + 1) csh := by simp
      _ = domainIso.inv ≫ domainIso.hom ≫
            sheafH_filtered_colimit_comparison Ysh (m + 1 + 1) csh := by simp
      _ = domainIso.inv ≫
            (sheafH_filtered_colimit_comparison
              (sheafH_filtered_colimit_succ_quotient Ysh) (m + 1) qCocone ≫
                codomainIso.hom) := by rw [hcompat]
      _ = domainIso.inv ≫
            sheafH_filtered_colimit_comparison
              (sheafH_filtered_colimit_succ_quotient Ysh) (m + 1) qCocone ≫
            codomainIso.hom := by simp [Category.assoc]
  have hYshIso :
      IsIso (sheafH_filtered_colimit_comparison Ysh (m + 1 + 1) csh) := by
    rw [hrewrite]
    infer_instance
  exact hYshIso

private theorem sheafH_filtered_colimit_comparison_isIso
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Ysh : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (csh : Cocone Ysh) (hcsh : IsColimit csh)
    (n : ℕ) :
    IsIso (sheafH_filtered_colimit_comparison Ysh n csh) := by
  let P : ℕ → Prop := fun n =>
    ∀ {J' : Type u} [SmallCategory J'] [IsFiltered J']
      (Ysh : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
      (csh : Cocone Ysh) (hcsh : IsColimit csh),
      IsIso (sheafH_filtered_colimit_comparison Ysh n csh)
  have hP : ∀ n, P n := by
    intro n
    induction n with
    | zero =>
        intro J' _ _ Ysh csh hcsh
        exact sheafH_filtered_colimit_comparison_isIso_zero Ysh csh hcsh
    | succ n ih =>
        cases n with
        | zero =>
            intro J' _ _ Ysh csh hcsh
            exact sheafH_filtered_colimit_comparison_isIso_one Ysh csh hcsh
        | succ m =>
            intro J' _ _ Ysh csh hcsh
            exact sheafH_filtered_colimit_comparison_isIso_succ_succ
              (Ysh := Ysh) (csh := csh) (hcsh := hcsh) (m := m) ih
  exact hP n Ysh csh hcsh

/-- **Sheaf cohomology commutes with filtered colimits** on Noetherian spaces:
    the canonical comparison `colim H^n(F_j) ≅ H^n(colim F_j)` is an isomorphism. -/
noncomputable def sheafH_preserves_filtered_colimits
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (c' : Cocone Y') (hc' : IsColimit c')
    (n : ℕ) :
    colimit (Y' ⋙ sheafCohomologyFunctor X n) ≅ AddCommGrpCat.of (Sheaf.H c'.pt n) := by
  haveI : IsIso (sheafH_filtered_colimit_comparison Y' n c') := by
    exact sheafH_filtered_colimit_comparison_isIso Y' c' hc' n
  exact asIso (sheafH_filtered_colimit_comparison Y' n c')
