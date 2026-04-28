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
      let alpha := sheafH_filtered_colimit_h1_gTopNat Y'
      let ev := CategoryTheory.evaluation J' AddCommGrpCat.{u}
      let e_j := PreservesCokernel.iso (ev.obj j) alpha
      let e_j' := PreservesCokernel.iso (ev.obj j') alpha
      apply (cancel_epi (cokernel.π (alpha.app j))).mp
      have hπj :
          cokernel.π (alpha.app j) ≫ e_j.inv = (cokernel.π alpha).app j := by
        symm
        exact (Iso.eq_comp_inv e_j).2 (by
          simpa only [e_j] using (PreservesCokernel.π_iso_hom (ev.obj j) alpha))
      have hπj' :
          cokernel.π (alpha.app j') ≫ e_j'.inv = (cokernel.π alpha).app j' := by
        symm
        exact (Iso.eq_comp_inv e_j').2 (by
          simpa only [e_j'] using (PreservesCokernel.π_iso_hom (ev.obj j') alpha))
      change cokernel.π (alpha.app j) ≫
          (sheafH_filtered_colimit_h1_cokernelFunctor Y').map f ≫ e_j'.inv =
        cokernel.π (alpha.app j) ≫ e_j.inv ≫ (cokernel alpha).map f
      dsimp [sheafH_filtered_colimit_h1_cokernelFunctor]
      rw [← Category.assoc, cokernel.π_desc, Category.assoc, hπj']
      rw [← Category.assoc, hπj]
      simpa [Category.assoc] using
        (cokernel.π alpha).naturality f)

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
  rw [colimit.ι_map_assoc]
  simp [eQ, eInj, sectionsFunctor]
  exact congrArg
    (fun β :
      ((sheafH_filtered_colimit_succ_Inj Y').obj j) ⟶ qCocone.pt =>
        β.val.app (op ⊤))
    (cokernel.π_desc _ _ _)

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
  have hInj (j) : Injective (Inj.obj j) := by
    let ffData := MorphismProperty.functorialFactorizationData
      (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X))
      (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X)).rlp
    change Injective (ffData.Z.obj (Arrow.mk (0 : Ysh.obj j ⟶ 0)))
    exact IsGrothendieckAbelian.instInjectiveZMonomorphismsRlpMonoMapFactorizationDataRlpOfNatHom
  have h_mid (j) : Subsingleton (Sheaf.H (Inj.obj j) 1) := by
    letI : Injective (Inj.obj j) := hInj j
    exact sheafH_subsingleton_of_injective (Inj.obj j) 0
  have h_colim :=
    sheafH_filtered_colimit_succ_inj_subsingleton (X := X) (Y' := Ysh) 0 hInj
  haveI := createsFilteredColimit Inj
  have hc_psh_inj :=
    isColimitOfPreserves (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (colimit.isColimit Inj)
  have hc_sections_inj :=
    isColimitOfPreserves
      ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) hc_psh_inj
  haveI := createsFilteredColimit (sheafH_filtered_colimit_succ_quotient Ysh)
  have hc_psh_q :=
    isColimitOfPreserves (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (sheafH_filtered_colimit_succ_quotientCocone_isColimit Ysh csh hcsh)
  have hc_sections_q :=
    isColimitOfPreserves
      ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) hc_psh_q
  let eInj :=
    (colimit.isColimit (Inj ⋙ sectionsFunctor)).coconePointUniqueUpToIso hc_sections_inj
  let eQ :=
    (colimit.isColimit (sheafH_filtered_colimit_succ_quotient Ysh ⋙ sectionsFunctor)).coconePointUniqueUpToIso hc_sections_q
  let globalIso := by
    simpa [sectionsFunctor, ι'] using
      (sheafH_filtered_colimit_h1_global_cokernel_iso (Y' := Ysh) (c' := csh) (hc' := hcsh) h_colim)
  exact
    (HasColimit.isoOfNatIso (sheafH_filtered_colimit_h1_stageNatIso Ysh h_mid)).symm ≪≫
      HasColimit.isoOfNatIso (sheafH_filtered_colimit_h1_cokernelFunctorIso Ysh) ≪≫
      PreservesCokernel.iso (colim (J := J') (C := AddCommGrpCat.{u}))
        (sheafH_filtered_colimit_h1_gTopNat Ysh) ≪≫
      (cokernel.mapIso (f := (colim (J := J') (C := AddCommGrpCat.{u})).map
          (sheafH_filtered_colimit_h1_gTopNat Ysh))
        (sectionsFunctor.map (cokernel.π ι')) eInj eQ (by
          simpa [Inj, qCocone, sectionsFunctor, ι', eInj, eQ] using
            (sheafH_filtered_colimit_h1_boundary_square (Y' := Ysh) (c' := csh) (hc' := hcsh)
              (hc_sections_inj := hc_sections_inj) (hc_sections_q := hc_sections_q)))) ≪≫
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
  let toPsh := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let evTop := (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  let sectionsFunctor := sheafH_filtered_colimit_h1_sectionsFunctor (X := X)
  let ι' := sheafH_filtered_colimit_succ_iota Ysh csh hcsh
  have hInj (j) : Injective (Inj.obj j) := inferInstanceAs
    (Injective (IsGrothendieckAbelian.monoMapFactorizationDataRlp (0 : Ysh.obj j ⟶ 0)).Z)
  have h_mid (j) : Subsingleton (Sheaf.H (Inj.obj j) 1) := by
    letI : Injective (Inj.obj j) := hInj j
    exact sheafH_subsingleton_of_injective (Inj.obj j) 0
  have h_colim := sheafH_filtered_colimit_succ_inj_subsingleton (Y' := Ysh) 0 hInj
  haveI := createsFilteredColimit Inj
  have hc_sections_inj := isColimitOfPreserves evTop (isColimitOfPreserves toPsh (colimit.isColimit Inj))
  haveI := createsFilteredColimit (sheafH_filtered_colimit_succ_quotient Ysh)
  have hc_sections_q := isColimitOfPreserves evTop (isColimitOfPreserves toPsh (sheafH_filtered_colimit_succ_quotientCocone_isColimit Ysh csh hcsh))
  let eInj := (colimit.isColimit (Inj ⋙ sectionsFunctor)).coconePointUniqueUpToIso hc_sections_inj
  let eQ := (colimit.isColimit (sheafH_filtered_colimit_succ_quotient Ysh ⋙ sectionsFunctor)).coconePointUniqueUpToIso hc_sections_q
  let α := sheafH_filtered_colimit_h1_gTopNat Ysh
  let mapIso := cokernel.mapIso (f := (colim (C := AddCommGrpCat.{u})).map α) (sectionsFunctor.map (cokernel.π ι')) eInj eQ
      (sheafH_filtered_colimit_h1_boundary_square Ysh csh hcsh hc_sections_inj hc_sections_q)
  let globalIso := sheafH_filtered_colimit_h1_global_cokernel_iso Ysh csh hcsh h_colim
  dsimp [sheafH_filtered_colimit_comparison_one_iso]
  refine colimit.hom_ext (fun j => ?_)
  let stageHom := sheafH_filtered_colimit_succ_stage_hom Ysh csh hcsh j
  let appTop {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) := f.val.app (op ⊤)
  let stageCokMap :=
    cokernel.map (α.app j) (sectionsFunctor.map (cokernel.π ι'))
      (appTop stageHom.τ₂) (appTop stageHom.τ₃) (congrArg appTop stageHom.comm₂₃.symm)
  have hnat : stageCokMap ≫ globalIso.hom = _ ≫ (sheafCohomologyFunctor X 1).map (csh.ι.app j) :=
    sheafH1_cokernel_iso_of_subsingleton_middle_natural (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Ysh) j) (sheafH_filtered_colimit_succ_shortExact Ysh csh hcsh) stageHom (h_mid j) h_colim
  rw [HasColimit.isoOfNatIso_ι_inv_assoc, HasColimit.isoOfNatIso_ι_hom_assoc, colimit_ι_sheafH_filtered_colimit_comparison]
  let cokIso := sheafH_filtered_colimit_h1_cokernelFunctorIso Ysh
  simpa [Category.assoc, hnat, sheafH_filtered_colimit_h1_stageNatIso] using congrArg (fun t => (sheafH_filtered_colimit_h1_stageNatIso Ysh h_mid).inv.app j ≫ t ≫ globalIso.hom)
    (show cokIso.hom.app j ≫ colimit.ι (cokernel α) j ≫ (PreservesCokernel.iso (colim (C := AddCommGrpCat.{u})) α).hom ≫ mapIso.hom = stageCokMap from by
      apply (cancel_epi (cokernel.π (α.app j))).mp
      rw [← Category.assoc, show cokernel.π (α.app j) ≫ cokIso.hom.app j = (cokernel.π α).app j from (Iso.comp_inv_eq _).2 <| by
        simpa [cokIso, sheafH_filtered_colimit_h1_cokernelFunctorIso, α] using (PreservesCokernel.π_iso_hom ((evaluation J' AddCommGrpCat.{u}).obj j) α).symm,
        ← colimit.ι_map_assoc, PreservesCokernel.π_iso_hom_assoc, cokernel.mapIso_hom,
        cokernel.π_desc, colimit.comp_coconePointUniqueUpToIso_hom_assoc]
      exact (cokernel.π_desc _ _ _).symm)

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
  haveI :
      IsIso
        (sheafH_filtered_colimit_comparison
          (sheafH_filtered_colimit_succ_quotient Ysh) (m + 1) qCocone) :=
    ih
      (Ysh := sheafH_filtered_colimit_succ_quotient Ysh) (csh := qCocone)
      (sheafH_filtered_colimit_succ_quotientCocone_isColimit Ysh csh hcsh)
  have hInj (j) : Injective (Inj.obj j) := inferInstanceAs
    (Injective (IsGrothendieckAbelian.monoMapFactorizationDataRlp (0 : Ysh.obj j ⟶ 0)).Z)
  have h_mid (r) (j) : Subsingleton (Sheaf.H (Inj.obj j) (r + 1)) := by
    letI : Injective (Inj.obj j) := hInj j
    exact sheafH_subsingleton_of_injective (Inj.obj j) r
  have hFlasqueInj : IsFlasqueSheaf injCocone.pt := fun i => by
    simpa using
      (isFlasque_filtered_colimit
        (F := Inj)
        (hFlasque := fun j => by
          letI : Injective (Inj.obj j) := hInj j
          exact fun {_ _} i => (isFlasque_of_injective (Inj.obj j)) i)
        (c := injCocone)
        (hc := colimit.isColimit Inj)) i
  have h_colim (r) : Subsingleton (Sheaf.H injCocone.pt (r + 1)) := by
    simpa using sheafH_subsingleton_of_flasque X injCocone.pt hFlasqueInj r
  let domainIso :=
    sheafH_filtered_colimit_succ_shiftDomainIso Ysh (m + 1) (h_mid m) (h_mid (m + 1))
  let codomainIso :=
    sheafH_filtered_colimit_succ_shiftCodomainIso
      Ysh csh hcsh (m + 1) (h_colim m) (h_colim (m + 1))
  have hcompat :
      domainIso.hom ≫ sheafH_filtered_colimit_comparison Ysh (m + 1 + 1) csh =
        sheafH_filtered_colimit_comparison
            (sheafH_filtered_colimit_succ_quotient Ysh) (m + 1) qCocone ≫
          codomainIso.hom := by
    simpa [domainIso, codomainIso, qCocone] using
      sheafH_filtered_colimit_comparison_succ_compatibility
        (Ysh := Ysh) (csh := csh) (hcsh := hcsh) (n := m + 1)
        (h_mid m) (h_mid (m + 1)) (h_colim m) (h_colim (m + 1))
  rw [show
      sheafH_filtered_colimit_comparison Ysh (m + 1 + 1) csh =
        domainIso.inv ≫ domainIso.hom ≫
          sheafH_filtered_colimit_comparison Ysh (m + 1 + 1) csh by simp,
    hcompat]
  simp
  infer_instance

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
