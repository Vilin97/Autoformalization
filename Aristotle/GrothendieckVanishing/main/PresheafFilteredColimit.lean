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
noncomputable def sheafH_filtered_colimit_h1_sectionsFunctor
    {X : TopCat.{u}} :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)

/-- The stagewise top-sections map from the injective replacement to its quotient in the
degree-`1` filtered-colimit comparison. -/
noncomputable def sheafH_filtered_colimit_h1_gTopNat
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
noncomputable def sheafH_filtered_colimit_h1_cokernelFunctor
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
noncomputable def sheafH_filtered_colimit_h1_cokernelFunctorIso
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
noncomputable def sheafH_filtered_colimit_h1_stageNatIso
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
        (sheafH1_cokernel_iso_of_subsingleton_middle_presheaf
          (h₁ := (Y'.obj j).cond)
          (h₂ := ((sheafH_filtered_colimit_succ_Inj Y').obj j).cond)
          (h₃ := (cokernel ((sheafH_filtered_colimit_succ_eta Y').app j)).cond)
          (f := ((sheafH_filtered_colimit_succ_eta Y').app j).val)
          (g := (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j)).val)
          (sheafH_filtered_colimit_succ_eta_val_comp_cokernel_pi (Y' := Y') j)
          (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Y') j)
          (h_mid j)))
    (fun {j j'} f => by
      ext y
      simpa [sheafCohomologyFunctor_map_apply] using congrArg
        (fun m => AddCommGrpCat.Hom.hom m y)
        (sheafH1_cokernel_iso_of_subsingleton_middle_presheaf_natural
          (h₁₁ := (Y'.obj j).cond)
          (h₁₂ := ((sheafH_filtered_colimit_succ_Inj Y').obj j).cond)
          (h₁₃ := (cokernel ((sheafH_filtered_colimit_succ_eta Y').app j)).cond)
          (h₂₁ := (Y'.obj j').cond)
          (h₂₂ := ((sheafH_filtered_colimit_succ_Inj Y').obj j').cond)
          (h₂₃ := (cokernel ((sheafH_filtered_colimit_succ_eta Y').app j')).cond)
          (f₁ := ((sheafH_filtered_colimit_succ_eta Y').app j).val)
          (g₁ := (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j)).val)
          (sheafH_filtered_colimit_succ_eta_val_comp_cokernel_pi (Y' := Y') j)
          (f₂ := ((sheafH_filtered_colimit_succ_eta Y').app j').val)
          (g₂ := (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j')).val)
          (sheafH_filtered_colimit_succ_eta_val_comp_cokernel_pi (Y' := Y') j')
          (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Y') j)
          (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Y') j')
          (τ₁ := (Y'.map f).val)
          (τ₂ := ((sheafH_filtered_colimit_succ_Inj Y').map f).val)
          (τ₃ := ((sheafH_filtered_colimit_succ_quotient Y').map f).val)
          (by
            simpa using congrArg Sheaf.Hom.val
              ((sheafH_filtered_colimit_succ_stage_map_hom (Y' := Y') f).comm₁₂))
          (by
            simpa using congrArg Sheaf.Hom.val
              ((sheafH_filtered_colimit_succ_stage_map_hom (Y' := Y') f).comm₂₃))
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
    (sheafH1_cokernel_iso_of_subsingleton_middle_presheaf
      (h₁ := c'.pt.cond)
      (h₂ := (sheafH_filtered_colimit_succ_injCocone Y').pt.cond)
      (h₃ := qCocone.pt.cond)
      (f := ι'.val)
      (g := (cokernel.π ι').val)
      (by
        simpa [ι'] using
          sheafH_filtered_colimit_succ_iota_val_comp_cokernel_pi Y' c' hc')
      (sheafH_filtered_colimit_succ_shortExact Y' c' hc')
      h_colim)

/-- The degree-`1` filtered-colimit comparison isomorphism on the sheaf diagram attached to
a presheaf cocone, before rewriting it as `sheafH_filtered_colimit_comparison_presheaf`. -/
noncomputable def sheafH_filtered_colimit_comparison_one_iso_presheaf_boundary
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y : J' ⥤ TopCat.Presheaf AddCommGrpCat.{u} X)
    (hY : ∀ j, TopCat.Presheaf.IsSheaf (Y.obj j))
    (c : Cocone Y) (hc : IsColimit c)
    (hc_pt : TopCat.Presheaf.IsSheaf c.pt) :
    colimit (sheafH_filtered_colimit_presheafDiagram Y hY ⋙ sheafCohomologyFunctor X 1) ≅
      AddCommGrpCat.of (Sheaf.H (⟨c.pt, hc_pt⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) 1) := by
  let Ysh := sheafH_filtered_colimit_presheafDiagram Y hY
  let csh := sheafH_filtered_colimit_presheafCocone Y hY c hc_pt
  let hcsh : IsColimit csh :=
    sheafH_filtered_colimit_presheafCocone_isColimit Y hY c hc hc_pt
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
      (sheafH_filtered_colimit_succ_inj_subsingleton_presheaf
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

@[simp] theorem sheafH_filtered_colimit_comparison_one_iso_presheaf_boundary_hom
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y : J' ⥤ TopCat.Presheaf AddCommGrpCat.{u} X)
    (hY : ∀ j, TopCat.Presheaf.IsSheaf (Y.obj j))
    (c : Cocone Y) (hc : IsColimit c)
    (hc_pt : TopCat.Presheaf.IsSheaf c.pt) :
    (sheafH_filtered_colimit_comparison_one_iso_presheaf_boundary
      (Y := Y) (hY := hY) (c := c) (hc := hc) (hc_pt := hc_pt)).hom =
      sheafH_filtered_colimit_comparison
        (sheafH_filtered_colimit_presheafDiagram Y hY) 1
        (sheafH_filtered_colimit_presheafCocone Y hY c hc_pt) := by
  let Ysh := sheafH_filtered_colimit_presheafDiagram Y hY
  let csh := sheafH_filtered_colimit_presheafCocone Y hY c hc_pt
  let hcsh : IsColimit csh :=
    sheafH_filtered_colimit_presheafCocone_isColimit Y hY c hc hc_pt
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
      (sheafH_filtered_colimit_succ_inj_subsingleton_presheaf
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
    sheafH1_cokernel_iso_of_subsingleton_middle_presheaf
      (h₁ := (Ysh.obj j).cond)
      (h₂ := ((sheafH_filtered_colimit_succ_Inj Ysh).obj j).cond)
      (h₃ := (cokernel ((sheafH_filtered_colimit_succ_eta Ysh).app j)).cond)
      (f := ((sheafH_filtered_colimit_succ_eta Ysh).app j).val)
      (g := (cokernel.π ((sheafH_filtered_colimit_succ_eta Ysh).app j)).val)
      (sheafH_filtered_colimit_succ_eta_val_comp_cokernel_pi (Y' := Ysh) j)
      stageShort (h_mid j)
  let stageHom := sheafH_filtered_colimit_succ_stage_hom Ysh csh hcsh j
  let stageCokMap :
      cokernel ((sheafH_filtered_colimit_h1_gTopNat Ysh).app j) ⟶
        cokernel (sectionsFunctor.map (cokernel.π ι')) :=
    cokernel.map
      ((sheafH_filtered_colimit_h1_gTopNat Ysh).app j)
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
    have hQj :
        colimit.ι (sheafH_filtered_colimit_succ_quotient Ysh ⋙ sectionsFunctor) j ≫ eQ.hom =
          (sectionsFunctor.mapCocone qCocone).ι.app j := by
      simpa [eQ] using
        (colimit.comp_coconePointUniqueUpToIso_hom
          (F := sheafH_filtered_colimit_succ_quotient Ysh ⋙ sectionsFunctor) hc_sections_q j)
    have hQj_assoc :
        colimit.ι (sheafH_filtered_colimit_succ_quotient Ysh ⋙ sectionsFunctor) j ≫
            eQ.hom ≫ cokernel.π (sectionsFunctor.map (cokernel.π ι')) =
          (sectionsFunctor.mapCocone qCocone).ι.app j ≫
            cokernel.π (sectionsFunctor.map (cokernel.π ι')) := by
      simpa [Category.assoc] using
        congrArg (fun t => t ≫ cokernel.π (sectionsFunctor.map (cokernel.π ι'))) hQj
    have hmapIso :
        cokernel.π (colim.map α) ≫ mapIso.hom =
          eQ.hom ≫ cokernel.π (sectionsFunctor.map (cokernel.π ι')) := by
      exact cokernel.π_desc _ _ _
    have hmapIso_assoc :
        colimit.ι (sheafH_filtered_colimit_succ_quotient Ysh ⋙ sectionsFunctor) j ≫
            cokernel.π (colim.map α) ≫ mapIso.hom =
          colimit.ι (sheafH_filtered_colimit_succ_quotient Ysh ⋙ sectionsFunctor) j ≫
            eQ.hom ≫ cokernel.π (sectionsFunctor.map (cokernel.π ι')) := by
      simpa [Category.assoc] using
        congrArg
          (fun t =>
            colimit.ι (sheafH_filtered_colimit_succ_quotient Ysh ⋙ sectionsFunctor) j ≫ t)
          hmapIso
    apply (cancel_epi (cokernel.π ((sheafH_filtered_colimit_h1_gTopNat Ysh).app j))).mp
    change cokernel.π ((sheafH_filtered_colimit_h1_gTopNat Ysh).app j) ≫
        (functorCokIso.hom.app j) ≫
          colimit.ι (cokernel α) j ≫
          colimCokIso.hom ≫
          mapIso.hom =
      cokernel.π ((sheafH_filtered_colimit_h1_gTopNat Ysh).app j) ≫ stageCokMap
    have hfunctorCok :
        cokernel.π ((sheafH_filtered_colimit_h1_gTopNat Ysh).app j) ≫ functorCokIso.hom.app j =
          (cokernel.π α).app j := by
      change cokernel.π (α.app j) ≫ e_j.inv = (cokernel.π α).app j
      symm
      exact (Iso.eq_comp_inv e_j).2 (by
        simpa using
          (PreservesCokernel.π_iso_hom
            ((CategoryTheory.evaluation J' AddCommGrpCat.{u}).obj j) α))
    have hfunctorCok_assoc :
        cokernel.π ((sheafH_filtered_colimit_h1_gTopNat Ysh).app j) ≫
            functorCokIso.hom.app j ≫
              colimit.ι (cokernel α) j ≫
                colimCokIso.hom ≫ mapIso.hom =
          (cokernel.π α).app j ≫
            colimit.ι (cokernel α) j ≫
              colimCokIso.hom ≫ mapIso.hom := by
      simpa [Category.assoc] using
        congrArg
          (fun t =>
            t ≫ colimit.ι (cokernel α) j ≫ colimCokIso.hom ≫ mapIso.hom)
          hfunctorCok
    rw [hfunctorCok_assoc]
    rw [← colimit.ι_map_assoc, PreservesCokernel.π_iso_hom_assoc, hmapIso_assoc, hQj_assoc]
    exact (cokernel.π_desc _ _ _).symm
  have hnat :
      stageCokMap ≫ globalIso.hom =
        stageIsoH1.hom ≫ (sheafCohomologyFunctor X 1).map (csh.ι.app j) := by
    simpa [stageShort, stageIsoH1, globalIso, stageCokMap, stageHom, sectionsFunctor,
      sheafH_filtered_colimit_h1_global_cokernel_iso,
      sheafH_filtered_colimit_h1_gTopNat, sheafH_filtered_colimit_succ_shortComplex] using
      (sheafH1_cokernel_iso_of_subsingleton_middle_presheaf_natural
        (h₁₁ := (Ysh.obj j).cond)
        (h₁₂ := ((sheafH_filtered_colimit_succ_Inj Ysh).obj j).cond)
        (h₁₃ := (cokernel ((sheafH_filtered_colimit_succ_eta Ysh).app j)).cond)
        (h₂₁ := csh.pt.cond)
        (h₂₂ := (sheafH_filtered_colimit_succ_injCocone Ysh).pt.cond)
        (h₂₃ := qCocone.pt.cond)
        (f₁ := ((sheafH_filtered_colimit_succ_eta Ysh).app j).val)
        (g₁ := (cokernel.π ((sheafH_filtered_colimit_succ_eta Ysh).app j)).val)
        (sheafH_filtered_colimit_succ_eta_val_comp_cokernel_pi (Y' := Ysh) j)
        (f₂ := ι'.val)
        (g₂ := (cokernel.π ι').val)
        (by
          simpa [ι'] using
            sheafH_filtered_colimit_succ_iota_val_comp_cokernel_pi Ysh csh hcsh)
        stageShort
        (sheafH_filtered_colimit_succ_shortExact Ysh csh hcsh)
        (τ₁ := (csh.ι.app j).val)
        (τ₂ := ((sheafH_filtered_colimit_succ_injCocone Ysh).ι.app j).val)
        (τ₃ := (qCocone.ι.app j).val)
        (by
          simpa using congrArg Sheaf.Hom.val stageHom.comm₁₂)
        (by
          simpa using congrArg Sheaf.Hom.val stageHom.comm₂₃)
        (h_mid j) h_colim)
  dsimp [comparisonOne]
  rw [HasColimit.isoOfNatIso_ι_inv_assoc, HasColimit.isoOfNatIso_ι_hom_assoc,
    colimit_ι_sheafH_filtered_colimit_comparison]
  have hmain :
      stageIsoH1.inv ≫
          functorCokIso.hom.app j ≫
            colimit.ι (cokernel α) j ≫
              colimCokIso.hom ≫ mapIso.hom ≫ globalIso.hom =
        (sheafCohomologyFunctor X 1).map (csh.ι.app j) := by
    have hstage_cok_assoc :
        stageIsoH1.inv ≫
            functorCokIso.hom.app j ≫
              colimit.ι (cokernel α) j ≫
                colimCokIso.hom ≫ mapIso.hom ≫ globalIso.hom =
          stageIsoH1.inv ≫ stageCokMap ≫ globalIso.hom := by
      simpa [Category.assoc] using
        congrArg (fun t => stageIsoH1.inv ≫ t ≫ globalIso.hom) hstage_cok
    rw [hstage_cok_assoc]
    calc
      stageIsoH1.inv ≫ stageCokMap ≫ globalIso.hom
          = stageIsoH1.inv ≫
              (stageIsoH1.hom ≫ (sheafCohomologyFunctor X 1).map (csh.ι.app j)) := by
                rw [hnat]
      _ = (sheafCohomologyFunctor X 1).map (csh.ι.app j) := by simp [Category.assoc]
  simpa [stageIso, stageIsoH1] using hmain

/-- In degree `0`, the presheaf-boundary filtered-colimit comparison is the canonical
isomorphism obtained from the associated sheaf diagram. -/
noncomputable def sheafH_filtered_colimit_comparison_zero_iso_presheaf
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y : J' ⥤ TopCat.Presheaf AddCommGrpCat.{u} X)
    (hY : ∀ j, TopCat.Presheaf.IsSheaf (Y.obj j))
    (c : Cocone Y) (hc : IsColimit c)
    (hc_pt : TopCat.Presheaf.IsSheaf c.pt) :
    colimit (sheafH_presheafDiagram Y hY 0) ≅
      AddCommGrpCat.of (Sheaf.H (⟨c.pt, hc_pt⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) 0) := by
  simpa [sheafH_presheafDiagram] using
    (sheafH_filtered_colimit_comparison_zero_iso_presheaf_boundary
      (Y := Y) (hY := hY) (c := c) (hc := hc) (hc_pt := hc_pt))

@[simp] theorem sheafH_filtered_colimit_comparison_zero_iso_presheaf_hom
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y : J' ⥤ TopCat.Presheaf AddCommGrpCat.{u} X)
    (hY : ∀ j, TopCat.Presheaf.IsSheaf (Y.obj j))
    (c : Cocone Y) (hc : IsColimit c)
    (hc_pt : TopCat.Presheaf.IsSheaf c.pt) :
    (sheafH_filtered_colimit_comparison_zero_iso_presheaf
      (Y := Y) (hY := hY) (c := c) (hc := hc) (hc_pt := hc_pt)).hom =
      sheafH_filtered_colimit_comparison_presheaf Y hY c hc_pt 0 := by
  change
    (sheafH_filtered_colimit_comparison_zero_iso_presheaf_boundary
      (Y := Y) (hY := hY) (c := c) (hc := hc) (hc_pt := hc_pt)).hom =
        sheafH_filtered_colimit_comparison
          (sheafH_filtered_colimit_presheafDiagram Y hY) 0
          (sheafH_filtered_colimit_presheafCocone Y hY c hc_pt)
  exact sheafH_filtered_colimit_comparison_zero_iso_presheaf_boundary_hom
    (Y := Y) (hY := hY) (c := c) (hc := hc) (hc_pt := hc_pt)

/-- On a Noetherian space and for a filtered diagram, the degree-`0` presheaf-boundary
comparison morphism `colim H⁰(F_j) ⟶ H⁰(colim F_j)` is an isomorphism. -/
theorem sheafH_filtered_colimit_comparison_isIso_zero_presheaf
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y : J' ⥤ TopCat.Presheaf AddCommGrpCat.{u} X)
    (hY : ∀ j, TopCat.Presheaf.IsSheaf (Y.obj j))
    (c : Cocone Y) (hc : IsColimit c)
    (hc_pt : TopCat.Presheaf.IsSheaf c.pt) :
    IsIso (sheafH_filtered_colimit_comparison_presheaf Y hY c hc_pt 0) := by
  rw [← sheafH_filtered_colimit_comparison_zero_iso_presheaf_hom
    (Y := Y) (hY := hY) (c := c) (hc := hc) (hc_pt := hc_pt)]
  infer_instance

/-- In degree `1`, the presheaf-boundary filtered-colimit comparison is obtained by
identifying `H¹` with the cokernel of top sections for the injective-replacement short
exact sequence, commuting filtered colimits with that cokernel, and then applying the
colimit-level `H¹ ≅ cokernel` identification. -/
noncomputable def sheafH_filtered_colimit_comparison_one_iso_presheaf
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y : J' ⥤ TopCat.Presheaf AddCommGrpCat.{u} X)
    (hY : ∀ j, TopCat.Presheaf.IsSheaf (Y.obj j))
    (c : Cocone Y) (hc : IsColimit c)
    (hc_pt : TopCat.Presheaf.IsSheaf c.pt) :
    colimit (sheafH_presheafDiagram Y hY 1) ≅
      AddCommGrpCat.of (Sheaf.H (⟨c.pt, hc_pt⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) 1) := by
  simpa [sheafH_presheafDiagram] using
    (sheafH_filtered_colimit_comparison_one_iso_presheaf_boundary
      (Y := Y) (hY := hY) (c := c) (hc := hc) (hc_pt := hc_pt))

@[simp] theorem sheafH_filtered_colimit_comparison_one_iso_presheaf_hom
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y : J' ⥤ TopCat.Presheaf AddCommGrpCat.{u} X)
    (hY : ∀ j, TopCat.Presheaf.IsSheaf (Y.obj j))
    (c : Cocone Y) (hc : IsColimit c)
    (hc_pt : TopCat.Presheaf.IsSheaf c.pt) :
    (sheafH_filtered_colimit_comparison_one_iso_presheaf
      (Y := Y) (hY := hY) (c := c) (hc := hc) (hc_pt := hc_pt)).hom =
      sheafH_filtered_colimit_comparison_presheaf Y hY c hc_pt 1 := by
  change
    (sheafH_filtered_colimit_comparison_one_iso_presheaf_boundary
      (Y := Y) (hY := hY) (c := c) (hc := hc) (hc_pt := hc_pt)).hom =
        sheafH_filtered_colimit_comparison
          (sheafH_filtered_colimit_presheafDiagram Y hY) 1
          (sheafH_filtered_colimit_presheafCocone Y hY c hc_pt)
  exact sheafH_filtered_colimit_comparison_one_iso_presheaf_boundary_hom
    (Y := Y) (hY := hY) (c := c) (hc := hc) (hc_pt := hc_pt)

/-- On a Noetherian space and for a filtered diagram, the degree-`1` presheaf-boundary
comparison morphism `colim H¹(F_j) ⟶ H¹(colim F_j)` is an isomorphism. -/
theorem sheafH_filtered_colimit_comparison_isIso_one_presheaf
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y : J' ⥤ TopCat.Presheaf AddCommGrpCat.{u} X)
    (hY : ∀ j, TopCat.Presheaf.IsSheaf (Y.obj j))
    (c : Cocone Y) (hc : IsColimit c)
    (hc_pt : TopCat.Presheaf.IsSheaf c.pt) :
    IsIso (sheafH_filtered_colimit_comparison_presheaf Y hY c hc_pt 1) := by
  rw [← sheafH_filtered_colimit_comparison_one_iso_presheaf_hom
    (Y := Y) (hY := hY) (c := c) (hc := hc) (hc_pt := hc_pt)]
  infer_instance

/-- In degree `0`, the filtered-colimit comparison is the canonical isomorphism obtained by
transporting `H⁰ ≅ (-)(⊤)` across the created presheaf colimit and evaluation at `⊤`. -/
noncomputable def sheafH_filtered_colimit_comparison_zero_iso
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (c' : Cocone Y') (hc' : IsColimit c') :
    colimit (Y' ⋙ sheafCohomologyFunctor X 0) ≅ AddCommGrpCat.of (Sheaf.H c'.pt 0) := by
  haveI : CreatesColimit Y'
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    createsFilteredColimit Y'
  simpa [sheafH_presheafDiagram_sheafToPresheaf,
    sheafH_filtered_colimit_presheafDiagram_sheafToPresheaf,
    sheafH_filtered_colimit_presheafCocone_sheafToPresheaf] using
    (sheafH_filtered_colimit_comparison_zero_iso_presheaf
      (Y := Y' ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (hY := fun j => (Y'.obj j).cond)
      (c := (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone c')
      (hc := isColimitOfPreserves
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) hc')
      (hc_pt := c'.pt.cond))

@[simp] theorem sheafH_filtered_colimit_comparison_zero_iso_hom
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (c' : Cocone Y') (hc' : IsColimit c') :
    (sheafH_filtered_colimit_comparison_zero_iso Y' c' hc').hom =
      sheafH_filtered_colimit_comparison Y' 0 c' := by
  haveI : CreatesColimit Y'
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    createsFilteredColimit Y'
  change
    (sheafH_filtered_colimit_comparison_zero_iso_presheaf
      (Y := Y' ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (hY := fun j => (Y'.obj j).cond)
      (c := (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone c')
      (hc := isColimitOfPreserves
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) hc')
      (hc_pt := c'.pt.cond)).hom =
        sheafH_filtered_colimit_comparison Y' 0 c'
  rw [sheafH_filtered_colimit_comparison_zero_iso_presheaf_hom,
    sheafH_filtered_colimit_comparison_sheafToPresheaf]

/-- On a Noetherian space and for a filtered diagram, the degree-`0` comparison morphism
    `colim H⁰(F_j) ⟶ H⁰(colim F_j)` is an isomorphism. -/
theorem sheafH_filtered_colimit_comparison_isIso_zero
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (c' : Cocone Y') (hc' : IsColimit c') :
    IsIso (sheafH_filtered_colimit_comparison Y' 0 c') := by
  haveI : CreatesColimit Y'
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    createsFilteredColimit Y'
  simpa [sheafH_presheafDiagram_sheafToPresheaf,
    sheafH_filtered_colimit_comparison_presheaf,
    sheafH_filtered_colimit_presheafDiagram_sheafToPresheaf,
    sheafH_filtered_colimit_presheafCocone_sheafToPresheaf] using
    (sheafH_filtered_colimit_comparison_isIso_zero_presheaf
      (Y := Y' ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (hY := fun j => (Y'.obj j).cond)
      (c := (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone c')
      (hc := isColimitOfPreserves
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) hc')
      (hc_pt := c'.pt.cond))

/-- In degree `1`, the filtered-colimit comparison is obtained by identifying `H¹`
with the cokernel of top sections for the injective-replacement short exact sequence,
commuting filtered colimits with that cokernel, and then applying the colimit-level
`H¹ ≅ cokernel` identification. -/
noncomputable def sheafH_filtered_colimit_comparison_one_iso
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (c' : Cocone Y') (hc' : IsColimit c') :
    colimit (Y' ⋙ sheafCohomologyFunctor X 1) ≅ AddCommGrpCat.of (Sheaf.H c'.pt 1) := by
  haveI : CreatesColimit Y'
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    createsFilteredColimit Y'
  simpa [sheafH_presheafDiagram_sheafToPresheaf,
    sheafH_filtered_colimit_presheafDiagram_sheafToPresheaf,
    sheafH_filtered_colimit_presheafCocone_sheafToPresheaf] using
    (sheafH_filtered_colimit_comparison_one_iso_presheaf
      (Y := Y' ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (hY := fun j => (Y'.obj j).cond)
      (c := (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone c')
      (hc := isColimitOfPreserves
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) hc')
      (hc_pt := c'.pt.cond))

@[simp] theorem sheafH_filtered_colimit_comparison_one_iso_hom
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (c' : Cocone Y') (hc' : IsColimit c') :
    (sheafH_filtered_colimit_comparison_one_iso Y' c' hc').hom =
      sheafH_filtered_colimit_comparison Y' 1 c' := by
  haveI : CreatesColimit Y'
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    createsFilteredColimit Y'
  change
    (sheafH_filtered_colimit_comparison_one_iso_presheaf
      (Y := Y' ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (hY := fun j => (Y'.obj j).cond)
      (c := (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone c')
      (hc := isColimitOfPreserves
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) hc')
      (hc_pt := c'.pt.cond)).hom =
        sheafH_filtered_colimit_comparison Y' 1 c'
  rw [sheafH_filtered_colimit_comparison_one_iso_presheaf_hom,
    sheafH_filtered_colimit_comparison_sheafToPresheaf]

/-- On a Noetherian space and for a filtered diagram, the degree-`1` comparison morphism
    `colim H¹(F_j) ⟶ H¹(colim F_j)` is an isomorphism. -/
theorem sheafH_filtered_colimit_comparison_isIso_one
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (c' : Cocone Y') (hc' : IsColimit c') :
    IsIso (sheafH_filtered_colimit_comparison Y' 1 c') := by
  haveI : CreatesColimit Y'
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    createsFilteredColimit Y'
  simpa [sheafH_presheafDiagram_sheafToPresheaf,
    sheafH_filtered_colimit_comparison_presheaf,
    sheafH_filtered_colimit_presheafDiagram_sheafToPresheaf,
    sheafH_filtered_colimit_presheafCocone_sheafToPresheaf] using
    (sheafH_filtered_colimit_comparison_isIso_one_presheaf
      (Y := Y' ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (hY := fun j => (Y'.obj j).cond)
      (c := (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone c')
      (hc := isColimitOfPreserves
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) hc')
      (hc_pt := c'.pt.cond))

/-- The concrete filtered-colimit comparison isomorphism, stated at the presheaf boundary:
if the stages and the cocone point are sheaves, then the canonical comparison for the
associated sheaf diagram is an isomorphism. -/
theorem sheafH_filtered_colimit_comparison_isIso_presheaf
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y : J' ⥤ TopCat.Presheaf AddCommGrpCat.{u} X)
    (hY : ∀ j, TopCat.Presheaf.IsSheaf (Y.obj j))
    (c : Cocone Y) (hc : IsColimit c)
    (hc_pt : TopCat.Presheaf.IsSheaf c.pt)
    (n : ℕ) :
    IsIso (sheafH_filtered_colimit_comparison_presheaf Y hY c hc_pt n) := by
  let P : ℕ → Prop := fun n =>
    ∀ {J' : Type u} [SmallCategory J'] [IsFiltered J']
      (Y : J' ⥤ TopCat.Presheaf AddCommGrpCat.{u} X)
      (hY : ∀ j, TopCat.Presheaf.IsSheaf (Y.obj j))
      (c : Cocone Y) (hc : IsColimit c)
      (hc_pt : TopCat.Presheaf.IsSheaf c.pt),
      IsIso (sheafH_filtered_colimit_comparison_presheaf Y hY c hc_pt n)
  have hP : ∀ n, P n := by
    intro n
    induction n with
    | zero =>
        intro J' _ _ Y hY c hc hc_pt
        exact sheafH_filtered_colimit_comparison_isIso_zero_presheaf Y hY c hc hc_pt
    | succ n ih =>
        cases n with
        | zero =>
            intro J' _ _ Y hY c hc hc_pt
            exact sheafH_filtered_colimit_comparison_isIso_one_presheaf Y hY c hc hc_pt
        | succ m =>
            intro J' _ _ Y hY c hc hc_pt
            letI : Zero (TopCat.Sheaf AddCommGrpCat.{u} X) := Limits.HasZeroObject.zero' _
            let Ysh := sheafH_filtered_colimit_presheafDiagram Y hY
            let csh := sheafH_filtered_colimit_presheafCocone Y hY c hc_pt
            let hcsh : IsColimit csh :=
              sheafH_filtered_colimit_presheafCocone_isColimit Y hY c hc hc_pt
            let Inj := sheafH_filtered_colimit_succ_Inj Ysh
            let injCocone := sheafH_filtered_colimit_succ_injCocone Ysh
            let qCocone := sheafH_filtered_colimit_succ_quotientCocone Ysh csh hcsh
            have hqColim : IsColimit qCocone :=
              sheafH_filtered_colimit_succ_quotientCocone_isColimit Ysh csh hcsh
            have h_quot :
                IsIso
                  (sheafH_filtered_colimit_comparison
                    (sheafH_filtered_colimit_succ_quotient Ysh) (m + 1) qCocone) := by
              haveI : CreatesColimit (sheafH_filtered_colimit_succ_quotient Ysh)
                  (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
                createsFilteredColimit (sheafH_filtered_colimit_succ_quotient Ysh)
              simpa [sheafH_presheafDiagram_sheafToPresheaf,
                sheafH_filtered_colimit_comparison_presheaf,
                sheafH_filtered_colimit_presheafDiagram_sheafToPresheaf,
                sheafH_filtered_colimit_presheafCocone_sheafToPresheaf] using
                (ih
                  (Y := sheafH_filtered_colimit_succ_quotient Ysh ⋙
                    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
                  (hY := fun j => ((sheafH_filtered_colimit_succ_quotient Ysh).obj j).cond)
                  (c := (sheafToPresheaf (Opens.grothendieckTopology X)
                    AddCommGrpCat.{u}).mapCocone qCocone)
                  (hc := isColimitOfPreserves
                    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
                    hqColim)
                  (hc_pt := qCocone.pt.cond))
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
            haveI hFlasqueInj : IsFlasqueSheaf injCocone.pt := by
              haveI : CreatesColimit Inj
                  (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
                createsFilteredColimit Inj
              simpa using
                (isFlasque_filtered_colimit_presheaf
                  (F := Inj ⋙ sheafToPresheaf (Opens.grothendieckTopology X)
                    AddCommGrpCat.{u})
                  (hF := fun j => (Inj.obj j).cond)
                  (hFlasque := fun j => by
                    letI : Injective (Inj.obj j) := hInj j
                    simpa using (isFlasque_of_injective (Inj.obj j)))
                  (c := (sheafToPresheaf (Opens.grothendieckTopology X)
                    AddCommGrpCat.{u}).mapCocone injCocone)
                  (hc := isColimitOfPreserves
                    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
                    (colimit.isColimit Inj))
                  (hc_pt := injCocone.pt.cond))
            have h_colim_n : Subsingleton (Sheaf.H injCocone.pt (m + 1)) := by
              let F : TopCat.Presheaf AddCommGrpCat.{u} X := injCocone.pt.val
              have hF : F.IsSheaf := by
                simpa [F] using injCocone.pt.cond
              letI : IsFlasqueSheaf ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) := by
                simpa [F, hF] using hFlasqueInj
              simpa [F, hF] using
                (sheafH_subsingleton_of_flasque_presheaf (X := X) (F := F) hF m)
            have h_colim_succ : Subsingleton (Sheaf.H injCocone.pt (m + 2)) := by
              let F : TopCat.Presheaf AddCommGrpCat.{u} X := injCocone.pt.val
              have hF : F.IsSheaf := by
                simpa [F] using injCocone.pt.cond
              letI : IsFlasqueSheaf ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) := by
                simpa [F, hF] using hFlasqueInj
              simpa [F, hF] using
                (sheafH_subsingleton_of_flasque_presheaf (X := X) (F := F) hF (m + 1))
            let domainIso :=
              sheafH_filtered_colimit_succ_shiftDomainIso Ysh (m + 1) h_mid_n h_mid_succ
            let codomainIso :=
              sheafH_filtered_colimit_succ_shiftCodomainIso
                Ysh csh hcsh (m + 1) h_colim_n h_colim_succ
            have hcompare :
                sheafH_filtered_colimit_comparison_presheaf Y hY c hc_pt (m + 1 + 1) =
                  sheafH_filtered_colimit_comparison Ysh (m + 1 + 1) csh := by
              simpa [Ysh, csh] using
                (sheafH_filtered_colimit_comparison_sheafToPresheaf
                  (Y' := Ysh) (n := m + 1 + 1) (c' := csh))
            have hcompat_presheaf :
                domainIso.hom ≫
                    sheafH_filtered_colimit_comparison_presheaf Y hY c hc_pt (m + 1 + 1) =
                  sheafH_filtered_colimit_comparison
                      (sheafH_filtered_colimit_succ_quotient Ysh) (m + 1) qCocone ≫
                    codomainIso.hom := by
              simpa [domainIso, codomainIso, qCocone, Ysh, csh, hcsh] using
                sheafH_filtered_colimit_comparison_succ_compatibility_presheaf
                  (Y := Y) (hY := hY) (c := c) (hc_pt := hc_pt) (hcsh := hcsh) (n := m + 1)
                  h_mid_n h_mid_succ h_colim_n h_colim_succ
            have hcompat :
                domainIso.hom ≫ sheafH_filtered_colimit_comparison Ysh (m + 1 + 1) csh =
                  sheafH_filtered_colimit_comparison
                      (sheafH_filtered_colimit_succ_quotient Ysh) (m + 1) qCocone ≫
                    codomainIso.hom := by
              rw [← hcompare]
              exact hcompat_presheaf
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
            simpa [Ysh, csh, sheafH_presheafDiagram, sheafH_filtered_colimit_comparison_presheaf]
              using hYshIso
  exact hP n Y hY c hc hc_pt

/-- On a Noetherian space and for a filtered diagram, the canonical comparison morphism
    `colim H^n(F_j) ⟶ H^n(colim F_j)` is an isomorphism in every degree. -/
theorem sheafH_filtered_colimit_comparison_isIso
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) (c' : Cocone Y') (hc' : IsColimit c') :
    IsIso (sheafH_filtered_colimit_comparison Y' n c') := by
  haveI : CreatesColimit Y'
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    createsFilteredColimit Y'
  simpa [sheafH_presheafDiagram_sheafToPresheaf,
    sheafH_filtered_colimit_comparison_presheaf,
    sheafH_filtered_colimit_presheafDiagram_sheafToPresheaf,
    sheafH_filtered_colimit_presheafCocone_sheafToPresheaf] using
    (sheafH_filtered_colimit_comparison_isIso_presheaf
      (Y := Y' ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (hY := fun j => (Y'.obj j).cond)
      (c := (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone c')
      (hc := isColimitOfPreserves
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) hc')
      (hc_pt := c'.pt.cond) (n := n))

/-- The concrete filtered-colimit comparison isomorphism, stated at the presheaf boundary:
if the stages and the cocone point are sheaves, then the canonical comparison for the
associated sheaf diagram is an isomorphism. -/
noncomputable def sheafH_filtered_colimit_comparison_iso_presheaf
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y : J' ⥤ TopCat.Presheaf AddCommGrpCat.{u} X)
    (hY : ∀ j, TopCat.Presheaf.IsSheaf (Y.obj j))
    (c : Cocone Y) (hc : IsColimit c)
    (hc_pt : TopCat.Presheaf.IsSheaf c.pt)
    (n : ℕ) :
    colimit (sheafH_presheafDiagram Y hY n) ≅
      AddCommGrpCat.of (Sheaf.H (⟨c.pt, hc_pt⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) n) := by
  letI := sheafH_filtered_colimit_comparison_isIso_presheaf
    (Y := Y) (hY := hY) (c := c) (hc := hc) (hc_pt := hc_pt) (n := n)
  exact asIso (sheafH_filtered_colimit_comparison_presheaf Y hY c hc_pt n)

@[simp] theorem sheafH_filtered_colimit_comparison_iso_presheaf_hom
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y : J' ⥤ TopCat.Presheaf AddCommGrpCat.{u} X)
    (hY : ∀ j, TopCat.Presheaf.IsSheaf (Y.obj j))
    (c : Cocone Y) (hc : IsColimit c)
    (hc_pt : TopCat.Presheaf.IsSheaf c.pt)
    (n : ℕ) :
    (sheafH_filtered_colimit_comparison_iso_presheaf
      (Y := Y) (hY := hY) (c := c) (hc := hc) (hc_pt := hc_pt) (n := n)).hom =
      sheafH_filtered_colimit_comparison_presheaf Y hY c hc_pt n := by
  simp [sheafH_filtered_colimit_comparison_iso_presheaf]

/-- The canonical comparison isomorphism `colim H^n(F_j) ≅ H^n(colim F_j)` for filtered
    diagrams on Noetherian spaces. -/
noncomputable def sheafH_filtered_colimit_comparison_iso
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) (c' : Cocone Y') (hc' : IsColimit c') :
    colimit (Y' ⋙ sheafCohomologyFunctor X n) ≅ AddCommGrpCat.of (Sheaf.H c'.pt n) := by
  haveI : CreatesColimit Y'
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    createsFilteredColimit Y'
  simpa using
    (sheafH_filtered_colimit_comparison_iso_presheaf
      (Y := Y' ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (hY := fun j => (Y'.obj j).cond)
      (c := (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone c')
      (hc := isColimitOfPreserves
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) hc')
      (hc_pt := c'.pt.cond) (n := n))

@[simp] theorem sheafH_filtered_colimit_comparison_iso_hom
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) (c' : Cocone Y') (hc' : IsColimit c') :
    (sheafH_filtered_colimit_comparison_iso Y' n c' hc').hom =
      sheafH_filtered_colimit_comparison Y' n c' := by
  haveI : CreatesColimit Y'
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    createsFilteredColimit Y'
  change
    (sheafH_filtered_colimit_comparison_iso_presheaf
      (Y := Y' ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (hY := fun j => (Y'.obj j).cond)
      (c := (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone c')
      (hc := isColimitOfPreserves
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) hc')
      (hc_pt := c'.pt.cond) (n := n)).hom =
        sheafH_filtered_colimit_comparison Y' n c'
  rw [sheafH_filtered_colimit_comparison_iso_presheaf_hom,
    sheafH_filtered_colimit_comparison_sheafToPresheaf]

/-- **Sheaf cohomology commutes with filtered colimits** on Noetherian spaces:
    presheaf form. If the stages and cocone point are sheaves, the canonical comparison
    `colim H^n(F_j) ≅ H^n(colim F_j)` holds for the associated sheaf diagram. -/
noncomputable def sheafH_preserves_filtered_colimits_presheaf
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y : J' ⥤ TopCat.Presheaf AddCommGrpCat.{u} X)
    (hY : ∀ j, TopCat.Presheaf.IsSheaf (Y.obj j))
    (c : Cocone Y) (hc : IsColimit c)
    (hc_pt : TopCat.Presheaf.IsSheaf c.pt)
    (n : ℕ) :
    colimit (sheafH_presheafDiagram Y hY n) ≅
      AddCommGrpCat.of (Sheaf.H (⟨c.pt, hc_pt⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) n) :=
  sheafH_filtered_colimit_comparison_iso_presheaf
    (Y := Y) (hY := hY) (c := c) (hc := hc) (hc_pt := hc_pt) (n := n)

/-- The presheaf-form filtered-colimit comparison isomorphism has epi hom. -/
theorem sheafH_preserves_filtered_colimits_presheaf_hom_epi
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y : J' ⥤ TopCat.Presheaf AddCommGrpCat.{u} X)
    (hY : ∀ j, TopCat.Presheaf.IsSheaf (Y.obj j))
    (c : Cocone Y) (hc : IsColimit c)
    (hc_pt : TopCat.Presheaf.IsSheaf c.pt)
    (n : ℕ) :
    Epi ((sheafH_preserves_filtered_colimits_presheaf
      (Y := Y) (hY := hY) (c := c) (hc := hc) (hc_pt := hc_pt) (n := n)).hom) := by
  infer_instance

/-- The presheaf-boundary filtered-colimit comparison morphism is epi. -/
theorem sheafH_filtered_colimit_comparison_epi_presheaf
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y : J' ⥤ TopCat.Presheaf AddCommGrpCat.{u} X)
    (hY : ∀ j, TopCat.Presheaf.IsSheaf (Y.obj j))
    (c : Cocone Y) (hc : IsColimit c)
    (hc_pt : TopCat.Presheaf.IsSheaf c.pt)
    (n : ℕ) :
    Epi (sheafH_filtered_colimit_comparison_presheaf Y hY c hc_pt n) := by
  simpa [sheafH_preserves_filtered_colimits_presheaf] using
    (sheafH_preserves_filtered_colimits_presheaf_hom_epi
      (Y := Y) (hY := hY) (c := c) (hc := hc) (hc_pt := hc_pt) (n := n))

/-- On a Noetherian space and for a filtered diagram, the canonical comparison morphism
    `colim H^n(F_j) ⟶ H^n(colim F_j)` is epi. -/
theorem sheafH_filtered_colimit_comparison_epi
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) (c' : Cocone Y') (hc' : IsColimit c') :
    Epi (sheafH_filtered_colimit_comparison Y' n c') := by
  haveI : CreatesColimit Y'
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    createsFilteredColimit Y'
  simpa [sheafH_filtered_colimit_comparison_sheafToPresheaf] using
    (sheafH_filtered_colimit_comparison_epi_presheaf
      (Y := Y' ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (hY := fun j => (Y'.obj j).cond)
      (c := (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone c')
      (hc := isColimitOfPreserves
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) hc')
      (hc_pt := c'.pt.cond) (n := n))

/-- **Sheaf cohomology commutes with filtered colimits** on Noetherian spaces:
    the canonical comparison `colim H^n(F_j) ≅ H^n(colim F_j)`. -/
noncomputable def sheafH_preserves_filtered_colimits
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (c' : Cocone Y') (hc' : IsColimit c')
    (n : ℕ) :
    colimit (Y' ⋙ sheafCohomologyFunctor X n) ≅ AddCommGrpCat.of (Sheaf.H c'.pt n) := by
  haveI : CreatesColimit Y'
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    createsFilteredColimit Y'
  simpa using
    (sheafH_preserves_filtered_colimits_presheaf
      (Y := Y' ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (hY := fun j => (Y'.obj j).cond)
      (c := (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone c')
      (hc := isColimitOfPreserves
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) hc')
      (hc_pt := c'.pt.cond) (n := n))
