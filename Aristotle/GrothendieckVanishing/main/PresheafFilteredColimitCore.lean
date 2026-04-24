import Aristotle.GrothendieckVanishing.main.PresheafFilteredColimitGeneral
import Aristotle.GrothendieckVanishing.main.ClosedImmersionCohomology

/-!
  # Noetherian filtered-colimit infrastructure for sheaf cohomology

  This file contains the Noetherian sheaf infrastructure used to compare sheaf
  cohomology with filtered colimits: creation by `sheafToPresheaf`, flasqueness,
  successor-stage dimension shifts, and presheaf-boundary comparison maps.
-/

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

/-- On a Noetherian space, a filtered colimit cocone of presheaves is a sheaf if all
    diagram objects are sheaves. Proof: compactness reduces the sheaf condition to finite
    covers, then filtered colimit merging passes from per-piece data to glued data. -/
theorem isSheaf_of_isColimit_of_isSheaf
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (P : J' ⥤ (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (hP : ∀ j, TopCat.Presheaf.IsSheaf (P.obj j))
    (c : Cocone P) (hc : IsColimit c) :
    TopCat.Presheaf.IsSheaf c.pt := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hcompat
  obtain ⟨t, ht⟩ := (NoetherianSpace.isCompact (↑(iSup U) : Set X)).elim_finite_subcover
    (fun i => ↑(U i)) (fun i => (U i).isOpen) (by simp [Opens.coe_iSup])
  have hsup_le : iSup U ≤ ⨆ i ∈ t, U i := by
    rw [SetLike.le_def]
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Opens.mem_iSup.mpr ⟨i, Opens.mem_iSup.mpr ⟨hi, hxi⟩⟩
  exact colimit_existsUnique_gluing_of_compatible_finite_subcover
    P hP hc U sf hcompat hsup_le

/-- On a Noetherian space, `sheafToPresheaf` creates filtered colimits of sheaves by
    applying `isSheaf_of_isColimit_of_isSheaf` to the underlying presheaf diagram. -/
noncomputable def createsFilteredColimit
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) :
    CreatesColimit Y' (sheafToPresheaf _ _) :=
  Sheaf.createsColimitOfIsSheaf Y' (fun c hc =>
    isSheaf_of_isColimit_of_isSheaf
      (P := Y' ⋙ sheafToPresheaf _ _)
      (hP := fun j => (Y'.obj j).cond)
      (c := c) (hc := hc))

/-! ### Filtered colimits of flasque sheaves

On Noetherian spaces, `sheafToPresheaf` creates filtered colimits, so restrictions of
filtered colimits are colimits of restrictions. Filtered colimits in `AddCommGrpCat`
preserve surjections, hence stagewise flasque sheaves have flasque colimit. -/

/-- Filtered colimits of stagewise flasque sheaves on Noetherian spaces are flasque:
    presheaf-boundary form. -/
theorem isFlasque_filtered_colimit_presheaf
    {X : TopCat.{u}} [NoetherianSpace X]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ TopCat.Presheaf AddCommGrpCat.{u} X)
    (hF : ∀ j, TopCat.Presheaf.IsSheaf (F.obj j))
    (hFlasque : ∀ j, IsFlasqueSheaf (⟨F.obj j, hF j⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    {c : Cocone F} (hc : IsColimit c)
    (hc_pt : TopCat.Presheaf.IsSheaf c.pt) :
    IsFlasqueSheaf (⟨c.pt, hc_pt⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) := by
  constructor
  intro U V i
  rw [AddCommGrpCat.epi_iff_surjective]
  intro b
  have hc_U := isColimitOfPreserves
    ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)) hc
  obtain ⟨j₀, b₀, hb₀⟩ := Concrete.isColimit_exists_rep _ hc_U b
  obtain ⟨a₀, ha₀⟩ := (AddCommGrpCat.epi_iff_surjective _).mp ((hFlasque j₀).epi_map i) b₀
  refine ⟨ConcreteCategory.hom ((c.ι.app j₀).app (op V)) a₀, ?_⟩
  rw [show ConcreteCategory.hom (c.pt.map i.op)
      (ConcreteCategory.hom ((c.ι.app j₀).app (op V)) a₀) =
    ConcreteCategory.hom ((c.ι.app j₀).app (op U))
      (ConcreteCategory.hom ((F.obj j₀).map i.op) a₀) from
    congrFun (congrArg DFunLike.coe
      (congrArg ConcreteCategory.hom ((c.ι.app j₀).naturality i.op).symm)) a₀,
    ha₀]
  exact hb₀

/-- Filtered colimits of flasque sheaves on Noetherian spaces are flasque. -/
theorem isFlasque_filtered_colimit
    {X : TopCat.{u}} [NoetherianSpace X]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (hFlasque : ∀ j, IsFlasqueSheaf (F.obj j))
    {c : Cocone F} (hc : IsColimit c) :
    IsFlasqueSheaf c.pt := by
  letI : CreatesColimit F
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    createsFilteredColimit F
  simpa using
    (isFlasque_filtered_colimit_presheaf
      (F := F ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (hF := fun j => (F.obj j).cond)
      (hFlasque := fun j => by simpa using hFlasque j)
      (c := (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone c)
      (hc := isColimitOfPreserves
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) hc)
      (hc_pt := c.pt.cond))

/-! ### Sheaf cohomology and filtered colimits

The formal comparison map
`sheafH_filtered_colimit_comparison : colim H^n(F_j) ⟶ H^n(colim F_j)`
is defined for any small diagram and cocone by `colimit.desc`.

The genuinely geometric input starts afterwards:
- `sheafH_filtered_colimit_comparison_epi_presheaf`: at the presheaf boundary, if the
  stages and cocone point are sheaves, the canonical comparison is epi
- `sheafH_filtered_colimit_comparison_epi`: on Noetherian spaces and filtered diagrams,
  this canonical comparison is epi
- `sheafH_filtered_colimit_surj`: every element of `H^n(colim F_j)` comes from some `H^n(F_j)`
  via the canonical map. The proof uses per-object functorial injective embeddings via Mathlib's
  `IsGrothendieckAbelian.instHasFunctorialFactorizationMonomorphismsRlp` and dimension shifting.
- `sheafH_preserves_filtered_colimits_presheaf`: the filtered-colimit comparison isomorphism
  for a presheaf diagram whose stages and cocone point are sheaves
- `sheafH_preserves_filtered_colimits`: packages the preceding isomorphism result as the
  canonical comparison `colim H^n(F_j) ≅ H^n(colim F_j)`. -/

section SheafHFilteredColimitSucc

variable {X : TopCat.{u}}
variable {J' : Type u} [SmallCategory J'] [IsFiltered J']
variable (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
variable [Zero (TopCat.Sheaf AddCommGrpCat.{u} X)]

/-- The arrow diagram used in the successor-step dimension-shift construction. -/
noncomputable def sheafH_filtered_colimit_succ_toArrow :
    J' ⥤ Arrow (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  { obj := fun j => Arrow.mk (0 : Y'.obj j ⟶ 0)
    map := fun f => Arrow.homMk (Y'.map f) (𝟙 0) (by simp)
    map_id := fun j => by ext <;> simp
    map_comp := fun f g => by ext <;> simp }

/-- Objectwise injective envelopes coming from functorial factorization of `0 : Y_j ⟶ 0`. -/
noncomputable def sheafH_filtered_colimit_succ_Inj :
    J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  sheafH_filtered_colimit_succ_toArrow Y' ⋙
    (MorphismProperty.functorialFactorizationData
      (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X))
      (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X)).rlp).Z

/-- The natural monomorphism from the original diagram into the injective replacement. -/
noncomputable def sheafH_filtered_colimit_succ_eta :
    Y' ⟶ sheafH_filtered_colimit_succ_Inj Y' :=
  let ffData := MorphismProperty.functorialFactorizationData
    (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X))
    (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X)).rlp
  { app := fun j => ffData.i.app ((sheafH_filtered_colimit_succ_toArrow Y').obj j)
    naturality := fun _ _ f => ffData.i.naturality ((sheafH_filtered_colimit_succ_toArrow Y').map f) }

theorem sheafH_filtered_colimit_succ_eta_mono (j : J') :
    Mono ((sheafH_filtered_colimit_succ_eta Y').app j) := by
  let ffData := MorphismProperty.functorialFactorizationData
    (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X))
    (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X)).rlp
  exact ffData.hi ((sheafH_filtered_colimit_succ_toArrow Y').obj j)

/-- The colimit cocone of the injective replacement diagram. -/
noncomputable def sheafH_filtered_colimit_succ_injCocone :
    Cocone (sheafH_filtered_colimit_succ_Inj Y') :=
  colimit.cocone (sheafH_filtered_colimit_succ_Inj Y')

/-- The cocone obtained by composing the original cocone maps with the injective replacement. -/
noncomputable def sheafH_filtered_colimit_succ_iotaCocone
    (c' : Cocone Y') :
    Cocone Y' :=
  Cocone.mk (sheafH_filtered_colimit_succ_injCocone Y').pt
    { app := fun j =>
        (sheafH_filtered_colimit_succ_eta Y').app j ≫
          (sheafH_filtered_colimit_succ_injCocone Y').ι.app j
      naturality := fun j j' f => by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
          ← (sheafH_filtered_colimit_succ_injCocone Y').w f, ← Category.assoc,
          (sheafH_filtered_colimit_succ_eta Y').naturality f] }

/-- The induced map from the colimit of the original diagram to the colimit of its injective
    replacement. -/
noncomputable def sheafH_filtered_colimit_succ_iota
    (c' : Cocone Y') (hc' : IsColimit c') :
    c'.pt ⟶ (sheafH_filtered_colimit_succ_injCocone Y').pt :=
  hc'.desc (sheafH_filtered_colimit_succ_iotaCocone Y' c')

theorem sheafH_filtered_colimit_succ_iota_fac
    (c' : Cocone Y') (hc' : IsColimit c') (j : J') :
    c'.ι.app j ≫ sheafH_filtered_colimit_succ_iota Y' c' hc' =
      (sheafH_filtered_colimit_succ_eta Y').app j ≫
        (sheafH_filtered_colimit_succ_injCocone Y').ι.app j :=
  hc'.fac (sheafH_filtered_colimit_succ_iotaCocone Y' c') j

noncomputable instance sheafH_filtered_colimit_succ_iota_mono
    (c' : Cocone Y') (hc' : IsColimit c') :
    Mono (sheafH_filtered_colimit_succ_iota Y' c' hc') := by
  haveI : ∀ j, Mono ((sheafH_filtered_colimit_succ_eta Y').app j) :=
    sheafH_filtered_colimit_succ_eta_mono (Y' := Y')
  haveI : Mono (sheafH_filtered_colimit_succ_eta Y') := NatTrans.mono_of_mono_app _
  exact colim.map_mono' (sheafH_filtered_colimit_succ_eta Y') hc'
    (colimit.isColimit (sheafH_filtered_colimit_succ_Inj Y'))
    (sheafH_filtered_colimit_succ_iota Y' c' hc')
    (sheafH_filtered_colimit_succ_iota_fac Y' c' hc')

omit [IsFiltered J'] in
/-- The injective-replacement inclusion vanishes after the objectwise cokernel projection,
    after forgetting sheaf morphisms to presheaf morphisms. -/
theorem sheafH_filtered_colimit_succ_eta_val_comp_cokernel_pi (j : J') :
    ((sheafH_filtered_colimit_succ_eta Y').app j).val ≫
      (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j)).val = 0 := by
  exact congrArg Sheaf.Hom.val
    (cokernel.condition ((sheafH_filtered_colimit_succ_eta Y').app j))

/-- The colimit inclusion into the injective-replacement colimit vanishes after its
    cokernel projection, after forgetting sheaf morphisms to presheaf morphisms. -/
theorem sheafH_filtered_colimit_succ_iota_val_comp_cokernel_pi
    (c' : Cocone Y') (hc' : IsColimit c') :
    (sheafH_filtered_colimit_succ_iota Y' c' hc').val ≫
      (cokernel.π (sheafH_filtered_colimit_succ_iota Y' c' hc')).val = 0 := by
  exact congrArg Sheaf.Hom.val
    (cokernel.condition (sheafH_filtered_colimit_succ_iota Y' c' hc'))

/-- The short exact sequence on colimit objects obtained from the injective replacement. -/
noncomputable def sheafH_filtered_colimit_succ_shortComplex
    (c' : Cocone Y') (hc' : IsColimit c') :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  let ι' := sheafH_filtered_colimit_succ_iota Y' c' hc'
  ShortComplex.mk ι' (cokernel.π ι') (cokernel.condition ι')

theorem sheafH_filtered_colimit_succ_shortExact
    (c' : Cocone Y') (hc' : IsColimit c') :
    (sheafH_filtered_colimit_succ_shortComplex Y' c' hc').ShortExact := by
  let ι' := sheafH_filtered_colimit_succ_iota Y' c' hc'
  change (ShortComplex.mk ι' (cokernel.π ι') (cokernel.condition ι')).ShortExact
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ι')) inferInstance inferInstance

/-- The quotient diagram obtained by objectwise cokernels of the injective replacement maps. -/
noncomputable def sheafH_filtered_colimit_succ_quotient :
    J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  { obj := fun j => cokernel ((sheafH_filtered_colimit_succ_eta Y').app j)
    map := fun {j j'} f =>
      cokernel.map _ _
        (Y'.map f) ((sheafH_filtered_colimit_succ_Inj Y').map f)
        ((sheafH_filtered_colimit_succ_eta Y').naturality f).symm
    map_id := fun j => by ext; simp [cokernel.map]
    map_comp := fun {j j' j''} f g => by ext; simp [cokernel.map, Functor.map_comp] }

/-- The quotient cocone on the cokernel diagram induced by the colimit short exact sequence. -/
noncomputable def sheafH_filtered_colimit_succ_quotientCocone
    (c' : Cocone Y') (hc' : IsColimit c') :
    Cocone (sheafH_filtered_colimit_succ_quotient Y') :=
  let ι' := sheafH_filtered_colimit_succ_iota Y' c' hc'
  let S := sheafH_filtered_colimit_succ_shortComplex Y' c' hc'
  Cocone.mk S.X₃
    { app := fun j =>
        cokernel.map ((sheafH_filtered_colimit_succ_eta Y').app j) ι'
          (c'.ι.app j) ((sheafH_filtered_colimit_succ_injCocone Y').ι.app j)
          (sheafH_filtered_colimit_succ_iota_fac Y' c' hc' j).symm
      naturality := fun j j' f => by
        apply (cancel_epi (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j))).mp
        simp [sheafH_filtered_colimit_succ_quotient, sheafH_filtered_colimit_succ_iota_fac,
          Functor.const_obj_map, Category.assoc, (sheafH_filtered_colimit_succ_injCocone Y').w f] }

private noncomputable def sheafH_filtered_colimit_succ_liftedCocone
    (s : Cocone (sheafH_filtered_colimit_succ_quotient Y')) :
    Cocone (sheafH_filtered_colimit_succ_Inj Y') :=
  Cocone.mk s.pt
    { app := fun j =>
        cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ s.ι.app j
      naturality := fun j j' a => by
        dsimp
        have hdesc :
            cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫
                (sheafH_filtered_colimit_succ_quotient Y').map a =
              (sheafH_filtered_colimit_succ_Inj Y').map a ≫
                cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j') := by
          simp [sheafH_filtered_colimit_succ_quotient]
        rw [← Category.assoc, ← hdesc, Category.assoc, s.w]
        simp }

omit [IsFiltered J'] in
@[simp]
private theorem sheafH_filtered_colimit_succ_liftedCocone_ι_app
    (s : Cocone (sheafH_filtered_colimit_succ_quotient Y')) (j : J') :
    (sheafH_filtered_colimit_succ_liftedCocone Y' s).ι.app j =
      cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ s.ι.app j := rfl

noncomputable def sheafH_filtered_colimit_succ_quotientCocone_isColimit
    (c' : Cocone Y') (hc' : IsColimit c') :
    IsColimit (sheafH_filtered_colimit_succ_quotientCocone Y' c' hc') := by
  let Inj := sheafH_filtered_colimit_succ_Inj Y'
  let injCocone := sheafH_filtered_colimit_succ_injCocone Y'
  let qCocone := sheafH_filtered_colimit_succ_quotientCocone Y' c' hc'
  let ι' := sheafH_filtered_colimit_succ_iota Y' c' hc'
  let injColim := colimit.isColimit Inj
  have hπ (j) : cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ qCocone.ι.app j =
      injCocone.ι.app j ≫ cokernel.π ι' := cokernel.π_desc _ _ _
  exact
  { desc := fun s =>
      let lifted := sheafH_filtered_colimit_succ_liftedCocone Y' s
      cokernel.desc ι' (injColim.desc lifted) (hc'.hom_ext fun j => by
        have hfac_lifted :
            injCocone.ι.app j ≫ injColim.desc lifted =
              cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ s.ι.app j := by
          simpa [lifted, injCocone] using injColim.fac lifted j
        rw [comp_zero]
        conv_lhs =>
          rw [← Category.assoc, sheafH_filtered_colimit_succ_iota_fac Y' c' hc' j, Category.assoc]
        rw [hfac_lifted, ← Category.assoc, cokernel.condition, zero_comp])
    fac := fun s j => (cancel_epi (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j))).mp (by
      let lifted := sheafH_filtered_colimit_succ_liftedCocone Y' s
      have hfac_lifted :
          injCocone.ι.app j ≫ injColim.desc lifted =
            cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ s.ι.app j := by
        simpa [lifted, injCocone] using injColim.fac lifted j
      rw [← Category.assoc, hπ, Category.assoc, cokernel.π_desc, hfac_lifted])
    uniq := fun s m hm => (cancel_epi (cokernel.π ι')).mp (by
      rw [cokernel.π_desc]
      let lifted := sheafH_filtered_colimit_succ_liftedCocone Y' s
      exact injColim.hom_ext fun j => by
        have hπ' :
            (colimit.cocone Inj).ι.app j ≫ cokernel.π ι' =
              cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ qCocone.ι.app j := by
          simpa [injCocone] using (hπ j).symm
        have hfac_lifted' :
            (colimit.cocone Inj).ι.app j ≫ injColim.desc lifted =
              cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ s.ι.app j := by
          simpa [lifted] using injColim.fac lifted j
        have hπ'_assoc :
            (colimit.cocone Inj).ι.app j ≫ cokernel.π ι' ≫ m =
              (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ qCocone.ι.app j) ≫ m := by
          simpa [Category.assoc] using congrArg (fun t => t ≫ m) hπ'
        rw [hπ'_assoc, Category.assoc, hm]
        exact hfac_lifted'.symm) }

theorem sheafH_filtered_colimit_succ_stage_shortExact (j : J') :
    (ShortComplex.mk ((sheafH_filtered_colimit_succ_eta Y').app j)
      (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j))
      (cokernel.condition ((sheafH_filtered_colimit_succ_eta Y').app j))).ShortExact := by
  haveI : Mono ((sheafH_filtered_colimit_succ_eta Y').app j) :=
    sheafH_filtered_colimit_succ_eta_mono (Y' := Y') j
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ((sheafH_filtered_colimit_succ_eta Y').app j)))
    inferInstance inferInstance

/-- The morphism between stagewise short exact sequences induced by a transition map in the
    filtered diagram. -/
noncomputable def sheafH_filtered_colimit_succ_stage_map_hom
    {j j' : J'} (f : j ⟶ j') :
    ShortComplex.mk ((sheafH_filtered_colimit_succ_eta Y').app j)
        (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j))
        (cokernel.condition ((sheafH_filtered_colimit_succ_eta Y').app j)) ⟶
      ShortComplex.mk ((sheafH_filtered_colimit_succ_eta Y').app j')
        (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j'))
        (cokernel.condition ((sheafH_filtered_colimit_succ_eta Y').app j')) :=
  ShortComplex.homMk
    (Y'.map f)
    ((sheafH_filtered_colimit_succ_Inj Y').map f)
    ((sheafH_filtered_colimit_succ_quotient Y').map f)
    ((sheafH_filtered_colimit_succ_eta Y').naturality f)
    (cokernel.π_desc _ _ _).symm

/-- The morphism from the stagewise short exact sequence to the colimit short exact sequence. -/
noncomputable def sheafH_filtered_colimit_succ_stage_hom
    (c' : Cocone Y') (hc' : IsColimit c') (j : J') :
    ShortComplex.mk ((sheafH_filtered_colimit_succ_eta Y').app j)
        (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j))
        (cokernel.condition ((sheafH_filtered_colimit_succ_eta Y').app j)) ⟶
      sheafH_filtered_colimit_succ_shortComplex Y' c' hc' :=
  ShortComplex.homMk
    (c'.ι.app j)
    ((sheafH_filtered_colimit_succ_injCocone Y').ι.app j)
    ((sheafH_filtered_colimit_succ_quotientCocone Y' c' hc').ι.app j)
    (sheafH_filtered_colimit_succ_iota_fac Y' c' hc' j)
    (cokernel.π_desc _ _ _).symm

/-- The stagewise dimension-shift natural isomorphism between the quotient diagram in degree
    `n` and the original diagram in degree `n + 1`. -/
noncomputable def sheafH_filtered_colimit_succ_shiftNatIso
    (n : ℕ)
    (h_mid_n : ∀ j, Subsingleton (Sheaf.H ((sheafH_filtered_colimit_succ_Inj Y').obj j) n))
    (h_mid_succ : ∀ j,
      Subsingleton (Sheaf.H ((sheafH_filtered_colimit_succ_Inj Y').obj j) (n + 1))) :
    sheafH_filtered_colimit_succ_quotient Y' ⋙ sheafCohomologyFunctor X n ≅
      Y' ⋙ sheafCohomologyFunctor X (n + 1) :=
  NatIso.ofComponents
    (fun j =>
      sheafH_extClassIso_of_subsingleton_middle_presheaf
        (h₁ := (Y'.obj j).cond)
        (h₂ := ((sheafH_filtered_colimit_succ_Inj Y').obj j).cond)
        (h₃ := (cokernel ((sheafH_filtered_colimit_succ_eta Y').app j)).cond)
        (f := ((sheafH_filtered_colimit_succ_eta Y').app j).val)
        (g := (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j)).val)
        (by
          ext U
          rename_i s
          change AddCommGrpCat.Hom.hom
              (((((sheafH_filtered_colimit_succ_eta Y').app j) ≫
                    cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j)).val).app
                (op U)) s = 0
          have happ :
              (((sheafH_filtered_colimit_succ_eta Y').app j ≫
                    cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j)).val).app
                (op U) =
              NatTrans.app
                (0 : (Y'.obj j).val ⟶
                  (cokernel ((sheafH_filtered_colimit_succ_eta Y').app j)).val) (op U) :=
            NatTrans.congr_app
              (congrArg (fun α => α.val)
                (cokernel.condition ((sheafH_filtered_colimit_succ_eta Y').app j)))
              (op U)
          rw [happ]
          simp)
        (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Y') j) n
        (h_mid_n j) (h_mid_succ j))
    (fun {j j'} f => by
      ext y
      simpa using congrArg (fun m => AddCommGrpCat.Hom.hom m y)
        ((sheafH_extClassIso_of_subsingleton_middle_presheaf_natural
          (h₁₁ := (Y'.obj j).cond)
          (h₁₂ := ((sheafH_filtered_colimit_succ_Inj Y').obj j).cond)
          (h₁₃ := (cokernel ((sheafH_filtered_colimit_succ_eta Y').app j)).cond)
          (h₂₁ := (Y'.obj j').cond)
          (h₂₂ := ((sheafH_filtered_colimit_succ_Inj Y').obj j').cond)
          (h₂₃ := (cokernel ((sheafH_filtered_colimit_succ_eta Y').app j')).cond)
          (f₁ := ((sheafH_filtered_colimit_succ_eta Y').app j).val)
          (g₁ := (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j)).val)
          (by
            ext U
            rename_i s
            change AddCommGrpCat.Hom.hom
                (((((sheafH_filtered_colimit_succ_eta Y').app j) ≫
                      cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j)).val).app
                  (op U)) s = 0
            have happ :
                (((sheafH_filtered_colimit_succ_eta Y').app j ≫
                      cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j)).val).app
                  (op U) =
                NatTrans.app
                  (0 : (Y'.obj j).val ⟶
                    (cokernel ((sheafH_filtered_colimit_succ_eta Y').app j)).val) (op U) :=
              NatTrans.congr_app
                (congrArg (fun α => α.val)
                  (cokernel.condition ((sheafH_filtered_colimit_succ_eta Y').app j)))
                (op U)
            rw [happ]
            simp)
          (f₂ := ((sheafH_filtered_colimit_succ_eta Y').app j').val)
          (g₂ := (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j')).val)
          (by
            ext U
            rename_i s
            change AddCommGrpCat.Hom.hom
                (((((sheafH_filtered_colimit_succ_eta Y').app j') ≫
                      cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j')).val).app
                  (op U)) s = 0
            have happ :
                (((sheafH_filtered_colimit_succ_eta Y').app j' ≫
                      cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j')).val).app
                  (op U) =
                NatTrans.app
                  (0 : (Y'.obj j').val ⟶
                    (cokernel ((sheafH_filtered_colimit_succ_eta Y').app j')).val) (op U) :=
              NatTrans.congr_app
                (congrArg (fun α => α.val)
                  (cokernel.condition ((sheafH_filtered_colimit_succ_eta Y').app j')))
                (op U)
            rw [happ]
            simp)
          (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Y') j)
          (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Y') j')
          (τ₁ := (Y'.map f).val)
          (τ₂ := ((sheafH_filtered_colimit_succ_Inj Y').map f).val)
          (τ₃ := ((sheafH_filtered_colimit_succ_quotient Y').map f).val)
          (by
            simpa using congrArg (fun α => α.val)
              ((sheafH_filtered_colimit_succ_stage_map_hom (Y' := Y') f).comm₁₂))
          (by
            simpa using congrArg (fun α => α.val)
              ((sheafH_filtered_colimit_succ_stage_map_hom (Y' := Y') f).comm₂₃))
          n (h_mid_n j) (h_mid_succ j) (h_mid_n j') (h_mid_succ j')).symm))

/-- The induced colimit isomorphism from the successor-step stagewise dimension shift. -/
noncomputable def sheafH_filtered_colimit_succ_shiftDomainIso
    (n : ℕ)
    (h_mid_n : ∀ j, Subsingleton (Sheaf.H ((sheafH_filtered_colimit_succ_Inj Y').obj j) n))
    (h_mid_succ : ∀ j,
      Subsingleton (Sheaf.H ((sheafH_filtered_colimit_succ_Inj Y').obj j) (n + 1))) :
    colimit (sheafH_filtered_colimit_succ_quotient Y' ⋙ sheafCohomologyFunctor X n) ≅
      colimit (Y' ⋙ sheafCohomologyFunctor X (n + 1)) :=
  HasColimit.isoOfNatIso (sheafH_filtered_colimit_succ_shiftNatIso Y' n h_mid_n h_mid_succ)

/-- The colimit-level dimension-shift isomorphism for the short exact sequence obtained from
    the injective replacement of the filtered colimit cocone. -/
noncomputable def sheafH_filtered_colimit_succ_shiftCodomainIso
    (c' : Cocone Y') (hc' : IsColimit c') (n : ℕ)
    (h_colim_n :
      Subsingleton (Sheaf.H (sheafH_filtered_colimit_succ_injCocone Y').pt n))
    (h_colim_succ :
      Subsingleton (Sheaf.H (sheafH_filtered_colimit_succ_injCocone Y').pt (n + 1))) :
    AddCommGrpCat.of
        (Sheaf.H (sheafH_filtered_colimit_succ_quotientCocone Y' c' hc').pt n) ≅
      AddCommGrpCat.of (Sheaf.H c'.pt (n + 1)) :=
  sheafH_extClassIso_of_subsingleton_middle_presheaf
    (h₁ := c'.pt.cond)
    (h₂ := (sheafH_filtered_colimit_succ_injCocone Y').pt.cond)
    (h₃ := (sheafH_filtered_colimit_succ_quotientCocone Y' c' hc').pt.cond)
    (f := (sheafH_filtered_colimit_succ_iota Y' c' hc').val)
    (g := (cokernel.π (sheafH_filtered_colimit_succ_iota Y' c' hc')).val)
    (by
      ext U
      rename_i s
      change AddCommGrpCat.Hom.hom
          ((((sheafH_filtered_colimit_succ_iota Y' c' hc' ≫
                cokernel.π (sheafH_filtered_colimit_succ_iota Y' c' hc')).val).app
            (op U))) s = 0
      have happ :
          ((sheafH_filtered_colimit_succ_iota Y' c' hc' ≫
                cokernel.π (sheafH_filtered_colimit_succ_iota Y' c' hc')).val).app
              (op U) =
            NatTrans.app
              (0 : c'.pt.val ⟶
                (sheafH_filtered_colimit_succ_quotientCocone Y' c' hc').pt.val) (op U) :=
        NatTrans.congr_app
          (congrArg (fun α => α.val)
            (cokernel.condition (sheafH_filtered_colimit_succ_iota Y' c' hc')))
          (op U)
      rw [happ]
      simp)
    (sheafH_filtered_colimit_succ_shortExact Y' c' hc') n h_colim_n h_colim_succ

/-- The filtered-colimit successor-step vanishing lemma for the injective replacement:
the middle term of the induced short exact sequence has trivial cohomology in degree `n + 1`. -/
theorem sheafH_filtered_colimit_succ_inj_subsingleton_presheaf
    [NoetherianSpace X] (n : ℕ)
    (hInj : ∀ j, Injective ((sheafH_filtered_colimit_succ_Inj Y').obj j)) :
    Subsingleton (Sheaf.H (sheafH_filtered_colimit_succ_injCocone Y').pt (n + 1)) := by
  let Inj := sheafH_filtered_colimit_succ_Inj Y'
  let injCocone := sheafH_filtered_colimit_succ_injCocone Y'
  haveI : CreatesColimit Inj
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    createsFilteredColimit Inj
  have hFlasque : IsFlasqueSheaf injCocone.pt := by
    simpa [Inj, injCocone] using
      (isFlasque_filtered_colimit_presheaf
        (F := Inj ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (hF := fun j => (Inj.obj j).cond)
        (hFlasque := fun j => by
          letI : Injective (Inj.obj j) := hInj j
          simpa using (isFlasque_of_injective (Inj.obj j)))
        (c := (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone
          injCocone)
        (hc := isColimitOfPreserves
          (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
          (colimit.isColimit Inj))
        (hc_pt := injCocone.pt.cond))
  let F : TopCat.Presheaf AddCommGrpCat.{u} X := injCocone.pt.val
  have hF : F.IsSheaf := by
    simpa [F, injCocone] using injCocone.pt.cond
  letI : IsFlasqueSheaf ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) := by
    simpa [F, hF, injCocone] using hFlasque
  simpa [F, hF, injCocone] using
    (sheafH_subsingleton_of_flasque_presheaf (X := X) (F := F) hF n)

end SheafHFilteredColimitSucc

/-- **Sheaf cohomology commutes with filtered colimits (surjectivity)** on Noetherian spaces.
    Presheaf form: if the stages and cocone point are sheaves, every element of
    `H^n(c.pt)` comes from some stage via the cocone map. -/
theorem sheafH_filtered_colimit_surj_presheaf
    {X : TopCat.{u}} [NoetherianSpace X]
    (n : ℕ) :
    ∀ {J' : Type u} [SmallCategory J'] [IsFiltered J']
      (Y : J' ⥤ TopCat.Presheaf AddCommGrpCat.{u} X)
      (hY : ∀ j, TopCat.Presheaf.IsSheaf (Y.obj j))
      (c : Cocone Y) (_ : IsColimit c)
      (hc_pt : TopCat.Presheaf.IsSheaf c.pt)
      (x : Sheaf.H (⟨c.pt, hc_pt⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) n),
    ∃ (j : J')
      (y : Sheaf.H (⟨Y.obj j, hY j⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) n),
      ConcreteCategory.hom
        ((sheafCohomologyFunctor X n).map (Sheaf.Hom.mk (c.ι.app j))) y = x := by
  induction n with
  | zero =>
    intro J' inst1 inst2 Y hY c hc hc_pt x
    letI := inst1
    letI := inst2
    have hc_top := isColimitOfPreserves
      ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) hc
    let x_sec := sheafH0EquivSections_presheaf hc_pt x
    obtain ⟨j, s_j, hs_j⟩ := Concrete.isColimit_exists_rep _ hc_top x_sec
    let y := (sheafH0EquivSections_presheaf (hY j)).symm s_j
    refine ⟨j, y, ?_⟩
    have h_nat :
        sheafH0EquivSections_presheaf hc_pt
          (ConcreteCategory.hom
            ((sheafCohomologyFunctor X 0).map (Sheaf.Hom.mk (c.ι.app j))) y) =
        ConcreteCategory.hom ((c.ι.app j).app (op ⊤))
          (sheafH0EquivSections_presheaf (hY j) y) := by
      simpa [sheafCohomologyFunctor_map_apply] using
        (sheafH0EquivSections_presheaf_natural
          (hF := hY j) (hG := hc_pt) (f := c.ι.app j) (x := y))
    apply (sheafH0EquivSections_presheaf hc_pt).injective
    change sheafH0EquivSections_presheaf hc_pt
      (ConcreteCategory.hom
        ((sheafCohomologyFunctor X 0).map (Sheaf.Hom.mk (c.ι.app j))) y) = x_sec
    rw [h_nat, AddEquiv.apply_symm_apply]
    exact hs_j
  | succ n ih =>
    intro J' inst1 inst2 Y hY c hc hc_pt x
    letI := inst1
    letI := inst2
    let Ysh : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
      { obj := fun j => ⟨Y.obj j, hY j⟩
        map := fun f => Sheaf.Hom.mk (Y.map f)
        map_id := fun j => Sheaf.Hom.ext <| Y.map_id j
        map_comp := fun f g => Sheaf.Hom.ext <| Y.map_comp f g }
    let csh : Cocone Ysh :=
      { pt := ⟨c.pt, hc_pt⟩
        ι :=
          { app := fun j => Sheaf.Hom.mk (c.ι.app j)
            naturality := fun _ _ f => Sheaf.Hom.ext <| c.ι.naturality f } }
    have hcsh : IsColimit csh := by
      letI : CreatesColimit Ysh (sheafToPresheaf (Opens.grothendieckTopology X)
          AddCommGrpCat.{u}) := createsFilteredColimit Ysh
      simpa [Ysh, csh] using
        (liftedColimitIsColimit
          (F := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
          (K := Ysh) (c := c) hc)
    letI : Zero (TopCat.Sheaf AddCommGrpCat.{u} X) := Limits.HasZeroObject.zero' _
    let Inj := sheafH_filtered_colimit_succ_Inj Ysh
    let η := sheafH_filtered_colimit_succ_eta Ysh
    let injCocone := sheafH_filtered_colimit_succ_injCocone Ysh
    let ι' := sheafH_filtered_colimit_succ_iota Ysh csh hcsh
    let S := sheafH_filtered_colimit_succ_shortComplex Ysh csh hcsh
    have hSE : S.ShortExact := sheafH_filtered_colimit_succ_shortExact Ysh csh hcsh
    have hInj : ∀ j, Injective (Inj.obj j) := by
      intro j
      let ffData := MorphismProperty.functorialFactorizationData
        (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X))
        (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X)).rlp
      change Injective (ffData.Z.obj (Arrow.mk (0 : Ysh.obj j ⟶ 0)))
      exact IsGrothendieckAbelian.instInjectiveZMonomorphismsRlpMonoMapFactorizationDataRlpOfNatHom
    have hI : Subsingleton (Sheaf.H injCocone.pt (n + 1)) := by
      simpa [injCocone, Inj] using
        (sheafH_filtered_colimit_succ_inj_subsingleton_presheaf
          (X := X) (Y' := Ysh) n hInj)
    let Q := sheafH_filtered_colimit_succ_quotient Ysh
    let qCocone := sheafH_filtered_colimit_succ_quotientCocone Ysh csh hcsh
    have hqColim : IsColimit qCocone :=
      sheafH_filtered_colimit_succ_quotientCocone_isColimit Ysh csh hcsh
    haveI : CreatesColimit Q
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
      createsFilteredColimit Q
    have hSE_j : ∀ j, (ShortComplex.mk (η.app j) (cokernel.π (η.app j))
        (cokernel.condition (η.app j))).ShortExact :=
      sheafH_filtered_colimit_succ_stage_shortExact (Y' := Ysh)
    obtain ⟨y, hy⟩ := sheafH_exists_preimage_extClass_presheaf
      S.X₁.cond S.X₂.cond S.X₃.cond
      (f := S.f.val) (g := S.g.val)
      (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
      (by simpa using hSE) n
      (by simpa using hI) x
    obtain ⟨j₀, y_j, hy_j⟩ := by
      simpa using
        (ih
          (Y := Q ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
          (hY := fun j => (Q.obj j).cond)
          (c := (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone
            qCocone)
          (hc_pt := qCocone.pt.cond) (x := y)
          (isColimitOfPreserves
            (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) hqColim))
    haveI : Mono (η.app j₀) := sheafH_filtered_colimit_succ_eta_mono (Y' := Ysh) j₀
    let x_j : Sheaf.H (Ysh.obj j₀) (n + 1) := y_j.comp (hSE_j j₀).extClass rfl
    refine ⟨j₀, x_j, ?_⟩
    show ConcreteCategory.hom
        ((sheafCohomologyFunctor X (n + 1)).map ((csh.ι.app j₀))) x_j = x
    rw [show x_j = y_j.comp (hSE_j j₀).extClass rfl from rfl]
    exact (sheafCohomologyFunctor_map_extClass_of_map_eq_presheaf
      (h₁₁ := (Ysh.obj j₀).cond)
      (h₁₂ := ((sheafH_filtered_colimit_succ_Inj Ysh).obj j₀).cond)
      (h₁₃ := (cokernel ((sheafH_filtered_colimit_succ_eta Ysh).app j₀)).cond)
      (h₂₁ := csh.pt.cond)
      (h₂₂ := (sheafH_filtered_colimit_succ_injCocone Ysh).pt.cond)
      (h₂₃ := qCocone.pt.cond)
      (f₁ := ((sheafH_filtered_colimit_succ_eta Ysh).app j₀).val)
      (g₁ := (cokernel.π ((sheafH_filtered_colimit_succ_eta Ysh).app j₀)).val)
      (by
        ext U s
        change ConcreteCategory.hom
            ((((sheafH_filtered_colimit_succ_eta Ysh).app j₀) ≫
                cokernel.π ((sheafH_filtered_colimit_succ_eta Ysh).app j₀)).val.app
              (op U)) s = 0
        have happ :
            (((((sheafH_filtered_colimit_succ_eta Ysh).app j₀) ≫
                  cokernel.π ((sheafH_filtered_colimit_succ_eta Ysh).app j₀)).val).app
                (op U)) =
              NatTrans.app
                (0 : (Ysh.obj j₀).val ⟶
                  (cokernel ((sheafH_filtered_colimit_succ_eta Ysh).app j₀)).val) (op U) := by
          exact NatTrans.congr_app
            (congrArg
              (fun α :
                Ysh.obj j₀ ⟶ cokernel ((sheafH_filtered_colimit_succ_eta Ysh).app j₀) =>
                  α.val)
              (cokernel.condition ((sheafH_filtered_colimit_succ_eta Ysh).app j₀)))
            (op U)
        rw [happ]
        simp)
      (f₂ := ι'.val)
      (g₂ := (cokernel.π ι').val)
      (by
        ext U s
        change ConcreteCategory.hom (((ι' ≫ cokernel.π ι').val).app (op U)) s = 0
        have happ :
            (((ι' ≫ cokernel.π ι').val).app (op U)) =
              NatTrans.app (0 : csh.pt.val ⟶ (cokernel ι').val) (op U) := by
          exact NatTrans.congr_app
            (congrArg (fun α : csh.pt ⟶ cokernel ι' => α.val)
              (cokernel.condition ι'))
            (op U)
        rw [happ]
        simp)
      (hSE_j j₀) hSE
      (τ₁ := (csh.ι.app j₀).val)
      (τ₂ := ((sheafH_filtered_colimit_succ_injCocone Ysh).ι.app j₀).val)
      (τ₃ := (qCocone.ι.app j₀).val)
      (by
        simpa using congrArg Sheaf.Hom.val
          ((sheafH_filtered_colimit_succ_stage_hom Ysh csh hcsh j₀).comm₁₂))
      (by
        simpa using congrArg Sheaf.Hom.val
          ((sheafH_filtered_colimit_succ_stage_hom Ysh csh hcsh j₀).comm₂₃))
      n hy_j).trans hy

/-- **Sheaf cohomology commutes with filtered colimits (surjectivity)** on Noetherian spaces.
    Every element of `H^n(colim F_j)` comes from some `H^n(F_j)` via the canonical map.
    Together with injectivity (not proved here), this gives `colim H^n(F_j) ≅ H^n(colim F_j)`. -/
theorem sheafH_filtered_colimit_surj
    {X : TopCat.{u}} [NoetherianSpace X]
    (n : ℕ) :
    ∀ {J' : Type u} [SmallCategory J'] [IsFiltered J']
      (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
      (c' : Cocone Y') (_ : IsColimit c')
      (x : Sheaf.H c'.pt n),
    ∃ (j : J') (y : Sheaf.H (Y'.obj j) n),
      ConcreteCategory.hom ((sheafCohomologyFunctor X n).map (c'.ι.app j)) y = x := by
  intro J' inst1 inst2 Y' c' hc' x
  letI := inst1
  letI := inst2
  haveI : CreatesColimit Y'
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    createsFilteredColimit Y'
  simpa using
    (sheafH_filtered_colimit_surj_presheaf (X := X) (n := n)
      (Y := Y' ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (hY := fun j => (Y'.obj j).cond)
      (c := (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone c')
      (hc_pt := c'.pt.cond) (x := x)
      (isColimitOfPreserves
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) hc'))

/-- The sheaf-valued diagram obtained by bundling a presheaf diagram whose stages are sheaves. -/
def sheafH_filtered_colimit_presheafDiagram
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J']
    (Y : J' ⥤ TopCat.Presheaf AddCommGrpCat.{u} X)
    (hY : ∀ j, TopCat.Presheaf.IsSheaf (Y.obj j)) :
    J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  { obj := fun j => ⟨Y.obj j, hY j⟩
    map := fun f => Sheaf.Hom.mk (Y.map f)
    map_id := fun j => Sheaf.Hom.ext <| Y.map_id j
    map_comp := fun f g => Sheaf.Hom.ext <| Y.map_comp f g }

/-- The sheaf-valued cocone obtained by bundling a presheaf cocone whose legs and point
    satisfy the sheaf condition. -/
def sheafH_filtered_colimit_presheafCocone
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J']
    (Y : J' ⥤ TopCat.Presheaf AddCommGrpCat.{u} X)
    (hY : ∀ j, TopCat.Presheaf.IsSheaf (Y.obj j))
    (c : Cocone Y) (hc_pt : TopCat.Presheaf.IsSheaf c.pt) :
    Cocone (sheafH_filtered_colimit_presheafDiagram Y hY) :=
  { pt := ⟨c.pt, hc_pt⟩
    ι :=
      { app := fun j => Sheaf.Hom.mk (c.ι.app j)
        naturality := fun _ _ f => Sheaf.Hom.ext <| c.ι.naturality f } }

/-- Bundling a sheaf-valued diagram after forgetting to presheaves recovers the original
    diagram. -/
theorem sheafH_filtered_colimit_presheafDiagram_sheafToPresheaf
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) :
    sheafH_filtered_colimit_presheafDiagram
      (Y' ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (fun j => (Y'.obj j).cond) = Y' := by
  cases Y'
  rfl

/-- Bundling a sheaf-valued cocone after forgetting to presheaves recovers the original
    cocone. -/
theorem sheafH_filtered_colimit_presheafCocone_sheafToPresheaf
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (c' : Cocone Y') :
    sheafH_filtered_colimit_presheafCocone
      (Y' ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (fun j => (Y'.obj j).cond)
      ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone c')
      c'.pt.cond = c' := by
  cases Y'
  cases c'
  rfl

/-- The cohomology diagram attached to a presheaf diagram whose stages are sheaves. -/
noncomputable def sheafH_presheafDiagram
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J']
    (Y : J' ⥤ TopCat.Presheaf AddCommGrpCat.{u} X)
    (hY : ∀ j, TopCat.Presheaf.IsSheaf (Y.obj j))
    (n : ℕ) :
    J' ⥤ AddCommGrpCat.{u} :=
  sheafH_filtered_colimit_presheafDiagram Y hY ⋙ sheafCohomologyFunctor X n

@[simp] theorem sheafH_presheafDiagram_sheafToPresheaf
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) :
    sheafH_presheafDiagram
      (Y' ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (fun j => (Y'.obj j).cond) n =
    Y' ⋙ sheafCohomologyFunctor X n := by
  dsimp [sheafH_presheafDiagram]
  rw [sheafH_filtered_colimit_presheafDiagram_sheafToPresheaf]

/-- The canonical comparison morphism `colim H^n(F_j) ⟶ H^n(colim F_j)` at the presheaf
boundary, assuming the stages and cocone point are sheaves. -/
noncomputable def sheafH_filtered_colimit_comparison_presheaf
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J']
    (Y : J' ⥤ TopCat.Presheaf AddCommGrpCat.{u} X)
    (hY : ∀ j, TopCat.Presheaf.IsSheaf (Y.obj j))
    (c : Cocone Y) (hc_pt : TopCat.Presheaf.IsSheaf c.pt)
    (n : ℕ) :
    colimit (sheafH_presheafDiagram Y hY n) ⟶
      AddCommGrpCat.of (Sheaf.H (⟨c.pt, hc_pt⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) n) :=
  colimit.desc _ ((sheafCohomologyFunctor X n).mapCocone
    (sheafH_filtered_colimit_presheafCocone Y hY c hc_pt))

@[simp] theorem colimit_ι_sheafH_filtered_colimit_comparison_presheaf
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J']
    (Y : J' ⥤ TopCat.Presheaf AddCommGrpCat.{u} X)
    (hY : ∀ j, TopCat.Presheaf.IsSheaf (Y.obj j))
    (c : Cocone Y) (hc_pt : TopCat.Presheaf.IsSheaf c.pt)
    (n : ℕ) (j : J') :
    colimit.ι (sheafH_presheafDiagram Y hY n) j ≫
        sheafH_filtered_colimit_comparison_presheaf Y hY c hc_pt n =
      (sheafCohomologyFunctor X n).map (Sheaf.Hom.mk (c.ι.app j)) := by
  simp [sheafH_presheafDiagram, sheafH_filtered_colimit_comparison_presheaf,
    sheafH_filtered_colimit_presheafCocone]

/-- The canonical comparison morphism `colim H^n(F_j) ⟶ H^n(colim F_j)` induced by a cocone. -/
noncomputable def sheafH_filtered_colimit_comparison
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) (c' : Cocone Y') :
    colimit (Y' ⋙ sheafCohomologyFunctor X n) ⟶ AddCommGrpCat.of (Sheaf.H c'.pt n) :=
  sheafH_filtered_colimit_comparison_presheaf
    (Y' ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (fun j => (Y'.obj j).cond)
    ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone c')
    c'.pt.cond n

theorem sheafH_filtered_colimit_comparison_sheafToPresheaf
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) (c' : Cocone Y') :
    sheafH_filtered_colimit_comparison_presheaf
      (Y' ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (fun j => (Y'.obj j).cond)
      ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone c')
      c'.pt.cond n =
    sheafH_filtered_colimit_comparison Y' n c' := by
  rfl

@[simp] theorem colimit_ι_sheafH_filtered_colimit_comparison
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) (c' : Cocone Y') (j : J') :
    colimit.ι (Y' ⋙ sheafCohomologyFunctor X n) j ≫
        sheafH_filtered_colimit_comparison Y' n c' =
      (sheafCohomologyFunctor X n).map (c'.ι.app j) := by
  change colimit.ι
      (sheafH_presheafDiagram
        (Y' ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (fun j => (Y'.obj j).cond) n) j ≫
      sheafH_filtered_colimit_comparison_presheaf
        (Y' ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (fun j => (Y'.obj j).cond)
        ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone c')
        c'.pt.cond n =
    (sheafCohomologyFunctor X n).map (Sheaf.Hom.mk
      (((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone c').ι.app j))
  simpa [sheafH_presheafDiagram_sheafToPresheaf] using
    (colimit_ι_sheafH_filtered_colimit_comparison_presheaf
      (Y := Y' ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (hY := fun j => (Y'.obj j).cond)
      (c := (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone c')
      (hc_pt := c'.pt.cond) (n := n) (j := j))

/-- If a presheaf cocone is a colimit and its stages and point are sheaves, then the
    bundled sheaf-valued cocone is also a colimit. -/
noncomputable def sheafH_filtered_colimit_presheafCocone_isColimit
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y : J' ⥤ TopCat.Presheaf AddCommGrpCat.{u} X)
    (hY : ∀ j, TopCat.Presheaf.IsSheaf (Y.obj j))
    (c : Cocone Y) (hc : IsColimit c)
    (hc_pt : TopCat.Presheaf.IsSheaf c.pt) :
    IsColimit (sheafH_filtered_colimit_presheafCocone Y hY c hc_pt) := by
  refine
    { desc := fun s => ?_
      fac := fun s j => ?_
      uniq := fun s m hm => ?_ }
  · let sVal : Cocone Y :=
      { pt := s.pt.val
        ι :=
          { app := fun j => (s.ι.app j).val
            naturality := fun _ _ f => congrArg Sheaf.Hom.val (s.ι.naturality f) } }
    exact Sheaf.Hom.mk (hc.desc sVal)
  · let sVal : Cocone Y :=
      { pt := s.pt.val
        ι :=
          { app := fun j => (s.ι.app j).val
            naturality := fun _ _ f => congrArg Sheaf.Hom.val (s.ι.naturality f) } }
    exact Sheaf.Hom.ext (hc.fac sVal j)
  · apply Sheaf.Hom.ext
    let sVal : Cocone Y :=
      { pt := s.pt.val
        ι :=
          { app := fun j => (s.ι.app j).val
            naturality := fun _ _ f => congrArg Sheaf.Hom.val (s.ι.naturality f) } }
    exact hc.hom_ext fun j => by
      calc
        c.ι.app j ≫ m.val = (s.ι.app j).val := congrArg Sheaf.Hom.val (hm j)
        _ = c.ι.app j ≫ (hc.desc sVal) := (hc.fac sVal j).symm

/-- Presheaf-boundary successor-step compatibility for the filtered-colimit comparison map:
whenever the associated sheaf diagram and the colimit sheaf have vanishing injective-replacement
cohomology in degrees `n` and `n + 1`, the degree-`n + 1` comparison is conjugate to the
degree-`n` comparison for the quotient diagram. -/
theorem sheafH_filtered_colimit_comparison_succ_compatibility_presheaf
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y : J' ⥤ TopCat.Presheaf AddCommGrpCat.{u} X)
    (hY : ∀ j, TopCat.Presheaf.IsSheaf (Y.obj j))
    [Zero (TopCat.Sheaf AddCommGrpCat.{u} X)]
    (c : Cocone Y) (hc_pt : TopCat.Presheaf.IsSheaf c.pt)
    (hcsh : IsColimit (sheafH_filtered_colimit_presheafCocone Y hY c hc_pt))
    (n : ℕ)
    (h_mid_n : ∀ j,
      Subsingleton (Sheaf.H
        ((sheafH_filtered_colimit_succ_Inj
          (sheafH_filtered_colimit_presheafDiagram Y hY)).obj j) n))
    (h_mid_succ : ∀ j,
      Subsingleton (Sheaf.H
        ((sheafH_filtered_colimit_succ_Inj
          (sheafH_filtered_colimit_presheafDiagram Y hY)).obj j) (n + 1)))
    (h_colim_n :
      Subsingleton (Sheaf.H
        (sheafH_filtered_colimit_succ_injCocone
          (sheafH_filtered_colimit_presheafDiagram Y hY)).pt n))
    (h_colim_succ :
      Subsingleton (Sheaf.H
        (sheafH_filtered_colimit_succ_injCocone
          (sheafH_filtered_colimit_presheafDiagram Y hY)).pt (n + 1))) :
    let Ysh := sheafH_filtered_colimit_presheafDiagram Y hY
    let csh := sheafH_filtered_colimit_presheafCocone Y hY c hc_pt
    (sheafH_filtered_colimit_succ_shiftDomainIso Ysh n h_mid_n h_mid_succ).hom ≫
        sheafH_filtered_colimit_comparison_presheaf Y hY c hc_pt (n + 1) =
      sheafH_filtered_colimit_comparison
        (sheafH_filtered_colimit_succ_quotient Ysh) n
        (sheafH_filtered_colimit_succ_quotientCocone Ysh csh hcsh) ≫
      (sheafH_filtered_colimit_succ_shiftCodomainIso Ysh csh hcsh n
        h_colim_n h_colim_succ).hom := by
  let Ysh := sheafH_filtered_colimit_presheafDiagram Y hY
  let csh := sheafH_filtered_colimit_presheafCocone Y hY c hc_pt
  change
    (sheafH_filtered_colimit_succ_shiftDomainIso Ysh n h_mid_n h_mid_succ).hom ≫
        sheafH_filtered_colimit_comparison Ysh (n + 1) csh =
      sheafH_filtered_colimit_comparison (sheafH_filtered_colimit_succ_quotient Ysh) n
        (sheafH_filtered_colimit_succ_quotientCocone Ysh csh hcsh) ≫
      (sheafH_filtered_colimit_succ_shiftCodomainIso Ysh csh hcsh n
        h_colim_n h_colim_succ).hom
  apply colimit.hom_ext
  intro j
  rw [show (sheafH_filtered_colimit_succ_shiftDomainIso Ysh n h_mid_n h_mid_succ).hom =
      (HasColimit.isoOfNatIso (sheafH_filtered_colimit_succ_shiftNatIso Ysh n
        h_mid_n h_mid_succ)).hom from rfl]
  rw [HasColimit.isoOfNatIso_ι_hom_assoc]
  rw [colimit_ι_sheafH_filtered_colimit_comparison]
  have hqj := colimit_ι_sheafH_filtered_colimit_comparison
    (X := X) (Y' := sheafH_filtered_colimit_succ_quotient Ysh) (n := n)
    (c' := sheafH_filtered_colimit_succ_quotientCocone Ysh csh hcsh) j
  have hqj_assoc :
      (colimit.ι (sheafH_filtered_colimit_succ_quotient Ysh ⋙ sheafCohomologyFunctor X n) j ≫
          sheafH_filtered_colimit_comparison (sheafH_filtered_colimit_succ_quotient Ysh) n
            (sheafH_filtered_colimit_succ_quotientCocone Ysh csh hcsh)) ≫
        (sheafH_filtered_colimit_succ_shiftCodomainIso Ysh csh hcsh n
          h_colim_n h_colim_succ).hom =
      (sheafCohomologyFunctor X n).map
          ((sheafH_filtered_colimit_succ_quotientCocone Ysh csh hcsh).ι.app j) ≫
        (sheafH_filtered_colimit_succ_shiftCodomainIso Ysh csh hcsh n
          h_colim_n h_colim_succ).hom := by
    simpa [Category.assoc] using
      congrArg
        (fun t =>
          t ≫ (sheafH_filtered_colimit_succ_shiftCodomainIso Ysh csh hcsh n
            h_colim_n h_colim_succ).hom) hqj
  have hqj_assoc' :
      colimit.ι (sheafH_filtered_colimit_succ_quotient Ysh ⋙ sheafCohomologyFunctor X n) j ≫
          sheafH_filtered_colimit_comparison (sheafH_filtered_colimit_succ_quotient Ysh) n
            (sheafH_filtered_colimit_succ_quotientCocone Ysh csh hcsh) ≫
        (sheafH_filtered_colimit_succ_shiftCodomainIso Ysh csh hcsh n
          h_colim_n h_colim_succ).hom =
      (sheafCohomologyFunctor X n).map
          ((sheafH_filtered_colimit_succ_quotientCocone Ysh csh hcsh).ι.app j) ≫
        (sheafH_filtered_colimit_succ_shiftCodomainIso Ysh csh hcsh n
          h_colim_n h_colim_succ).hom := by
    exact hqj_assoc
  rw [hqj_assoc']
  change
    (sheafH_extClassIso_of_subsingleton_middle_presheaf
        (h₁ := (Ysh.obj j).cond)
        (h₂ := ((sheafH_filtered_colimit_succ_Inj Ysh).obj j).cond)
        (h₃ := (cokernel ((sheafH_filtered_colimit_succ_eta Ysh).app j)).cond)
        (f := ((sheafH_filtered_colimit_succ_eta Ysh).app j).val)
        (g := (cokernel.π ((sheafH_filtered_colimit_succ_eta Ysh).app j)).val)
        (by
          ext U
          rename_i s
          change AddCommGrpCat.Hom.hom
              (((((sheafH_filtered_colimit_succ_eta Ysh).app j) ≫
                    cokernel.π ((sheafH_filtered_colimit_succ_eta Ysh).app j)).val).app
                (op U)) s = 0
          have happ :
              (((sheafH_filtered_colimit_succ_eta Ysh).app j ≫
                    cokernel.π ((sheafH_filtered_colimit_succ_eta Ysh).app j)).val).app
                (op U) =
              NatTrans.app
                (0 : (Ysh.obj j).val ⟶
                  (cokernel ((sheafH_filtered_colimit_succ_eta Ysh).app j)).val) (op U) :=
            NatTrans.congr_app
              (congrArg (fun α => α.val)
                (cokernel.condition ((sheafH_filtered_colimit_succ_eta Ysh).app j)))
              (op U)
          rw [happ]
          simp)
        (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Ysh) j) n
        (h_mid_n j) (h_mid_succ j)).hom ≫
      (sheafCohomologyFunctor X (n + 1)).map (csh.ι.app j) =
    (sheafCohomologyFunctor X n).map
        ((sheafH_filtered_colimit_succ_quotientCocone Ysh csh hcsh).ι.app j) ≫
      (sheafH_filtered_colimit_succ_shiftCodomainIso Ysh csh hcsh n
        h_colim_n h_colim_succ).hom
  simpa [sheafH_filtered_colimit_succ_shiftNatIso,
    sheafH_filtered_colimit_succ_shiftCodomainIso] using
    (sheafH_extClassIso_of_subsingleton_middle_presheaf_natural
      (h₁₁ := (Ysh.obj j).cond)
      (h₁₂ := ((sheafH_filtered_colimit_succ_Inj Ysh).obj j).cond)
      (h₁₃ := (cokernel ((sheafH_filtered_colimit_succ_eta Ysh).app j)).cond)
      (h₂₁ := csh.pt.cond)
      (h₂₂ := (sheafH_filtered_colimit_succ_injCocone Ysh).pt.cond)
      (h₂₃ := (sheafH_filtered_colimit_succ_quotientCocone Ysh csh hcsh).pt.cond)
      (f₁ := ((sheafH_filtered_colimit_succ_eta Ysh).app j).val)
      (g₁ := (cokernel.π ((sheafH_filtered_colimit_succ_eta Ysh).app j)).val)
      (by
        ext U
        rename_i s
        change AddCommGrpCat.Hom.hom
            (((((sheafH_filtered_colimit_succ_eta Ysh).app j) ≫
                  cokernel.π ((sheafH_filtered_colimit_succ_eta Ysh).app j)).val).app
              (op U)) s = 0
        have happ :
            (((sheafH_filtered_colimit_succ_eta Ysh).app j ≫
                  cokernel.π ((sheafH_filtered_colimit_succ_eta Ysh).app j)).val).app
              (op U) =
            NatTrans.app
              (0 : (Ysh.obj j).val ⟶
                (cokernel ((sheafH_filtered_colimit_succ_eta Ysh).app j)).val) (op U) :=
          NatTrans.congr_app
            (congrArg (fun α => α.val)
              (cokernel.condition ((sheafH_filtered_colimit_succ_eta Ysh).app j)))
            (op U)
        rw [happ]
        simp)
      (f₂ := (sheafH_filtered_colimit_succ_iota Ysh csh hcsh).val)
      (g₂ := (cokernel.π (sheafH_filtered_colimit_succ_iota Ysh csh hcsh)).val)
      (by
        ext U
        rename_i s
        change AddCommGrpCat.Hom.hom
            ((((sheafH_filtered_colimit_succ_iota Ysh csh hcsh ≫
                  cokernel.π (sheafH_filtered_colimit_succ_iota Ysh csh hcsh)).val).app
              (op U))) s = 0
        have happ :
            ((sheafH_filtered_colimit_succ_iota Ysh csh hcsh ≫
                  cokernel.π (sheafH_filtered_colimit_succ_iota Ysh csh hcsh)).val).app
                (op U) =
              NatTrans.app
                (0 : csh.pt.val ⟶
                  (sheafH_filtered_colimit_succ_quotientCocone Ysh csh hcsh).pt.val) (op U) :=
          NatTrans.congr_app
            (congrArg (fun α => α.val)
              (cokernel.condition (sheafH_filtered_colimit_succ_iota Ysh csh hcsh)))
            (op U)
        rw [happ]
        simp)
      (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Ysh) j)
      (sheafH_filtered_colimit_succ_shortExact Ysh csh hcsh)
      (τ₁ := (csh.ι.app j).val)
      (τ₂ := ((sheafH_filtered_colimit_succ_injCocone Ysh).ι.app j).val)
      (τ₃ := ((sheafH_filtered_colimit_succ_quotientCocone Ysh csh hcsh).ι.app j).val)
      (by
        simpa using congrArg (fun α => α.val)
          ((sheafH_filtered_colimit_succ_stage_hom Ysh csh hcsh j).comm₁₂))
      (by
        simpa using congrArg (fun α => α.val)
          ((sheafH_filtered_colimit_succ_stage_hom Ysh csh hcsh j).comm₂₃))
      n (h_mid_n j) (h_mid_succ j) h_colim_n h_colim_succ)

/-- Successor-step compatibility for the filtered-colimit comparison map: whenever the
    stagewise and colimit injective replacement terms have vanishing cohomology in degrees
    `n` and `n + 1`, the comparison map in degree `n + 1` is conjugate to the comparison map
    for the cokernel diagram in degree `n`. -/
theorem sheafH_filtered_colimit_comparison_succ_compatibility
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    [Zero (TopCat.Sheaf AddCommGrpCat.{u} X)]
    (c' : Cocone Y') (hc' : IsColimit c')
    (n : ℕ)
    (h_mid_n : ∀ j, Subsingleton (Sheaf.H ((sheafH_filtered_colimit_succ_Inj Y').obj j) n))
    (h_mid_succ : ∀ j,
      Subsingleton (Sheaf.H ((sheafH_filtered_colimit_succ_Inj Y').obj j) (n + 1)))
    (h_colim_n :
      Subsingleton (Sheaf.H (sheafH_filtered_colimit_succ_injCocone Y').pt n))
    (h_colim_succ :
      Subsingleton (Sheaf.H (sheafH_filtered_colimit_succ_injCocone Y').pt (n + 1))) :
    (sheafH_filtered_colimit_succ_shiftDomainIso Y' n h_mid_n h_mid_succ).hom ≫
        sheafH_filtered_colimit_comparison Y' (n + 1) c' =
      sheafH_filtered_colimit_comparison (sheafH_filtered_colimit_succ_quotient Y') n
        (sheafH_filtered_colimit_succ_quotientCocone Y' c' hc') ≫
      (sheafH_filtered_colimit_succ_shiftCodomainIso Y' c' hc' n
        h_colim_n h_colim_succ).hom := by
  let Y := Y' ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let Ysh : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
    sheafH_filtered_colimit_presheafDiagram Y (fun j => (Y'.obj j).cond)
  let c := (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone c'
  let csh : Cocone Ysh :=
    sheafH_filtered_colimit_presheafCocone
      Y
      (fun j => (Y'.obj j).cond)
      c
      c'.pt.cond
  let hcsh : IsColimit csh := by
    dsimp [csh, Ysh, Y, c]
    simpa [sheafH_filtered_colimit_presheafCocone_sheafToPresheaf] using hc'
  have hcompat :=
    sheafH_filtered_colimit_comparison_succ_compatibility_presheaf
      (Y := Y)
      (hY := fun j => (Y'.obj j).cond)
      (c := c)
      (hc_pt := c'.pt.cond)
      (hcsh := hcsh)
      (n := n)
      h_mid_n h_mid_succ h_colim_n h_colim_succ
  change
    (sheafH_filtered_colimit_succ_shiftDomainIso Ysh n h_mid_n h_mid_succ).hom ≫
        sheafH_filtered_colimit_comparison_presheaf Y (fun j => (Y'.obj j).cond) c c'.pt.cond
          (n + 1) =
      sheafH_filtered_colimit_comparison (sheafH_filtered_colimit_succ_quotient Ysh) n
        (sheafH_filtered_colimit_succ_quotientCocone Ysh csh hcsh) ≫
      (sheafH_filtered_colimit_succ_shiftCodomainIso Ysh csh hcsh n
        h_colim_n h_colim_succ).hom at hcompat
  simpa [Ysh, csh, Y, c, hcsh,
    sheafH_filtered_colimit_comparison_sheafToPresheaf] using hcompat
