import Aristotle.GrothendieckVanishing.main.PresheafFilteredColimit
import Aristotle.GrothendieckVanishing.main.ClosedImmersionCohomology
import Aristotle.GrothendieckVanishing.main.ZeroOutsideFinset

/-!
  FinitelyGeneratedVanishing.lean — Noetherian finitely generated vanishing reduction

  Key results:
  - finsetGenFunctor / finsetGenCocone / finsetGenCocone_isColimit: K is the filtered
    colimit of its finitely generated subsheaves (PROVED)
  - cohomology_vanishing_of_finitelyGenerated_vanishing: H^m = 0 for all f.g. subsheaves
    implies H^m(K) = 0 (PROVED via sheafH_preserves_filtered_colimits)
  - finsetGeneratedSheaf_vanishing: vanishing for finitely generated sheaves by
    Finset.induction (PROVED)
  - directLimit_cohomology_vanishing: from epi-image vanishing to all sheaves (PROVED)

  Note: isFlasque_filtered_colimit_presheaf, sheafH_preserves_filtered_colimits, and
  sheafH_filtered_colimit_surj_presheaf live in the PresheafFilteredColimit modules.
-/

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

/-! ### Filtered diagram of finitely generated subsheaves

We build a functor `Finset(SectionIndex K) ⥤ Sheaf(X)` sending each finite set `S`
of local sections to the subsheaf `finsetGeneratedSheaf S`. The transition maps
(for `S ⊆ S'`) are monomorphisms, and K is the colimit of this filtered diagram. -/

section FilteredDiagram
open scoped Classical

variable {X : TopCat.{u}} [NoetherianSpace X]
    {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf)

/-- The functor `Finset(SectionIndex K) ⥤ Sheaf(X)` sending `S ↦ finsetGeneratedSheaf S`.
    Transition maps are the canonical image inclusions, which are monomorphisms. -/
noncomputable def finsetGenFunctor :
    Finset
        (TopCat.Presheaf.SectionIndex K) ⥤
      TopCat.Sheaf AddCommGrpCat.{u} X where
  obj S := TopCat.Presheaf.finsetGeneratedSheaf hK S
  map h := TopCat.Presheaf.finsetImageInclGen hK h.le
  map_id S := by
    apply (cancel_mono (Limits.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S))).1
    rw [TopCat.Presheaf.finsetImageInclGen_comp_ι, Category.id_comp]
  map_comp {S₁ S₂ S₃} h₁ h₂ := by
    apply (cancel_mono (Limits.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S₃))).1
    rw [Category.assoc, TopCat.Presheaf.finsetImageInclGen_comp_ι,
      TopCat.Presheaf.finsetImageInclGen_comp_ι,
      TopCat.Presheaf.finsetImageInclGen_comp_ι]

/-- Cocone with vertex `K`: the cocone maps are `image.ι : finsetGeneratedSheaf S ⟶ K`. -/
noncomputable def finsetGenCocone :
    Cocone (finsetGenFunctor hK) :=
  Cocone.mk (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)
    { app := fun S => Limits.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S)
      naturality := fun S S' h => by
        simp [finsetGenFunctor, TopCat.Presheaf.finsetImageInclGen_comp_ι] }

/-- The cocone is a colimit: `K` is the filtered colimit of its finitely generated subsheaves.
    Proof: the canonical map `colim → K` is mono (by AB5 + mono transitions) and epi
    (since `allSectionMap K` factors through it), hence an isomorphism. -/
noncomputable def finsetGenCocone_isColimit :
    IsColimit (finsetGenCocone hK) := by
  let Ksh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨K, hK⟩
  -- Show the comparison map colim → K is an iso, then transport IsColimit
  let d := colimit.desc (finsetGenFunctor hK) (finsetGenCocone hK)
  -- desc is mono: natural transformation to const K has all components mono (image.ι),
  -- and in a Grothendieck abelian category filtered colimits preserve monos
  have hd_mono : Mono d := by
    haveI : IsConnected
        (Finset (TopCat.Presheaf.SectionIndex K)) := IsFiltered.isConnected _
    let α : finsetGenFunctor hK ⟶ (Functor.const _).obj Ksh :=
      { app := fun S => Limits.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S)
        naturality := fun S S' h => by
          simp [finsetGenFunctor, TopCat.Presheaf.finsetImageInclGen_comp_ι] }
    haveI : ∀ j, Mono (α.app j) := fun _ => inferInstance
    haveI := NatTrans.mono_of_mono_app α
    exact colim.map_mono' α (colimit.isColimit _) (isColimitConstCocone _ _) d
      (fun j => by simp [d, α, finsetGenCocone, constCocone])
  -- desc is epi: allSectionMap K factors through desc
  have hd_epi : Epi d := by
    let g : (∐ fun σ : TopCat.Presheaf.SectionIndex K => TopCat.Sheaf.zeroOutsideInt σ.1) ⟶
        colimit (finsetGenFunctor hK) :=
      Sigma.desc fun σ =>
        Sigma.ι (fun τ : {τ // τ ∈ ({σ} : Finset _)} =>
            TopCat.Sheaf.zeroOutsideInt τ.1.1) ⟨σ, Finset.mem_singleton_self σ⟩ ≫
          factorThruImage (TopCat.Presheaf.finsetGeneratorMap hK {σ}) ≫
          colimit.ι (finsetGenFunctor hK) {σ}
    have hfac : g ≫ d = TopCat.Presheaf.allSectionMap hK := by
      dsimp only [g, d]; apply Sigma.hom_ext; intro σ
      rw [← Category.assoc, Sigma.ι_desc, Category.assoc, Category.assoc, colimit.ι_desc]
      change
        Sigma.ι (fun τ : {τ // τ ∈ ({σ} : Finset _)} => TopCat.Sheaf.zeroOutsideInt τ.1.1)
            ⟨σ, Finset.mem_singleton_self σ⟩ ≫
          factorThruImage (TopCat.Presheaf.finsetGeneratorMap hK {σ}) ≫
          Limits.image.ι (TopCat.Presheaf.finsetGeneratorMap hK {σ}) =
        Sigma.ι (fun τ : TopCat.Presheaf.SectionIndex K => TopCat.Sheaf.zeroOutsideInt τ.1) σ ≫
          TopCat.Presheaf.allSectionMap hK
      rw [Limits.image.fac]
      simp [TopCat.Presheaf.allSectionMap, TopCat.Presheaf.finsetGeneratorMap,
        TopCat.Sheaf.familyMap]
    haveI := TopCat.Presheaf.allSectionMap_epi (F := K) hK
    exact epi_of_epi_fac hfac
  -- mono + epi → iso in abelian category
  haveI := hd_mono; haveI := hd_epi
  haveI : IsIso ((colimit.isColimit (finsetGenFunctor hK)).desc (finsetGenCocone hK)) :=
    isIso_of_mono_of_epi d
  exact (colimit.isColimit (finsetGenFunctor hK)).ofPointIso

end FilteredDiagram

/-- **Hartshorne III, Ex. 2.9 core**: on a Noetherian space, if `H^m = 0` for all finitely generated
    subsheaves of `K`, then `H^m(K) = 0`. Uses the filtered-colimit comparison isomorphism
    for the diagram of finitely generated subsheaves and transports zero across it. -/
theorem cohomology_vanishing_of_finitelyGenerated_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf) (m : ℕ)
    (hfg : ∀ (S : Finset
        (TopCat.Presheaf.SectionIndex K))
      [HasCoproduct fun σ : {σ // σ ∈ S} => TopCat.Sheaf.zeroOutsideInt σ.1.1],
      Subsingleton (Sheaf.H (TopCat.Presheaf.finsetGeneratedSheaf hK S) m)) :
    Subsingleton (Sheaf.H (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) m) := by
  have hZeroDiagram : IsZero (finsetGenFunctor hK ⋙ sheafCohomologyFunctor X m) := by
    refine Functor.isZero _ ?_
    intro S
    haveI : Subsingleton (Sheaf.H (TopCat.Presheaf.finsetGeneratedSheaf hK S) m) := hfg S
    simpa [finsetGenFunctor, sheafCohomologyFunctor_obj] using
      (AddCommGrpCat.isZero_of_subsingleton
        (AddCommGrpCat.of (Sheaf.H (TopCat.Presheaf.finsetGeneratedSheaf hK S) m)))
  have hZeroColim :
      IsZero (colimit (finsetGenFunctor hK ⋙ sheafCohomologyFunctor X m)) :=
    (colimit.isColimit _).isZero_pt hZeroDiagram
  haveI : CreatesColimit (finsetGenFunctor hK)
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    createsFilteredColimit (finsetGenFunctor hK)
  have hZeroTarget :
      IsZero (AddCommGrpCat.of
        (Sheaf.H (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) m)) := by
    simpa [finsetGenCocone] using
      IsZero.of_iso hZeroColim
        (sheafH_preserves_filtered_colimits_presheaf
          (Y := finsetGenFunctor hK ⋙
            sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
          (hY := fun j => (finsetGenFunctor hK).obj j |>.cond)
          (c := (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone
            (finsetGenCocone hK))
          (hc := isColimitOfPreserves
            (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
            (finsetGenCocone_isColimit hK))
          (hc_pt := hK) m).symm
  simpa using AddCommGrpCat.subsingleton_of_isZero hZeroTarget

section FinsetGenerated
open scoped Classical

variable {X : TopCat.{u}} {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf)

/-- **Step 3B–3C**: vanishing for `finsetGeneratedSheaf S` by `Finset.induction`. -/
theorem finsetGeneratedSheaf_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf)
    (m : ℕ)
    (hzero : ∀ {G : TopCat.Presheaf AddCommGrpCat.{u} X} (hG : G.IsSheaf) {V : Opens X}
      (f : (TopCat.Sheaf.zeroOutsideInt V).val ⟶ G),
      TopCat.Presheaf.IsLocallySurjective f →
      Subsingleton (Sheaf.H (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) m))
    (S : Finset
      (TopCat.Presheaf.SectionIndex K))
    [HasCoproduct fun σ : {σ // σ ∈ S} => TopCat.Sheaf.zeroOutsideInt σ.1.1] :
    Subsingleton (Sheaf.H (TopCat.Presheaf.finsetGeneratedSheaf hK S) m) := by
  suffices h : ∀ (T : Finset (TopCat.Presheaf.SectionIndex K)),
      Subsingleton (Sheaf.H (TopCat.Presheaf.finsetGeneratedSheaf hK T) m) from by
    exact h S
  intro T; induction T using Finset.induction with
  | empty =>
    simpa using sheafH_subsingleton_of_isZero_presheaf
      (F := (TopCat.Presheaf.finsetGeneratedSheaf hK ∅).val)
      (hF := (TopCat.Presheaf.finsetGeneratedSheaf hK ∅).cond)
      (hzero := by
        simpa using (show IsZero (TopCat.Presheaf.finsetGeneratedSheaf hK ∅) from by
          apply IsZero.of_iso (isZero_zero _) (imageZero' _)
          apply Sigma.hom_ext
          intro ⟨σ, hσ⟩
          simp at hσ))
      m
  | @insert σ₀ S' _ ih =>
    let h_sub := Finset.subset_insert σ₀ S'
    let SC := ShortComplex.mk (TopCat.Presheaf.finsetImageInclGen hK h_sub)
      (cokernel.π (TopCat.Presheaf.finsetImageInclGen hK h_sub)) (cokernel.condition _)
    have hSE : SC.ShortExact := ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel
        (TopCat.Presheaf.finsetImageInclGen hK h_sub)))
      inferInstance inferInstance
    have hCoker : Subsingleton (Sheaf.H SC.X₃ m) :=
      by
        let g :
            TopCat.Sheaf.zeroOutsideInt σ₀.1 ⟶ SC.X₃ :=
          Sigma.ι (fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1)
            ⟨σ₀, Finset.mem_insert_self σ₀ S'⟩ ≫
          factorThruImage (TopCat.Presheaf.finsetGeneratorMap hK (insert σ₀ S')) ≫
          cokernel.π (TopCat.Presheaf.finsetImageInclGen hK h_sub)
        haveI : Epi g := by
          let proj :
              (∐ fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1) ⟶
                TopCat.Sheaf.zeroOutsideInt σ₀.1 :=
            Sigma.desc fun σ =>
              if h : σ.1 = σ₀ then
                eqToHom (by rw [h])
              else 0
          have heq : TopCat.Presheaf.finsetCoproductInclGen h_sub ≫
              factorThruImage (TopCat.Presheaf.finsetGeneratorMap hK (insert σ₀ S')) =
            factorThruImage (TopCat.Presheaf.finsetGeneratorMap hK S') ≫
              TopCat.Presheaf.finsetImageInclGen hK h_sub := by
            apply (cancel_mono (Limits.image.ι
              (TopCat.Presheaf.finsetGeneratorMap hK (insert σ₀ S')))).1
            rw [Category.assoc, Limits.image.fac]
            have hlf : TopCat.Presheaf.finsetImageInclGen hK h_sub ≫
                Limits.image.ι (TopCat.Presheaf.finsetGeneratorMap hK (insert σ₀ S')) =
                Limits.image.ι (TopCat.Presheaf.finsetGeneratorMap hK S') := by
              simpa using TopCat.Presheaf.finsetImageInclGen_comp_ι
                (F := K) hK h_sub
            rw [Category.assoc, hlf, Limits.image.fac]
            ext ⟨σ', hσ'⟩
            simp [TopCat.Presheaf.finsetCoproductInclGen, TopCat.Presheaf.finsetGeneratorMap,
              TopCat.Sheaf.familyMap]
          have hfac : proj ≫ g =
              factorThruImage (TopCat.Presheaf.finsetGeneratorMap hK (insert σ₀ S')) ≫
                cokernel.π (TopCat.Presheaf.finsetImageInclGen hK h_sub) := by
            ext ⟨σ, hσ⟩
            simp only [proj]
            by_cases h : σ = σ₀
            · subst h
              simp [g]
            · rw [← Category.assoc
                (Sigma.ι (fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1)
                  ⟨σ, hσ⟩)
                (Sigma.desc _)]
              rw [colimit.ι_desc, Cofan.mk_ι_app, dif_neg h, zero_comp]
              symm
              have hι : Sigma.ι (fun τ : {τ // τ ∈ S'} => TopCat.Sheaf.zeroOutsideInt τ.1.1)
                  ⟨σ, Finset.mem_of_mem_insert_of_ne hσ h⟩ ≫
                  TopCat.Presheaf.finsetCoproductInclGen h_sub =
                Sigma.ι (fun τ : {τ // τ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt τ.1.1)
                  ⟨σ, hσ⟩ := by
                simp [TopCat.Presheaf.finsetCoproductInclGen]
              rw [← hι, Category.assoc, reassoc_of% heq]
              simp [cokernel.condition]
          exact epi_of_epi_fac hfac
        letI : Balanced (CategoryTheory.Sheaf (Opens.grothendieckTopology X)
            AddCommGrpCat.{u}) := balanced_of_strongEpiCategory
        have hg_loc : TopCat.Presheaf.IsLocallySurjective g.val := by
          simpa [g] using
            (show Sheaf.IsLocallySurjective g from
              (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} g).mpr inferInstance)
        simpa [g] using hzero SC.X₃.cond g.val hg_loc
    haveI : Mono SC.f.val := Functor.map_mono
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X) SC.f
    simpa [SC, h_sub] using
      (subsingleton_sheafH_of_shortExact_middle_presheaf
        (hF := SC.X₁.cond) (hG := SC.X₂.cond) (f := SC.f.val) m ih
        (by simpa [SC, h_sub] using hCoker))

end FinsetGenerated

/-- **Step 3A** (Hartshorne III.2.7): on a Noetherian space, if vanishing holds for
    all epi images of `zeroOutsideInt V`, then it holds for every sheaf.
    Assembles `finsetGeneratedSheaf_vanishing` (finite case) with
    `cohomology_vanishing_of_finitelyGenerated_vanishing` (colimit step). -/
theorem directLimit_cohomology_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf) (m : ℕ)
    (hzero : ∀ {G : TopCat.Presheaf AddCommGrpCat.{u} X} (hG : G.IsSheaf) {V : Opens X}
      (f : (TopCat.Sheaf.zeroOutsideInt V).val ⟶ G),
      TopCat.Presheaf.IsLocallySurjective f →
      Subsingleton (Sheaf.H (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) m)) :
    Subsingleton (Sheaf.H (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) m) := by
  exact cohomology_vanishing_of_finitelyGenerated_vanishing hK m
    (fun S _ => finsetGeneratedSheaf_vanishing hK m hzero S)
