import Aristotle.GrothendieckVanishing.main.PresheafFilteredColimit
import Aristotle.GrothendieckVanishing.main.ClosedImmersionCohomology
import Aristotle.GrothendieckVanishing.main.ZeroOutsideFinset

/-!
  FiniteGeneratorReduction.lean — Colimit step and finitely generated vanishing

  Key results:
  - finsetGenFunctor / finsetGenCocone / finsetGenCocone_isColimit: K is the filtered
    colimit of its finitely generated subsheaves (PROVED)
  - cohomology_vanishing_of_finitelyGenerated_vanishing: H^m = 0 for all f.g. subsheaves
    implies H^m(K) = 0 (PROVED via sheafH_preserves_filtered_colimits)
  - finsetGeneratedSheaf_vanishing: vanishing for finitely generated sheaves by
    Finset.induction (PROVED)
  - directLimit_cohomology_vanishing: from epi-image vanishing to all sheaves (PROVED)

  Note: isFlasque_filtered_colimit, sheafH_preserves_filtered_colimits, and
  sheafH_filtered_colimit_surj have been moved to PresheafFilteredColimit.lean.
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

/-- Coproduct inclusion for general `S ⊆ S'`. -/
private noncomputable def finsetCoproductInclGen
    {S S' : Finset
      (TopCat.Sheaf.SectionIndex (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))}
    (h : S ⊆ S') :
    (∐ fun σ : {σ // σ ∈ S} => TopCat.Sheaf.zeroOutsideInt σ.1.1) ⟶
    (∐ fun σ : {σ // σ ∈ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1) :=
  Sigma.desc fun σ =>
    Sigma.ι (fun τ : {τ // τ ∈ S'} => TopCat.Sheaf.zeroOutsideInt τ.1.1) ⟨σ.1, h σ.2⟩

/-- Image inclusion for general `S ⊆ S'`: `finsetGeneratedSheaf S ⟶ finsetGeneratedSheaf S'`. -/
private noncomputable def finsetImageInclGen
    {S S' : Finset
      (TopCat.Sheaf.SectionIndex (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))}
    (h : S ⊆ S') :
    TopCat.Sheaf.finsetGeneratedSheaf S ⟶ TopCat.Sheaf.finsetGeneratedSheaf S' :=
  Limits.image.lift
    { I := TopCat.Sheaf.finsetGeneratedSheaf S'
      m := TopCat.Sheaf.familyGeneratedSheafι
        (fun σ : {σ // σ ∈ S'} => σ.1.1) (fun σ => σ.1.2)
      e := finsetCoproductInclGen hK h ≫ factorThruImage (TopCat.Sheaf.finsetGeneratorMap S')
      fac := by
        rw [TopCat.Sheaf.familyGeneratedSheaf_ι_eq, Category.assoc, Limits.image.fac]
        ext ⟨σ, hσ⟩
        simp [finsetCoproductInclGen, TopCat.Sheaf.finsetGeneratorMap,
              TopCat.Sheaf.familyMap] }

omit [NoetherianSpace X] in
private lemma finsetImageInclGen_comp_ι
    {S S' : Finset
      (TopCat.Sheaf.SectionIndex (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))}
    (h : S ⊆ S') :
    finsetImageInclGen hK h ≫
        TopCat.Sheaf.familyGeneratedSheafι
          (fun σ : {σ // σ ∈ S'} => σ.1.1) (fun σ => σ.1.2) =
      TopCat.Sheaf.familyGeneratedSheafι
        (fun σ : {σ // σ ∈ S} => σ.1.1) (fun σ => σ.1.2) := by
  change finsetImageInclGen hK h ≫ Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap S') =
      Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap S)
  exact Limits.image.lift_fac _

private instance finsetImageInclGen_mono
    {S S' : Finset
      (TopCat.Sheaf.SectionIndex (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))}
    (h : S ⊆ S') :
    Mono (finsetImageInclGen hK h) :=
  mono_of_mono_fac (finsetImageInclGen_comp_ι hK h)

/-- The functor `Finset(SectionIndex K) ⥤ Sheaf(X)` sending `S ↦ finsetGeneratedSheaf S`.
    Transition maps are the canonical image inclusions, which are monomorphisms. -/
private noncomputable def finsetGenFunctor :
    Finset
        (TopCat.Sheaf.SectionIndex (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) ⥤
      TopCat.Sheaf AddCommGrpCat.{u} X where
  obj S := TopCat.Sheaf.finsetGeneratedSheaf S
  map h := finsetImageInclGen hK h.le
  map_id S := by
    apply (cancel_mono (TopCat.Sheaf.familyGeneratedSheafι
      (fun σ : {σ // σ ∈ S} => σ.1.1) (fun σ => σ.1.2))).1
    rw [finsetImageInclGen_comp_ι, Category.id_comp]
  map_comp {S₁ S₂ S₃} h₁ h₂ := by
    apply (cancel_mono (TopCat.Sheaf.familyGeneratedSheafι
      (fun σ : {σ // σ ∈ S₃} => σ.1.1) (fun σ => σ.1.2))).1
    rw [Category.assoc, finsetImageInclGen_comp_ι, finsetImageInclGen_comp_ι,
        finsetImageInclGen_comp_ι]

/-- Cocone with vertex `K`: the cocone maps are `image.ι : finsetGeneratedSheaf S ⟶ K`. -/
private noncomputable def finsetGenCocone :
    Cocone (finsetGenFunctor hK) :=
  Cocone.mk (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)
    { app := fun S => TopCat.Sheaf.familyGeneratedSheafι
        (fun σ : {σ // σ ∈ S} => σ.1.1) (fun σ => σ.1.2)
      naturality := fun S S' h => by
        simp [finsetGenFunctor, finsetImageInclGen_comp_ι] }

/-- The cocone is a colimit: `K` is the filtered colimit of its finitely generated subsheaves.
    Proof: the canonical map `colim → K` is mono (by AB5 + mono transitions) and epi
    (since `allSectionMap K` factors through it), hence an isomorphism. -/
private noncomputable def finsetGenCocone_isColimit :
    IsColimit (finsetGenCocone hK) := by
  let Ksh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨K, hK⟩
  -- Show the comparison map colim → K is an iso, then transport IsColimit
  let d := colimit.desc (finsetGenFunctor hK) (finsetGenCocone hK)
  -- desc is mono: natural transformation to const K has all components mono (image.ι),
  -- and in a Grothendieck abelian category filtered colimits preserve monos
  have hd_mono : Mono d := by
    haveI : IsConnected
        (Finset (TopCat.Sheaf.SectionIndex Ksh)) := IsFiltered.isConnected _
    let α : finsetGenFunctor hK ⟶ (Functor.const _).obj Ksh :=
      { app := fun S => TopCat.Sheaf.familyGeneratedSheafι
          (fun σ : {σ // σ ∈ S} => σ.1.1) (fun σ => σ.1.2)
        naturality := fun S S' h => by
          simp [finsetGenFunctor, finsetImageInclGen_comp_ι] }
    haveI : ∀ j, Mono (α.app j) := fun _ => inferInstance
    haveI := NatTrans.mono_of_mono_app α
    exact colim.map_mono' α (colimit.isColimit _) (isColimitConstCocone _ _) d
      (fun j => by simp [d, α, finsetGenCocone, constCocone])
  -- desc is epi: allSectionMap K factors through desc
  have hd_epi : Epi d := by
    let g : (∐ fun σ : TopCat.Sheaf.SectionIndex Ksh => TopCat.Sheaf.zeroOutsideInt σ.1) ⟶
        colimit (finsetGenFunctor hK) :=
      Sigma.desc fun σ =>
        Sigma.ι (fun τ : {τ // τ ∈ ({σ} : Finset _)} =>
            TopCat.Sheaf.zeroOutsideInt τ.1.1) ⟨σ, Finset.mem_singleton_self σ⟩ ≫
          factorThruImage (TopCat.Sheaf.finsetGeneratorMap {σ}) ≫
          colimit.ι (finsetGenFunctor hK) {σ}
    have hfac : g ≫ d = TopCat.Sheaf.allSectionMap Ksh := by
      dsimp only [g, d]; apply Sigma.hom_ext; intro σ
      rw [← Category.assoc, Sigma.ι_desc, Category.assoc, Category.assoc, colimit.ι_desc]
      change
        Sigma.ι (fun τ : {τ // τ ∈ ({σ} : Finset _)} => TopCat.Sheaf.zeroOutsideInt τ.1.1)
            ⟨σ, Finset.mem_singleton_self σ⟩ ≫
          factorThruImage (TopCat.Sheaf.finsetGeneratorMap {σ}) ≫
          TopCat.Sheaf.familyGeneratedSheafι
            (fun τ : {τ // τ ∈ ({σ} : Finset _)} => τ.1.1) (fun τ => τ.1.2) =
        Sigma.ι (fun τ : TopCat.Sheaf.SectionIndex Ksh => TopCat.Sheaf.zeroOutsideInt τ.1) σ ≫
          TopCat.Sheaf.allSectionMap Ksh
      rw [TopCat.Sheaf.familyGeneratedSheaf_ι_eq, Limits.image.fac]
      simp [TopCat.Sheaf.allSectionMap, TopCat.Sheaf.finsetGeneratorMap,
        TopCat.Sheaf.familyMap]
    haveI := TopCat.Sheaf.allSectionMap_epi Ksh
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
        (TopCat.Sheaf.SectionIndex (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)))
      [HasCoproduct fun σ : {σ // σ ∈ S} => TopCat.Sheaf.zeroOutsideInt σ.1.1],
      Subsingleton (Sheaf.H (TopCat.Sheaf.finsetGeneratedSheaf S) m)) :
    Subsingleton (Sheaf.H (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) m) := by
  have hZeroDiagram : IsZero (finsetGenFunctor hK ⋙ sheafCohomologyFunctor X m) := by
    refine Functor.isZero _ ?_
    intro S
    haveI : Subsingleton (Sheaf.H (TopCat.Sheaf.finsetGeneratedSheaf S) m) := hfg S
    simpa [finsetGenFunctor, sheafCohomologyFunctor_obj] using
      (AddCommGrpCat.isZero_of_subsingleton
        (AddCommGrpCat.of (Sheaf.H (TopCat.Sheaf.finsetGeneratedSheaf S) m)))
  have hZeroColim :
      IsZero (colimit (finsetGenFunctor hK ⋙ sheafCohomologyFunctor X m)) :=
    (colimit.isColimit _).isZero_pt hZeroDiagram
  have hZeroTarget :
      IsZero (AddCommGrpCat.of
        (Sheaf.H (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) m)) := by
    simpa [finsetGenCocone] using
      IsZero.of_iso hZeroColim
        (sheafH_preserves_filtered_colimits (finsetGenFunctor hK) (finsetGenCocone hK)
          (finsetGenCocone_isColimit hK) m).symm
  simpa using AddCommGrpCat.subsingleton_of_isZero hZeroTarget

section FinsetGenerated
open scoped Classical

variable {X : TopCat.{u}} {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf)
    {S' : Finset
      (TopCat.Sheaf.SectionIndex (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))}
    {σ₀ : TopCat.Sheaf.SectionIndex (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)}
    [HasCoproduct fun σ : {σ // σ ∈ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1]
    [HasCoproduct fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1]

/-- The `σ₀`-component maps epi onto the cokernel of `finsetImageInclGen`. -/
private theorem imageIncl_cokernel_epi :
    Epi (Sigma.ι (fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1)
      ⟨σ₀, Finset.mem_insert_self σ₀ S'⟩ ≫
      factorThruImage (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) ≫
      cokernel.π
        (finsetImageInclGen hK (Finset.subset_insert σ₀ S'))) := by
  let Ksh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨K, hK⟩
  let h_sub := Finset.subset_insert σ₀ S'
  let proj : (∐ fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1) ⟶
      TopCat.Sheaf.zeroOutsideInt σ₀.1 :=
    Sigma.desc fun σ =>
      if h : σ.1 = σ₀ then
        eqToHom (by rw [h])
      else 0
  have heq : finsetCoproductInclGen hK h_sub ≫
      factorThruImage (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) =
    factorThruImage (TopCat.Sheaf.finsetGeneratorMap S') ≫ finsetImageInclGen hK h_sub := by
    apply (cancel_mono (TopCat.Sheaf.familyGeneratedSheafι
      (fun σ : {σ // σ ∈ insert σ₀ S'} => σ.1.1) (fun σ => σ.1.2))).1
    rw [Category.assoc, TopCat.Sheaf.familyGeneratedSheaf_ι_eq, Limits.image.fac]
    have hlf : finsetImageInclGen hK h_sub ≫
        TopCat.Sheaf.familyGeneratedSheafι
          (fun σ : {σ // σ ∈ insert σ₀ S'} => σ.1.1) (fun σ => σ.1.2) =
        TopCat.Sheaf.familyGeneratedSheafι
          (fun σ : {σ // σ ∈ S'} => σ.1.1) (fun σ => σ.1.2) := by
      change finsetImageInclGen hK h_sub ≫
          Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) =
        Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap S')
      exact Limits.image.lift_fac _
    rw [Category.assoc, hlf, TopCat.Sheaf.familyGeneratedSheaf_ι_eq, Limits.image.fac]
    ext ⟨σ', hσ'⟩
    simp [finsetCoproductInclGen, TopCat.Sheaf.finsetGeneratorMap,
      TopCat.Sheaf.familyMap]
  have hfac : proj ≫
      (Sigma.ι (fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1)
        ⟨σ₀, Finset.mem_insert_self σ₀ S'⟩ ≫
      factorThruImage (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) ≫
      cokernel.π (finsetImageInclGen hK h_sub)) =
    factorThruImage (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) ≫
      cokernel.π (finsetImageInclGen hK h_sub) := by
    ext ⟨σ, hσ⟩
    simp only [proj]
    by_cases h : σ = σ₀
    · subst h; simp
    · rw [← Category.assoc
        (Sigma.ι (fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1) ⟨σ, hσ⟩)
        (Sigma.desc _)]
      rw [colimit.ι_desc, Cofan.mk_ι_app, dif_neg h, zero_comp]
      symm
      have hι : Sigma.ι (fun τ : {τ // τ ∈ S'} => TopCat.Sheaf.zeroOutsideInt τ.1.1)
          ⟨σ, Finset.mem_of_mem_insert_of_ne hσ h⟩ ≫
          finsetCoproductInclGen hK h_sub =
        Sigma.ι (fun τ : {τ // τ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt τ.1.1) ⟨σ, hσ⟩ := by
        simp [finsetCoproductInclGen]
      rw [← hι, Category.assoc, reassoc_of% heq]; simp [cokernel.condition]
  exact epi_of_epi_fac hfac

/-- **Step 3B–3C**: vanishing for `finsetGeneratedSheaf S` by `Finset.induction`. -/
theorem finsetGeneratedSheaf_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf)
    (m : ℕ)
    (hzero : ∀ {G : TopCat.Presheaf AddCommGrpCat.{u} X} (hG : G.IsSheaf) {V : Opens X}
      (f : TopCat.Sheaf.zeroOutsideInt V ⟶ (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)),
      Epi f → Subsingleton (Sheaf.H (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) m))
    (S : Finset
      (TopCat.Sheaf.SectionIndex (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)))
    [HasCoproduct fun σ : {σ // σ ∈ S} => TopCat.Sheaf.zeroOutsideInt σ.1.1] :
    Subsingleton (Sheaf.H (TopCat.Sheaf.finsetGeneratedSheaf S) m) := by
  let Ksh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨K, hK⟩
  suffices h : ∀ (T : Finset (TopCat.Sheaf.SectionIndex Ksh)),
      Subsingleton (Sheaf.H (TopCat.Sheaf.finsetGeneratedSheaf T) m) from by
    simpa [Ksh] using h S
  intro T; induction T using Finset.induction with
  | empty =>
    exact _root_.sheafH_subsingleton_of_isZero _ (by
      apply IsZero.of_iso (isZero_zero _) (imageZero' _)
      apply Sigma.hom_ext
      intro ⟨σ, hσ⟩
      simp at hσ) m
  | @insert σ₀ S' _ ih =>
    let h_sub := Finset.subset_insert σ₀ S'
    let SC := ShortComplex.mk (finsetImageInclGen hK h_sub)
      (cokernel.π (finsetImageInclGen hK h_sub)) (cokernel.condition _)
    have hSE : SC.ShortExact := ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (finsetImageInclGen hK h_sub)))
      inferInstance inferInstance
    have hCoker : Subsingleton (Sheaf.H SC.X₃ m) :=
      haveI := imageIncl_cokernel_epi (K := K) hK (σ₀ := σ₀) (S' := S')
      by
        simpa using hzero SC.X₃.cond
          (Sigma.ι (fun σ : {σ // σ ∈ insert σ₀ S'} =>
              TopCat.Sheaf.zeroOutsideInt σ.1.1) ⟨σ₀, Finset.mem_insert_self σ₀ S'⟩ ≫
            factorThruImage (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) ≫
            cokernel.π (finsetImageInclGen hK h_sub)) inferInstance
    exact subsingleton_sheafH_of_shortExact_middle hSE m ih hCoker

end FinsetGenerated

/-- **Step 3A** (Hartshorne III.2.7): on a Noetherian space, if vanishing holds for
    all epi images of `zeroOutsideInt V`, then it holds for every sheaf.
    Assembles `finsetGeneratedSheaf_vanishing` (finite case) with
    `cohomology_vanishing_of_finitelyGenerated_vanishing` (colimit step). -/
theorem directLimit_cohomology_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    {K : TopCat.Presheaf AddCommGrpCat.{u} X} (hK : K.IsSheaf) (m : ℕ)
    (hzero : ∀ {G : TopCat.Presheaf AddCommGrpCat.{u} X} (hG : G.IsSheaf) {V : Opens X}
      (f : TopCat.Sheaf.zeroOutsideInt V ⟶ (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)),
      Epi f → Subsingleton (Sheaf.H (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) m)) :
    Subsingleton (Sheaf.H (⟨K, hK⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) m) := by
  exact cohomology_vanishing_of_finitelyGenerated_vanishing hK m
    (fun S _ => finsetGeneratedSheaf_vanishing hK m hzero S)
