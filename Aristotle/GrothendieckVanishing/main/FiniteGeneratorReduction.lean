/-
  FiniteGeneratorReduction.lean — Colimit step and finitely generated vanishing

  Key results:
  - isSheaf_presheaf_filtered_colimit: presheaf-level filtered colimit of sheaves is a sheaf
    on Noetherian spaces (PROVED)
  - createsFilteredColimit: sheafToPresheaf creates filtered colimits (PROVED)
  - sheafH_filtered_colimit_aux / sheafH_preserves_filtered_colimits: H^n commutes with
    filtered colimits (1 sorry: hmono_ι — mono coprojections, true at call site)
  - finsetGenFunctor / finsetGenCocone / finsetGenCocone_isColimit: K is the filtered
    colimit of its finitely generated subsheaves (PROVED)
  - cohomology_vanishing_of_finitelyGenerated_vanishing: H^m = 0 for all f.g. subsheaves
    implies H^m(K) = 0 (PROVED via sheafH_preserves_filtered_colimits)
  - finsetGeneratedSheaf_vanishing: vanishing for finitely generated sheaves by
    Finset.induction (PROVED)
  - directLimit_cohomology_vanishing: from epi-image vanishing to all sheaves (PROVED)
-/
import Aristotle.GrothendieckVanishing.main.Setup
import Aristotle.GrothendieckVanishing.main.ZeroOutsideFinset

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

/-! ### Ext LES helper lemmas -/

section ExtHelpers
variable {C' : Type*} [Category C'] [Abelian C'] [HasExt C']

/-- Dimension shift for Ext via LES: given `0 → X₁ → X₂ → X₃ → 0` short exact,
    `Ext^n(Z, X₃) = 0` and `Ext^{n+1}(Z, X₂) = 0` imply `Ext^{n+1}(Z, X₁) = 0`. -/
private theorem ext_dimension_shift (Z : C') {S : ShortComplex C'} (hS : S.ShortExact) (n : ℕ)
    (h₃ : Subsingleton (Ext Z S.X₃ n))
    (h₂ : Subsingleton (Ext Z S.X₂ (n + 1))) :
    Subsingleton (Ext Z S.X₁ (n + 1)) := by
  constructor; intro a b
  have ha : a.comp (Ext.mk₀ S.f) rfl = 0 := @Subsingleton.elim _ h₂ _ _
  have hb : b.comp (Ext.mk₀ S.f) rfl = 0 := @Subsingleton.elim _ h₂ _ _
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ _ hS a ha rfl
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₁ _ hS b hb rfl
  rw [← hc, ← hd, @Subsingleton.elim _ h₃ c d]

/-- Reverse dimension shift: `Ext^n(Z, X₂) = 0` and `Ext^{n+1}(Z, X₁) = 0` imply
    `Ext^n(Z, X₃) = 0`. Uses exactness at X₃ in the covariant LES. -/
private theorem ext_dimension_shift_X₃ (Z : C') {S : ShortComplex C'} (hS : S.ShortExact) (n : ℕ)
    (h₂ : Subsingleton (Ext Z S.X₂ n))
    (h₁ : Subsingleton (Ext Z S.X₁ (n + 1))) :
    Subsingleton (Ext Z S.X₃ n) := by
  constructor; intro a b
  have ha : a.comp hS.extClass rfl = 0 := @Subsingleton.elim _ h₁ _ _
  have hb : b.comp hS.extClass rfl = 0 := @Subsingleton.elim _ h₁ _ _
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₃ _ hS a rfl ha
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₃ _ hS b rfl hb
  rw [← hc, ← hd, @Subsingleton.elim _ h₂ c d]

end ExtHelpers


/-! ### Filtered diagram of finitely generated subsheaves

We build a functor `Finset(SectionIndex K) ⥤ Sheaf(X)` sending each finite set `S`
of local sections to the subsheaf `finsetGeneratedSheaf S`. The transition maps
(for `S ⊆ S'`) are monomorphisms, and K is the colimit of this filtered diagram. -/

section FilteredDiagram
open scoped Classical

variable {X : TopCat.{u}} [NoetherianSpace X] (K : TopCat.Sheaf AddCommGrpCat.{u} X)

/-- Coproduct inclusion for general `S ⊆ S'`. -/
private noncomputable def finsetCoproductInclGen
    {S S' : Finset (TopCat.Sheaf.SectionIndex K)} (h : S ⊆ S') :
    (∐ fun σ : {σ // σ ∈ S} => TopCat.Sheaf.zeroOutsideInt σ.1.1) ⟶
    (∐ fun σ : {σ // σ ∈ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1) :=
  Sigma.desc fun σ =>
    Sigma.ι (fun τ : {τ // τ ∈ S'} => TopCat.Sheaf.zeroOutsideInt τ.1.1) ⟨σ.1, h σ.2⟩

/-- Image inclusion for general `S ⊆ S'`: `finsetGeneratedSheaf S ⟶ finsetGeneratedSheaf S'`. -/
private noncomputable def finsetImageInclGen
    {S S' : Finset (TopCat.Sheaf.SectionIndex K)} (h : S ⊆ S') :
    TopCat.Sheaf.finsetGeneratedSheaf S ⟶ TopCat.Sheaf.finsetGeneratedSheaf S' :=
  Limits.image.lift
    { I := TopCat.Sheaf.finsetGeneratedSheaf S'
      m := Limits.image.ι _
      e := finsetCoproductInclGen K h ≫ factorThruImage (TopCat.Sheaf.finsetGeneratorMap S')
      fac := by
        rw [Category.assoc, Limits.image.fac]
        ext ⟨σ, hσ⟩
        simp [finsetCoproductInclGen, TopCat.Sheaf.finsetGeneratorMap,
              TopCat.Sheaf.familyGeneratorMap] }

omit [NoetherianSpace X] in
private lemma finsetImageInclGen_comp_ι
    {S S' : Finset (TopCat.Sheaf.SectionIndex K)} (h : S ⊆ S') :
    finsetImageInclGen K h ≫ Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap S') =
      Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap S) :=
  Limits.image.lift_fac _

private instance finsetImageInclGen_mono
    {S S' : Finset (TopCat.Sheaf.SectionIndex K)} (h : S ⊆ S') :
    Mono (finsetImageInclGen K h) :=
  mono_of_mono_fac (finsetImageInclGen_comp_ι K h)

/-- The functor `Finset(SectionIndex K) ⥤ Sheaf(X)` sending `S ↦ finsetGeneratedSheaf S`.
    Transition maps are the canonical image inclusions, which are monomorphisms. -/
private noncomputable def finsetGenFunctor :
    Finset (TopCat.Sheaf.SectionIndex K) ⥤ TopCat.Sheaf AddCommGrpCat.{u} X where
  obj S := TopCat.Sheaf.finsetGeneratedSheaf S
  map h := finsetImageInclGen K h.le
  map_id S := by
    apply (cancel_mono (Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap S))).1
    rw [finsetImageInclGen_comp_ι, Category.id_comp]
  map_comp {S₁ S₂ S₃} h₁ h₂ := by
    apply (cancel_mono (Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap S₃))).1
    rw [Category.assoc, finsetImageInclGen_comp_ι, finsetImageInclGen_comp_ι,
        finsetImageInclGen_comp_ι]

/-- Cocone with vertex `K`: the cocone maps are `image.ι : finsetGeneratedSheaf S ⟶ K`. -/
private noncomputable def finsetGenCocone :
    Cocone (finsetGenFunctor K) :=
  Cocone.mk K
    { app := fun S => Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap S)
      naturality := fun S S' h => by
        dsimp [finsetGenFunctor]
        rw [finsetImageInclGen_comp_ι, Category.comp_id] }

/-- The cocone is a colimit: `K` is the filtered colimit of its finitely generated subsheaves.
    Proof: the canonical map `colim → K` is mono (by AB5 + mono transitions) and epi
    (since `allSectionMap K` factors through it), hence an isomorphism. -/
private noncomputable def finsetGenCocone_isColimit :
    IsColimit (finsetGenCocone K) := by
  -- Show the comparison map colim → K is an iso, then transport IsColimit
  let d := colimit.desc (finsetGenFunctor K) (finsetGenCocone K)
  -- desc is mono: natural transformation to const K has all components mono (image.ι),
  -- and in a Grothendieck abelian category filtered colimits preserve monos
  have hd_mono : Mono d := by
    haveI : IsConnected (Finset (TopCat.Sheaf.SectionIndex K)) := IsFiltered.isConnected _
    let α : finsetGenFunctor K ⟶ (Functor.const _).obj K :=
      { app := fun S => Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap S)
        naturality := fun S S' h => by
          dsimp [finsetGenFunctor]
          rw [finsetImageInclGen_comp_ι, Category.comp_id] }
    haveI : ∀ j, Mono (α.app j) := fun _ => inferInstance
    haveI := NatTrans.mono_of_mono_app α
    exact colim.map_mono' α (colimit.isColimit _) (isColimitConstCocone _ _) d
      (fun j => by simp [d, α, finsetGenCocone, constCocone])
  -- desc is epi: allSectionMap K factors through desc
  have hd_epi : Epi d := by
    let g : (∐ fun σ : TopCat.Sheaf.SectionIndex K => TopCat.Sheaf.zeroOutsideInt σ.1) ⟶
        colimit (finsetGenFunctor K) :=
      Sigma.desc fun σ =>
        Sigma.ι (fun τ : {τ // τ ∈ ({σ} : Finset _)} =>
            TopCat.Sheaf.zeroOutsideInt τ.1.1) ⟨σ, Finset.mem_singleton_self σ⟩ ≫
          factorThruImage (TopCat.Sheaf.finsetGeneratorMap {σ}) ≫
          colimit.ι (finsetGenFunctor K) {σ}
    have hfac : g ≫ d = TopCat.Sheaf.allSectionMap K := by
      dsimp only [g, d]
      apply Sigma.hom_ext; intro σ
      simp only [← Category.assoc, Sigma.ι_desc]
      simp only [Category.assoc, colimit.ι_desc]
      dsimp [finsetGenCocone]
      rw [Limits.image.fac]
      simp [TopCat.Sheaf.finsetGeneratorMap, TopCat.Sheaf.familyGeneratorMap,
            TopCat.Sheaf.allSectionMap]
    haveI := TopCat.Sheaf.allSectionMap_epi K
    exact epi_of_epi_fac hfac
  -- mono + epi → iso in abelian category
  haveI := hd_mono; haveI := hd_epi
  haveI : IsIso ((colimit.isColimit (finsetGenFunctor K)).desc (finsetGenCocone K)) :=
    isIso_of_mono_of_epi d
  exact (colimit.isColimit (finsetGenFunctor K)).ofPointIso

instance finsetGenFunctor_mono
    (j j' : Finset (TopCat.Sheaf.SectionIndex K))
    (φ : j ⟶ j') : Mono ((finsetGenFunctor K).map φ) :=
  finsetImageInclGen_mono K φ.le

end FilteredDiagram

/-- A section of a sheaf that restricts to 0 on a finite open cover is 0. -/
private theorem sheaf_section_zero_of_zero_on_finite_cover
    {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    {ι : Type u} (U : ι → Opens X) (t : Finset ι) (hcov : iSup U ≤ ⨆ i ∈ t, U i)
    (b : ToType (F.val.obj (op (iSup U))))
    (hzero : ∀ k ∈ t, ConcreteCategory.hom (F.val.map (Opens.leSupr U k).op) b = 0) :
    b = 0 := by
  have hFS : TopCat.Presheaf.IsSheaf F.val := F.cond
  exact hFS.section_ext (s := b) (t := 0) fun x hx => by
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (hcov hx)
    obtain ⟨hkt, hxk⟩ := Opens.mem_iSup.mp hk
    exact ⟨U k, le_iSup U k, hxk, (hzero k hkt).trans (map_zero _).symm⟩

/-- Merge finitely many eventually-zero transitions into one. -/
private theorem filtered_colimit_kills_all_restrictions
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    {X : TopCat.{u}} (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    {ι : Type u} (U : ι → Opens X) (j₀ : J')
    (b₀ : ToType ((Y'.obj j₀).val.obj (op (iSup U))))
    (t : Finset ι)
    (h_ev : ∀ k ∈ t, ∃ (jk : J') (fk : j₀ ⟶ jk),
      ConcreteCategory.hom ((Y'.obj jk).val.map (Opens.leSupr U k).op)
        (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map fk).app (op (iSup U))) b₀) = 0) :
    ∃ (j₁ : J') (g₀ : j₀ ⟶ j₁),
      ∀ k ∈ t, ConcreteCategory.hom ((Y'.obj j₁).val.map (Opens.leSupr U k).op)
        (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map g₀).app (op (iSup U))) b₀) = 0 := by
  classical
  induction t using Finset.induction with
  | empty => exact ⟨j₀, 𝟙 j₀, fun _ hk => absurd hk (by simp)⟩
  | @insert k₀ t₀ hk₀ ih =>
    obtain ⟨j_cur, g_cur, hg_cur⟩ := ih (fun k hk => h_ev k (Finset.mem_insert_of_mem hk))
    obtain ⟨jk₀, fk₀, hfk₀⟩ := h_ev k₀ (Finset.mem_insert_self k₀ t₀)
    let j₁ := IsFiltered.coeq (g_cur ≫ IsFiltered.leftToMax j_cur jk₀)
        (fk₀ ≫ IsFiltered.rightToMax j_cur jk₀)
    let h_eq := IsFiltered.coeqHom (g_cur ≫ IsFiltered.leftToMax j_cur jk₀)
        (fk₀ ≫ IsFiltered.rightToMax j_cur jk₀)
    have heq : g_cur ≫ IsFiltered.leftToMax j_cur jk₀ ≫ h_eq =
        fk₀ ≫ IsFiltered.rightToMax j_cur jk₀ ≫ h_eq := by
      have := IsFiltered.coeq_condition (g_cur ≫ IsFiltered.leftToMax j_cur jk₀)
        (fk₀ ≫ IsFiltered.rightToMax j_cur jk₀)
      simp only [Category.assoc] at this; exact this
    refine ⟨j₁, g_cur ≫ IsFiltered.leftToMax j_cur jk₀ ≫ h_eq, fun k hk => ?_⟩
    have htrans : ∀ {j j' : J'} (f : j₀ ⟶ j) (g : j ⟶ j') (k' : ι),
        ConcreteCategory.hom ((Y'.obj j).val.map (Opens.leSupr U k').op)
          (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map f).app (op (iSup U))) b₀) = 0 →
        ConcreteCategory.hom ((Y'.obj j').val.map (Opens.leSupr U k').op)
          (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map (f ≫ g)).app
            (op (iSup U))) b₀) = 0 := by
      intro j j' f g k' hfk
      let α := ((Y' ⋙ sheafToPresheaf _ _).map g)
      have hnat := α.naturality (Opens.leSupr U k').op
      change ConcreteCategory.hom
        (((Y' ⋙ sheafToPresheaf _ _).map (f ≫ g)).app (op (iSup U)) ≫
          (Y'.obj j').val.map (Opens.leSupr U k').op) b₀ = 0
      rw [(Y' ⋙ sheafToPresheaf _ _).map_comp, NatTrans.comp_app, Category.assoc,
        show α.app (op (iSup U)) ≫ (Y'.obj j').val.map (Opens.leSupr U k').op =
          (Y'.obj j).val.map (Opens.leSupr U k').op ≫ α.app (op (U k')) from hnat.symm,
        ← Category.assoc]
      show ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map f).app (op (iSup U)) ≫
        (Y'.obj j).val.map (Opens.leSupr U k').op ≫ α.app (op (U k'))) b₀ = 0
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply]
      change ConcreteCategory.hom (α.app (op (U k')))
        (ConcreteCategory.hom ((Y'.obj j).val.map (Opens.leSupr U k').op)
          (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map f).app (op (iSup U))) b₀)) = 0
      rw [hfk, map_zero]
    rw [Finset.mem_insert] at hk; rcases hk with rfl | hk
    · rw [heq]; exact htrans fk₀ (IsFiltered.rightToMax j_cur jk₀ ≫ h_eq) k hfk₀
    · exact htrans g_cur (IsFiltered.leftToMax j_cur jk₀ ≫ h_eq) k (hg_cur k hk)

/-- On a Noetherian space, the presheaf-level filtered colimit of sheaves is a sheaf.
    The sheaf category has filtered colimits and `sheafToPresheaf` preserves them,
    so the presheaf colimit is isomorphic to the presheaf underlying the sheaf colimit. -/
private theorem isSheaf_presheaf_filtered_colimit
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (c : Cocone (Y' ⋙ sheafToPresheaf _ _)) (hc : IsColimit c) :
    TopCat.Presheaf.IsSheaf c.pt := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hcompat
  -- Noetherian → finite subcover
  obtain ⟨t, ht⟩ := (NoetherianSpace.isCompact (↑(iSup U) : Set X)).elim_finite_subcover
    (fun i => ↑(U i)) (fun i => (U i).isOpen) (by simp [Opens.coe_iSup])
  have hsup_le : iSup U ≤ ⨆ i ∈ t, U i := by
    rw [SetLike.le_def]; intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Opens.mem_iSup.mpr ⟨i, Opens.mem_iSup.mpr ⟨hi, hxi⟩⟩
  -- Setup: evaluation colimits
  let ev V := (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V)
  have hcV : ∀ V, IsColimit ((ev V).mapCocone c) := fun V => isColimitOfPreserves (ev V) hc
  -- Separation: section zero on finite subcover is zero
  have hsep : ∀ (a : ToType (c.pt.obj (op (iSup U)))),
      (∀ k ∈ t, c.pt.map (Opens.leSupr U k).op a = 0) → a = 0 := by
    intro a ha
    obtain ⟨j₀, b₀, hb₀⟩ := Concrete.isColimit_exists_rep _ (hcV (iSup U)) a
    -- For each k: ι(b₀|_{Uk}) = a|_{Uk} = 0, so eventually zero
    let F_k k := (Y' ⋙ sheafToPresheaf _ _) ⋙ ev (U k)
    have h_ev_zero : ∀ k ∈ t, ∃ (jk : J') (fk : j₀ ⟶ jk),
        ConcreteCategory.hom ((F_k k).map fk)
          (ConcreteCategory.hom ((Y'.obj j₀).val.map (Opens.leSupr U k).op) b₀) = 0 := by
      intro k hk
      have hcTyp := isColimitOfPreserves (CategoryTheory.forget AddCommGrpCat) (hcV (U k))
      have hnat_k : ConcreteCategory.hom (((ev (U k)).mapCocone c).ι.app j₀)
          (ConcreteCategory.hom ((Y'.obj j₀).val.map (Opens.leSupr U k).op) b₀) =
        ConcreteCategory.hom (c.pt.map (Opens.leSupr U k).op) a := by
        simp only [Functor.mapCocone_ι_app]; rw [← hb₀]
        change ConcreteCategory.hom
          (((Y' ⋙ sheafToPresheaf _ _).obj j₀).map _ ≫ (c.ι.app j₀).app _) b₀ =
          ConcreteCategory.hom
          ((c.ι.app j₀).app _ ≫ (((Functor.const J').obj c.pt).obj j₀).map _) b₀
        rw [(c.ι.app j₀).naturality (Opens.leSupr U k).op]
      have hres_zero : ConcreteCategory.hom (((ev (U k)).mapCocone c).ι.app j₀)
          (ConcreteCategory.hom ((Y'.obj j₀).val.map (Opens.leSupr U k).op) b₀) = 0 :=
        hnat_k.trans (ha k hk)
      have h0 : ((CategoryTheory.forget AddCommGrpCat).mapCocone
          ((ev (U k)).mapCocone c)).ι.app j₀
          (ConcreteCategory.hom ((Y'.obj j₀).val.map (Opens.leSupr U k).op) b₀) =
        ((CategoryTheory.forget AddCommGrpCat).mapCocone
          ((ev (U k)).mapCocone c)).ι.app j₀ 0 := by
        change ConcreteCategory.hom (((ev (U k)).mapCocone c).ι.app j₀) _ =
          ConcreteCategory.hom (((ev (U k)).mapCocone c).ι.app j₀) 0
        rw [hres_zero, map_zero]
      rw [Types.FilteredColimit.isColimit_eq_iff' hcTyp] at h0
      obtain ⟨jk, fk, hfk⟩ := h0
      exact ⟨jk, fk, by simpa [map_zero] using hfk⟩
    -- Convert to transition-then-restrict form
    have h_ev' : ∀ k ∈ t, ∃ (jk : J') (fk : j₀ ⟶ jk),
        ConcreteCategory.hom ((Y'.obj jk).val.map (Opens.leSupr U k).op)
          (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map fk).app (op (iSup U))) b₀) = 0 := by
      intro k hk; obtain ⟨jk, fk, hfk⟩ := h_ev_zero k hk; refine ⟨jk, fk, ?_⟩
      have hnat' := ((Y' ⋙ sheafToPresheaf _ _).map fk).naturality (Opens.leSupr U k).op
      change ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map fk).app (op (iSup U)) ≫
        ((Y' ⋙ sheafToPresheaf _ _).obj jk).map (Opens.leSupr U k).op) b₀ = 0
      rw [← hnat']; exact hfk
    -- Merge via filtered_colimit_kills_all_restrictions
    obtain ⟨j₁, g₀, hg₀⟩ := filtered_colimit_kills_all_restrictions Y' U j₀ b₀ t h_ev'
    let b₁ := ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map g₀).app (op (iSup U))) b₀
    have hb₁_zero : b₁ = 0 :=
      sheaf_section_zero_of_zero_on_finite_cover (Y'.obj j₁) U t hsup_le b₁ hg₀
    rw [← hb₀]; change ConcreteCategory.hom ((c.ι.app j₀).app (op (iSup U))) b₀ = 0
    have hfac : (c.ι.app j₀).app (op (iSup U)) =
        ((Y' ⋙ sheafToPresheaf _ _).map g₀).app (op (iSup U)) ≫
        (c.ι.app j₁).app (op (iSup U)) := by
      have := congrArg (fun α => NatTrans.app α (op (iSup U))) (c.ι.naturality g₀)
      simp [Functor.const_obj_map] at this; exact this.symm
    conv_lhs => rw [hfac]
    change ConcreteCategory.hom ((c.ι.app j₁).app (op (iSup U))) b₁ = 0
    rw [hb₁_zero, map_zero]
  -- Existence: construct a gluing section
  classical
  choose j_all x_all hx_all using fun k =>
    Concrete.isColimit_exists_rep _ (hcV (U k)) (sf k)
  -- Merge j_all k (k ∈ t) to common index
  haveI : DecidableEq J' := Classical.decEq _
  obtain ⟨j₀, hj₀⟩ := IsFiltered.sup_objs_exists (t.image j_all)
  let g₀ : ∀ k, k ∈ t → (j_all k ⟶ j₀) :=
    fun k hk => (hj₀ (Finset.mem_image_of_mem j_all hk)).some
  -- Transport to j₀
  let x' : ∀ k, k ∈ t → ToType ((Y'.obj j₀).val.obj (op (U k))) :=
    fun k hk => ConcreteCategory.hom
      (((Y' ⋙ sheafToPresheaf _ _).map (g₀ k hk)).app (op (U k))) (x_all k)
  -- x' still maps to sf_k in the colimit
  have hx' : ∀ k (hk : k ∈ t),
      ConcreteCategory.hom (((ev (U k)).mapCocone c).ι.app j₀) (x' k hk) = sf k := by
    intro k hk; dsimp [x']
    have hfac := congrArg (fun α => NatTrans.app α (op (U k))) (c.ι.naturality (g₀ k hk))
    simp only [Functor.const_obj_map, NatTrans.comp_app, Category.comp_id] at hfac
    change ConcreteCategory.hom ((((Y' ⋙ sheafToPresheaf _ _).map (g₀ k hk)).app (op (U k))) ≫
      (c.ι.app j₀).app (op (U k))) (x_all k) = sf k
    rw [hfac]; exact hx_all k
  -- Pairwise compatibility after merging via IsFiltered
  obtain ⟨j₁, g₁, hg₁⟩ : ∃ (j₁ : J') (g₁ : j₀ ⟶ j₁),
      ∀ (k : ι) (hk : k ∈ t) (l : ι) (hl : l ∈ t),
        ConcreteCategory.hom ((Y'.obj j₁).val.map (Opens.infLELeft (U k) (U l)).op)
          (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map g₁).app (op (U k))) (x' k hk)) =
        ConcreteCategory.hom ((Y'.obj j₁).val.map (Opens.infLERight (U k) (U l)).op)
          (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map g₁).app (op (U l))) (x' l hl)) := by
    -- Step 1: each pair is eventually compatible
    have h_ev_compat : ∀ (k : ι) (hk : k ∈ t) (l : ι) (hl : l ∈ t),
        ∃ (j' : J') (f : j₀ ⟶ j'),
        ConcreteCategory.hom ((Y'.obj j').val.map (Opens.infLELeft (U k) (U l)).op)
          (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map f).app (op (U k))) (x' k hk)) =
        ConcreteCategory.hom ((Y'.obj j').val.map (Opens.infLERight (U k) (U l)).op)
          (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map f).app (op (U l))) (x' l hl)) := by
      intro k hk l hl
      have hcTyp := isColimitOfPreserves (CategoryTheory.forget AddCommGrpCat) (hcV (U k ⊓ U l))
      -- Both sides equal in colimit (by naturality + hcompat)
      have h_eq : ((CategoryTheory.forget AddCommGrpCat).mapCocone
          ((ev (U k ⊓ U l)).mapCocone c)).ι.app j₀
          (ConcreteCategory.hom ((Y'.obj j₀).val.map (Opens.infLELeft (U k) (U l)).op) (x' k hk)) =
        ((CategoryTheory.forget AddCommGrpCat).mapCocone
          ((ev (U k ⊓ U l)).mapCocone c)).ι.app j₀
          (ConcreteCategory.hom ((Y'.obj j₀).val.map (Opens.infLERight (U k) (U l)).op) (x' l hl)) := by
        change ConcreteCategory.hom (((ev (U k ⊓ U l)).mapCocone c).ι.app j₀) _ =
          ConcreteCategory.hom (((ev (U k ⊓ U l)).mapCocone c).ι.app j₀) _
        have hnat_m : ∀ (m : ι) (hm : m ∈ t) (φ : U k ⊓ U l ⟶ U m),
            ConcreteCategory.hom (((ev (U k ⊓ U l)).mapCocone c).ι.app j₀)
              (ConcreteCategory.hom ((Y'.obj j₀).val.map φ.op) (x' m hm)) =
            ConcreteCategory.hom (c.pt.map φ.op) (sf m) := by
          intro m hm φ; simp only [Functor.mapCocone_ι_app]; rw [← hx' m hm]
          change ConcreteCategory.hom
            (((Y' ⋙ sheafToPresheaf _ _).obj j₀).map _ ≫ (c.ι.app j₀).app _) (x' m hm) =
            ConcreteCategory.hom
            ((c.ι.app j₀).app _ ≫ (((Functor.const J').obj c.pt).obj j₀).map _) (x' m hm)
          rw [(c.ι.app j₀).naturality φ.op]
        rw [hnat_m k hk (Opens.infLELeft (U k) (U l)),
            hnat_m l hl (Opens.infLERight (U k) (U l))]
        exact hcompat k l
      -- Eventually equal
      rw [Types.FilteredColimit.isColimit_eq_iff' hcTyp] at h_eq
      obtain ⟨j', f, hf⟩ := h_eq
      refine ⟨j', f, ?_⟩
      -- Convert via naturality
      let α := (Y' ⋙ sheafToPresheaf _ _).map f
      change ConcreteCategory.hom
        (α.app (op (U k)) ≫ (Y'.obj j').val.map (Opens.infLELeft (U k) (U l)).op) (x' k hk) =
        ConcreteCategory.hom
        (α.app (op (U l)) ≫ (Y'.obj j').val.map (Opens.infLERight (U k) (U l)).op) (x' l hl)
      rw [show α.app (op (U k)) ≫ (Y'.obj j').val.map (Opens.infLELeft (U k) (U l)).op =
        (Y'.obj j₀).val.map (Opens.infLELeft (U k) (U l)).op ≫ α.app (op (U k ⊓ U l))
        from (α.naturality (Opens.infLELeft (U k) (U l)).op).symm,
        show α.app (op (U l)) ≫ (Y'.obj j').val.map (Opens.infLERight (U k) (U l)).op =
        (Y'.obj j₀).val.map (Opens.infLERight (U k) (U l)).op ≫ α.app (op (U k ⊓ U l))
        from (α.naturality (Opens.infLERight (U k) (U l)).op).symm]
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply]
      exact hf
    -- Step 2: merge via Finset.induction on t ×ˢ t
    haveI : DecidableEq ι := Classical.decEq _
    suffices h : ∀ (S : Finset (ι × ι)) (hS : S ⊆ t ×ˢ t),
        ∃ (j₁ : J') (g₁ : j₀ ⟶ j₁), ∀ (p : ι × ι) (hp : p ∈ S),
          ConcreteCategory.hom ((Y'.obj j₁).val.map (Opens.infLELeft (U p.1) (U p.2)).op)
            (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map g₁).app (op (U p.1)))
              (x' p.1 ((Finset.mem_product.mp (hS hp)).1))) =
          ConcreteCategory.hom ((Y'.obj j₁).val.map (Opens.infLERight (U p.1) (U p.2)).op)
            (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map g₁).app (op (U p.2)))
              (x' p.2 ((Finset.mem_product.mp (hS hp)).2))) by
      obtain ⟨j₁, g₁, hg₁⟩ := h (t ×ˢ t) (fun _ hx => hx)
      exact ⟨j₁, g₁, fun k hk l hl =>
        hg₁ (k, l) (Finset.mem_product.mpr ⟨hk, hl⟩)⟩
    intro S hS
    induction S using Finset.induction with
    | empty => exact ⟨j₀, 𝟙 j₀, fun _ hp => absurd hp (by simp)⟩
    | @insert p₀ rest hnin ih =>
      obtain ⟨j_cur, g_cur, hg_cur⟩ := ih (fun p hp => hS (Finset.mem_insert_of_mem hp))
      have hp₀t := hS (Finset.mem_insert_self p₀ rest)
      obtain ⟨j_new, f_new, hf_new⟩ := h_ev_compat p₀.1
        (Finset.mem_product.mp hp₀t).1 p₀.2 (Finset.mem_product.mp hp₀t).2
      -- Merge via IsFiltered.coeq
      refine ⟨IsFiltered.coeq (g_cur ≫ IsFiltered.leftToMax j_cur j_new)
          (f_new ≫ IsFiltered.rightToMax j_cur j_new),
        g_cur ≫ IsFiltered.leftToMax j_cur j_new ≫
          IsFiltered.coeqHom (g_cur ≫ IsFiltered.leftToMax j_cur j_new)
            (f_new ≫ IsFiltered.rightToMax j_cur j_new),
        fun p hp => ?_⟩
      -- htrans_compat: compat preserved under further transition
      let h_coeq := IsFiltered.coeqHom (g_cur ≫ IsFiltered.leftToMax j_cur j_new)
          (f_new ≫ IsFiltered.rightToMax j_cur j_new)
      have htrans : ∀ {j j' : J'} (f : j₀ ⟶ j) (g : j ⟶ j') (k₁ : ι) (hk₁ : k₁ ∈ t)
          (l₁ : ι) (hl₁ : l₁ ∈ t),
          ConcreteCategory.hom ((Y'.obj j).val.map (Opens.infLELeft (U k₁) (U l₁)).op)
            (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map f).app (op (U k₁))) (x' k₁ hk₁)) =
          ConcreteCategory.hom ((Y'.obj j).val.map (Opens.infLERight (U k₁) (U l₁)).op)
            (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map f).app (op (U l₁))) (x' l₁ hl₁)) →
          ConcreteCategory.hom ((Y'.obj j').val.map (Opens.infLELeft (U k₁) (U l₁)).op)
            (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map (f ≫ g)).app (op (U k₁))) (x' k₁ hk₁)) =
          ConcreteCategory.hom ((Y'.obj j').val.map (Opens.infLERight (U k₁) (U l₁)).op)
            (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map (f ≫ g)).app (op (U l₁))) (x' l₁ hl₁)) := by
        intro j j' f g k₁ hk₁ l₁ hl₁ hfkl
        let β := (Y' ⋙ sheafToPresheaf _ _).map g
        suffices ∀ (m : ι) (hm : m ∈ t) (φ : U k₁ ⊓ U l₁ ⟶ U m),
            ConcreteCategory.hom ((Y'.obj j').val.map φ.op)
              (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map (f ≫ g)).app (op (U m))) (x' m hm)) =
            ConcreteCategory.hom (β.app (op (U k₁ ⊓ U l₁)))
              (ConcreteCategory.hom ((Y'.obj j).val.map φ.op)
                (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map f).app (op (U m))) (x' m hm))) by
          rw [this k₁ hk₁ (Opens.infLELeft (U k₁) (U l₁)),
              this l₁ hl₁ (Opens.infLERight (U k₁) (U l₁)), hfkl]
        intro m hm φ
        -- F(f ≫ g) = F(f) ≫ β, then naturality: β(Um) ≫ res = res ≫ β(Ukl)
        simp only [Functor.map_comp, NatTrans.comp_app,
          AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply]
        -- Goal: res_j'(β(Um)(F(f)(x'))) = β(Ukl)(res_j(F(f)(x')))
        change ConcreteCategory.hom (β.app (op (U m)) ≫ (Y'.obj j').val.map φ.op) _ =
          ConcreteCategory.hom ((Y'.obj j).val.map φ.op ≫ β.app (op (U k₁ ⊓ U l₁))) _
        rw [show β.app (op (U m)) ≫ (Y'.obj j').val.map φ.op =
          (Y'.obj j).val.map φ.op ≫ β.app (op (U k₁ ⊓ U l₁))
          from (β.naturality φ.op).symm]; rfl
      -- Apply htrans to each case
      rw [Finset.mem_insert] at hp; rcases hp with rfl | hp
      · -- p = p₀: use coeq condition to equate transitions
        have heq : g_cur ≫ IsFiltered.leftToMax j_cur j_new ≫ h_coeq =
            f_new ≫ IsFiltered.rightToMax j_cur j_new ≫ h_coeq := by
          have := IsFiltered.coeq_condition (g_cur ≫ IsFiltered.leftToMax j_cur j_new)
            (f_new ≫ IsFiltered.rightToMax j_cur j_new)
          simp only [Category.assoc] at this; exact this
        rw [heq]
        exact htrans f_new (IsFiltered.rightToMax j_cur j_new ≫ h_coeq)
          _ ((Finset.mem_product.mp hp₀t).1)
          _ ((Finset.mem_product.mp hp₀t).2)
          hf_new
      · -- p ∈ rest: use hg_cur + transition
        exact htrans g_cur (IsFiltered.leftToMax j_cur j_new ≫ h_coeq)
          p.1 ((Finset.mem_product.mp (hS (Finset.mem_insert_of_mem hp))).1)
          p.2 ((Finset.mem_product.mp (hS (Finset.mem_insert_of_mem hp))).2)
          (hg_cur p hp)
  -- Glue in piece
  let W : ↥t → Opens X := fun ⟨k, _⟩ => U k
  let x'' : ∀ (k : ↥t), ToType ((Y'.obj j₁).val.obj (op (W k))) :=
    fun ⟨k, hk⟩ => ConcreteCategory.hom
      (((Y' ⋙ sheafToPresheaf _ _).map g₁).app (op (U k))) (x' k hk)
  have hx''_compat : Presheaf.IsCompatible (Y'.obj j₁).val W x'' :=
    fun ⟨k, hk⟩ ⟨l, hl⟩ => hg₁ k hk l hl
  have hcov_W : iSup U ≤ iSup W := by
    rw [show iSup W = ⨆ k ∈ t, U k from iSup_subtype (p := (· ∈ t))]; exact hsup_le
  obtain ⟨s₀, hs₀, _⟩ := (Y'.obj j₁).existsUnique_gluing' W (iSup U)
    (fun ⟨k, _⟩ => Opens.leSupr U k) hcov_W x'' hx''_compat
  -- Map to colimit
  let s : ToType (c.pt.obj (op (iSup U))) :=
    ConcreteCategory.hom ((c.ι.app j₁).app (op (iSup U))) s₀
  -- For k ∈ t: s|_{U_k} = sf_k
  have hs_k : ∀ k (hk : k ∈ t), c.pt.map (Opens.leSupr U k).op s = sf k := by
    intro k hk
    change ConcreteCategory.hom (c.pt.map (Opens.leSupr U k).op)
      (ConcreteCategory.hom ((c.ι.app j₁).app (op (iSup U))) s₀) = sf k
    change ConcreteCategory.hom
      ((c.ι.app j₁).app (op (iSup U)) ≫ c.pt.map (Opens.leSupr U k).op) s₀ = sf k
    rw [show (c.ι.app j₁).app (op (iSup U)) ≫ c.pt.map (Opens.leSupr U k).op =
      (Y'.obj j₁).val.map (Opens.leSupr U k).op ≫ (c.ι.app j₁).app (op (U k))
      from ((c.ι.app j₁).naturality (Opens.leSupr U k).op).symm]
    change ConcreteCategory.hom ((c.ι.app j₁).app (op (U k)))
      (ConcreteCategory.hom ((Y'.obj j₁).val.map (Opens.leSupr U k).op) s₀) = sf k
    rw [hs₀ ⟨k, hk⟩]; dsimp [x'']
    have hfac := congrArg (fun α => NatTrans.app α (op (U k))) (c.ι.naturality g₁)
    simp only [Functor.const_obj_map, NatTrans.comp_app, Category.comp_id] at hfac
    change ConcreteCategory.hom ((((Y' ⋙ sheafToPresheaf _ _).map g₁).app (op (U k)) ≫
      (c.ι.app j₁).app (op (U k)))) (x' k hk) = sf k
    rw [hfac]; exact hx' k hk
  -- For all i: s|_{U_i} = sf_i (by separation at U_i via hcompat)
  refine ⟨s, fun i => ?_, fun s' hs' => ?_⟩
  · -- s|_{U_i} = sf_i: show difference is 0 by checking on finite subcover of U_i
    have h_diff_zero : ∀ k ∈ t,
        ConcreteCategory.hom (c.pt.map (homOfLE (inf_le_left : U i ⊓ U k ≤ U i)).op)
          (c.pt.map (Opens.leSupr U i).op s - sf i) = 0 := by
      intro k hk; rw [map_sub, sub_eq_zero]
      -- LHS = s|_{U_i ⊓ U_k} = s|_{U_k}|_{U_i ⊓ U_k} = sf_k|_{U_i ⊓ U_k}
      -- RHS = sf_i|_{U_i ⊓ U_k} = sf_k|_{U_i ⊓ U_k} (by hcompat)
      trans (ConcreteCategory.hom (c.pt.map (Opens.infLERight (U i) (U k)).op) (sf k))
      · rw [← hs_k k hk, ← ConcreteCategory.comp_apply, ← c.pt.map_comp,
            ← ConcreteCategory.comp_apply, ← c.pt.map_comp]; congr 1
      · exact (hcompat i k).symm
    -- Colimit separation at U_i: d := s|_{U_i} - sf_i restricts to 0, hence = 0
    -- This is the SAME argument as hsep but at U_i with cover {U_i ⊓ U_k | k ∈ t}
    apply sub_eq_zero.mp
    obtain ⟨j₂, d₀, hd₀⟩ := Concrete.isColimit_exists_rep _ (hcV (U i))
      (c.pt.map (Opens.leSupr U i).op s - sf i)
    -- Eventually zero for each k: naturality + h_diff_zero + isColimit_eq_iff'
    have h_ev_d : ∀ k ∈ t, ∃ (jk : J') (fk : j₂ ⟶ jk),
        ConcreteCategory.hom ((Y'.obj jk).val.map (homOfLE (inf_le_left : U i ⊓ U k ≤ U i)).op)
          (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map fk).app (op (U i))) d₀) = 0 := by
      intro k hk
      have hcTyp := isColimitOfPreserves (CategoryTheory.forget AddCommGrpCat) (hcV (U i ⊓ U k))
      have hnat_d : ConcreteCategory.hom (((ev (U i ⊓ U k)).mapCocone c).ι.app j₂)
          (ConcreteCategory.hom ((Y'.obj j₂).val.map (homOfLE (inf_le_left : U i ⊓ U k ≤ U i)).op) d₀) =
        ConcreteCategory.hom (c.pt.map (homOfLE (inf_le_left : U i ⊓ U k ≤ U i)).op)
          (c.pt.map (Opens.leSupr U i).op s - sf i) := by
        simp only [Functor.mapCocone_ι_app]; rw [← hd₀]
        change ConcreteCategory.hom
          (((Y' ⋙ sheafToPresheaf _ _).obj j₂).map _ ≫ (c.ι.app j₂).app _) d₀ =
          ConcreteCategory.hom
          ((c.ι.app j₂).app _ ≫ (((Functor.const J').obj c.pt).obj j₂).map _) d₀
        rw [(c.ι.app j₂).naturality (homOfLE (inf_le_left : U i ⊓ U k ≤ U i)).op]
      have h0 : ((CategoryTheory.forget AddCommGrpCat).mapCocone
          ((ev (U i ⊓ U k)).mapCocone c)).ι.app j₂
          (ConcreteCategory.hom ((Y'.obj j₂).val.map (homOfLE inf_le_left).op) d₀) =
        ((CategoryTheory.forget AddCommGrpCat).mapCocone
          ((ev (U i ⊓ U k)).mapCocone c)).ι.app j₂ 0 := by
        change ConcreteCategory.hom (((ev (U i ⊓ U k)).mapCocone c).ι.app j₂) _ =
          ConcreteCategory.hom (((ev (U i ⊓ U k)).mapCocone c).ι.app j₂) 0
        rw [hnat_d, h_diff_zero k hk, map_zero]
      rw [Types.FilteredColimit.isColimit_eq_iff' hcTyp] at h0
      obtain ⟨jk, fk, hfk⟩ := h0; refine ⟨jk, fk, ?_⟩
      have hnat' := ((Y' ⋙ sheafToPresheaf _ _).map fk).naturality
        (homOfLE (inf_le_left : U i ⊓ U k ≤ U i)).op
      change ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map fk).app (op (U i)) ≫
        ((Y' ⋙ sheafToPresheaf _ _).obj jk).map (homOfLE inf_le_left).op) d₀ = 0
      rw [← hnat']
      have := hfk.trans (map_zero _)
      exact this
    -- Merge all to common index (suffices + Finset.induction)
    obtain ⟨j₃, g₃, hg₃⟩ : ∃ (j₃ : J') (g₃ : j₂ ⟶ j₃),
        ∀ k ∈ t, ConcreteCategory.hom ((Y'.obj j₃).val.map (homOfLE (inf_le_left : U i ⊓ U k ≤ U i)).op)
          (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map g₃).app (op (U i))) d₀) = 0 := by
      suffices ∀ (S : Finset ι) (_ : S ⊆ t),
          (∀ k ∈ S, ∃ (jk : J') (fk : j₂ ⟶ jk),
            ConcreteCategory.hom ((Y'.obj jk).val.map (homOfLE (inf_le_left : U i ⊓ U k ≤ U i)).op)
              (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map fk).app (op (U i))) d₀) = 0) →
          ∃ (j₃ : J') (g₃ : j₂ ⟶ j₃),
            ∀ k ∈ S, ConcreteCategory.hom ((Y'.obj j₃).val.map (homOfLE (inf_le_left : U i ⊓ U k ≤ U i)).op)
              (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map g₃).app (op (U i))) d₀) = 0 by
        exact this t (fun _ hx => hx) h_ev_d
      intro S hSt h_ev_S
      induction S using Finset.induction with
      | empty => exact ⟨j₂, 𝟙 j₂, fun _ hk => absurd hk (by simp)⟩
      | @insert k₀ t₁ hk₀ ih =>
        obtain ⟨j_cur, g_cur, hg_cur⟩ := ih
          (fun k hk => hSt (Finset.mem_insert_of_mem hk))
          (fun k hk => h_ev_S k (Finset.mem_insert_of_mem hk))
        obtain ⟨jk₀, fk₀, hfk₀⟩ := h_ev_S k₀ (Finset.mem_insert_self k₀ t₁)
        let j' := IsFiltered.coeq (g_cur ≫ IsFiltered.leftToMax j_cur jk₀)
            (fk₀ ≫ IsFiltered.rightToMax j_cur jk₀)
        let h_eq := IsFiltered.coeqHom (g_cur ≫ IsFiltered.leftToMax j_cur jk₀)
            (fk₀ ≫ IsFiltered.rightToMax j_cur jk₀)
        have heq : g_cur ≫ IsFiltered.leftToMax j_cur jk₀ ≫ h_eq =
            fk₀ ≫ IsFiltered.rightToMax j_cur jk₀ ≫ h_eq := by
          have := IsFiltered.coeq_condition (g_cur ≫ IsFiltered.leftToMax j_cur jk₀)
            (fk₀ ≫ IsFiltered.rightToMax j_cur jk₀)
          simp only [Category.assoc] at this; exact this
        refine ⟨j', g_cur ≫ IsFiltered.leftToMax j_cur jk₀ ≫ h_eq, fun k hk => ?_⟩
        -- htrans: if res(F(f)(d₀)) = 0 then res(F(f ≫ g)(d₀)) = 0
        have htrans_d : ∀ {ja jb : J'} (fa : j₂ ⟶ ja) (ga : ja ⟶ jb) (k' : ι),
            ConcreteCategory.hom ((Y'.obj ja).val.map (homOfLE (inf_le_left : U i ⊓ U k' ≤ U i)).op)
              (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map fa).app (op (U i))) d₀) = 0 →
            ConcreteCategory.hom ((Y'.obj jb).val.map (homOfLE (inf_le_left : U i ⊓ U k' ≤ U i)).op)
              (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map (fa ≫ ga)).app (op (U i))) d₀) = 0 := by
          intro ja jb fa ga k' hfa
          let α := ((Y' ⋙ sheafToPresheaf _ _).map ga)
          change ConcreteCategory.hom
            (((Y' ⋙ sheafToPresheaf _ _).map (fa ≫ ga)).app (op (U i)) ≫
              (Y'.obj jb).val.map (homOfLE inf_le_left).op) d₀ = 0
          rw [(Y' ⋙ sheafToPresheaf _ _).map_comp, NatTrans.comp_app, Category.assoc,
            show α.app (op (U i)) ≫ (Y'.obj jb).val.map (homOfLE inf_le_left).op =
              (Y'.obj ja).val.map (homOfLE inf_le_left).op ≫ α.app (op (U i ⊓ U k'))
              from (α.naturality (homOfLE (inf_le_left : U i ⊓ U k' ≤ U i)).op).symm,
            ← Category.assoc]
          show ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map fa).app (op (U i)) ≫
            (Y'.obj ja).val.map (homOfLE inf_le_left).op ≫ α.app (op (U i ⊓ U k'))) d₀ = 0
          simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply]
          change ConcreteCategory.hom (α.app (op (U i ⊓ U k')))
            (ConcreteCategory.hom ((Y'.obj ja).val.map (homOfLE inf_le_left).op)
              (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map fa).app (op (U i))) d₀)) = 0
          rw [hfa, map_zero]
        rw [Finset.mem_insert] at hk; rcases hk with rfl | hk
        · rw [heq]; exact htrans_d fk₀ (IsFiltered.rightToMax j_cur jk₀ ≫ h_eq) k hfk₀
        · exact htrans_d g_cur (IsFiltered.leftToMax j_cur jk₀ ≫ h_eq) k (hg_cur k hk)
    -- Sheaf separation in piece: F(g₃)(d₀) = 0
    let b₃ := ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map g₃).app (op (U i))) d₀
    have hb₃_zero : b₃ = 0 := by
      have hFS : TopCat.Presheaf.IsSheaf (Y'.obj j₃).val := (Y'.obj j₃).cond
      exact hFS.section_ext (s := b₃) (t := 0) fun x hx => by
        -- x ∈ U i, so x ∈ some U k with k ∈ t (since U i ≤ ⨆ k ∈ t, U k)
        obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (hsup_le (le_iSup U i hx))
        obtain ⟨hkt, hxk⟩ := Opens.mem_iSup.mp hk
        exact ⟨U i ⊓ U k, inf_le_left, ⟨hx, hxk⟩, (hg₃ k hkt).trans (map_zero _).symm⟩
    -- Cocone factorization: d = ι(d₀) = ι(F(g₃)(d₀)) = ι(b₃) = 0
    rw [← hd₀]; change ConcreteCategory.hom ((c.ι.app j₂).app (op (U i))) d₀ = 0
    have hfac_d : (c.ι.app j₂).app (op (U i)) =
        ((Y' ⋙ sheafToPresheaf _ _).map g₃).app (op (U i)) ≫
        (c.ι.app j₃).app (op (U i)) := by
      have := congrArg (fun α => NatTrans.app α (op (U i))) (c.ι.naturality g₃)
      simp [Functor.const_obj_map] at this; exact this.symm
    conv_lhs => rw [hfac_d]
    change ConcreteCategory.hom ((c.ι.app j₃).app (op (U i))) b₃ = 0
    rw [hb₃_zero, map_zero]
  · -- Uniqueness from hsep
    have h0 : s' - s = 0 := hsep (s' - s) (fun k hk => by
      show c.pt.map (Opens.leSupr U k).op (s' - s) = 0
      rw [map_sub, sub_eq_zero]
      exact (hs' k).trans (hs_k k hk).symm)
    rwa [sub_eq_zero] at h0

/-- On a Noetherian space, `sheafToPresheaf` creates filtered colimits of sheaves. -/
private noncomputable def createsFilteredColimit
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) :
    CreatesColimit Y' (sheafToPresheaf _ _) :=
  Sheaf.createsColimitOfIsSheaf Y' (fun c hc => isSheaf_presheaf_filtered_colimit Y' c hc)

/-- Auxiliary: sheaf cohomology vanishing commutes with filtered colimits, universally
    quantified over the degree `n` so that the IH applies to all diagrams.
    Proof by induction on `n` with dimension shifting. -/
private theorem sheafH_filtered_colimit_aux
    {X : TopCat.{u}} [NoetherianSpace X] (n : ℕ) :
    ∀ {J' : Type u} [inst1 : SmallCategory J'] [inst2 : IsFiltered J']
      (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
      (c' : Cocone Y') (hc' : IsColimit c')
      (hvan : ∀ j, Subsingleton (Sheaf.H (Y'.obj j) n)),
    Subsingleton (Sheaf.H c'.pt n) := by
  induction n with
  | zero =>
    -- Base case: H^0 = Ext^0 ≅ Hom ≅ global sections.
    -- On Noetherian spaces, sheafToPresheaf creates filtered colimits (via
    -- isSheaf_presheaf_filtered_colimit), so global sections commute with
    -- filtered colimits. If each piece has trivial global sections, so does the colimit.
    intro J' inst1 inst2 Y' c' hc' hvan
    letI := inst1; letI := inst2
    -- H^0 ≅ global sections, colimit of trivial sections is trivial
    haveI := createsFilteredColimit Y'
    let c_psh := (sheafToPresheaf _ _).mapCocone c'
    have hc_psh := isColimitOfPreserves (sheafToPresheaf _ _) hc'
    let ev_top := (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
    have hc_top := isColimitOfPreserves ev_top hc_psh
    have h_sec : ∀ j, Subsingleton ((Y'.obj j).val.obj (op ⊤)) := fun j => by
      haveI := hvan j; exact subsingleton_of_addEquiv (sheafH0EquivSections (Y'.obj j))
    have : Subsingleton (c'.pt.val.obj (op ⊤)) := by
      constructor; intro a b
      obtain ⟨j₁, x, hx⟩ := Concrete.isColimit_exists_rep _ hc_top a
      obtain ⟨j₂, y, hy⟩ := Concrete.isColimit_exists_rep _ hc_top b
      rw [← hx, ← hy, @Subsingleton.elim _ (h_sec j₁) x 0,
          @Subsingleton.elim _ (h_sec j₂) y 0, map_zero, map_zero]
    exact subsingleton_of_addEquiv (sheafH0EquivSections c'.pt).symm
  | succ n ih =>
    -- Inductive step: dimension shifting via injective embedding.
    intro J' inst1 inst2 Y' c' hc' hvan
    letI := inst1; letI := inst2
    -- Mono coprojections: needed for SES 0 → Y_j → I → Q_j → 0.
    -- At call site: finsetGenFunctor has mono transitions →
    -- IsColimit.mono_ι_app_of_isFiltered gives mono coprojections.
    -- The IH call on Q introduces its own mono sorry at recursive levels.
    have hmono_ι : ∀ j, Mono (c'.ι.app j) := sorry
    -- Embed c'.pt ↪ I (injective)
    haveI : EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{u} X) :=
      IsGrothendieckAbelian.enoughInjectives
    let ι' := Injective.ι c'.pt
    -- Short exact sequence 0 → c'.pt → I → cokernel ι' → 0
    let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
      ShortComplex.mk ι' (cokernel.π ι') (cokernel.condition ι')
    have hSE : S.ShortExact := ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) inferInstance inferInstance
    -- Ext^{n+1}(Z, I) = 0 since I is injective
    have hI : Subsingleton (Sheaf.H (Injective.under c'.pt) (n + 1)) :=
      Ext.subsingleton_of_injective _ _ n
    -- Ext^n(Z, cokernel ι') = 0 by IH applied to the quotient diagram
    -- (Q = colim Q_j where Q_j = coker(F_j → I), each Ext^n(Z, Q_j) = 0 by LES)
    -- Build quotient diagram Q_j = cokernel(c'.ι.app j ≫ ι') and apply IH
    let I := Injective.under c'.pt
    have hnat_ι : ∀ {j j' : J'} (f : j ⟶ j'),
        (c'.ι.app j ≫ ι') ≫ (𝟙 I) = Y'.map f ≫ (c'.ι.app j' ≫ ι') := by
      intro j j' f; rw [Category.comp_id, ← Category.assoc, Cocone.w]
    -- Quotient functor Q.obj j = cokernel(c'.ι.app j ≫ ι')
    let Q : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
      { obj := fun j => cokernel (c'.ι.app j ≫ ι')
        map := fun {j j'} f => cokernel.map _ _ (Y'.map f) (𝟙 I) (hnat_ι f)
        map_id := fun j => by ext; rw [cokernel.π_desc]; exact Category.id_comp _
        map_comp := fun {j j' j''} f g => by
          ext; show cokernel.π _ ≫ _ = cokernel.π _ ≫ _ ≫ _
          dsimp only [cokernel.map]
          conv_rhs => rw [← Category.assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc]
          rw [cokernel.π_desc]; exact congrArg (𝟙 I ≫ ·) (Category.id_comp _).symm }
    -- Cocone on Q with vertex S.X₃ = cokernel ι'
    let qCocone : Cocone Q := Cocone.mk S.X₃
      { app := fun j => cokernel.map _ _ (c'.ι.app j) (𝟙 I) (by rw [Category.comp_id])
        naturality := fun j j' f => by
          ext; show cokernel.π _ ≫ _ ≫ _ = cokernel.π _ ≫ _ ≫ _
          dsimp only [cokernel.map]; simp only [Functor.const_obj_map, Category.comp_id]
          conv_lhs => rw [← Category.assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc]
          conv_rhs => rw [← Category.assoc, cokernel.π_desc]
          exact (Category.id_comp _).symm.trans (Category.comp_id _).symm }
    -- IsColimit: cokernel preserves filtered colimits (AB5)
    have hqColim : IsColimit qCocone := by
      haveI : Nonempty J' := IsFiltered.nonempty
      -- cokernel.π(f_j) ≫ Q.map a = cokernel.π(f_{j'})
      have hπQ : ∀ {j₁ j₂ : J'} (a : j₁ ⟶ j₂),
          cokernel.π (c'.ι.app j₁ ≫ ι') ≫ Q.map a =
          cokernel.π (c'.ι.app j₂ ≫ ι') := by
        intro j₁ j₂ a
        exact (cokernel.π_desc _ _ _).trans (Category.id_comp _)
      -- cokernel.π(f_j) ≫ qCocone.ι.app j = cokernel.π(ι')
      have hπC : ∀ j, cokernel.π (c'.ι.app j ≫ ι') ≫ qCocone.ι.app j =
          cokernel.π ι' := by
        intro j
        exact (cokernel.π_desc _ _ _).trans (Category.id_comp _)
      -- g_j := cokernel.π(f_j) ≫ s.ι.app j is independent of j
      have g_eq : ∀ (s : Cocone Q) (j₁ j₂ : J'),
          cokernel.π (c'.ι.app j₁ ≫ ι') ≫ s.ι.app j₁ =
          cokernel.π (c'.ι.app j₂ ≫ ι') ≫ s.ι.app j₂ := by
        intro s j₁ j₂
        have h₁ : s.ι.app j₁ = Q.map (IsFiltered.leftToMax j₁ j₂) ≫
            s.ι.app (IsFiltered.max j₁ j₂) := by rw [s.w]
        have h₂ : s.ι.app j₂ = Q.map (IsFiltered.rightToMax j₁ j₂) ≫
            s.ι.app (IsFiltered.max j₁ j₂) := by rw [s.w]
        rw [h₁, h₂, ← Category.assoc, ← Category.assoc, hπQ, hπQ]
      let j₀ := Classical.arbitrary J'
      exact
      { desc := fun s => cokernel.desc ι'
            (cokernel.π (c'.ι.app j₀ ≫ ι') ≫ s.ι.app j₀)
            (hc'.hom_ext (fun j => by
              simp only [comp_zero, Category.assoc, g_eq _ j₀ j,
                ← Category.assoc (c'.ι.app j), ← Category.assoc (c'.ι.app j ≫ ι'),
                cokernel.condition, zero_comp]))
        fac := fun s j => by
          apply (cancel_epi (cokernel.π (c'.ι.app j ≫ ι'))).mp
          rw [← Category.assoc, hπC, cokernel.π_desc, g_eq s j₀ j]
        uniq := fun s m hm => by
          apply (cancel_epi (cokernel.π ι')).mp
          rw [cokernel.π_desc, ← hπC j₀, Category.assoc, hm j₀] }
    -- Split on n: n=0 needs direct H^1 argument, n≥1 uses dimension shift
    match n with
    | 0 =>
      -- Direct proof of H^1(c'.pt) = 0 using the LES + Ext^0 surjectivity.
      -- Pattern: every α ∈ Ext^1(Z, c'.pt) lifts to β ∈ Ext^0(Z, Q) (by exact₁),
      -- then β lifts to γ ∈ Ext^0(Z, I) (by surjectivity: Q = colim Q_j, each
      -- Ext^0(Z, I) ↠ Ext^0(Z, Q_j) from SES + Mono + H^1(Y_j)=0), hence
      -- β.comp hSE.extClass = 0 (by associativity + comp_extClass = 0).
      -- Ext^0 surjectivity: every element of Ext^0(Z, Q) lifts to Ext^0(Z, I)
      -- Ext^0 surjectivity: every element of Ext^0(Z, Q) lifts to Ext^0(Z, I).
      -- Proof: Γ(I) ↠ Γ(Q) because Q = colim Q_j, each Γ(I) ↠ Γ(Q_j) by LES + mono.
      have hΓg_epi : Epi (S.g.val.app (op ⊤)) := by
        rw [AddCommGrpCat.epi_iff_surjective]; intro q
        -- Γ(Q) = colim Γ(Q_j) via filtered colimit preservation
        haveI := createsFilteredColimit Q
        have hc_top_Q := isColimitOfPreserves
          ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤))
          (isColimitOfPreserves (sheafToPresheaf _ _) hqColim)
        obtain ⟨j₀, q₀, hq₀⟩ := Concrete.isColimit_exists_rep _ hc_top_Q q
        -- Per-piece: Γ(I) ↠ Γ(Q_{j₀}) from SES + mono + H^1(Y_{j₀}) = 0
        haveI : Mono ι' := inferInstance
        haveI : Mono (c'.ι.app j₀ ≫ ι') := mono_comp _ _
        let ip_j₀ : InjectivePresentation (Y'.obj j₀) :=
          { J := I, f := c'.ι.app j₀ ≫ ι' }
        have hπ_epi := epi_g_app_top_of_H1_vanishing ip_j₀ (hvan j₀)
        rw [AddCommGrpCat.epi_iff_surjective] at hπ_epi
        obtain ⟨p, hp⟩ := hπ_epi q₀
        -- Composition: I →[π_{j₀}] Q_{j₀} →[cocone] Q = I →[S.g] Q
        -- From hqColim: cokernel.π(f_{j₀}) ≫ qCocone.ι.app j₀ = cokernel.π(ι') = S.g
        have hcomp : ip_j₀.shortComplex.g ≫ qCocone.ι.app j₀ = S.g := by
          show cokernel.π _ ≫ _ = cokernel.π _
          exact (cokernel.π_desc _ _ _).trans (Category.id_comp _)
        refine ⟨p, ?_⟩
        show (S.g.val.app (op ⊤)) p = q
        have hkey := congrArg (·.val.app (op ⊤)) hcomp
        simp only [] at hkey
        rw [hkey.symm]; exact hq₀ ▸ hp ▸ rfl
      have h_surj := ext0_surj_of_epi_top (S := S) hΓg_epi
      constructor; intro a b
      have ha : a.comp (Ext.mk₀ S.f) rfl = 0 := @Subsingleton.elim _ hI _ _
      have hb : b.comp (Ext.mk₀ S.f) rfl = 0 := @Subsingleton.elim _ hI _ _
      obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ _ hSE a ha rfl
      obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₁ _ hSE b hb rfl
      obtain ⟨c', hc'⟩ := h_surj c
      obtain ⟨d', hd'⟩ := h_surj d
      have zero_c : c.comp hSE.extClass rfl = 0 := by
        rw [← hc', Ext.comp_assoc_of_second_deg_zero c' (Ext.mk₀ S.g)
          hSE.extClass rfl, hSE.comp_extClass, Ext.comp_zero c' _ 1 1 rfl]
      have zero_d : d.comp hSE.extClass rfl = 0 := by
        rw [← hd', Ext.comp_assoc_of_second_deg_zero d' (Ext.mk₀ S.g)
          hSE.extClass rfl, hSE.comp_extClass, Ext.comp_zero d' _ 1 1 rfl]
      rw [← hc, ← hd, zero_c, zero_d]
    | n' + 1 =>
      -- For n ≥ 1: dimension shift via h_van_Q + IH
      have h_van_Q : ∀ j, Subsingleton (Sheaf.H (Q.obj j) (n' + 1)) := by
        intro j
        let S_j : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
          ShortComplex.mk (c'.ι.app j ≫ ι') (cokernel.π (c'.ι.app j ≫ ι'))
            (cokernel.condition _)
        have hSE_j : S_j.ShortExact := by
          refine ShortComplex.ShortExact.mk'
            (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) ?_ inferInstance
          haveI : Mono ι' := inferInstance
          exact mono_comp (c'.ι.app j) ι'
        exact ext_dimension_shift_X₃ _ hSE_j (n' + 1)
          (Ext.subsingleton_of_injective _ _ n') (hvan j)
      have hQ : Subsingleton (Sheaf.H S.X₃ (n' + 1)) :=
        ih Q qCocone hqColim h_van_Q
      exact ext_dimension_shift _ hSE (n' + 1) hQ hI

/-- **Sheaf cohomology commutes with filtered colimits** on Noetherian spaces.
    This is the derived functor commutation theorem for `H^n = R^n Γ`:
    if `H^n(F_j) = 0` for all pieces of a filtered diagram, then `H^n(colim F_j) = 0`.

    Proof by induction on `n`:
    - `n = 0`: `Ext^0 = Hom ≅ global sections`, which commutes with filtered colimits on
      Noetherian spaces because `sheafToPresheaf` creates filtered colimits.
    - `n + 1`: Embed `colim F_j ↪ I` (injective). The cokernel `Q` is a filtered colimit
      of `Q_j = I / F_j`. The LES gives `Ext^{n+1}(Z, colim F_j) ≅ Ext^n(Z, Q)`.
      Each `Ext^n(Z, Q_j) = 0` by LES, so by IH `Ext^n(Z, Q) = 0`. -/
theorem sheafH_preserves_filtered_colimits
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (c' : Cocone Y') (hc' : IsColimit c')
    (n : ℕ)
    (hvan : ∀ j, Subsingleton (Sheaf.H (Y'.obj j) n)) :
    Subsingleton (Sheaf.H c'.pt n) :=
  sheafH_filtered_colimit_aux n Y' c' hc' hvan

/-- **Hartshorne 2.9 core**: on a Noetherian space, if `H^m = 0` for all finitely generated
    subsheaves of `K`, then `H^m(K) = 0`. Applies `sheafH_preserves_filtered_colimits`
    to the filtered diagram of finitely generated subsheaves. -/
theorem cohomology_vanishing_of_finitelyGenerated_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    (K : TopCat.Sheaf AddCommGrpCat.{u} X) (m : ℕ)
    (hfg : ∀ (S : Finset (TopCat.Sheaf.SectionIndex K))
      [HasCoproduct fun σ : {σ // σ ∈ S} => TopCat.Sheaf.zeroOutsideInt σ.1.1],
      Subsingleton (Sheaf.H (TopCat.Sheaf.finsetGeneratedSheaf S) m)) :
    Subsingleton (Sheaf.H K m) :=
  sheafH_preserves_filtered_colimits (finsetGenFunctor K) (finsetGenCocone K)
    (finsetGenCocone_isColimit K) m (fun S => hfg S)

section FinsetGenerated
open scoped Classical

/-- Coproduct inclusion from `S'` to `insert σ₀ S'`. -/
private noncomputable def finsetCoproductIncl
    {X : TopCat.{u}} {K : TopCat.Sheaf AddCommGrpCat.{u} X}
    {S' : Finset (TopCat.Sheaf.SectionIndex K)}
    {σ₀ : TopCat.Sheaf.SectionIndex K} (_ : σ₀ ∉ S')
    [HasCoproduct fun σ : {σ // σ ∈ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1]
    [HasCoproduct fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1] :
    (∐ fun σ : {σ // σ ∈ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1) ⟶
    (∐ fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1) :=
  Sigma.desc fun σ =>
    Sigma.ι (fun τ : {τ // τ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt τ.1.1)
      ⟨σ.1, Finset.mem_insert_of_mem σ.2⟩

/-- Mono from `image(S')` to `image(insert σ₀ S')` via coproduct inclusion. -/
private noncomputable def imageIncl
    {X : TopCat.{u}} {K : TopCat.Sheaf AddCommGrpCat.{u} X}
    {S' : Finset (TopCat.Sheaf.SectionIndex K)}
    {σ₀ : TopCat.Sheaf.SectionIndex K} (hσ₀ : σ₀ ∉ S')
    [HasCoproduct fun σ : {σ // σ ∈ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1]
    [HasCoproduct fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1] :
    TopCat.Sheaf.finsetGeneratedSheaf S' ⟶ TopCat.Sheaf.finsetGeneratedSheaf (insert σ₀ S') :=
  Limits.image.lift
    { I := TopCat.Sheaf.finsetGeneratedSheaf (insert σ₀ S')
      m := Limits.image.ι _
      e := finsetCoproductIncl hσ₀ ≫ factorThruImage (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S'))
      fac := by
        rw [Category.assoc, Limits.image.fac]
        ext ⟨σ, hσ⟩
        simp [finsetCoproductIncl, TopCat.Sheaf.finsetGeneratorMap, TopCat.Sheaf.familyGeneratorMap] }

private instance imageIncl_mono
    {X : TopCat.{u}} {K : TopCat.Sheaf AddCommGrpCat.{u} X}
    {S' : Finset (TopCat.Sheaf.SectionIndex K)}
    {σ₀ : TopCat.Sheaf.SectionIndex K} (hσ₀ : σ₀ ∉ S')
    [HasCoproduct fun σ : {σ // σ ∈ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1]
    [HasCoproduct fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1] :
    Mono (imageIncl hσ₀ : TopCat.Sheaf.finsetGeneratedSheaf S' ⟶ _) := by
  have h : imageIncl hσ₀ ≫ Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) =
      Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap S') := Limits.image.lift_fac _
  exact mono_of_mono_fac h

/-- The `σ₀`-component maps epi onto the cokernel of `imageIncl`. -/
private theorem imageIncl_cokernel_epi
    {X : TopCat.{u}} {K : TopCat.Sheaf AddCommGrpCat.{u} X}
    {S' : Finset (TopCat.Sheaf.SectionIndex K)}
    {σ₀ : TopCat.Sheaf.SectionIndex K} (hσ₀ : σ₀ ∉ S')
    [HasCoproduct fun σ : {σ // σ ∈ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1]
    [HasCoproduct fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1] :
    Epi (Sigma.ι (fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1)
      ⟨σ₀, Finset.mem_insert_self σ₀ S'⟩ ≫
      factorThruImage (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) ≫
      cokernel.π (imageIncl hσ₀)) := by
  let proj : (∐ fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1) ⟶
      TopCat.Sheaf.zeroOutsideInt σ₀.1 :=
    Sigma.desc fun σ =>
      if h : σ.1 = σ₀ then
        eqToHom (by rw [h])
      else 0
  have heq : finsetCoproductIncl hσ₀ ≫
      factorThruImage (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) =
    factorThruImage (TopCat.Sheaf.finsetGeneratorMap S') ≫ imageIncl hσ₀ := by
    apply (cancel_mono (Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')))).1
    rw [Category.assoc, Limits.image.fac]
    have hlf : imageIncl hσ₀ ≫ Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) =
        Limits.image.ι (TopCat.Sheaf.finsetGeneratorMap S') := Limits.image.lift_fac _
    rw [Category.assoc, hlf, Limits.image.fac]
    ext ⟨σ', hσ'⟩
    simp [finsetCoproductIncl, TopCat.Sheaf.finsetGeneratorMap, TopCat.Sheaf.familyGeneratorMap]
  have hfac : proj ≫
      (Sigma.ι (fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1)
        ⟨σ₀, Finset.mem_insert_self σ₀ S'⟩ ≫
      factorThruImage (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) ≫
      cokernel.π (imageIncl hσ₀)) =
    factorThruImage (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) ≫
      cokernel.π (imageIncl hσ₀) := by
    ext ⟨σ, hσ⟩
    simp only [proj, Category.assoc, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
    by_cases h : σ = σ₀
    · subst h; simp
    · rw [← Category.assoc
        (Sigma.ι (fun σ : {σ // σ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt σ.1.1) ⟨σ, hσ⟩)
        (Sigma.desc _)]
      rw [colimit.ι_desc, Cofan.mk_ι_app, dif_neg h, zero_comp]
      symm
      have hσ' : σ ∈ S' := Finset.mem_of_mem_insert_of_ne hσ h
      have hι : Sigma.ι (fun τ : {τ // τ ∈ S'} => TopCat.Sheaf.zeroOutsideInt τ.1.1) ⟨σ, hσ'⟩ ≫
          finsetCoproductIncl hσ₀ =
        Sigma.ι (fun τ : {τ // τ ∈ insert σ₀ S'} => TopCat.Sheaf.zeroOutsideInt τ.1.1) ⟨σ, hσ⟩ := by
        simp [finsetCoproductIncl]
      rw [← hι, Category.assoc, reassoc_of% heq]
      simp [cokernel.condition]
  exact epi_of_epi_fac hfac

/-- **Step 3B–3C**: vanishing for `finsetGeneratedSheaf S` by `Finset.induction`. -/
theorem finsetGeneratedSheaf_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    {K : TopCat.Sheaf AddCommGrpCat.{u} X}
    (m : ℕ)
    (hzero : ∀ {G : TopCat.Sheaf AddCommGrpCat.{u} X} {V : Opens X}
      (f : TopCat.Sheaf.zeroOutsideInt V ⟶ G), Epi f → Subsingleton (Sheaf.H G m))
    (S : Finset (TopCat.Sheaf.SectionIndex K))
    [HasCoproduct fun σ : {σ // σ ∈ S} => TopCat.Sheaf.zeroOutsideInt σ.1.1] :
    Subsingleton (Sheaf.H (TopCat.Sheaf.finsetGeneratedSheaf S) m) := by
  suffices h : ∀ (T : Finset (TopCat.Sheaf.SectionIndex K)),
      Subsingleton (Sheaf.H (TopCat.Sheaf.finsetGeneratedSheaf T) m) from h S
  intro T
  induction T using Finset.induction with
  | empty =>
    apply subsingleton_sheafH_of_isZero'
    apply IsZero.of_iso (isZero_zero _) (imageZero' _)
    apply Sigma.hom_ext; intro ⟨σ, hσ⟩; simp at hσ
  | @insert σ₀ S' hσ₀ ih =>
    haveI : Mono (imageIncl hσ₀) := imageIncl_mono hσ₀
    let SC := ShortComplex.mk (imageIncl hσ₀) (cokernel.π (imageIncl hσ₀))
      (cokernel.condition _)
    have hSE : SC.ShortExact := ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) inferInstance inferInstance
    have hCoker : Subsingleton (Sheaf.H SC.X₃ m) := by
      haveI := imageIncl_cokernel_epi hσ₀
      exact hzero (Sigma.ι (fun σ : {σ // σ ∈ insert σ₀ S'} =>
            TopCat.Sheaf.zeroOutsideInt σ.1.1) ⟨σ₀, Finset.mem_insert_self σ₀ S'⟩ ≫
          factorThruImage (TopCat.Sheaf.finsetGeneratorMap (insert σ₀ S')) ≫
          cokernel.π (imageIncl hσ₀)) inferInstance
    exact subsingleton_sheafH_of_shortExact_middle hSE m ih hCoker

end FinsetGenerated

/-- **Step 3A** (Hartshorne III.2.7): on a Noetherian space, if vanishing holds for
    all epi images of `zeroOutsideInt V`, then it holds for every sheaf.
    Assembles `finsetGeneratedSheaf_vanishing` (finite case) with
    `cohomology_vanishing_of_finitelyGenerated_vanishing` (colimit step). -/
theorem directLimit_cohomology_vanishing
    {X : TopCat.{u}} [NoetherianSpace X]
    (K : TopCat.Sheaf AddCommGrpCat.{u} X) (m : ℕ)
    (hzero : ∀ {G : TopCat.Sheaf AddCommGrpCat.{u} X} {V : Opens X}
      (f : TopCat.Sheaf.zeroOutsideInt V ⟶ G), Epi f → Subsingleton (Sheaf.H G m)) :
    Subsingleton (Sheaf.H K m) :=
  cohomology_vanishing_of_finitelyGenerated_vanishing K m
    (fun S _ => finsetGeneratedSheaf_vanishing m hzero S)
