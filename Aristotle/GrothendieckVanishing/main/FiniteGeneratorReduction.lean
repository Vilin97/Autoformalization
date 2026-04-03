/-
  FiniteGeneratorReduction.lean — Colimit step and finitely generated vanishing

  Key results:
  - Ext LES helper lemmas (ext_sandwich, addCommGrpCat_exact_sandwich)
  - sheafH_preserves_filtered_colimits: H^n commutes with filtered colimits (1 sorry)
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

/-- Exact sandwich in `AddCommGrpCat`: if a short complex is exact and both ends
    are subsingleton, the middle is subsingleton. -/
private theorem addCommGrpCat_exact_sandwich
    (S : ShortComplex AddCommGrpCat) (hS : S.Exact)
    (h₁ : Subsingleton S.X₁) (h₃ : Subsingleton S.X₃) :
    Subsingleton S.X₂ := by
  rw [ShortComplex.ab_exact_iff_range_eq_ker] at hS
  constructor; intro a b
  have hgab := @Subsingleton.elim _ h₃ (S.g.hom a) (S.g.hom b)
  have hmem : a - b ∈ S.g.hom.ker := by
    simp [AddMonoidHom.mem_ker, map_sub, sub_eq_zero.mpr hgab]
  rw [← hS] at hmem
  obtain ⟨y, hy⟩ := hmem
  rw [@Subsingleton.elim _ h₁ y 0, map_zero] at hy
  exact sub_eq_zero.mp hy.symm

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

/-- Ext sandwich via LES: given `0 → X₁ → X₂ → X₃ → 0` short exact,
    `Ext^n(Z, X₂) = 0` and `Ext^{n+1}(Z, X₁) = 0` imply `Ext^n(Z, X₃) = 0`. -/
private theorem ext_sandwich (Z : C') {S : ShortComplex C'} (hS : S.ShortExact) (n : ℕ)
    (h₂ : Subsingleton (Ext Z S.X₂ n))
    (h₁ : Subsingleton (Ext Z S.X₁ (n + 1))) :
    Subsingleton (Ext Z S.X₃ n) :=
  addCommGrpCat_exact_sandwich _ (Ext.covariant_sequence_exact₃' Z hS n (n+1) rfl) h₂ h₁

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

/-- **Sheaf cohomology commutes with filtered colimits** on Noetherian spaces.
    This is the derived functor commutation theorem for `H^n = R^n Γ`:
    if `H^n(F_j) = 0` for all pieces of a filtered diagram, then `H^n(colim F_j) = 0`.

    The proof requires showing that `R^n Γ` preserves filtered colimits, which follows from:
    (1) Γ = global sections preserves filtered colimits (sheafToPresheaf creates them on
        Noetherian spaces — the AB5 property), and
    (2) filtered colimits of injective resolutions are injective resolutions, and
    (3) cohomology of chain complexes commutes with filtered colimits (AB5 for Ab).

    This single sorry subsumes both the former sorry #1 (isSheaf_filtered_colimit_of_sheaves)
    and sorry #2 (hQprov in ext_vanishing_of_colimit_aux). -/
theorem sheafH_preserves_filtered_colimits
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (c' : Cocone Y') (hc' : IsColimit c')
    (n : ℕ)
    (hvan : ∀ j, Subsingleton (Sheaf.H (Y'.obj j) n)) :
    Subsingleton (Sheaf.H c'.pt n) := by
  sorry

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
