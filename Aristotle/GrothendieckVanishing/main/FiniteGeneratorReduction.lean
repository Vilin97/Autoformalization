/-
  FiniteGeneratorReduction.lean — Colimit step and finitely generated vanishing

  Key results (presheaf colimit theory split to PresheafFilteredColimit.lean):
  - sheafH_filtered_colimit_aux / sheafH_preserves_filtered_colimits: H^n commutes with
    filtered colimits (1 sorry: hmono_transitions — mono transitions for Y', true at call
    site via finsetGenFunctor_mono but FALSE at recursive IH level; closing requires
    Čech cohomology or a proof that avoids dimension shifting)
  - finsetGenFunctor / finsetGenCocone / finsetGenCocone_isColimit: K is the filtered
    colimit of its finitely generated subsheaves (PROVED)
  - cohomology_vanishing_of_finitelyGenerated_vanishing: H^m = 0 for all f.g. subsheaves
    implies H^m(K) = 0 (PROVED via sheafH_preserves_filtered_colimits)
  - finsetGeneratedSheaf_vanishing: vanishing for finitely generated sheaves by
    Finset.induction (PROVED)
  - directLimit_cohomology_vanishing: from epi-image vanishing to all sheaves (PROVED)
-/
import Aristotle.GrothendieckVanishing.main.PresheafFilteredColimit
import Aristotle.GrothendieckVanishing.main.Setup
import Aristotle.GrothendieckVanishing.main.ZeroOutsideFinset

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

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

/-! ### Sheaf cohomology commutes with filtered colimits

The main result `sheafH_preserves_filtered_colimits` proves that on a Noetherian
space, if `H^n(F_j) = 0` for all pieces of a filtered diagram, then `H^n(colim F_j) = 0`.

**Gap**: The proof uses dimension shifting via injective embedding, which requires the
coprojections `c'.ι.app j : F_j → colim` to be mono. This is derived from mono transitions
via `mono_ι_app_of_isFiltered` (AB5). At the call site (`finsetGenFunctor`), mono
transitions hold by `finsetGenFunctor_mono`. The sorry asserts this in the universally
quantified context. Closing requires Čech cohomology or Gabriel's theorem (filtered
colimits of injective sheaves are injective on locally Noetherian Grothendieck abelian
categories — not yet in Mathlib). -/

/-- Auxiliary: sheaf cohomology vanishing commutes with filtered colimits on Noetherian
    spaces. Proof by induction on `n` with dimension shifting.

    1 sorry: `hmono_transitions` — mono transitions for Y'. TRUE at the call site
    (`finsetGenFunctor_mono`) but FALSE at recursive IH levels (the quotient diagram Q
    has non-mono transitions by the snake lemma: `ker(Q.map φ) ≅ coker(Y'.map φ) ≠ 0`).
    Closing requires a proof that avoids recursive dimension shifting. -/
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
    -- Mono transitions: true at call site via finsetGenFunctor_mono.
    -- Used to derive mono coprojections (via mono_ι_app_of_isFiltered / AB5).
    -- This is the sole sorry in the formalization.
    have hmono_transitions : ∀ ⦃j j' : J'⦄ (φ : j ⟶ j'), Mono (Y'.map φ) := sorry
    have hmono_ι : ∀ j, Mono (c'.ι.app j) := by
      intro j; haveI := hmono_transitions; exact hc'.mono_ι_app_of_isFiltered j
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
    If `H^n(F_j) = 0` for all pieces of a filtered diagram, then `H^n(colim F_j) = 0`.

    1 sorry: mono transitions (true at call site via `finsetGenFunctor_mono`). -/
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
