/-
  PresheafFilteredColimit.lean — Presheaf filtered colimit is a sheaf on Noetherian spaces

  Split from FiniteGeneratorReduction.lean. Contains:
  - sheaf_section_zero_of_zero_on_finite_cover: sections vanishing on finite cover vanish
  - filtered_colimit_kills_all_restrictions: merge finitely many eventually-zero transitions
  - isSheaf_presheaf_filtered_colimit: presheaf-level filtered colimit of sheaves is a sheaf
    on Noetherian spaces (PROVED)
  - createsFilteredColimit: sheafToPresheaf creates filtered colimits (PROVED)
  - isFlasque_filtered_colimit: filtered colimits of flasque sheaves are flasque (PROVED)
-/
import Aristotle.GrothendieckVanishing.main.ClosedImmersionCohomology
import Aristotle.GrothendieckVanishing.main.ZeroOutsideFinset

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

/-- Zero is preserved under filtered transitions: if restricting a transition to an open
    gives 0, then restricting any further transition also gives 0. -/
private lemma transition_preserves_zero
    {X : TopCat.{u}} {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    {j₀ j j' : J'} (f : j₀ ⟶ j) (g : j ⟶ j')
    {U V : Opens X} (φ : U ⟶ V)
    (b₀ : ToType ((Y'.obj j₀).val.obj (op V)))
    (h : ConcreteCategory.hom ((Y'.obj j).val.map φ.op)
      (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map f).app (op V)) b₀) = 0) :
    ConcreteCategory.hom ((Y'.obj j').val.map φ.op)
      (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map (f ≫ g)).app (op V)) b₀) = 0 := by
  let α := (Y' ⋙ sheafToPresheaf _ _).map g
  change ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map (f ≫ g)).app (op V) ≫
    (Y'.obj j').val.map φ.op) b₀ = 0
  rw [(Y' ⋙ sheafToPresheaf _ _).map_comp, NatTrans.comp_app, Category.assoc,
    show α.app (op V) ≫ (Y'.obj j').val.map φ.op =
      (Y'.obj j).val.map φ.op ≫ α.app (op U) from (α.naturality φ.op).symm,
    ← Category.assoc]
  simp only [ConcreteCategory.comp_apply]
  exact (congr_arg (ConcreteCategory.hom (α.app (op U))) h).trans (map_zero _)

/-- Pairwise compatibility is preserved under filtered transitions. -/
private lemma transition_preserves_compat
    {X : TopCat.{u}} {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    {j₀ j j' : J'} (f : j₀ ⟶ j) (g : j ⟶ j')
    {U V : Opens X} (a : ToType ((Y'.obj j₀).val.obj (op U)))
    (b : ToType ((Y'.obj j₀).val.obj (op V)))
    (h : ConcreteCategory.hom ((Y'.obj j).val.map (Opens.infLELeft U V).op)
      (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map f).app (op U)) a) =
     ConcreteCategory.hom ((Y'.obj j).val.map (Opens.infLERight U V).op)
      (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map f).app (op V)) b)) :
    ConcreteCategory.hom ((Y'.obj j').val.map (Opens.infLELeft U V).op)
      (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map (f ≫ g)).app (op U)) a) =
    ConcreteCategory.hom ((Y'.obj j').val.map (Opens.infLERight U V).op)
      (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map (f ≫ g)).app (op V)) b) := by
  let β := (Y' ⋙ sheafToPresheaf _ _).map g
  -- Factor F(f ≫ g) = F(f) ≫ β; for each side use naturality: β ≫ res = res ≫ β
  suffices ∀ {W : Opens X} (φ : U ⊓ V ⟶ W) (c₀ : ToType ((Y'.obj j₀).val.obj (op W))),
      ConcreteCategory.hom ((Y'.obj j').val.map φ.op)
        (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map (f ≫ g)).app (op W)) c₀) =
      ConcreteCategory.hom (β.app (op (U ⊓ V)))
        (ConcreteCategory.hom ((Y'.obj j).val.map φ.op)
          (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map f).app (op W)) c₀)) by
    rw [this (Opens.infLELeft U V) a, this (Opens.infLERight U V) b, h]
  intro W φ c₀
  simp only [Functor.map_comp, NatTrans.comp_app, AddCommGrpCat.hom_comp,
    AddMonoidHom.coe_comp, Function.comp_apply]
  change ConcreteCategory.hom (β.app (op W) ≫ (Y'.obj j').val.map φ.op) _ =
    ConcreteCategory.hom ((Y'.obj j).val.map φ.op ≫ β.app (op (U ⊓ V))) _
  rw [show β.app (op W) ≫ (Y'.obj j').val.map φ.op =
    (Y'.obj j).val.map φ.op ≫ β.app (op (U ⊓ V))
    from (β.naturality φ.op).symm]; rfl

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

/-- Merge finitely many eventually-zero restrictions into a common index. -/
private theorem filtered_colimit_kills_all_restrictions
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    {X : TopCat.{u}} (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    {ι : Type u} {V : Opens X} {W : ι → Opens X} (hW : ∀ k, W k ≤ V) (j₀ : J')
    (b₀ : ToType ((Y'.obj j₀).val.obj (op V)))
    (t : Finset ι)
    (h_ev : ∀ k ∈ t, ∃ (jk : J') (fk : j₀ ⟶ jk),
      ConcreteCategory.hom ((Y'.obj jk).val.map (homOfLE (hW k)).op)
        (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map fk).app (op V)) b₀) = 0) :
    ∃ (j₁ : J') (g₀ : j₀ ⟶ j₁),
      ∀ k ∈ t, ConcreteCategory.hom ((Y'.obj j₁).val.map (homOfLE (hW k)).op)
        (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map g₀).app (op V)) b₀) = 0 := by
  classical
  induction t using Finset.induction with
  | empty => exact ⟨j₀, 𝟙 j₀, fun _ hk => absurd hk (by simp)⟩
  | @insert k₀ t₀ hk₀ ih =>
    obtain ⟨j_cur, g_cur, hg_cur⟩ := ih (fun k hk => h_ev k (Finset.mem_insert_of_mem hk))
    obtain ⟨jk₀, fk₀, hfk₀⟩ := h_ev k₀ (Finset.mem_insert_self k₀ t₀)
    let h_eq := IsFiltered.coeqHom (g_cur ≫ IsFiltered.leftToMax j_cur jk₀)
        (fk₀ ≫ IsFiltered.rightToMax j_cur jk₀)
    have heq : g_cur ≫ IsFiltered.leftToMax j_cur jk₀ ≫ h_eq =
        fk₀ ≫ IsFiltered.rightToMax j_cur jk₀ ≫ h_eq := by
      simpa only [Category.assoc] using IsFiltered.coeq_condition
        (g_cur ≫ IsFiltered.leftToMax j_cur jk₀) (fk₀ ≫ IsFiltered.rightToMax j_cur jk₀)
    refine ⟨_, g_cur ≫ IsFiltered.leftToMax j_cur jk₀ ≫ h_eq, fun k hk => ?_⟩
    rw [Finset.mem_insert] at hk; rcases hk with rfl | hk
    · rw [heq]; exact transition_preserves_zero Y' fk₀
        (IsFiltered.rightToMax j_cur jk₀ ≫ h_eq) (homOfLE (hW k)) b₀ hfk₀
    · exact transition_preserves_zero Y' g_cur
        (IsFiltered.leftToMax j_cur jk₀ ≫ h_eq) (homOfLE (hW k)) b₀ (hg_cur k hk)

/-- On a Noetherian space, the presheaf-level filtered colimit of sheaves is a sheaf.
    Proof: Noetherian compactness reduces the sheaf condition to finite covers, then
    filtered colimit merging passes from per-piece data to glued data. -/
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
    have h_ev_zero : ∀ k ∈ t, ∃ (jk : J') (fk : j₀ ⟶ jk),
        ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _) ⋙ ev (U k)).map fk)
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
      have h0 : ((CategoryTheory.forget AddCommGrpCat).mapCocone
          ((ev (U k)).mapCocone c)).ι.app j₀
          (ConcreteCategory.hom ((Y'.obj j₀).val.map (Opens.leSupr U k).op) b₀) =
        ((CategoryTheory.forget AddCommGrpCat).mapCocone
          ((ev (U k)).mapCocone c)).ι.app j₀ 0 := by
        change ConcreteCategory.hom (((ev (U k)).mapCocone c).ι.app j₀) _ =
          ConcreteCategory.hom (((ev (U k)).mapCocone c).ι.app j₀) 0
        rw [hnat_k.trans (ha k hk), map_zero]
      rw [Types.FilteredColimit.isColimit_eq_iff' hcTyp] at h0
      obtain ⟨jk, fk, hfk⟩ := h0
      exact ⟨jk, fk, by simpa [map_zero] using hfk⟩
    -- Merge via filtered_colimit_kills_all_restrictions
    obtain ⟨j₁, g₀, hg₀⟩ := filtered_colimit_kills_all_restrictions Y'
        (fun k => le_iSup U k) j₀ b₀ t (by
      intro k hk; obtain ⟨jk, fk, hfk⟩ := h_ev_zero k hk; refine ⟨jk, fk, ?_⟩
      change ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map fk).app (op (iSup U)) ≫
        ((Y' ⋙ sheafToPresheaf _ _).obj jk).map (Opens.leSupr U k).op) b₀ = 0
      rw [← ((Y' ⋙ sheafToPresheaf _ _).map fk).naturality (Opens.leSupr U k).op]; exact hfk)
    rw [← hb₀]; change ConcreteCategory.hom ((c.ι.app j₀).app (op (iSup U))) b₀ = 0
    conv_lhs => rw [show (c.ι.app j₀).app (op (iSup U)) =
        ((Y' ⋙ sheafToPresheaf _ _).map g₀).app (op (iSup U)) ≫
        (c.ι.app j₁).app (op (iSup U)) from by
      simpa [Functor.const_obj_map] using
        (congrArg (fun α => NatTrans.app α (op (iSup U))) (c.ι.naturality g₀)).symm]
    change ConcreteCategory.hom ((c.ι.app j₁).app (op (iSup U)))
      (ConcreteCategory.hom (((Y' ⋙ sheafToPresheaf _ _).map g₀).app (op (iSup U))) b₀) = 0
    rw [sheaf_section_zero_of_zero_on_finite_cover (Y'.obj j₁) U t hsup_le _ hg₀, map_zero]
  -- Existence: construct a gluing section
  classical
  choose j_all x_all hx_all using fun k =>
    Concrete.isColimit_exists_rep _ (hcV (U k)) (sf k)
  -- Merge j_all k (k ∈ t) to common index
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
    change ConcreteCategory.hom ((((Y' ⋙ sheafToPresheaf _ _).map (g₀ k hk)).app (op (U k))) ≫
      (c.ι.app j₀).app (op (U k))) (x_all k) = sf k
    rw [show ((Y' ⋙ sheafToPresheaf _ _).map (g₀ k hk)).app (op (U k)) ≫
        (c.ι.app j₀).app (op (U k)) = (c.ι.app (j_all k)).app (op (U k)) from by
      simpa using congrArg (fun α => NatTrans.app α (op (U k))) (c.ι.naturality (g₀ k hk))]
    exact hx_all k
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
      let h_coeq := IsFiltered.coeqHom (g_cur ≫ IsFiltered.leftToMax j_cur j_new)
          (f_new ≫ IsFiltered.rightToMax j_cur j_new)
      have heq : g_cur ≫ IsFiltered.leftToMax j_cur j_new ≫ h_coeq =
          f_new ≫ IsFiltered.rightToMax j_cur j_new ≫ h_coeq := by
        simpa only [Category.assoc] using IsFiltered.coeq_condition
          (g_cur ≫ IsFiltered.leftToMax j_cur j_new)
          (f_new ≫ IsFiltered.rightToMax j_cur j_new)
      refine ⟨_, g_cur ≫ IsFiltered.leftToMax j_cur j_new ≫ h_coeq, fun p hp => ?_⟩
      rw [Finset.mem_insert] at hp; rcases hp with rfl | hp
      · rw [heq]; exact transition_preserves_compat Y' f_new
          (IsFiltered.rightToMax j_cur j_new ≫ h_coeq) _ _ hf_new
      · exact transition_preserves_compat Y' g_cur
          (IsFiltered.leftToMax j_cur j_new ≫ h_coeq) _ _ (hg_cur p hp)
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
    simp only [Functor.const_obj_map, NatTrans.comp_app] at hfac
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
      rw [← hnat']; exact hfk.trans (map_zero _)
    -- Merge all to common index
    obtain ⟨j₃, g₃, hg₃⟩ := filtered_colimit_kills_all_restrictions Y'
      (fun k => inf_le_left (a := U i) (b := U k)) j₂ d₀ t h_ev_d
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
      simpa [Functor.const_obj_map] using this.symm
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
noncomputable def createsFilteredColimit
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) :
    CreatesColimit Y' (sheafToPresheaf _ _) :=
  Sheaf.createsColimitOfIsSheaf Y' (fun c hc => isSheaf_presheaf_filtered_colimit Y' c hc)

/-! ### Filtered colimits of flasque sheaves

On a Noetherian topological space, filtered colimits of flasque sheaves are flasque.
This is because `sheafToPresheaf` creates filtered colimits (presheaf colimits of sheaves
are already sheaves on Noetherian spaces), so restrictions of the colimit are colimits of
per-piece restrictions. Filtered colimits in `AddCommGrpCat` preserve surjections, and
flasque means all restrictions are surjective.

This replaces the result that filtered colimits of injectives are injective for our
purposes: we only need `H^n(colim I_j) = 0` for injective `I_j`, and `FlasqueVanishing`
gives this since injective sheaves are flasque (`isFlasque_of_injective`). -/

/-- Filtered colimits of flasque sheaves on Noetherian spaces are flasque. -/
theorem isFlasque_filtered_colimit
    {X : TopCat.{u}} [NoetherianSpace X]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (hFlasque : ∀ j, IsFlasqueSheaf (F.obj j))
    {c : Cocone F} (hc : IsColimit c) :
    IsFlasqueSheaf c.pt := by
  constructor; intro U V i
  rw [AddCommGrpCat.epi_iff_surjective]
  intro b; haveI := createsFilteredColimit F
  have hc_psh := isColimitOfPreserves (sheafToPresheaf _ _) hc
  have hc_U := isColimitOfPreserves
    ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)) hc_psh
  obtain ⟨j₀, b₀, hb₀⟩ := Concrete.isColimit_exists_rep _ hc_U b
  obtain ⟨a₀, ha₀⟩ := (AddCommGrpCat.epi_iff_surjective _).mp ((hFlasque j₀).epi_map i) b₀
  refine ⟨ConcreteCategory.hom ((c.ι.app j₀).val.app (op V)) a₀, ?_⟩
  rw [show ConcreteCategory.hom (c.pt.val.map i.op)
      (ConcreteCategory.hom ((c.ι.app j₀).val.app (op V)) a₀) =
    ConcreteCategory.hom ((c.ι.app j₀).val.app (op U))
      (ConcreteCategory.hom ((F.obj j₀).val.map i.op) a₀) from
    congrFun (congrArg DFunLike.coe
      (congrArg ConcreteCategory.hom ((c.ι.app j₀).val.naturality i.op).symm)) a₀,
    ha₀]; exact hb₀
