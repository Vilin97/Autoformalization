import Aristotle.GrothendieckVanishing.main.CohomologyAPI

/-!
  # General filtered-colimit infrastructure for presheaves

  This file contains presheaf-level filtered-colimit helpers that do not use
  Noetherian hypotheses: finite-cover separation, eventual vanishing, compatible
  representative extraction, and finite-subcover gluing in cocone points.
-/

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite TopCat

/-- Zero is preserved under filtered transitions: if restricting a transition to an open
    gives 0, then restricting any further transition also gives 0. -/
lemma transition_preserves_zero
    {X : TopCat.{u}} {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    {j₀ j j' : J'} (f : j₀ ⟶ j) (g : j ⟶ j')
    {U V : Opens X} (φ : U ⟶ V)
    (b₀ : ToType ((Y'.obj j₀).obj (op V)))
    (h : ConcreteCategory.hom ((Y'.obj j).map φ.op)
      (ConcreteCategory.hom ((Y'.map f).app (op V)) b₀) = 0) :
    ConcreteCategory.hom ((Y'.obj j').map φ.op)
      (ConcreteCategory.hom ((Y'.map (f ≫ g)).app (op V)) b₀) = 0 := by
  let α := Y'.map g
  change ConcreteCategory.hom ((Y'.map (f ≫ g)).app (op V) ≫
    (Y'.obj j').map φ.op) b₀ = 0
  rw [Y'.map_comp, NatTrans.comp_app, Category.assoc,
    show α.app (op V) ≫ (Y'.obj j').map φ.op =
      (Y'.obj j).map φ.op ≫ α.app (op U) from (α.naturality φ.op).symm,
    ← Category.assoc]
  simp only [ConcreteCategory.comp_apply]
  exact (congr_arg (ConcreteCategory.hom (α.app (op U))) h).trans (map_zero _)

/-- Pairwise compatibility is preserved under filtered transitions. -/
lemma transition_preserves_compat
    {X : TopCat.{u}} {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    {j₀ j j' : J'} (f : j₀ ⟶ j) (g : j ⟶ j')
    {U V : Opens X} (a : ToType ((Y'.obj j₀).obj (op U)))
    (b : ToType ((Y'.obj j₀).obj (op V)))
    (h : ConcreteCategory.hom ((Y'.obj j).map (Opens.infLELeft U V).op)
      (ConcreteCategory.hom ((Y'.map f).app (op U)) a) =
     ConcreteCategory.hom ((Y'.obj j).map (Opens.infLERight U V).op)
      (ConcreteCategory.hom ((Y'.map f).app (op V)) b)) :
    ConcreteCategory.hom ((Y'.obj j').map (Opens.infLELeft U V).op)
      (ConcreteCategory.hom ((Y'.map (f ≫ g)).app (op U)) a) =
    ConcreteCategory.hom ((Y'.obj j').map (Opens.infLERight U V).op)
      (ConcreteCategory.hom ((Y'.map (f ≫ g)).app (op V)) b) := by
  let β := Y'.map g
  -- Factor F(f ≫ g) = F(f) ≫ β; for each side use naturality: β ≫ res = res ≫ β
  suffices ∀ {W : Opens X} (φ : U ⊓ V ⟶ W) (c₀ : ToType ((Y'.obj j₀).obj (op W))),
      ConcreteCategory.hom ((Y'.obj j').map φ.op)
        (ConcreteCategory.hom ((Y'.map (f ≫ g)).app (op W)) c₀) =
      ConcreteCategory.hom (β.app (op (U ⊓ V)))
        (ConcreteCategory.hom ((Y'.obj j).map φ.op)
          (ConcreteCategory.hom ((Y'.map f).app (op W)) c₀)) by
    rw [this (Opens.infLELeft U V) a, this (Opens.infLERight U V) b, h]
  intro W φ c₀
  simp only [Functor.map_comp, NatTrans.comp_app, AddCommGrpCat.hom_comp,
    AddMonoidHom.coe_comp, Function.comp_apply]
  change ConcreteCategory.hom (β.app (op W) ≫ (Y'.obj j').map φ.op) _ =
    ConcreteCategory.hom ((Y'.obj j).map φ.op ≫ β.app (op (U ⊓ V))) _
  rw [show β.app (op W) ≫ (Y'.obj j').map φ.op =
    (Y'.obj j).map φ.op ≫ β.app (op (U ⊓ V))
    from (β.naturality φ.op).symm]

/-- A section of a sheaf that restricts to 0 on a finite open cover is 0. -/
theorem sheaf_section_zero_of_zero_on_cover
    {X : TopCat.{u}} {F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (hF : TopCat.Presheaf.IsSheaf F)
    {ι : Type u} {V : Opens X} {W : ι → Opens X} (hW : ∀ k, W k ≤ V)
    {t : Finset ι} (hcov : V ≤ ⨆ k ∈ t, W k)
    (b : ToType (F.obj (op V)))
    (hzero : ∀ k ∈ t, ConcreteCategory.hom (F.map (homOfLE (hW k)).op) b = 0) :
    b = 0 :=
  hF.section_ext (s := b) (t := 0) fun x hx => by
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (hcov hx)
    obtain ⟨hkt, hxk⟩ := Opens.mem_iSup.mp hk
    exact ⟨W k, hW k, hxk, (hzero k hkt).trans (map_zero _).symm⟩

/-- Merge finitely many eventually-zero restrictions into a common index. -/
theorem filtered_colimit_kills_all_restrictions
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    {X : TopCat.{u}} (Y' : J' ⥤ (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    {ι : Type u} {V : Opens X} {W : ι → Opens X} (hW : ∀ k, W k ≤ V) (j₀ : J')
    (b₀ : ToType ((Y'.obj j₀).obj (op V)))
    (t : Finset ι)
    (h_ev : ∀ k ∈ t, ∃ (jk : J') (fk : j₀ ⟶ jk),
      ConcreteCategory.hom ((Y'.obj jk).map (homOfLE (hW k)).op)
        (ConcreteCategory.hom ((Y'.map fk).app (op V)) b₀) = 0) :
    ∃ (j₁ : J') (g₀ : j₀ ⟶ j₁),
      ∀ k ∈ t, ConcreteCategory.hom ((Y'.obj j₁).map (homOfLE (hW k)).op)
        (ConcreteCategory.hom ((Y'.map g₀).app (op V)) b₀) = 0 := by
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

/-- If a representative of a colimit section restricts to zero in the cocone point,
    then after some filtered transition its restriction is already zero. -/
theorem filtered_colimit_restriction_eventually_zero_of_zero
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    {c : Cocone Y'} (hc : IsColimit c)
    {U V : Opens X} (φ : U ⟶ V)
    (a : ToType (c.pt.obj (op V)))
    {j₀ : J'} (b₀ : ToType ((Y'.obj j₀).obj (op V)))
    (hb₀ : ConcreteCategory.hom ((c.ι.app j₀).app (op V)) b₀ = a)
    (ha : c.pt.map φ.op a = 0) :
    ∃ (j' : J') (f : j₀ ⟶ j'),
      ConcreteCategory.hom ((Y'.obj j').map φ.op)
        (ConcreteCategory.hom ((Y'.map f).app (op V)) b₀) = 0 := by
  let ev V := (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V)
  have hcU : IsColimit ((ev U).mapCocone c) := isColimitOfPreserves (ev U) hc
  have hcTyp := isColimitOfPreserves (CategoryTheory.forget AddCommGrpCat) hcU
  have hnat : ConcreteCategory.hom (((ev U).mapCocone c).ι.app j₀)
      (ConcreteCategory.hom ((Y'.obj j₀).map φ.op) b₀) =
    ConcreteCategory.hom (c.pt.map φ.op) a := by
    simp only [Functor.mapCocone_ι_app]
    rw [← hb₀]
    change ConcreteCategory.hom
      ((Y'.obj j₀).map _ ≫ (c.ι.app j₀).app _) b₀ =
      ConcreteCategory.hom
      ((c.ι.app j₀).app _ ≫ (((Functor.const J').obj c.pt).obj j₀).map _) b₀
    rw [(c.ι.app j₀).naturality φ.op]
  have h0 : ((CategoryTheory.forget AddCommGrpCat).mapCocone
      ((ev U).mapCocone c)).ι.app j₀
      (ConcreteCategory.hom ((Y'.obj j₀).map φ.op) b₀) =
    ((CategoryTheory.forget AddCommGrpCat).mapCocone
      ((ev U).mapCocone c)).ι.app j₀ 0 := by
    change ConcreteCategory.hom (((ev U).mapCocone c).ι.app j₀) _ =
      ConcreteCategory.hom (((ev U).mapCocone c).ι.app j₀) 0
    rw [hnat, ha, map_zero]
  rw [Types.FilteredColimit.isColimit_eq_iff' hcTyp] at h0
  obtain ⟨j', f, hf⟩ := h0
  refine ⟨j', f, ?_⟩
  have hf' : ConcreteCategory.hom (((Y' ⋙ ev U).map f))
      (ConcreteCategory.hom ((Y'.obj j₀).map φ.op) b₀) = 0 := by
    simpa [map_zero] using hf
  change ConcreteCategory.hom (((Y'.map f).app (op V)) ≫ (Y'.obj j').map φ.op) b₀ = 0
  rw [show ((Y'.map f).app (op V)) ≫ (Y'.obj j').map φ.op =
    (Y'.obj j₀).map φ.op ≫ (Y'.map f).app (op U)
    from ((Y'.map f).naturality φ.op).symm]
  change ConcreteCategory.hom ((Y'.map f).app (op U))
    (ConcreteCategory.hom ((Y'.obj j₀).map φ.op) b₀) = 0
  simpa [ev] using hf'

/-- A section of a filtered colimit that restricts to zero on a finite open cover is zero.
    Combines representative extraction, per-element eventual vanishing,
    merging to a common index, and sheaf separation. -/
theorem colimit_section_zero_of_zero_on_cover
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (hY : ∀ j, TopCat.Presheaf.IsSheaf (Y'.obj j))
    {c : Cocone Y'} (hc : IsColimit c)
    {ι : Type u} {V : Opens X} {W : ι → Opens X} (hW : ∀ k, W k ≤ V)
    {t : Finset ι} (hcov : V ≤ ⨆ k ∈ t, W k)
    (a : ToType (c.pt.obj (op V)))
    (ha : ∀ k ∈ t, c.pt.map (homOfLE (hW k)).op a = 0) :
    a = 0 := by
  let ev V := (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V)
  have hcV : ∀ V, IsColimit ((ev V).mapCocone c) := fun V => isColimitOfPreserves (ev V) hc
  obtain ⟨j₀, b₀, hb₀⟩ := Concrete.isColimit_exists_rep _ (hcV V) a
  -- For each k ∈ t: ι(b₀|_{W_k}) = a|_{W_k} = 0, so eventually zero
  have h_ev_zero : ∀ k ∈ t, ∃ (jk : J') (fk : j₀ ⟶ jk),
      ConcreteCategory.hom ((Y'.obj jk).map (homOfLE (hW k)).op)
        (ConcreteCategory.hom ((Y'.map fk).app (op V)) b₀) = 0 := by
    intro k hk
    exact filtered_colimit_restriction_eventually_zero_of_zero
      Y' hc (homOfLE (hW k)) a b₀ hb₀ (ha k hk)
  -- Merge via filtered_colimit_kills_all_restrictions
  obtain ⟨j₁, g₀, hg₀⟩ := filtered_colimit_kills_all_restrictions Y' hW j₀ b₀ t h_ev_zero
  -- Conclude: the transition is zero by sheaf separation, hence a = 0
  rw [← hb₀]; change ConcreteCategory.hom ((c.ι.app j₀).app (op V)) b₀ = 0
  have hnat : (c.ι.app j₀).app (op V) =
      (Y'.map g₀).app (op V) ≫
      (c.ι.app j₁).app (op V) := by
    simpa [Functor.const_obj_map] using
      (congrArg (fun α => NatTrans.app α (op V)) (c.ι.naturality g₀)).symm
  rw [hnat]
  rw [ConcreteCategory.comp_apply,
    sheaf_section_zero_of_zero_on_cover (hY j₁) hW hcov _ hg₀, map_zero]

/-- A finite compatible family in a filtered colimit admits representatives at one filtered
    stage that are pairwise compatible on the chosen finite subfamily. -/
theorem filtered_colimit_exists_compatible_representatives
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (P : J' ⥤ (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    {c : Cocone P} (hc : IsColimit c)
    {ι : Type u} (U : ι → Opens X)
    (sf : ∀ i, ToType (c.pt.obj (op (U i))))
    (hcompat : Presheaf.IsCompatible c.pt U sf)
    {t : Finset ι} :
    ∃ (j₁ : J')
      (x'' : ∀ k : ↥t, ToType ((P.obj j₁).obj (op (U k.1)))),
      Presheaf.IsCompatible (P.obj j₁) (fun k : ↥t => U k.1) x'' ∧
      (∀ k : ↥t, ConcreteCategory.hom ((c.ι.app j₁).app (op (U k.1))) (x'' k) = sf k.1) := by
  classical
  let ev V := (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V)
  have hcV : ∀ V, IsColimit ((ev V).mapCocone c) := fun V => isColimitOfPreserves (ev V) hc
  choose j_all x_all hx_all using fun k =>
    Concrete.isColimit_exists_rep _ (hcV (U k)) (sf k)
  obtain ⟨j₀, hj₀⟩ := IsFiltered.sup_objs_exists (t.image j_all)
  let g₀ : ∀ k, k ∈ t → (j_all k ⟶ j₀) :=
    fun k hk => (hj₀ (Finset.mem_image_of_mem j_all hk)).some
  let x' : ∀ k, k ∈ t → ToType ((P.obj j₀).obj (op (U k))) :=
    fun k hk => ConcreteCategory.hom
      ((P.map (g₀ k hk)).app (op (U k))) (x_all k)
  have hx' : ∀ k (hk : k ∈ t),
      ConcreteCategory.hom ((c.ι.app j₀).app (op (U k))) (x' k hk) = sf k := by
    intro k hk
    change ConcreteCategory.hom (((P.map (g₀ k hk)).app (op (U k))) ≫
      (c.ι.app j₀).app (op (U k))) (x_all k) = sf k
    convert hx_all k using 1
    simp [Functor.const_obj_map, ev]
  obtain ⟨j₁, g₁, hg₁⟩ : ∃ (j₁ : J') (g₁ : j₀ ⟶ j₁),
      ∀ (k : ι) (hk : k ∈ t) (l : ι) (hl : l ∈ t),
        ConcreteCategory.hom ((P.obj j₁).map (Opens.infLELeft (U k) (U l)).op)
          (ConcreteCategory.hom ((P.map g₁).app (op (U k))) (x' k hk)) =
        ConcreteCategory.hom ((P.obj j₁).map (Opens.infLERight (U k) (U l)).op)
          (ConcreteCategory.hom ((P.map g₁).app (op (U l))) (x' l hl)) := by
    have h_ev_compat : ∀ (k : ι) (hk : k ∈ t) (l : ι) (hl : l ∈ t),
        ∃ (j' : J') (f : j₀ ⟶ j'),
        ConcreteCategory.hom ((P.obj j').map (Opens.infLELeft (U k) (U l)).op)
          (ConcreteCategory.hom ((P.map f).app (op (U k))) (x' k hk)) =
        ConcreteCategory.hom ((P.obj j').map (Opens.infLERight (U k) (U l)).op)
          (ConcreteCategory.hom ((P.map f).app (op (U l))) (x' l hl)) := by
      intro k hk l hl
      have h_eq : ((CategoryTheory.forget AddCommGrpCat).mapCocone
          ((ev (U k ⊓ U l)).mapCocone c)).ι.app j₀
          (ConcreteCategory.hom ((P.obj j₀).map (Opens.infLELeft (U k) (U l)).op) (x' k hk)) =
        ((CategoryTheory.forget AddCommGrpCat).mapCocone
          ((ev (U k ⊓ U l)).mapCocone c)).ι.app j₀
          (ConcreteCategory.hom ((P.obj j₀).map (Opens.infLERight (U k) (U l)).op) (x' l hl)) := by
        change ConcreteCategory.hom (((ev (U k ⊓ U l)).mapCocone c).ι.app j₀) _ =
          ConcreteCategory.hom (((ev (U k ⊓ U l)).mapCocone c).ι.app j₀) _
        have hnat_m : ∀ (m : ι) (hm : m ∈ t) (φ : U k ⊓ U l ⟶ U m),
            ConcreteCategory.hom (((ev (U k ⊓ U l)).mapCocone c).ι.app j₀)
              (ConcreteCategory.hom ((P.obj j₀).map φ.op) (x' m hm)) =
            ConcreteCategory.hom (c.pt.map φ.op) (sf m) := by
          intro m hm φ
          rw [← hx' m hm]
          change ConcreteCategory.hom
            ((P.obj j₀).map _ ≫ (c.ι.app j₀).app _) (x' m hm) =
            ConcreteCategory.hom
            ((c.ι.app j₀).app _ ≫ (((Functor.const J').obj c.pt).obj j₀).map _) (x' m hm)
          rw [(c.ι.app j₀).naturality φ.op]
        rw [hnat_m k hk (Opens.infLELeft (U k) (U l)),
            hnat_m l hl (Opens.infLERight (U k) (U l)), hcompat k l]
      rw [Types.FilteredColimit.isColimit_eq_iff'
        (isColimitOfPreserves (CategoryTheory.forget AddCommGrpCat) (hcV (U k ⊓ U l)))] at h_eq
      obtain ⟨j', f, hf⟩ := h_eq
      refine ⟨j', f, ?_⟩
      simpa [ev, AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] using hf
    suffices h : ∀ (S : Finset (ι × ι)) (hS : S ⊆ t ×ˢ t),
        ∃ (j₁ : J') (g₁ : j₀ ⟶ j₁), ∀ (p : ι × ι) (hp : p ∈ S),
          ConcreteCategory.hom ((P.obj j₁).map (Opens.infLELeft (U p.1) (U p.2)).op)
            (ConcreteCategory.hom ((P.map g₁).app (op (U p.1)))
              (x' p.1 ((Finset.mem_product.mp (hS hp)).1))) =
          ConcreteCategory.hom ((P.obj j₁).map (Opens.infLERight (U p.1) (U p.2)).op)
            (ConcreteCategory.hom ((P.map g₁).app (op (U p.2)))
              (x' p.2 ((Finset.mem_product.mp (hS hp)).2))) by
      obtain ⟨j₁, g₁, hg₁⟩ := h (t ×ˢ t) (fun _ hx => hx)
      exact ⟨j₁, g₁, fun k hk l hl =>
        hg₁ (k, l) (Finset.mem_product.mpr ⟨hk, hl⟩)⟩
    intro S hS
    induction S using Finset.induction with
    | empty => exact ⟨j₀, 𝟙 j₀, fun _ hp => absurd hp (by simp)⟩
    | @insert p₀ rest hnin ih =>
      obtain ⟨j_cur, g_cur, hg_cur⟩ := ih (fun p hp => hS (Finset.mem_insert_of_mem hp))
      obtain ⟨hp₀l, hp₀r⟩ := Finset.mem_product.mp (hS (Finset.mem_insert_self p₀ rest))
      obtain ⟨j_new, f_new, hf_new⟩ := h_ev_compat p₀.1 hp₀l p₀.2 hp₀r
      let h_coeq := IsFiltered.coeqHom (g_cur ≫ IsFiltered.leftToMax j_cur j_new)
          (f_new ≫ IsFiltered.rightToMax j_cur j_new)
      have heq : g_cur ≫ IsFiltered.leftToMax j_cur j_new ≫ h_coeq =
          f_new ≫ IsFiltered.rightToMax j_cur j_new ≫ h_coeq := by
        simpa only [Category.assoc] using IsFiltered.coeq_condition
          (g_cur ≫ IsFiltered.leftToMax j_cur j_new)
          (f_new ≫ IsFiltered.rightToMax j_cur j_new)
      refine ⟨_, g_cur ≫ IsFiltered.leftToMax j_cur j_new ≫ h_coeq, fun p hp => ?_⟩
      rw [Finset.mem_insert] at hp
      rcases hp with rfl | hp
      · rw [heq]
        exact transition_preserves_compat P f_new _ _ _ hf_new
      · exact transition_preserves_compat P g_cur _ _ _ (hg_cur p hp)
  let x'' : ∀ (k : ↥t), ToType ((P.obj j₁).obj (op (U k.1))) :=
    fun ⟨k, hk⟩ => ConcreteCategory.hom
      ((P.map g₁).app (op (U k))) (x' k hk)
  exact ⟨j₁, x'', fun ⟨k, hk⟩ ⟨l, hl⟩ => hg₁ k hk l hl, fun ⟨k, hk⟩ => by
    change ConcreteCategory.hom ((P.map g₁).app (op (U k)) ≫
      (c.ι.app j₁).app (op (U k))) (x' k hk) = sf k
    convert hx' k hk using 1
    simp [Functor.const_obj_map]⟩

/-- A compatible family on a finite subcover, represented at a single filtered index,
    glues to a section of any cocone point with the prescribed finite restrictions. -/
theorem colimit_exists_gluing_of_compatible_finite_subcover
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (P : J' ⥤ (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (hP : ∀ j, TopCat.Presheaf.IsSheaf (P.obj j))
    {c : Cocone P}
    {ι : Type u} (U : ι → Opens X)
    (sf : ∀ i, ToType (c.pt.obj (op (U i))))
    {t : Finset ι} (hsup_le : iSup U ≤ ⨆ k ∈ t, U k)
    (j₁ : J')
    (x'' : ∀ k : ↥t, ToType ((P.obj j₁).obj (op (U k.1))))
    (hx''_compat : Presheaf.IsCompatible (P.obj j₁) (fun k : ↥t => U k.1) x'')
    (hx'' : ∀ k : ↥t,
      ConcreteCategory.hom ((c.ι.app j₁).app (op (U k.1))) (x'' k) = sf k.1) :
    ∃ s : ToType (c.pt.obj (op (iSup U))),
      ∀ k, k ∈ t → c.pt.map (Opens.leSupr U k).op s = sf k := by
  let W : ↥t → Opens X := fun k => U k.1
  have hcov_W : iSup W = iSup U := by
    apply le_antisymm
    · refine iSup_le ?_
      intro k
      exact le_iSup U k.1
    · rw [show iSup W = ⨆ k ∈ t, U k from iSup_subtype (p := (· ∈ t))]
      exact hsup_le
  obtain ⟨sW, hsW, _⟩ := (hP j₁).isSheafUniqueGluing W x''
    (by simpa [W] using hx''_compat)
  let s₀ : ToType ((P.obj j₁).obj (op (iSup U))) :=
    ConcreteCategory.hom ((P.obj j₁).map (eqToHom hcov_W.symm).op) sW
  have hs₀ : ∀ k (hk : k ∈ t),
      ConcreteCategory.hom ((P.obj j₁).map (Opens.leSupr U k).op) s₀ = x'' ⟨k, hk⟩ := by
    intro k hk
    dsimp [s₀]
    rw [← ConcreteCategory.comp_apply, ← (P.obj j₁).map_comp]
    have hle_k : Opens.leSupr U k ≫ eqToHom hcov_W.symm = Opens.leSupr W ⟨k, hk⟩ := by
      simpa [W] using
        (Subsingleton.elim
          (Opens.leSupr U k ≫ eqToHom hcov_W.symm)
          (Opens.leSupr W ⟨k, hk⟩))
    rw [show (eqToHom hcov_W.symm).op ≫ (Opens.leSupr U k).op =
        (Opens.leSupr W ⟨k, hk⟩).op by
      simpa using congrArg Quiver.Hom.op hle_k]
    exact hsW ⟨k, hk⟩
  let s : ToType (c.pt.obj (op (iSup U))) :=
    ConcreteCategory.hom ((c.ι.app j₁).app (op (iSup U))) s₀
  refine ⟨s, ?_⟩
  intro k hk
  change ConcreteCategory.hom
    ((c.ι.app j₁).app (op (iSup U)) ≫ c.pt.map (Opens.leSupr U k).op) s₀ = sf k
  rw [show (c.ι.app j₁).app (op (iSup U)) ≫ c.pt.map (Opens.leSupr U k).op =
    (P.obj j₁).map (Opens.leSupr U k).op ≫ (c.ι.app j₁).app (op (U k))
    from ((c.ι.app j₁).naturality (Opens.leSupr U k).op).symm]
  change ConcreteCategory.hom ((c.ι.app j₁).app (op (U k)))
    (ConcreteCategory.hom ((P.obj j₁).map (Opens.leSupr U k).op) s₀) = sf k
  rw [hs₀ k hk]
  exact hx'' ⟨k, hk⟩

/-- If a section on `iSup U` agrees with a compatible family on a finite subcover,
    then it restricts to that family on every `U i`. -/
theorem colimit_restrict_eq_of_eq_on_finite_subcover
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (P : J' ⥤ (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (hP : ∀ j, TopCat.Presheaf.IsSheaf (P.obj j))
    {c : Cocone P} (hc : IsColimit c)
    {ι : Type u} (U : ι → Opens X)
    (sf : ∀ i, ToType (c.pt.obj (op (U i))))
    (hcompat : Presheaf.IsCompatible c.pt U sf)
    {t : Finset ι} (hsup_le : iSup U ≤ ⨆ k ∈ t, U k)
    (s : ToType (c.pt.obj (op (iSup U))))
    (hs_k : ∀ k, k ∈ t → c.pt.map (Opens.leSupr U k).op s = sf k) :
    ∀ i, c.pt.map (Opens.leSupr U i).op s = sf i := by
  intro i
  apply sub_eq_zero.mp
  refine colimit_section_zero_of_zero_on_cover
    P hP hc
    (fun k => inf_le_left (a := U i) (b := U k))
    (t := t)
    ?_
    (c.pt.map (Opens.leSupr U i).op s - sf i)
    ?_
  · rw [SetLike.le_def]
    intro x hx
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (hsup_le (le_iSup U i hx))
    obtain ⟨hkt, hxk⟩ := Opens.mem_iSup.mp hk
    exact Opens.mem_iSup.mpr ⟨k, Opens.mem_iSup.mpr ⟨hkt, ⟨hx, hxk⟩⟩⟩
  · intro k hk
    rw [map_sub, sub_eq_zero]
    trans (ConcreteCategory.hom (c.pt.map (Opens.infLERight (U i) (U k)).op) (sf k))
    · rw [← hs_k k hk, ← ConcreteCategory.comp_apply, ← c.pt.map_comp,
          ← ConcreteCategory.comp_apply, ← c.pt.map_comp]
      congr 1
    · exact (hcompat i k).symm

/-- A compatible family in a filtered colimit admits a unique gluing once the total open
    is dominated by a finite subcover. -/
theorem colimit_existsUnique_gluing_of_compatible_finite_subcover
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (P : J' ⥤ (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (hP : ∀ j, TopCat.Presheaf.IsSheaf (P.obj j))
    {c : Cocone P} (hc : IsColimit c)
    {ι : Type u} (U : ι → Opens X)
    (sf : ∀ i, ToType (c.pt.obj (op (U i))))
    (hcompat : Presheaf.IsCompatible c.pt U sf)
    {t : Finset ι} (hsup_le : iSup U ≤ ⨆ k ∈ t, U k) :
    ∃! s : ToType (c.pt.obj (op (iSup U))), Presheaf.IsGluing c.pt U sf s := by
  obtain ⟨j₁, x'', hx''_compat, hx''⟩ := filtered_colimit_exists_compatible_representatives
    P hc U sf hcompat
  obtain ⟨s, hs_k⟩ := colimit_exists_gluing_of_compatible_finite_subcover
    P hP U sf hsup_le j₁ x'' hx''_compat hx''
  refine ⟨s, ?_, ?_⟩
  · intro i
    exact colimit_restrict_eq_of_eq_on_finite_subcover
      P hP hc U sf hcompat hsup_le s hs_k i
  · intro s' hs'
    apply sub_eq_zero.mp
    exact colimit_section_zero_of_zero_on_cover
      P hP hc
      (fun k => le_iSup U k) hsup_le (s' - s) (fun k hk => by
        show c.pt.map (Opens.leSupr U k).op (s' - s) = 0
        rw [map_sub, sub_eq_zero]
        exact (hs' k).trans (hs_k k hk).symm)
