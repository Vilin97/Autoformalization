import Aristotle.GrothendieckVanishing.main.CohomologyAPI
import Aristotle.GrothendieckVanishing.main.ClosedImmersionCohomology
import Aristotle.GrothendieckVanishing.main.ZeroOutsideFinset

/-!
  # Presheaf filtered colimit is a sheaf on Noetherian spaces

  Split from FiniteGeneratorReduction.lean. Contains:

  ## Presheaf-level helpers (work for any `J' ⥤ (Opens X)ᵒᵖ ⥤ AddCommGrpCat`)
  - `transition_preserves_zero`: zero is preserved under filtered transitions
  - `transition_preserves_compat`: pairwise compatibility is preserved under filtered transitions
  - `sheaf_section_zero_of_zero_on_cover`: sections vanishing on finite cover vanish
  - `filtered_colimit_kills_all_restrictions`: merge finitely many eventually-zero transitions
  - `filtered_colimit_exists_compatible_representatives`: merge a finite compatible family
    to one filtered stage of pairwise-compatible representatives
  - `colimit_section_zero_of_zero_on_cover`: colimit section vanishing on finite cover is zero
    (no `NoetherianSpace` hypothesis needed)

  ## Sheaf-level results
  - `isSheaf_presheaf_filtered_colimit`: presheaf-level filtered colimit of sheaves is a sheaf
    on Noetherian spaces
  - `createsFilteredColimit`: `sheafToPresheaf` creates filtered colimits
  - `isFlasque_filtered_colimit`: filtered colimits of flasque sheaves are flasque

  ## Sheaf cohomology and filtered colimits
  - `sheafH_preserves_filtered_colimits`: the canonical comparison
    `colim H^n(F_j) ≅ H^n(colim F_j)` on filtered diagrams
  - `sheafH_filtered_colimit_surj`: every element of `H^n(colim F_j)` comes from some
    `H^n(F_j)` via the canonical map
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
    dsimp [x']
    change ConcreteCategory.hom (((P.map (g₀ k hk)).app (op (U k))) ≫
      (c.ι.app j₀).app (op (U k))) (x_all k) = sf k
    rw [show (P.map (g₀ k hk)).app (op (U k)) ≫
        (c.ι.app j₀).app (op (U k)) = (c.ι.app (j_all k)).app (op (U k)) from by
      simpa [Functor.const_obj_map] using
        congrArg (fun α => NatTrans.app α (op (U k))) (c.ι.naturality (g₀ k hk))]
    exact hx_all k
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
      have hcTyp := isColimitOfPreserves (CategoryTheory.forget AddCommGrpCat) (hcV (U k ⊓ U l))
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
          simp only [Functor.mapCocone_ι_app]
          rw [← hx' m hm]
          change ConcreteCategory.hom
            ((P.obj j₀).map _ ≫ (c.ι.app j₀).app _) (x' m hm) =
            ConcreteCategory.hom
            ((c.ι.app j₀).app _ ≫ (((Functor.const J').obj c.pt).obj j₀).map _) (x' m hm)
          rw [(c.ι.app j₀).naturality φ.op]
        rw [hnat_m k hk (Opens.infLELeft (U k) (U l)),
            hnat_m l hl (Opens.infLERight (U k) (U l))]
        exact hcompat k l
      rw [Types.FilteredColimit.isColimit_eq_iff' hcTyp] at h_eq
      obtain ⟨j', f, hf⟩ := h_eq
      refine ⟨j', f, ?_⟩
      let α := P.map f
      change ConcreteCategory.hom
        (α.app (op (U k)) ≫ (P.obj j').map (Opens.infLELeft (U k) (U l)).op) (x' k hk) =
        ConcreteCategory.hom
        (α.app (op (U l)) ≫ (P.obj j').map (Opens.infLERight (U k) (U l)).op) (x' l hl)
      rw [show α.app (op (U k)) ≫ (P.obj j').map (Opens.infLELeft (U k) (U l)).op =
        (P.obj j₀).map (Opens.infLELeft (U k) (U l)).op ≫ α.app (op (U k ⊓ U l))
        from (α.naturality (Opens.infLELeft (U k) (U l)).op).symm,
        show α.app (op (U l)) ≫ (P.obj j').map (Opens.infLERight (U k) (U l)).op =
        (P.obj j₀).map (Opens.infLERight (U k) (U l)).op ≫ α.app (op (U k ⊓ U l))
        from (α.naturality (Opens.infLERight (U k) (U l)).op).symm]
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply]
      exact hf
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
      have hp₀t := hS (Finset.mem_insert_self p₀ rest)
      obtain ⟨j_new, f_new, hf_new⟩ := h_ev_compat p₀.1
        (Finset.mem_product.mp hp₀t).1 p₀.2 (Finset.mem_product.mp hp₀t).2
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
        exact transition_preserves_compat P f_new
          (IsFiltered.rightToMax j_cur j_new ≫ h_coeq) _ _ hf_new
      · exact transition_preserves_compat P g_cur
          (IsFiltered.leftToMax j_cur j_new ≫ h_coeq) _ _ (hg_cur p hp)
  let x'' : ∀ (k : ↥t), ToType ((P.obj j₁).obj (op (U k.1))) :=
    fun ⟨k, hk⟩ => ConcreteCategory.hom
      ((P.map g₁).app (op (U k))) (x' k hk)
  have hx''_compat :
      Presheaf.IsCompatible (P.obj j₁) (fun k : ↥t => U k.1) x'' :=
    fun ⟨k, hk⟩ ⟨l, hl⟩ => hg₁ k hk l hl
  have hx'' : ∀ k : ↥t,
      ConcreteCategory.hom ((c.ι.app j₁).app (op (U k.1))) (x'' k) = sf k.1 := by
    intro k
    rcases k with ⟨k, hk⟩
    dsimp [x'']
    change ConcreteCategory.hom ((P.map g₁).app (op (U k)) ≫
      (c.ι.app j₁).app (op (U k))) (x' k hk) = sf k
    have := congrArg (fun α => NatTrans.app α (op (U k))) (c.ι.naturality g₁)
    simp only [Functor.const_obj_map, NatTrans.comp_app] at this
    rw [this]
    exact hx' k hk
  exact ⟨j₁, x'', hx''_compat, hx''⟩

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
  have hsep : ∀ (a : ToType (c.pt.obj (op (iSup U)))),
      (∀ k ∈ t, c.pt.map (Opens.leSupr U k).op a = 0) → a = 0 :=
    fun a ha => colimit_section_zero_of_zero_on_cover
      P hP hc
      (fun k => le_iSup U k) hsup_le a ha
  obtain ⟨j₁, x'', hx''_compat, hx''⟩ := filtered_colimit_exists_compatible_representatives
    P hc U sf hcompat
  obtain ⟨s, hs_k⟩ := colimit_exists_gluing_of_compatible_finite_subcover
    P hP U sf hsup_le j₁ x'' hx''_compat hx''
  refine ⟨s, fun i => ?_, fun s' hs' => ?_⟩
  · exact colimit_restrict_eq_of_eq_on_finite_subcover
      P hP hc U sf hcompat hsup_le s hs_k i
  · have h0 : s' - s = 0 := hsep (s' - s) (fun k hk => by
      show c.pt.map (Opens.leSupr U k).op (s' - s) = 0
      rw [map_sub, sub_eq_zero]
      exact (hs' k).trans (hs_k k hk).symm)
    rwa [sub_eq_zero] at h0

/-- On a Noetherian space, the presheaf-level filtered colimit of sheaves is a sheaf.
    Proof: Noetherian compactness reduces the sheaf condition to finite covers, then
    filtered colimit merging passes from per-piece data to glued data. -/
theorem isSheaf_presheaf_filtered_colimit
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (c : Cocone (Y' ⋙ sheafToPresheaf _ _)) (hc : IsColimit c) :
    TopCat.Presheaf.IsSheaf c.pt := by
  simpa using isSheaf_of_isColimit_of_isSheaf
    (P := Y' ⋙ sheafToPresheaf _ _)
    (hP := fun j => (Y'.obj j).cond)
    (c := c) (hc := hc)

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

/-! ### Sheaf cohomology and filtered colimits

The formal comparison map
`sheafH_filtered_colimit_comparison : colim H^n(F_j) ⟶ H^n(colim F_j)`
is defined for any small diagram and cocone by `colimit.desc`.

The genuinely geometric input starts afterwards:
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
  { desc := fun s => cokernel.desc ι' (injColim.desc ⟨s.pt,
      { app := fun j => cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ s.ι.app j
        naturality := fun j j' a => by
          dsimp
          have hdesc :
              cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫
                  (sheafH_filtered_colimit_succ_quotient Y').map a =
                (sheafH_filtered_colimit_succ_Inj Y').map a ≫
                  cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j') := by
            simp [sheafH_filtered_colimit_succ_quotient, Category.assoc]
          have hdesc_assoc :
              ((sheafH_filtered_colimit_succ_Inj Y').map a ≫
                  cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j')) ≫
                s.ι.app j' =
              (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫
                  (sheafH_filtered_colimit_succ_quotient Y').map a) ≫
                s.ι.app j' := by
            simpa [Category.assoc] using
              congrArg (fun m => m ≫ s.ι.app j') hdesc.symm
          have hdesc_assoc' :
              (sheafH_filtered_colimit_succ_Inj Y').map a ≫
                  cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j') ≫
                s.ι.app j' =
              (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫
                  (sheafH_filtered_colimit_succ_quotient Y').map a) ≫
                s.ι.app j' := by
            simpa [Category.assoc] using hdesc_assoc
          rw [hdesc_assoc', Category.assoc, s.w]
          simp }⟩) (hc'.hom_ext fun j => by
      let lifted : Cocone Inj := ⟨s.pt,
        { app := fun j => cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ s.ι.app j
          naturality := fun j j' a => by
            dsimp
            have hdesc :
                cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫
                    (sheafH_filtered_colimit_succ_quotient Y').map a =
                  (sheafH_filtered_colimit_succ_Inj Y').map a ≫
                    cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j') := by
              simp [sheafH_filtered_colimit_succ_quotient]
            have hdesc_assoc :
                ((sheafH_filtered_colimit_succ_Inj Y').map a ≫
                    cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j')) ≫
                  s.ι.app j' =
                (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫
                    (sheafH_filtered_colimit_succ_quotient Y').map a) ≫
                  s.ι.app j' := by
              simpa [Category.assoc] using
                congrArg (fun m => m ≫ s.ι.app j') hdesc.symm
            have hdesc_assoc' :
                (sheafH_filtered_colimit_succ_Inj Y').map a ≫
                    cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j') ≫
                  s.ι.app j' =
                (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫
                    (sheafH_filtered_colimit_succ_quotient Y').map a) ≫
                  s.ι.app j' := by
              simpa [Category.assoc] using hdesc_assoc
            rw [hdesc_assoc', Category.assoc, s.w]
            simp }⟩
      have hfac_lifted :
          injCocone.ι.app j ≫ injColim.desc lifted =
            cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ s.ι.app j := by
        simpa [lifted, injCocone] using injColim.fac lifted j
      rw [comp_zero]
      conv_lhs =>
        rw [← Category.assoc, sheafH_filtered_colimit_succ_iota_fac Y' c' hc' j, Category.assoc]
      rw [hfac_lifted, ← Category.assoc, cokernel.condition, zero_comp])
    fac := fun s j => (cancel_epi (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j))).mp (by
      let lifted : Cocone Inj := ⟨s.pt,
        { app := fun j => cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ s.ι.app j
          naturality := fun j j' a => by
            dsimp
            have hdesc :
                cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫
                    (sheafH_filtered_colimit_succ_quotient Y').map a =
                  (sheafH_filtered_colimit_succ_Inj Y').map a ≫
                    cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j') := by
              simp [sheafH_filtered_colimit_succ_quotient]
            have hdesc_assoc :
                ((sheafH_filtered_colimit_succ_Inj Y').map a ≫
                    cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j')) ≫
                  s.ι.app j' =
                (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫
                    (sheafH_filtered_colimit_succ_quotient Y').map a) ≫
                  s.ι.app j' := by
              simpa [Category.assoc] using
                congrArg (fun m => m ≫ s.ι.app j') hdesc.symm
            have hdesc_assoc' :
                (sheafH_filtered_colimit_succ_Inj Y').map a ≫
                    cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j') ≫
                  s.ι.app j' =
                (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫
                    (sheafH_filtered_colimit_succ_quotient Y').map a) ≫
                  s.ι.app j' := by
              simpa [Category.assoc] using hdesc_assoc
            rw [hdesc_assoc', Category.assoc, s.w]
            simp }⟩
      have hfac_lifted :
          injCocone.ι.app j ≫ injColim.desc lifted =
            cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ s.ι.app j := by
        simpa [lifted, injCocone] using injColim.fac lifted j
      rw [← Category.assoc, hπ, Category.assoc, cokernel.π_desc, hfac_lifted])
    uniq := fun s m hm => (cancel_epi (cokernel.π ι')).mp (by
      rw [cokernel.π_desc]
      let lifted : Cocone Inj := ⟨s.pt,
        { app := fun j => cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ s.ι.app j
          naturality := fun j j' a => by
            dsimp
            have hdesc :
                cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫
                    (sheafH_filtered_colimit_succ_quotient Y').map a =
                  (sheafH_filtered_colimit_succ_Inj Y').map a ≫
                    cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j') := by
              simp [sheafH_filtered_colimit_succ_quotient]
            have hdesc_assoc :
                ((sheafH_filtered_colimit_succ_Inj Y').map a ≫
                    cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j')) ≫
                  s.ι.app j' =
                (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫
                    (sheafH_filtered_colimit_succ_quotient Y').map a) ≫
                  s.ι.app j' := by
              simpa [Category.assoc] using
                congrArg (fun m => m ≫ s.ι.app j') hdesc.symm
            have hdesc_assoc' :
                (sheafH_filtered_colimit_succ_Inj Y').map a ≫
                    cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j') ≫
                  s.ι.app j' =
                (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫
                    (sheafH_filtered_colimit_succ_quotient Y').map a) ≫
                  s.ι.app j' := by
              simpa [Category.assoc] using hdesc_assoc
            rw [hdesc_assoc', Category.assoc, s.w]
            simp }⟩
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

private theorem sheafH_filtered_colimit_succ_stage_hfg (j : J') :
    ((sheafH_filtered_colimit_succ_eta Y').app j).val ≫
      (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j)).val = 0 := by
  ext U s
  change ConcreteCategory.hom
      ((((sheafH_filtered_colimit_succ_eta Y').app j) ≫
          cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j)).val.app U) s = 0
  have happ :
      (((((sheafH_filtered_colimit_succ_eta Y').app j) ≫
            cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j)).val).app
          U) =
        NatTrans.app
          (0 : (Y'.obj j).val ⟶
            (cokernel ((sheafH_filtered_colimit_succ_eta Y').app j)).val) U := by
    exact NatTrans.congr_app
      (congrArg (fun α => α.val)
        (cokernel.condition ((sheafH_filtered_colimit_succ_eta Y').app j)))
      U
  rw [happ]
  simp

private theorem sheafH_filtered_colimit_succ_iota_hfg
    (c' : Cocone Y') (hc' : IsColimit c') :
    (sheafH_filtered_colimit_succ_iota Y' c' hc').val ≫
      (cokernel.π (sheafH_filtered_colimit_succ_iota Y' c' hc')).val = 0 := by
  ext U s
  let ι' := sheafH_filtered_colimit_succ_iota Y' c' hc'
  change ConcreteCategory.hom (((ι' ≫ cokernel.π ι').val).app U) s = 0
  have happ :
      (((ι' ≫ cokernel.π ι').val).app U) =
        NatTrans.app (0 : c'.pt.val ⟶ (cokernel ι').val) U := by
    exact NatTrans.congr_app
      (congrArg (fun α => α.val) (cokernel.condition ι'))
      U
  rw [happ]
  simp

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
    haveI hInj : ∀ j, Injective (Inj.obj j) := fun j => by
      let ffData := MorphismProperty.functorialFactorizationData
        (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X))
        (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X)).rlp
      change Injective (ffData.Z.obj (Arrow.mk (0 : Ysh.obj j ⟶ 0)))
      exact IsGrothendieckAbelian.instInjectiveZMonomorphismsRlpMonoMapFactorizationDataRlpOfNatHom
    haveI hFlasqueInj : IsFlasqueSheaf (colimit Inj) :=
      isFlasque_filtered_colimit Inj (fun j => inferInstance) (colimit.isColimit Inj)
    have hI : Subsingleton (Sheaf.H injCocone.pt (n + 1)) := by
      let F : TopCat.Presheaf AddCommGrpCat.{u} X := injCocone.pt.val
      have hF : F.IsSheaf := by
        simpa [F] using injCocone.pt.cond
      letI : IsFlasqueSheaf ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) := by
        simpa [F, hF] using hFlasqueInj
      simpa [F, hF] using
        (sheafH_subsingleton_of_flasque_presheaf (X := X) (F := F) hF n)
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
    exact (sheafCohomologyFunctor_map_extClass_of_map_eq (hSE_j j₀) hSE
      (sheafH_filtered_colimit_succ_stage_hom Ysh csh hcsh j₀) n hy_j).trans hy

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

/-- The canonical comparison morphism `colim H^n(F_j) ⟶ H^n(colim F_j)` induced by a cocone. -/
noncomputable def sheafH_filtered_colimit_comparison
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) (c' : Cocone Y') :
    colimit (Y' ⋙ sheafCohomologyFunctor X n) ⟶ AddCommGrpCat.of (Sheaf.H c'.pt n) :=
  colimit.desc _ ((sheafCohomologyFunctor X n).mapCocone c')

@[simp] theorem colimit_ι_sheafH_filtered_colimit_comparison
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) (c' : Cocone Y') (j : J') :
    colimit.ι (Y' ⋙ sheafCohomologyFunctor X n) j ≫
        sheafH_filtered_colimit_comparison Y' n c' =
      (sheafCohomologyFunctor X n).map (c'.ι.app j) := by
  simp [sheafH_filtered_colimit_comparison]

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
  apply colimit.hom_ext
  intro j
  rw [show (sheafH_filtered_colimit_succ_shiftDomainIso Y' n h_mid_n h_mid_succ).hom =
      (HasColimit.isoOfNatIso (sheafH_filtered_colimit_succ_shiftNatIso Y' n
        h_mid_n h_mid_succ)).hom from rfl]
  rw [HasColimit.isoOfNatIso_ι_hom_assoc]
  rw [colimit_ι_sheafH_filtered_colimit_comparison]
  have hqj := colimit_ι_sheafH_filtered_colimit_comparison
    (X := X) (Y' := sheafH_filtered_colimit_succ_quotient Y') (n := n)
    (c' := sheafH_filtered_colimit_succ_quotientCocone Y' c' hc') j
  have hqj_assoc :
      (colimit.ι (sheafH_filtered_colimit_succ_quotient Y' ⋙ sheafCohomologyFunctor X n) j ≫
          sheafH_filtered_colimit_comparison (sheafH_filtered_colimit_succ_quotient Y') n
            (sheafH_filtered_colimit_succ_quotientCocone Y' c' hc')) ≫
        (sheafH_filtered_colimit_succ_shiftCodomainIso Y' c' hc' n
          h_colim_n h_colim_succ).hom =
      (sheafCohomologyFunctor X n).map
          ((sheafH_filtered_colimit_succ_quotientCocone Y' c' hc').ι.app j) ≫
        (sheafH_filtered_colimit_succ_shiftCodomainIso Y' c' hc' n
          h_colim_n h_colim_succ).hom := by
    simpa [Category.assoc] using
      congrArg
        (fun t =>
          t ≫ (sheafH_filtered_colimit_succ_shiftCodomainIso Y' c' hc' n
            h_colim_n h_colim_succ).hom) hqj
  have hqj_assoc' :
      colimit.ι (sheafH_filtered_colimit_succ_quotient Y' ⋙ sheafCohomologyFunctor X n) j ≫
          sheafH_filtered_colimit_comparison (sheafH_filtered_colimit_succ_quotient Y') n
            (sheafH_filtered_colimit_succ_quotientCocone Y' c' hc') ≫
        (sheafH_filtered_colimit_succ_shiftCodomainIso Y' c' hc' n
          h_colim_n h_colim_succ).hom =
      (sheafCohomologyFunctor X n).map
          ((sheafH_filtered_colimit_succ_quotientCocone Y' c' hc').ι.app j) ≫
        (sheafH_filtered_colimit_succ_shiftCodomainIso Y' c' hc' n
          h_colim_n h_colim_succ).hom := by
    exact hqj_assoc
  rw [hqj_assoc']
  change
    (sheafH_extClassIso_of_subsingleton_middle_presheaf
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
        (h_mid_n j) (h_mid_succ j)).hom ≫
      (sheafCohomologyFunctor X (n + 1)).map (c'.ι.app j) =
    (sheafCohomologyFunctor X n).map
        ((sheafH_filtered_colimit_succ_quotientCocone Y' c' hc').ι.app j) ≫
      (sheafH_filtered_colimit_succ_shiftCodomainIso Y' c' hc' n
        h_colim_n h_colim_succ).hom
  simpa [sheafH_filtered_colimit_succ_shiftNatIso,
    sheafH_filtered_colimit_succ_shiftCodomainIso] using
    (sheafH_extClassIso_of_subsingleton_middle_presheaf_natural
      (h₁₁ := (Y'.obj j).cond)
      (h₁₂ := ((sheafH_filtered_colimit_succ_Inj Y').obj j).cond)
      (h₁₃ := (cokernel ((sheafH_filtered_colimit_succ_eta Y').app j)).cond)
      (h₂₁ := c'.pt.cond)
      (h₂₂ := (sheafH_filtered_colimit_succ_injCocone Y').pt.cond)
      (h₂₃ := (sheafH_filtered_colimit_succ_quotientCocone Y' c' hc').pt.cond)
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
      (f₂ := (sheafH_filtered_colimit_succ_iota Y' c' hc').val)
      (g₂ := (cokernel.π (sheafH_filtered_colimit_succ_iota Y' c' hc')).val)
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
      (sheafH_filtered_colimit_succ_stage_shortExact (Y' := Y') j)
      (sheafH_filtered_colimit_succ_shortExact Y' c' hc')
      (τ₁ := (c'.ι.app j).val)
      (τ₂ := ((sheafH_filtered_colimit_succ_injCocone Y').ι.app j).val)
      (τ₃ := ((sheafH_filtered_colimit_succ_quotientCocone Y' c' hc').ι.app j).val)
      (by
        simpa using congrArg (fun α => α.val)
          ((sheafH_filtered_colimit_succ_stage_hom Y' c' hc' j).comm₁₂))
      (by
        simpa using congrArg (fun α => α.val)
          ((sheafH_filtered_colimit_succ_stage_hom Y' c' hc' j).comm₂₃))
      n (h_mid_n j) (h_mid_succ j) h_colim_n h_colim_succ)

/-- In degree `0`, the filtered-colimit comparison is the canonical isomorphism obtained by
transporting `H⁰ ≅ (-)(⊤)` across the created presheaf colimit and evaluation at `⊤`. -/
noncomputable def sheafH_filtered_colimit_comparison_zero_iso
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (c' : Cocone Y') (hc' : IsColimit c') :
    colimit (Y' ⋙ sheafCohomologyFunctor X 0) ≅ AddCommGrpCat.of (Sheaf.H c'.pt 0) := by
  let sectionsFunctor :
      TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  haveI := createsFilteredColimit Y'
  have hc_sections : IsColimit (sectionsFunctor.mapCocone c') :=
    isColimitOfPreserves sectionsFunctor hc'
  exact
    HasColimit.isoOfNatIso (Functor.isoWhiskerLeft Y' (sheafH0NatIsoSections (X := X))) ≪≫
      (colimit.isColimit (Y' ⋙ sectionsFunctor)).coconePointUniqueUpToIso hc_sections ≪≫
      ((sheafH0NatIsoSections (X := X)).app c'.pt).symm

@[simp] theorem sheafH_filtered_colimit_comparison_zero_iso_hom
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (c' : Cocone Y') (hc' : IsColimit c') :
    (sheafH_filtered_colimit_comparison_zero_iso Y' c' hc').hom =
      sheafH_filtered_colimit_comparison Y' 0 c' := by
  let sectionsFunctor :
      TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  haveI := createsFilteredColimit Y'
  have hc_sections : IsColimit (sectionsFunctor.mapCocone c') :=
    isColimitOfPreserves sectionsFunctor hc'
  apply colimit.hom_ext
  intro j
  simp only [sheafH_filtered_colimit_comparison_zero_iso, Iso.trans_hom]
  rw [HasColimit.isoOfNatIso_ι_hom_assoc, colimit.comp_coconePointUniqueUpToIso_hom_assoc,
    colimit_ι_sheafH_filtered_colimit_comparison]
  change ((sheafH0NatIsoSections (X := X)).hom.app (Y'.obj j)) ≫
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
          (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)).map
        (c'.ι.app j) ≫
      ((sheafH0NatIsoSections (X := X)).app c'.pt).symm.hom =
    (sheafCohomologyFunctor X 0).map (c'.ι.app j)
  rw [← (sheafH0NatIsoSections (X := X)).hom.naturality_assoc (c'.ι.app j)]
  simp

/-- On a Noetherian space and for a filtered diagram, the degree-`0` comparison morphism
    `colim H⁰(F_j) ⟶ H⁰(colim F_j)` is an isomorphism. -/
theorem sheafH_filtered_colimit_comparison_isIso_zero
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (c' : Cocone Y') (hc' : IsColimit c') :
    IsIso (sheafH_filtered_colimit_comparison Y' 0 c') := by
  rw [← sheafH_filtered_colimit_comparison_zero_iso_hom (Y' := Y') (c' := c') (hc' := hc')]
  infer_instance

private noncomputable def sheafH_filtered_colimit_h1_sectionsFunctor
    {X : TopCat.{u}} :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)

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
        (sheafH1_cokernel_iso_of_subsingleton_middle_presheaf
          (h₁ := (Y'.obj j).cond)
          (h₂ := ((sheafH_filtered_colimit_succ_Inj Y').obj j).cond)
          (h₃ := (cokernel ((sheafH_filtered_colimit_succ_eta Y').app j)).cond)
          (f := ((sheafH_filtered_colimit_succ_eta Y').app j).val)
          (g := (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j)).val)
          (sheafH_filtered_colimit_succ_stage_hfg (Y' := Y') j)
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
          (sheafH_filtered_colimit_succ_stage_hfg (Y' := Y') j)
          (f₂ := ((sheafH_filtered_colimit_succ_eta Y').app j').val)
          (g₂ := (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j')).val)
          (sheafH_filtered_colimit_succ_stage_hfg (Y' := Y') j')
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
  letI : Zero (TopCat.Sheaf AddCommGrpCat.{u} X) := Limits.HasZeroObject.zero' _
  let Inj := sheafH_filtered_colimit_succ_Inj Y'
  let qCocone := sheafH_filtered_colimit_succ_quotientCocone Y' c' hc'
  let sectionsFunctor := sheafH_filtered_colimit_h1_sectionsFunctor (X := X)
  let ι' := sheafH_filtered_colimit_succ_iota Y' c' hc'
  have hqColim : IsColimit qCocone :=
    sheafH_filtered_colimit_succ_quotientCocone_isColimit Y' c' hc'
  have hInj : ∀ j, Injective (Inj.obj j) := by
    intro j
    let ffData := MorphismProperty.functorialFactorizationData
      (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X))
      (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X)).rlp
    change Injective (ffData.Z.obj (Arrow.mk (0 : Y'.obj j ⟶ 0)))
    exact IsGrothendieckAbelian.instInjectiveZMonomorphismsRlpMonoMapFactorizationDataRlpOfNatHom
  have h_mid : ∀ j, Subsingleton (Sheaf.H (Inj.obj j) 1) := by
    intro j
    letI : Injective (Inj.obj j) := hInj j
    exact Ext.subsingleton_of_injective _ _ 0
  haveI hFlasqueInj : IsFlasqueSheaf (sheafH_filtered_colimit_succ_injCocone Y').pt :=
    isFlasque_filtered_colimit Inj (fun j => isFlasque_of_injective (Inj.obj j)) (colimit.isColimit Inj)
  have h_colim : Subsingleton (Sheaf.H (sheafH_filtered_colimit_succ_injCocone Y').pt 1) := by
    let F : TopCat.Presheaf AddCommGrpCat.{u} X :=
      (sheafH_filtered_colimit_succ_injCocone Y').pt.val
    have hF : F.IsSheaf := by
      simpa [F] using (sheafH_filtered_colimit_succ_injCocone Y').pt.cond
    letI : IsFlasqueSheaf ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) := by
      simpa [F, hF] using hFlasqueInj
    exact sheafH_subsingleton_H1_of_flasque_presheaf
      (X := X) (F := F) hF
  haveI := createsFilteredColimit Inj
  have hc_psh_inj :
      IsColimit ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone
        (sheafH_filtered_colimit_succ_injCocone Y')) :=
    isColimitOfPreserves (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (colimit.isColimit Inj)
  have hc_sections_inj :
      IsColimit (sectionsFunctor.mapCocone (sheafH_filtered_colimit_succ_injCocone Y')) :=
    isColimitOfPreserves
      ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) hc_psh_inj
  haveI := createsFilteredColimit (sheafH_filtered_colimit_succ_quotient Y')
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
        sectionsFunctor.obj (sheafH_filtered_colimit_succ_injCocone Y').pt :=
    (colimit.isColimit (Inj ⋙ sectionsFunctor)).coconePointUniqueUpToIso hc_sections_inj
  let eQ :
      colimit (sheafH_filtered_colimit_succ_quotient Y' ⋙ sectionsFunctor) ≅
        sectionsFunctor.obj qCocone.pt :=
    (colimit.isColimit (sheafH_filtered_colimit_succ_quotient Y' ⋙ sectionsFunctor)).coconePointUniqueUpToIso hc_sections_q
  have hsq :
      (colim (J := J') (C := AddCommGrpCat.{u})).map
          (sheafH_filtered_colimit_h1_gTopNat Y') ≫
        eQ.hom =
      eInj.hom ≫ sectionsFunctor.map (cokernel.π ι') := by
    apply colimit.hom_ext
    intro j
    have hQj :
        colimit.ι (sheafH_filtered_colimit_succ_quotient Y' ⋙ sectionsFunctor) j ≫ eQ.hom =
          (sectionsFunctor.mapCocone qCocone).ι.app j := by
      simpa [eQ] using
        (colimit.comp_coconePointUniqueUpToIso_hom
          (F := sheafH_filtered_colimit_succ_quotient Y' ⋙ sectionsFunctor) hc_sections_q j)
    have hInjj :
        colimit.ι (Inj ⋙ sectionsFunctor) j ≫ eInj.hom =
          (sectionsFunctor.mapCocone (sheafH_filtered_colimit_succ_injCocone Y')).ι.app j := by
      simpa [eInj] using
        (colimit.comp_coconePointUniqueUpToIso_hom
          (F := Inj ⋙ sectionsFunctor) hc_sections_inj j)
    have hInjj_assoc :
        colimit.ι (Inj ⋙ sectionsFunctor) j ≫ eInj.hom ≫
            sectionsFunctor.map (cokernel.π ι') =
          (sectionsFunctor.mapCocone (sheafH_filtered_colimit_succ_injCocone Y')).ι.app j ≫
            sectionsFunctor.map (cokernel.π ι') := by
      simpa [Category.assoc] using
        congrArg (fun t => t ≫ sectionsFunctor.map (cokernel.π ι')) hInjj
    rw [colimit.ι_map_assoc, hQj, hInjj_assoc]
    change ((cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j)).val.app (op ⊤)) ≫
        ((qCocone.ι.app j).val.app (op ⊤)) =
      ((sheafH_filtered_colimit_succ_injCocone Y').ι.app j).val.app (op ⊤) ≫
        ((cokernel.π ι').val.app (op ⊤))
    have hπj :
        cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ qCocone.ι.app j =
          (sheafH_filtered_colimit_succ_injCocone Y').ι.app j ≫ cokernel.π ι' := by
      exact cokernel.π_desc _ _ _
    exact (congrArg
      (fun β :
        ((sheafH_filtered_colimit_succ_Inj Y').obj j) ⟶ qCocone.pt =>
          β.val.app (op ⊤))
      hπj)
  let globalIso :
      cokernel (sectionsFunctor.map (cokernel.π ι')) ≅
        AddCommGrpCat.of (Sheaf.H c'.pt 1) := by
    simpa [sectionsFunctor] using
      (sheafH1_cokernel_iso_of_subsingleton_middle_presheaf
        (h₁ := c'.pt.cond)
        (h₂ := (sheafH_filtered_colimit_succ_injCocone Y').pt.cond)
        (h₃ := qCocone.pt.cond)
        (f := ι'.val)
        (g := (cokernel.π ι').val)
        (sheafH_filtered_colimit_succ_iota_hfg (Y' := Y') c' hc')
        (sheafH_filtered_colimit_succ_shortExact Y' c' hc')
        h_colim)
  exact
    (HasColimit.isoOfNatIso (sheafH_filtered_colimit_h1_stageNatIso Y' h_mid)).symm ≪≫
      HasColimit.isoOfNatIso (sheafH_filtered_colimit_h1_cokernelFunctorIso Y') ≪≫
      PreservesCokernel.iso (colim (J := J') (C := AddCommGrpCat.{u}))
        (sheafH_filtered_colimit_h1_gTopNat Y') ≪≫
      (cokernel.mapIso (f := (colim (J := J') (C := AddCommGrpCat.{u})).map
          (sheafH_filtered_colimit_h1_gTopNat Y'))
        (sectionsFunctor.map (cokernel.π ι')) eInj eQ hsq) ≪≫
      globalIso

@[simp] theorem sheafH_filtered_colimit_comparison_one_iso_hom
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (c' : Cocone Y') (hc' : IsColimit c') :
    (sheafH_filtered_colimit_comparison_one_iso Y' c' hc').hom =
      sheafH_filtered_colimit_comparison Y' 1 c' := by
  letI : Zero (TopCat.Sheaf AddCommGrpCat.{u} X) := Limits.HasZeroObject.zero' _
  let Inj := sheafH_filtered_colimit_succ_Inj Y'
  let qCocone := sheafH_filtered_colimit_succ_quotientCocone Y' c' hc'
  let sectionsFunctor := sheafH_filtered_colimit_h1_sectionsFunctor (X := X)
  let ι' := sheafH_filtered_colimit_succ_iota Y' c' hc'
  have hqColim : IsColimit qCocone :=
    sheafH_filtered_colimit_succ_quotientCocone_isColimit Y' c' hc'
  have hInj : ∀ j, Injective (Inj.obj j) := by
    intro j
    let ffData := MorphismProperty.functorialFactorizationData
      (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X))
      (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X)).rlp
    change Injective (ffData.Z.obj (Arrow.mk (0 : Y'.obj j ⟶ 0)))
    exact IsGrothendieckAbelian.instInjectiveZMonomorphismsRlpMonoMapFactorizationDataRlpOfNatHom
  have h_mid : ∀ j, Subsingleton (Sheaf.H (Inj.obj j) 1) := by
    intro j
    letI : Injective (Inj.obj j) := hInj j
    exact Ext.subsingleton_of_injective _ _ 0
  haveI hFlasqueInj : IsFlasqueSheaf (sheafH_filtered_colimit_succ_injCocone Y').pt :=
    isFlasque_filtered_colimit Inj (fun j => isFlasque_of_injective (Inj.obj j)) (colimit.isColimit Inj)
  have h_colim : Subsingleton (Sheaf.H (sheafH_filtered_colimit_succ_injCocone Y').pt 1) := by
    let F : TopCat.Presheaf AddCommGrpCat.{u} X :=
      (sheafH_filtered_colimit_succ_injCocone Y').pt.val
    have hF : F.IsSheaf := by
      simpa [F] using (sheafH_filtered_colimit_succ_injCocone Y').pt.cond
    letI : IsFlasqueSheaf ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) := by
      simpa [F, hF] using hFlasqueInj
    exact sheafH_subsingleton_H1_of_flasque_presheaf
      (X := X) (F := F) hF
  haveI := createsFilteredColimit Inj
  have hc_psh_inj :
      IsColimit ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone
        (sheafH_filtered_colimit_succ_injCocone Y')) :=
    isColimitOfPreserves (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (colimit.isColimit Inj)
  have hc_sections_inj :
      IsColimit (sectionsFunctor.mapCocone (sheafH_filtered_colimit_succ_injCocone Y')) :=
    isColimitOfPreserves
      ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) hc_psh_inj
  haveI := createsFilteredColimit (sheafH_filtered_colimit_succ_quotient Y')
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
        sectionsFunctor.obj (sheafH_filtered_colimit_succ_injCocone Y').pt :=
    (colimit.isColimit (Inj ⋙ sectionsFunctor)).coconePointUniqueUpToIso hc_sections_inj
  let eQ :
      colimit (sheafH_filtered_colimit_succ_quotient Y' ⋙ sectionsFunctor) ≅
        sectionsFunctor.obj qCocone.pt :=
    (colimit.isColimit (sheafH_filtered_colimit_succ_quotient Y' ⋙ sectionsFunctor)).coconePointUniqueUpToIso hc_sections_q
  let α := sheafH_filtered_colimit_h1_gTopNat Y'
  let stageIso :
      sheafH_filtered_colimit_h1_cokernelFunctor Y' ≅
        Y' ⋙ sheafCohomologyFunctor X 1 :=
    sheafH_filtered_colimit_h1_stageNatIso Y' h_mid
  let functorCokIso :
      sheafH_filtered_colimit_h1_cokernelFunctor Y' ≅ cokernel α :=
    sheafH_filtered_colimit_h1_cokernelFunctorIso Y'
  let colimCokIso :
      colimit (cokernel α) ≅
        cokernel ((colim (J := J') (C := AddCommGrpCat.{u})).map α) :=
    PreservesCokernel.iso (colim (J := J') (C := AddCommGrpCat.{u})) α
  let mapIso :
      cokernel ((colim (J := J') (C := AddCommGrpCat.{u})).map α) ≅
        cokernel (sectionsFunctor.map (cokernel.π ι')) :=
    cokernel.mapIso (f := (colim (J := J') (C := AddCommGrpCat.{u})).map α)
      (sectionsFunctor.map (cokernel.π ι')) eInj eQ (by
      apply colimit.hom_ext
      intro j
      have hQj :
          colimit.ι (sheafH_filtered_colimit_succ_quotient Y' ⋙ sectionsFunctor) j ≫ eQ.hom =
            (sectionsFunctor.mapCocone qCocone).ι.app j := by
        simpa [eQ] using
          (colimit.comp_coconePointUniqueUpToIso_hom
            (F := sheafH_filtered_colimit_succ_quotient Y' ⋙ sectionsFunctor) hc_sections_q j)
      have hInjj :
          colimit.ι (Inj ⋙ sectionsFunctor) j ≫ eInj.hom =
            (sectionsFunctor.mapCocone (sheafH_filtered_colimit_succ_injCocone Y')).ι.app j := by
        simpa [eInj] using
          (colimit.comp_coconePointUniqueUpToIso_hom
            (F := Inj ⋙ sectionsFunctor) hc_sections_inj j)
      have hInjj_assoc :
          colimit.ι (Inj ⋙ sectionsFunctor) j ≫ eInj.hom ≫
              sectionsFunctor.map (cokernel.π ι') =
            (sectionsFunctor.mapCocone (sheafH_filtered_colimit_succ_injCocone Y')).ι.app j ≫
              sectionsFunctor.map (cokernel.π ι') := by
        simpa [Category.assoc] using
          congrArg (fun t => t ≫ sectionsFunctor.map (cokernel.π ι')) hInjj
      rw [colimit.ι_map_assoc, hQj, hInjj_assoc]
      change ((cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j)).val.app (op ⊤)) ≫
          ((qCocone.ι.app j).val.app (op ⊤)) =
        ((sheafH_filtered_colimit_succ_injCocone Y').ι.app j).val.app (op ⊤) ≫
          ((cokernel.π ι').val.app (op ⊤))
      have hπj :
          cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j) ≫ qCocone.ι.app j =
            (sheafH_filtered_colimit_succ_injCocone Y').ι.app j ≫ cokernel.π ι' := by
        exact cokernel.π_desc _ _ _
      exact (congrArg
        (fun β :
          ((sheafH_filtered_colimit_succ_Inj Y').obj j) ⟶ qCocone.pt =>
            β.val.app (op ⊤))
        hπj))
  let globalIso :
      cokernel (sectionsFunctor.map (cokernel.π ι')) ≅
        AddCommGrpCat.of (Sheaf.H c'.pt 1) := by
    simpa [sectionsFunctor] using
      (sheafH1_cokernel_iso_of_subsingleton_middle_presheaf
        (h₁ := c'.pt.cond)
        (h₂ := (sheafH_filtered_colimit_succ_injCocone Y').pt.cond)
        (h₃ := qCocone.pt.cond)
        (f := ι'.val)
        (g := (cokernel.π ι').val)
        (sheafH_filtered_colimit_succ_iota_hfg (Y' := Y') c' hc')
        (sheafH_filtered_colimit_succ_shortExact Y' c' hc')
        h_colim)
  let comparisonOne :=
    (HasColimit.isoOfNatIso stageIso).symm ≪≫
      HasColimit.isoOfNatIso functorCokIso ≪≫
      colimCokIso ≪≫ mapIso ≪≫ globalIso
  change comparisonOne.hom = sheafH_filtered_colimit_comparison Y' 1 c'
  apply colimit.hom_ext
  intro j
  let stageShort := sheafH_filtered_colimit_succ_stage_shortExact (Y' := Y') j
  let stageIsoH1 :=
    sheafH1_cokernel_iso_of_subsingleton_middle_presheaf
      (h₁ := (Y'.obj j).cond)
      (h₂ := ((sheafH_filtered_colimit_succ_Inj Y').obj j).cond)
      (h₃ := (cokernel ((sheafH_filtered_colimit_succ_eta Y').app j)).cond)
      (f := ((sheafH_filtered_colimit_succ_eta Y').app j).val)
      (g := (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j)).val)
      (sheafH_filtered_colimit_succ_stage_hfg (Y' := Y') j)
      stageShort (h_mid j)
  let stageHom := sheafH_filtered_colimit_succ_stage_hom Y' c' hc' j
  let stageCokMap :
      cokernel ((sheafH_filtered_colimit_h1_gTopNat Y').app j) ⟶
        cokernel (sectionsFunctor.map (cokernel.π ι')) :=
    cokernel.map
      ((sheafH_filtered_colimit_h1_gTopNat Y').app j)
      (sectionsFunctor.map (cokernel.π ι'))
      (((sheafH_filtered_colimit_succ_injCocone Y').ι.app j).val.app (op ⊤))
      ((qCocone.ι.app j).val.app (op ⊤))
      (by
        simpa [sectionsFunctor, sheafH_filtered_colimit_h1_gTopNat,
          sheafH_filtered_colimit_succ_shortComplex] using
          congrArg
            (fun β :
              ((sheafH_filtered_colimit_succ_Inj Y').obj j) ⟶
                (sheafH_filtered_colimit_succ_shortComplex Y' c' hc').X₃ =>
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
        colimit.ι (sheafH_filtered_colimit_succ_quotient Y' ⋙ sectionsFunctor) j ≫ eQ.hom =
          (sectionsFunctor.mapCocone qCocone).ι.app j := by
      simpa [eQ] using
        (colimit.comp_coconePointUniqueUpToIso_hom
          (F := sheafH_filtered_colimit_succ_quotient Y' ⋙ sectionsFunctor) hc_sections_q j)
    have hQj_assoc :
        colimit.ι (sheafH_filtered_colimit_succ_quotient Y' ⋙ sectionsFunctor) j ≫
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
        colimit.ι (sheafH_filtered_colimit_succ_quotient Y' ⋙ sectionsFunctor) j ≫
            cokernel.π (colim.map α) ≫ mapIso.hom =
          colimit.ι (sheafH_filtered_colimit_succ_quotient Y' ⋙ sectionsFunctor) j ≫
            eQ.hom ≫ cokernel.π (sectionsFunctor.map (cokernel.π ι')) := by
      simpa [Category.assoc] using
        congrArg
          (fun t =>
            colimit.ι (sheafH_filtered_colimit_succ_quotient Y' ⋙ sectionsFunctor) j ≫ t)
          hmapIso
    apply (cancel_epi (cokernel.π ((sheafH_filtered_colimit_h1_gTopNat Y').app j))).mp
    change cokernel.π ((sheafH_filtered_colimit_h1_gTopNat Y').app j) ≫
        (functorCokIso.hom.app j) ≫
          colimit.ι (cokernel α) j ≫
          colimCokIso.hom ≫
          mapIso.hom =
      cokernel.π ((sheafH_filtered_colimit_h1_gTopNat Y').app j) ≫ stageCokMap
    have hfunctorCok :
        cokernel.π ((sheafH_filtered_colimit_h1_gTopNat Y').app j) ≫ functorCokIso.hom.app j =
          (cokernel.π α).app j := by
      change cokernel.π (α.app j) ≫ e_j.inv = (cokernel.π α).app j
      symm
      exact (Iso.eq_comp_inv e_j).2 (by
        simpa using
          (PreservesCokernel.π_iso_hom
            ((CategoryTheory.evaluation J' AddCommGrpCat.{u}).obj j) α))
    have hfunctorCok_assoc :
        cokernel.π ((sheafH_filtered_colimit_h1_gTopNat Y').app j) ≫
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
        stageIsoH1.hom ≫ (sheafCohomologyFunctor X 1).map (c'.ι.app j) := by
    simpa [stageShort, stageIsoH1, globalIso, stageCokMap, stageHom, sectionsFunctor,
      sheafH_filtered_colimit_h1_gTopNat, sheafH_filtered_colimit_succ_shortComplex] using
      (sheafH1_cokernel_iso_of_subsingleton_middle_presheaf_natural
        (h₁₁ := (Y'.obj j).cond)
        (h₁₂ := ((sheafH_filtered_colimit_succ_Inj Y').obj j).cond)
        (h₁₃ := (cokernel ((sheafH_filtered_colimit_succ_eta Y').app j)).cond)
        (h₂₁ := c'.pt.cond)
        (h₂₂ := (sheafH_filtered_colimit_succ_injCocone Y').pt.cond)
        (h₂₃ := qCocone.pt.cond)
        (f₁ := ((sheafH_filtered_colimit_succ_eta Y').app j).val)
        (g₁ := (cokernel.π ((sheafH_filtered_colimit_succ_eta Y').app j)).val)
        (sheafH_filtered_colimit_succ_stage_hfg (Y' := Y') j)
        (f₂ := ι'.val)
        (g₂ := (cokernel.π ι').val)
        (sheafH_filtered_colimit_succ_iota_hfg (Y' := Y') c' hc')
        stageShort
        (sheafH_filtered_colimit_succ_shortExact Y' c' hc')
        (τ₁ := (c'.ι.app j).val)
        (τ₂ := ((sheafH_filtered_colimit_succ_injCocone Y').ι.app j).val)
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
        (sheafCohomologyFunctor X 1).map (c'.ι.app j) := by
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
              (stageIsoH1.hom ≫ (sheafCohomologyFunctor X 1).map (c'.ι.app j)) := by
                rw [hnat]
      _ = (sheafCohomologyFunctor X 1).map (c'.ι.app j) := by simp [Category.assoc]
  simpa [stageIso, stageIsoH1] using hmain

/-- On a Noetherian space and for a filtered diagram, the degree-`1` comparison morphism
    `colim H¹(F_j) ⟶ H¹(colim F_j)` is an isomorphism. -/
theorem sheafH_filtered_colimit_comparison_isIso_one
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (c' : Cocone Y') (hc' : IsColimit c') :
    IsIso (sheafH_filtered_colimit_comparison Y' 1 c') := by
  rw [← sheafH_filtered_colimit_comparison_one_iso_hom (Y' := Y') (c' := c') (hc' := hc')]
  infer_instance

/-- On a Noetherian space and for a filtered diagram, the canonical comparison morphism
    `colim H^n(F_j) ⟶ H^n(colim F_j)` is an isomorphism in every degree. -/
theorem sheafH_filtered_colimit_comparison_isIso
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) (c' : Cocone Y') (hc' : IsColimit c') :
    IsIso (sheafH_filtered_colimit_comparison Y' n c') := by
  let P : ℕ → Prop := fun n =>
    ∀ {J' : Type u} [SmallCategory J'] [IsFiltered J']
      (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
      (c' : Cocone Y') (hc' : IsColimit c'),
      IsIso (sheafH_filtered_colimit_comparison Y' n c')
  have hP : ∀ n, P n := by
    intro n
    induction n with
    | zero =>
        intro J' _ _ Y' c' hc'
        exact sheafH_filtered_colimit_comparison_isIso_zero Y' c' hc'
    | succ n ih =>
        cases n with
        | zero =>
            intro J' _ _ Y' c' hc'
            exact sheafH_filtered_colimit_comparison_isIso_one Y' c' hc'
        | succ m =>
            intro J' _ _ Y' c' hc'
            letI : Zero (TopCat.Sheaf AddCommGrpCat.{u} X) := Limits.HasZeroObject.zero' _
            let Inj := sheafH_filtered_colimit_succ_Inj Y'
            let injCocone := sheafH_filtered_colimit_succ_injCocone Y'
            let qCocone := sheafH_filtered_colimit_succ_quotientCocone Y' c' hc'
            have hqColim : IsColimit qCocone :=
              sheafH_filtered_colimit_succ_quotientCocone_isColimit Y' c' hc'
            have h_quot :
                IsIso
                  (sheafH_filtered_colimit_comparison
                    (sheafH_filtered_colimit_succ_quotient Y') (m + 1) qCocone) :=
              ih (Y' := sheafH_filtered_colimit_succ_quotient Y') (c' := qCocone) hqColim
            letI :
                IsIso
                  (sheafH_filtered_colimit_comparison
                    (sheafH_filtered_colimit_succ_quotient Y') (m + 1) qCocone) := h_quot
            have hInj : ∀ j, Injective (Inj.obj j) := by
              intro j
              let fac :=
                IsGrothendieckAbelian.monoMapFactorizationDataRlp
                  (C := TopCat.Sheaf AddCommGrpCat.{u} X) (0 : Y'.obj j ⟶ 0)
              change Injective fac.Z
              simpa only [injective_iff_rlp_monomorphisms_zero,
                (isZero_zero (TopCat.Sheaf AddCommGrpCat.{u} X)).eq_of_tgt fac.p 0] using fac.hp
            have h_mid_n : ∀ j, Subsingleton (Sheaf.H (Inj.obj j) (m + 1)) := by
              intro j
              letI : Injective (Inj.obj j) := hInj j
              exact Ext.subsingleton_of_injective _ _ m
            have h_mid_succ : ∀ j, Subsingleton (Sheaf.H (Inj.obj j) (m + 2)) := by
              intro j
              letI : Injective (Inj.obj j) := hInj j
              exact Ext.subsingleton_of_injective _ _ (m + 1)
            haveI hFlasqueInj : IsFlasqueSheaf injCocone.pt :=
              isFlasque_filtered_colimit Inj
                (fun j => by
                  letI : Injective (Inj.obj j) := hInj j
                  exact isFlasque_of_injective (Inj.obj j))
                (colimit.isColimit Inj)
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
              sheafH_filtered_colimit_succ_shiftDomainIso Y' (m + 1) h_mid_n h_mid_succ
            let codomainIso :=
              sheafH_filtered_colimit_succ_shiftCodomainIso
                Y' c' hc' (m + 1) h_colim_n h_colim_succ
            have hcompat :
                domainIso.hom ≫ sheafH_filtered_colimit_comparison Y' (m + 2) c' =
                  sheafH_filtered_colimit_comparison
                      (sheafH_filtered_colimit_succ_quotient Y') (m + 1) qCocone ≫
                    codomainIso.hom := by
              simpa [domainIso, codomainIso] using
                sheafH_filtered_colimit_comparison_succ_compatibility
                  (Y' := Y') (c' := c') (hc' := hc') (n := m + 1)
                  h_mid_n h_mid_succ h_colim_n h_colim_succ
            have hrewrite :
                sheafH_filtered_colimit_comparison Y' (m + 2) c' =
                  domainIso.inv ≫
                    sheafH_filtered_colimit_comparison
                      (sheafH_filtered_colimit_succ_quotient Y') (m + 1) qCocone ≫
                    codomainIso.hom := by
              calc
                sheafH_filtered_colimit_comparison Y' (m + 2) c'
                    = 𝟙 _ ≫ sheafH_filtered_colimit_comparison Y' (m + 2) c' := by simp
                _ = domainIso.inv ≫ domainIso.hom ≫
                      sheafH_filtered_colimit_comparison Y' (m + 2) c' := by simp
                _ = domainIso.inv ≫
                      (sheafH_filtered_colimit_comparison
                        (sheafH_filtered_colimit_succ_quotient Y') (m + 1) qCocone ≫
                          codomainIso.hom) := by rw [hcompat]
                _ = domainIso.inv ≫
                      sheafH_filtered_colimit_comparison
                        (sheafH_filtered_colimit_succ_quotient Y') (m + 1) qCocone ≫
                      codomainIso.hom := by simp [Category.assoc]
            rw [hrewrite]
            infer_instance
  exact hP n Y' c' hc'

private def sheafH_filtered_colimit_presheafDiagram
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J']
    (Y : J' ⥤ TopCat.Presheaf AddCommGrpCat.{u} X)
    (hY : ∀ j, TopCat.Presheaf.IsSheaf (Y.obj j)) :
    J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  { obj := fun j => ⟨Y.obj j, hY j⟩
    map := fun f => Sheaf.Hom.mk (Y.map f)
    map_id := fun j => Sheaf.Hom.ext <| Y.map_id j
    map_comp := fun f g => Sheaf.Hom.ext <| Y.map_comp f g }

private def sheafH_filtered_colimit_presheafCocone
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

private theorem sheafH_filtered_colimit_presheafDiagram_sheafToPresheaf
    {X : TopCat.{u}}
    {J' : Type u} [SmallCategory J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) :
    sheafH_filtered_colimit_presheafDiagram
      (Y' ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (fun j => (Y'.obj j).cond) = Y' := by
  cases Y'
  rfl

private theorem sheafH_filtered_colimit_presheafCocone_sheafToPresheaf
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
    colimit (sheafH_filtered_colimit_presheafDiagram Y hY ⋙ sheafCohomologyFunctor X n) ≅
      AddCommGrpCat.of
        (Sheaf.H (sheafH_filtered_colimit_presheafCocone Y hY c hc_pt).pt n) := by
  let Ysh := sheafH_filtered_colimit_presheafDiagram Y hY
  let csh := sheafH_filtered_colimit_presheafCocone Y hY c hc_pt
  have hcsh : IsColimit csh := by
    letI : CreatesColimit Ysh
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
      createsFilteredColimit Ysh
    simpa [Ysh, csh, sheafH_filtered_colimit_presheafDiagram,
      sheafH_filtered_colimit_presheafCocone] using
      (liftedColimitIsColimit
        (F := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (K := Ysh) (c := c) hc)
  letI := sheafH_filtered_colimit_comparison_isIso (Y' := Ysh) (n := n) (c' := csh) hcsh
  exact asIso (sheafH_filtered_colimit_comparison Ysh n csh)

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
      sheafH_filtered_colimit_comparison
        (sheafH_filtered_colimit_presheafDiagram Y hY) n
        (sheafH_filtered_colimit_presheafCocone Y hY c hc_pt) := by
  let Ysh := sheafH_filtered_colimit_presheafDiagram Y hY
  let csh := sheafH_filtered_colimit_presheafCocone Y hY c hc_pt
  have hcsh : IsColimit csh := by
    letI : CreatesColimit Ysh
        (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
      createsFilteredColimit Ysh
    simpa [Ysh, csh, sheafH_filtered_colimit_presheafDiagram,
      sheafH_filtered_colimit_presheafCocone] using
      (liftedColimitIsColimit
        (F := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (K := Ysh) (c := c) hc)
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
  simpa [sheafH_filtered_colimit_presheafDiagram,
    sheafH_filtered_colimit_presheafCocone] using
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
  rw [sheafH_filtered_colimit_comparison_iso_presheaf_hom]
  let Ysh : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
    sheafH_filtered_colimit_presheafDiagram
      (Y' ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (fun j => (Y'.obj j).cond)
  let csh : Cocone Ysh :=
    sheafH_filtered_colimit_presheafCocone
      (Y' ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (fun j => (Y'.obj j).cond)
      ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapCocone c')
      c'.pt.cond
  change sheafH_filtered_colimit_comparison Ysh n csh =
    sheafH_filtered_colimit_comparison Y' n c'
  have hYsh : Ysh = Y' := by
    dsimp [Ysh]
    exact sheafH_filtered_colimit_presheafDiagram_sheafToPresheaf (Y' := Y')
  subst Ysh
  have hcsh : csh = c' := by
    dsimp [csh]
    exact sheafH_filtered_colimit_presheafCocone_sheafToPresheaf (Y' := Y') (c' := c')
  subst csh
  rfl

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
    (n : ℕ) := by
  simpa [sheafH_filtered_colimit_presheafDiagram,
    sheafH_filtered_colimit_presheafCocone] using
    (sheafH_filtered_colimit_comparison_iso_presheaf
      (Y := Y) (hY := hY) (c := c) (hc := hc) (hc_pt := hc_pt) (n := n))

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
  simpa [sheafH_preserves_filtered_colimits_presheaf] using
    (sheafH_preserves_filtered_colimits_presheaf_hom_epi
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
