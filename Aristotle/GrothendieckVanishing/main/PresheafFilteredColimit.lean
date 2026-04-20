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
  - `sheafH_preserves_filtered_colimits`: if `H^n(F_j) = 0` for all pieces of a filtered
    diagram, then `H^n(colim F_j) = 0`
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
- `sheafH_preserves_filtered_colimits`: if `H^n(F_j) = 0` for all pieces of a filtered diagram,
  then `H^n(colim F_j) = 0`. This is a direct corollary of surjectivity: every element of
  `H^n(colim)` lifts to some `H^n(F_j) = 0`, hence is zero. -/

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
  induction n with
  | zero =>
    intro J' inst1 inst2 Y' c' hc' x
    letI := inst1; letI := inst2
    haveI := createsFilteredColimit Y'
    have hc_psh := isColimitOfPreserves (sheafToPresheaf _ _) hc'
    have hc_top := isColimitOfPreserves
      ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) hc_psh
    let x_sec := sheafH0EquivSections c'.pt x
    obtain ⟨j, s_j, hs_j⟩ := Concrete.isColimit_exists_rep _ hc_top x_sec
    let y := (sheafH0EquivSections (Y'.obj j)).symm s_j
    refine ⟨j, y, ?_⟩
    have h_nat :
        sheafH0EquivSections c'.pt
          (ConcreteCategory.hom ((sheafCohomologyFunctor X 0).map (c'.ι.app j)) y) =
        ConcreteCategory.hom ((c'.ι.app j).val.app (op ⊤))
          (sheafH0EquivSections (Y'.obj j) y) := by
      simpa [sheafCohomologyFunctor_map_apply] using
        (sheafH0EquivSections_natural (f := c'.ι.app j) (x := y))
    apply (sheafH0EquivSections c'.pt).injective
    change sheafH0EquivSections c'.pt
      (ConcreteCategory.hom ((sheafCohomologyFunctor X 0).map (c'.ι.app j)) y) = x_sec
    rw [h_nat, AddEquiv.apply_symm_apply]
    exact hs_j
  | succ n ih =>
    intro J' inst1 inst2 Y' c' hc' x
    letI := inst1; letI := inst2
    letI : Zero (TopCat.Sheaf AddCommGrpCat.{u} X) := Limits.HasZeroObject.zero' _
    let toArrow : J' ⥤ Arrow (TopCat.Sheaf AddCommGrpCat.{u} X) :=
      { obj := fun j => Arrow.mk (0 : Y'.obj j ⟶ 0)
        map := fun f => Arrow.homMk (Y'.map f) (𝟙 0) (by simp)
        map_id := fun j => by ext <;> simp
        map_comp := fun f g => by ext <;> simp }
    let ffData := MorphismProperty.functorialFactorizationData
      (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X))
      (MorphismProperty.monomorphisms (TopCat.Sheaf AddCommGrpCat.{u} X)).rlp
    let Inj : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X := toArrow ⋙ ffData.Z
    let η : Y' ⟶ Inj :=
      { app := fun j => ffData.i.app (toArrow.obj j)
        naturality := fun _ _ f => ffData.i.naturality (toArrow.map f) }
    have hη_mono : ∀ j, Mono (η.app j) := fun j => ffData.hi (toArrow.obj j)
    haveI hInj : ∀ j, Injective (Inj.obj j) := fun j => by
      change Injective (ffData.Z.obj (Arrow.mk (0 : Y'.obj j ⟶ 0)))
      exact IsGrothendieckAbelian.instInjectiveZMonomorphismsRlpMonoMapFactorizationDataRlpOfNatHom
    let injCocone : Cocone Inj := colimit.cocone Inj
    let ι'Cocone : Cocone Y' := Cocone.mk injCocone.pt
      { app := fun j => η.app j ≫ injCocone.ι.app j
        naturality := fun j j' f => by
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
            ← injCocone.w f, ← Category.assoc, η.naturality f] }
    let ι' : c'.pt ⟶ injCocone.pt := hc'.desc ι'Cocone
    haveI : Mono ι' := by
      haveI : ∀ j, Mono (η.app j) := hη_mono
      haveI := NatTrans.mono_of_mono_app η
      exact colim.map_mono' η hc' (colimit.isColimit Inj) ι' (fun j => hc'.fac ι'Cocone j)
    let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
      ShortComplex.mk ι' (cokernel.π ι') (cokernel.condition ι')
    have hSE : S.ShortExact := ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ι')) inferInstance inferInstance
    haveI := isFlasque_filtered_colimit Inj (fun j => inferInstance)
        (colimit.isColimit Inj)
    have hI : Subsingleton (Sheaf.H injCocone.pt (n + 1)) := inferInstance
    let Q : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
      { obj := fun j => cokernel (η.app j)
        map := fun {j j'} f => cokernel.map _ _ (Y'.map f) (Inj.map f) (η.naturality f).symm
        map_id := fun j => by ext; simp [cokernel.map]
        map_comp := fun {j j' j''} f g => by ext; simp [cokernel.map, Functor.map_comp] }
    have hfac_ι : ∀ j, c'.ι.app j ≫ ι' = η.app j ≫ injCocone.ι.app j := hc'.fac ι'Cocone
    let qCocone : Cocone Q := Cocone.mk S.X₃
      { app := fun j => cokernel.map (η.app j) ι' (c'.ι.app j) (injCocone.ι.app j)
            (hfac_ι j).symm
        naturality := fun j j' f => by
          ext; show cokernel.π _ ≫ Q.map f ≫ _ = cokernel.π _ ≫ _ ≫ _
          rw [← Category.assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc]
          simp [cokernel.π_desc, Functor.const_obj_map] }
    have hqColim : IsColimit qCocone := by
      let injColim := colimit.isColimit Inj
      have hπ (j) : cokernel.π (η.app j) ≫ qCocone.ι.app j =
          injCocone.ι.app j ≫ cokernel.π ι' := cokernel.π_desc _ _ _
      exact
      { desc := fun s => cokernel.desc ι' (injColim.desc ⟨s.pt,
          { app := fun j => cokernel.π (η.app j) ≫ s.ι.app j
            naturality := fun j j' a => by
              dsimp; rw [Category.comp_id, ← Category.assoc,
                ← (cokernel.π_desc _ _ _ : cokernel.π (η.app j) ≫ Q.map a = _),
                Category.assoc, s.w] }⟩) (hc'.hom_ext fun j => by
          rw [comp_zero]; conv_lhs => rw [← Category.assoc, hfac_ι j, Category.assoc]
          rw [injColim.fac, ← Category.assoc, cokernel.condition, zero_comp])
        fac := fun s j => (cancel_epi (cokernel.π (η.app j))).mp (by
          rw [← Category.assoc, hπ, Category.assoc, cokernel.π_desc, injColim.fac])
        uniq := fun s m hm => (cancel_epi (cokernel.π ι')).mp (by
          rw [cokernel.π_desc]; exact injColim.hom_ext fun j => by
            rw [injColim.fac, ← Category.assoc, ← hπ, Category.assoc, hm]) }
    have hSE_j : ∀ j, (ShortComplex.mk (η.app j) (cokernel.π (η.app j))
        (cokernel.condition (η.app j))).ShortExact := fun j => by
      haveI : Mono (η.app j) := hη_mono j
      exact ShortComplex.ShortExact.mk'
        (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (η.app j)))
        inferInstance inferInstance
    obtain ⟨y, hy⟩ := sheafH_exists_preimage_extClass hSE n hI x
    obtain ⟨j₀, y_j, hy_j⟩ := ih (Y' := Q) qCocone hqColim y
    haveI : Mono (η.app j₀) := hη_mono j₀
    let x_j : Sheaf.H (Y'.obj j₀) (n + 1) := y_j.comp (hSE_j j₀).extClass rfl
    refine ⟨j₀, x_j, ?_⟩
    show ConcreteCategory.hom ((sheafCohomologyFunctor X (n + 1)).map (c'.ι.app j₀)) x_j = x
    rw [show x_j = y_j.comp (hSE_j j₀).extClass rfl from rfl]
    exact (sheafCohomologyFunctor_map_extClass_of_map_eq (hSE_j j₀) hSE
      (ShortComplex.homMk (c'.ι.app j₀) (injCocone.ι.app j₀)
        (qCocone.ι.app j₀) (hfac_ι j₀) (cokernel.π_desc _ _ _).symm) n hy_j).trans hy

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

/-- On a Noetherian space and for a filtered diagram, the canonical comparison morphism
    `colim H^n(F_j) ⟶ H^n(colim F_j)` is epi. -/
theorem sheafH_filtered_colimit_comparison_epi
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) (c' : Cocone Y') (hc' : IsColimit c') :
    Epi (sheafH_filtered_colimit_comparison Y' n c') := by
  rw [AddCommGrpCat.epi_iff_surjective]
  intro x
  obtain ⟨j, y, hy⟩ := sheafH_filtered_colimit_surj n Y' c' hc' x
  refine ⟨ConcreteCategory.hom (colimit.ι (Y' ⋙ sheafCohomologyFunctor X n) j) y, ?_⟩
  change ConcreteCategory.hom
      ((colimit.ι (Y' ⋙ sheafCohomologyFunctor X n) j) ≫
        sheafH_filtered_colimit_comparison Y' n c') y = x
  rw [colimit_ι_sheafH_filtered_colimit_comparison]
  exact hy

/-- **Sheaf cohomology commutes with filtered colimits** on Noetherian spaces.
    If `H^n(F_j) = 0` for all pieces of a filtered diagram, then `H^n(colim F_j) = 0`.
    Derived from `sheafH_filtered_colimit_surj`: every element lifts to some `H^n(F_j) = 0`. -/
theorem sheafH_preserves_filtered_colimits
    {X : TopCat.{u}} [NoetherianSpace X]
    {J' : Type u} [SmallCategory J'] [IsFiltered J']
    (Y' : J' ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)
    (c' : Cocone Y') (hc' : IsColimit c')
    (n : ℕ)
    (hvan : ∀ j, Subsingleton (Sheaf.H (Y'.obj j) n)) :
    Subsingleton (Sheaf.H c'.pt n) := by
  constructor; intro x y
  obtain ⟨jx, ex, hex⟩ := sheafH_filtered_colimit_surj n Y' c' hc' x
  obtain ⟨jy, ey, hey⟩ := sheafH_filtered_colimit_surj n Y' c' hc' y
  rw [← hex, ← hey, @Subsingleton.elim _ (hvan jx) ex 0,
      @Subsingleton.elim _ (hvan jy) ey 0, map_zero, map_zero]
