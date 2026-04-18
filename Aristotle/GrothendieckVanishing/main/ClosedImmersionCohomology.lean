/-
  ClosedImmersionCohomology.lean — Closed immersion cohomology infrastructure

  Provides:
  1. `PushforwardHVanishing` (pushforward preserves cohomological vanishing)
  2. `epi_unit_of_closedImmersion` (adjunction unit is epi)
  3. `closedImmersionSES` (short exact sequence from closed immersion)

  Depends on FlasqueCohomology.lean for `FlasqueVanishing`, `sheafH0EquivSections`,
  and FlasqueVanishing.lean for `IsFlasqueSheaf`, `isFlasque_of_injective`.
-/
import Aristotle.GrothendieckVanishing.main.FlasqueCohomology

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

/-- The induction hypothesis for Grothendieck vanishing: vanishing holds for all
    sheaves on all spaces of strictly smaller Krull dimension than X. -/
abbrev VanishingIH (dimX : WithBot ℕ∞) : Prop :=
  ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
    (m : ℕ) (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
    topologicalKrullDim Y < dimX →
    m > topologicalKrullDim Y →
    Subsingleton (Sheaf.H G m)

/-! ## Building blocks for the closed-open decomposition

ReducibleVanishing and IrreduciblePosVanishing require two building blocks:

1. PushforwardHVanishing: pushforward along closed immersion preserves vanishing
   (adjunction + mono preservation + exactness of i_*)
2. closedImmersionSES: the adjunction unit F -> i_*(i^*F) gives a short exact sequence
-/

-- Stalkwise surjectivity of pushed-forward g
private theorem closedIncl_pushforward_epi_g
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s))}
    (hSE : S.ShortExact) :
    Epi ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).map S.g) := by
  letI : Balanced (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := balanced_of_strongEpiCategory
  rw [← Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u}]
  change TopCat.Presheaf.IsLocallySurjective
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).map S.g).val
  rw [TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks]
  intro x; by_cases hx : (x : X) ∈ s
  · let z : TopCat.of s := ⟨x, hx⟩
    haveI : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs) S.X₂.val z) :=
      TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        AddCommGrpCat.{u} hs.isClosedEmbedding_subtypeVal.isInducing _ z
    haveI : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs) S.X₃.val z) :=
      TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        AddCommGrpCat.{u} hs.isClosedEmbedding_subtypeVal.isInducing _ z
    have hg_surj : Function.Surjective
        (ConcreteCategory.hom
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
            S.g.val)) :=
      ((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
          (T := S.g.val)).mp
        ((Sheaf.isLocallySurjective_iff_epi'
            AddCommGrpCat.{u} _).mpr hSE.epi_g)) z
    apply (AddCommGrpCat.epi_iff_surjective _).mp
    have hnat : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
        (ConcreteCategory.hom (TopCat.closedIncl hs) z)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).map S.g.val) ≫
      TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} (TopCat.closedIncl hs) S.X₃.val z =
    TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} (TopCat.closedIncl hs) S.X₂.val z ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map S.g.val := by
      apply TopCat.Presheaf.stalk_hom_ext; intro U hU
      simp only [TopCat.Presheaf.stalkFunctor_map_germ_assoc,
        TopCat.Presheaf.stalkPushforward_germ,
        TopCat.Presheaf.stalkPushforward_germ_assoc,
        TopCat.Presheaf.stalkFunctor_map_germ]; rfl
    haveI : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map S.g.val) :=
      (AddCommGrpCat.epi_iff_surjective _).mpr hg_surj
    change Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
        ((ConcreteCategory.hom (TopCat.closedIncl hs)) z)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).map S.g.val))
    haveI : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
        ((ConcreteCategory.hom (TopCat.closedIncl hs)) z)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).map S.g.val) ≫
        TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
          (TopCat.closedIncl hs) S.X₃.val z) := by
      rw [hnat]; exact epi_comp _ _
    rw [show (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
        ((ConcreteCategory.hom (TopCat.closedIncl hs)) z)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).map S.g.val) =
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
          ((ConcreteCategory.hom (TopCat.closedIncl hs)) z)).map
          ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).map S.g.val) ≫
        TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
          (TopCat.closedIncl hs) S.X₃.val z) ≫
      inv (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs) S.X₃.val z) from by
      rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]]
    exact epi_comp _ _
  · intro b
    have hb : b = 0 := by
      let F := (TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).obj S.X₃.val
      obtain ⟨U, hxU, sU, rfl⟩ := F.germ_exist x b
      let W : Opens X := U ⊓ ⟨sᶜ, hs.isOpen_compl⟩
      have hxW : x ∈ W := ⟨hxU, hx⟩
      have hW_bot : (Opens.map (TopCat.closedIncl hs)).obj W = ⊥ :=
        le_antisymm (fun ⟨_, hy⟩ h => absurd hy h.2) bot_le
      have hFW_zero : IsZero (F.obj (op W)) := by
        change IsZero (S.X₃.val.obj (op ((Opens.map (TopCat.closedIncl hs)).obj W)))
        rw [hW_bot]; exact S.X₃.isTerminalOfEmpty.isZero
      let sW := ConcreteCategory.hom (F.map (homOfLE (show W ≤ U from inf_le_left)).op) sU
      have hsW_eq : sW = 0 := by
        have h0 : (𝟙 (F.obj (op W)) : _ ⟶ _) = 0 := hFW_zero.eq_of_src _ _
        calc sW = ConcreteCategory.hom (𝟙 (F.obj (op W))) sW := (ConcreteCategory.id_apply sW).symm
          _ = 0 := by rw [h0]; exact AddMonoidHom.zero_apply _
      rw [← TopCat.Presheaf.germ_res_apply F
        (homOfLE (show W ≤ U from inf_le_left)) x hxW sU]
      change ConcreteCategory.hom (F.germ W x hxW) sW = 0
      rw [hsW_eq]; exact AddMonoidHom.map_zero _
    rw [hb]
    exact ⟨0, AddMonoidHom.map_zero _⟩

-- Pushforward along closed immersion preserves ShortExact.
theorem closedIncl_pushforward_shortExact
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s))}
    (hSE : S.ShortExact) :
    (S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs))).ShortExact := by
  haveI := hSE.mono_f
  haveI : Mono ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).map S.f) :=
    Functor.map_mono _ _
  have hExact : (S.map
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs))).Exact :=
    hSE.exact.map_of_mono_of_preservesKernel _ hSE.mono_f inferInstance
  haveI : Epi ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).map S.g) :=
    closedIncl_pushforward_epi_g hs hSE
  exact ShortComplex.ShortExact.mk' hExact ‹_› ‹_›

-- Epi of g at ⊤ from H^1(X₁)=0 via LES + adj + separator
theorem epi_g_app_top_of_H1_vanishing
    {Z : TopCat.{u}} [NoetherianSpace Z]
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} Z)}
    (hSE : S.ShortExact)
    (hG' : Subsingleton (Sheaf.H S.X₁ 1)) :
    Epi (S.g.val.app (op ⊤)) := by
  rw [AddCommGrpCat.epi_iff_surjective]; intro r
  let R_top := S.X₃.val.obj (op ⊤)
  let φ_hom : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ R_top :=
    AddCommGrpCat.ofHom
      (AddMonoidHom.mk' (fun (n : ULift.{u} ℤ) => (n.down : ℤ) • (r : R_top))
        (fun a b => by simp [add_zsmul]))
  let adj_Z := constantSheafAdj (Opens.grothendieckTopology Z)
    AddCommGrpCat.{u} Limits.isTerminalTop
  let φ := (adj_Z.homEquiv _ S.X₃).symm φ_hom
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ _ hSE _ rfl
    (@Subsingleton.elim _ hG' _ _)
  have hψ : Ext.addEquiv₀ z ≫ S.g = φ := by
    apply Ext.addEquiv₀.symm.injective
    change Ext.mk₀ (Ext.addEquiv₀ z ≫ S.g) = Ext.addEquiv₀.symm φ
    rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]; exact hz
  let ψ_hom := (adj_Z.homEquiv _ S.X₂) (Ext.addEquiv₀ z)
  have hfact := Adjunction.homEquiv_naturality_right adj_Z (Ext.addEquiv₀ z) S.g
  rw [hψ, Equiv.apply_symm_apply] at hfact
  change φ_hom = ψ_hom ≫ S.g.val.app (op ⊤) at hfact
  refine ⟨ψ_hom (ULift.up 1), ?_⟩
  change (ConcreteCategory.hom (ψ_hom ≫ S.g.val.app (op ⊤))) (ULift.up 1) = r
  rw [← hfact]; simp [φ_hom]

-- Surjectivity of Ext⁰ map from epi at ⊤ via adjunction + projectivity of ULift ℤ
theorem ext0_surj_of_epi_top
    {X : TopCat.{u}} [NoetherianSpace X]
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hg_epi_top : Epi (S.g.val.app (op ⊤))) :
    ∀ y : Sheaf.H S.X₃ 0,
      ∃ z : Sheaf.H S.X₂ 0,
        z.comp (Ext.mk₀ S.g) (add_zero 0) = y := by
  intro y; suffices ∃ ψ : _ ⟶ S.X₂, ψ ≫ S.g = Ext.addEquiv₀ y by
    obtain ⟨ψ, hψ⟩ := this
    exact ⟨Ext.mk₀ ψ, by rw [Ext.mk₀_comp_mk₀, hψ, Ext.mk₀_addEquiv₀_apply]⟩
  have hΓg : Epi ((Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map S.g) := by
    have h := hg_epi_top
    exact @epi_of_epi_fac _ _ _ _ _ _ _ _ (epi_comp' h (IsIso.epi_of_iso _))
      ((Sheaf.ΓNatIsoSheafSections _ _ Limits.isTerminalTop).inv.naturality S.g).symm
  let adj := constantSheafΓAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let M := AddCommGrpCat.of (ULift.{u} ℤ)
  haveI : Projective M := ulift_int_projective
  exact ⟨(adj.homEquiv M _).symm (Projective.factorThru
    ((adj.homEquiv M _) (Ext.addEquiv₀ y))
    ((Sheaf.Γ _ _).map S.g)), by
    apply (adj.homEquiv M _).injective
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
      Projective.factorThru_comp]⟩

-- Pushforward along closed immersion preserves cohomological vanishing.
-- Proof by induction: n=0 via sections, n=1 via Ext^0 surjectivity, n≥2 via LES dimension shift.
theorem PushforwardHVanishing
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    [NoetherianSpace X]
    (G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)) (n : ℕ)
    (h : Subsingleton (Sheaf.H G n)) :
    Subsingleton (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hZ)).obj G) n) := by
  let i := TopCat.closedIncl hZ
  suffices ∀ (m : ℕ) (G' : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)),
      Subsingleton (Sheaf.H G' m) →
      Subsingleton (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G') m) from
    this n G h
  intro m; induction m with
  | zero =>
    intro G' hG'
    let F' := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G'
    have hsec : Subsingleton (G'.val.obj (op ⊤)) := by
      letI := hG'; exact (sheafH0EquivSections G').toEquiv.subsingleton_congr.mp ‹_›
    have hobj : F'.val.obj (op ⊤) = G'.val.obj (op ⊤) := by
      change G'.val.obj (op ((Opens.map i).obj ⊤)) = G'.val.obj (op ⊤)
      simp [show ((Opens.map i).obj ⊤ : Opens (TopCat.of Z)) = ⊤ from by ext; simp [Opens.map]]
    constructor; intro a b
    apply (sheafH0EquivSections F').injective
    exact @Subsingleton.elim (F'.val.obj (op ⊤)) (hobj ▸ hsec) _ _
  | succ k ih_push =>
    intro G' hG'
    obtain ⟨ip⟩ := EnoughInjectives.presentation G'
    have hSE_X : (ip.shortComplex.map
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i)).ShortExact :=
      closedIncl_pushforward_shortExact hZ ip.shortExact_shortComplex
    haveI : IsFlasqueSheaf (ip.shortComplex.map
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i)).X₂ := by
      constructor; intro U V j
      change Epi (ip.shortComplex.X₂.val.map ((Opens.map i).op.map j.op))
      exact IsFlasqueSheaf.epi_map ((Opens.map i).map j)
    cases k with
    | zero =>
      exact subsingleton_H1_via_surj _ hSE_X (FlasqueVanishing _ _ 0)
        (ext0_surj_of_epi_top (by
          show Epi (ip.shortComplex.g.val.app (op ((Opens.map i).obj ⊤)))
          rw [show ((Opens.map i).obj ⊤ : Opens (TopCat.of Z)) = ⊤ from by ext; simp [Opens.map]]
          exact epi_g_app_top_of_H1_vanishing ip.shortExact_shortComplex hG'))
    | succ m =>
      exact ext_dimension_shift _ hSE_X (m + 1)
        (ih_push ip.shortComplex.X₃ (ext_dimension_shift_X₃ _ ip.shortExact_shortComplex (m + 1)
          (Ext.subsingleton_of_injective _ _ m) hG'))
        (FlasqueVanishing _ _ (m + 1))

-- The adjunction unit F → i_*(i^*F) is epi for closed immersions.
-- Proof: stalkwise surjective (identity on Z, maps to 0 outside Z).
-- Requires: stalkPushforward_iso_of_isInducing + stalk of i_*G = 0 outside Z.
-- epi via surjective on stalks
theorem epi_unit_of_closedImmersion
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    [NoetherianSpace X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Epi ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
      (TopCat.closedIncl hZ)).unit.app F) := by
  let i := TopCat.closedIncl hZ
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i
  rw [← Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} (adj.unit.app F),
    show Sheaf.IsLocallySurjective (adj.unit.app F) =
      TopCat.Presheaf.IsLocallySurjective (adj.unit.app F).val from rfl,
    TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks]
  intro x; by_cases hxZ : (x : X) ∈ Z
  · -- x ∈ Z: stalk map is surjective (it's an iso)
    haveI := TopCat.closedIncl_unit_stalk_isIso hZ F ⟨x, hxZ⟩
    exact (ConcreteCategory.bijective_of_isIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} ((TopCat.closedIncl hZ) ⟨x, hxZ⟩)).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
          (TopCat.closedIncl hZ)).unit.app F).val)).2
  · -- x ∉ Z: target stalk is 0 (pushforward has zero stalk outside closed Z)
    -- Show stalk is IsZero by showing all colimit injections (germs) are 0.
    -- Each germ_V factors through V' = V ∩ (X\Z) where the source is 0.
    let D := (OpenNhds.inclusion x).op ⋙
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} i).obj F)).val
    have hstalk_zero : IsZero (colimit D) := by
      rw [IsZero.iff_id_eq_zero]
      apply colimit.hom_ext; intro ⟨⟨V, hxV⟩⟩
      simp only [comp_zero, Category.comp_id]
      let Zc : Opens X := ⟨Zᶜ, hZ.isOpen_compl⟩
      let V'_nhd : OpenNhds x := ⟨V ⊓ Zc, ⟨hxV, hxZ⟩⟩
      rw [show colimit.ι D (op ⟨V, hxV⟩) =
        D.map (homOfLE (show V'_nhd.1 ≤ V from inf_le_left) : V'_nhd ⟶ ⟨V, hxV⟩).op ≫
          colimit.ι D (op V'_nhd) from (colimit.w D _).symm]
      suffices IsZero (D.obj (op V'_nhd)) by
        rw [this.eq_zero_of_src (colimit.ι D (op V'_nhd)), comp_zero]
      change IsZero (((TopCat.Sheaf.pullback AddCommGrpCat.{u} i).obj F).val.obj
        (op ((Opens.map i).obj V'_nhd.1)))
      rw [show (Opens.map i).obj V'_nhd.1 = ⊥ from le_antisymm (fun ⟨_, hy⟩ hmem => by
        simp only [Opens.map, Opens.mem_mk] at hmem; exact absurd hy (hmem.2 ·)) bot_le]
      exact (TopCat.Sheaf.isTerminalOfEmpty _).isZero
    -- The stalk is IsZero → surjective
    exact fun b => ⟨0, by simp [(@Subsingleton.elim _
      (AddCommGrpCat.subsingleton_of_isZero hstalk_zero) b 0).symm]⟩

/-- The short exact sequence `0 → ker(η) → F → i_*(i^*F) → 0` from a closed immersion,
    where `η` is the pullback-pushforward adjunction unit and `i : Z ↪ X` is the
    inclusion of a closed subset. -/
noncomputable def closedImmersionSES
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    [NoetherianSpace X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  let i := TopCat.closedIncl hZ
  let η := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).unit.app F
  ShortComplex.mk (kernel.ι η) η (kernel.condition η)

theorem closedImmersionSES_shortExact
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    [NoetherianSpace X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (closedImmersionSES Z hZ F).ShortExact := by
  delta closedImmersionSES
  haveI := epi_unit_of_closedImmersion Z hZ F
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)) inferInstance inferInstance

/-- Vanishing for a sheaf supported on the complement of an open V, via closed-immersion SES.
    Given:
    - C is a sheaf on irreducible Noetherian X
    - V ≠ ⊥ is an open with n > dim X
    - IH gives vanishing on all spaces of smaller dimension
    - Stalks of C vanish at all points of V (the `hStalksOnV` hypothesis)
    Concludes H^n(C) = 0 by building the SES on Y = Vᶜ. -/
theorem closedComplementVanishing
    {X : TopCat.{u}} [NoetherianSpace X] [IrreducibleSpace X]
    (V : Opens X) (hV : V ≠ ⊥)
    (C : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (hn : ↑n > topologicalKrullDim X)
    (ih : VanishingIH.{u} (topologicalKrullDim X))
    (hStalksOnV : ∀ x ∈ V,
      ∀ (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj C.val), a = 0) :
    Subsingleton (Sheaf.H C n) := by
  set Y := (V : Set X)ᶜ
  have hYcl : IsClosed Y := V.2.isClosed_compl
  have hY_dim_lt : topologicalKrullDim Y < topologicalKrullDim X :=
    topologicalKrullDim_lt_of_isIrreducible_of_isClosed hYcl (compl_ne_univ_of_ne_bot hV)
      (lt_of_le_of_lt (topologicalKrullDim_subspace_le (X := (↑X : Type u)) Y)
        (lt_of_lt_of_le hn le_top))
  let S := closedImmersionSES Y hYcl C
  have hSE := closedImmersionSES_shortExact Y hYcl C
  exact subsingleton_sheafH_of_shortExact_middle hSE n
    (by apply Ext.subsingleton_of_isZero_tgt; apply sheaf_isZero_of_zero_stalks X; intro x a
        by_cases hxY : x ∈ Y
        · haveI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.g.val) :=
            TopCat.closedIncl_unit_stalk_isIso hYcl C ⟨x, hxY⟩
          exact stalk_zero_of_ses_g_iso hSE x inferInstance a
        · exact stalk_zero_of_shortExact_kernel hSE x
            (fun b => hStalksOnV x (by rwa [Set.mem_compl_iff, not_not] at hxY) b) a)
    (PushforwardHVanishing Y hYcl _ n
      (@ih (TopCat.of Y) _ n _ hY_dim_lt (lt_trans hY_dim_lt hn)))
