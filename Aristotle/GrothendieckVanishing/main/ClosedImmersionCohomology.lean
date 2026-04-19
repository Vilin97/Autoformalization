import Aristotle.GrothendieckVanishing.main.FlasqueCohomology

/-!
  ClosedImmersionCohomology.lean — Closed immersion cohomology infrastructure

  Provides:
  1. `closedIncl_pushforward_preservesEpis/Monos` (pushforward preserves epis/monos)
  2. `closedIncl_pushforward_shortExact` (pushforward preserves ShortExact)
  3. `PushforwardHVanishing` (pushforward preserves cohomological vanishing)
  4. `epi_unit_of_closedImmersion` (adjunction unit is epi)
  5. `closedImmersionSES` (short exact sequence from closed immersion)

  Depends on FlasqueCohomology.lean for `FlasqueVanishing`, `sheafH0EquivSections`,
  and FlasqueVanishing.lean for `IsFlasqueSheaf`, `isFlasque_of_injective`.
-/

set_option linter.unusedSimpArgs false

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

/-- Stalks of a pushforward along a closed inclusion vanish outside the closed set:
    if `x ∉ s`, every element of `stalk(i_*(G), x)` is zero. -/
theorem pushforward_closedIncl_stalk_eq_zero
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    (G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s))
    {x : X} (hx : x ∉ s)
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).obj G).val) :
    a = 0 := by
  let F' := (TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).obj G.val
  obtain ⟨U, hxU, sU, rfl⟩ := F'.germ_exist x a
  let W : Opens X := U ⊓ ⟨sᶜ, hs.isOpen_compl⟩
  have hW_bot : (Opens.map (TopCat.closedIncl hs)).obj W = ⊥ :=
    le_antisymm (fun ⟨_, hy⟩ h => absurd hy h.2) bot_le
  haveI : Subsingleton (F'.obj (op W)) := AddCommGrpCat.subsingleton_of_isZero (by
    change IsZero (G.val.obj (op ((Opens.map (TopCat.closedIncl hs)).obj W)))
    rw [hW_bot]; exact G.isTerminalOfEmpty.isZero)
  rw [← TopCat.Presheaf.germ_res_apply F'
    (homOfLE (show W ≤ U from inf_le_left)) x ⟨hxU, hx⟩ sU]
  simp [Subsingleton.eq_zero (ConcreteCategory.hom (F'.map (homOfLE (show W ≤ U from
    inf_le_left)).op) sU)]

/-- Pushforward along a closed immersion preserves epis: if `f : F ⟶ G` is epi in
    sheaves on the closed subspace, then `i_*(f)` is epi in sheaves on the ambient space.
    Proof: stalkwise surjectivity (identity on the closed set, zero outside). -/
theorem epi_pushforward_map_closedIncl
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {F G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)}
    (f : F ⟶ G) [Epi f] :
    Epi ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).map f) := by
  letI : Balanced (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := balanced_of_strongEpiCategory
  rw [← Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u}]
  change TopCat.Presheaf.IsLocallySurjective
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).map f).val
  rw [TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks]
  intro x; by_cases hx : (x : X) ∈ s
  · let z : TopCat.of s := ⟨x, hx⟩
    haveI : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs) F.val z) :=
      TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        AddCommGrpCat.{u} (TopCat.closedIncl_isInducing hs) _ z
    haveI : IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs) G.val z) :=
      TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        AddCommGrpCat.{u} (TopCat.closedIncl_isInducing hs) _ z
    haveI : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map f.val) :=
      (AddCommGrpCat.epi_iff_surjective _).mpr
        (((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
            (T := f.val)).mp
          ((Sheaf.isLocallySurjective_iff_epi'
              AddCommGrpCat.{u} _).mpr inferInstance)) z)
    have hnat : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
        (ConcreteCategory.hom (TopCat.closedIncl hs) z)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).map f.val) ≫
      TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} (TopCat.closedIncl hs) G.val z =
    TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} (TopCat.closedIncl hs) F.val z ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map f.val := by
      apply TopCat.Presheaf.stalk_hom_ext; intro U hU
      rw [TopCat.Presheaf.stalkFunctor_map_germ_assoc,
        TopCat.Presheaf.stalkPushforward_germ,
        TopCat.Presheaf.stalkPushforward_germ_assoc,
        TopCat.Presheaf.stalkFunctor_map_germ]; rfl
    apply (AddCommGrpCat.epi_iff_surjective _).mp
    change Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
        ((ConcreteCategory.hom (TopCat.closedIncl hs)) z)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).map f.val))
    rw [← epi_comp_iff_of_isIso _ (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs) G.val z), hnat]
    exact epi_comp _ _
  · intro b
    rw [pushforward_closedIncl_stalk_eq_zero hs G hx b]
    exact ⟨0, AddMonoidHom.map_zero _⟩

instance closedIncl_pushforward_preservesEpis
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).PreservesEpimorphisms where
  preserves f := epi_pushforward_map_closedIncl hs f

instance closedIncl_pushforward_preservesMonos
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).PreservesMonomorphisms := inferInstance

-- Pushforward along closed immersion preserves ShortExact.
theorem closedIncl_pushforward_shortExact
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s))}
    (hSE : S.ShortExact) :
    (S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs))).ShortExact := by
  let F := TopCat.Sheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)
  haveI := hSE.mono_f; haveI := hSE.epi_g
  haveI : Mono (F.map S.f) := inferInstance
  haveI : Epi (F.map S.g) := inferInstance
  exact ShortComplex.ShortExact.mk'
    (hSE.exact.map_of_mono_of_preservesKernel _ hSE.mono_f inferInstance) ‹_› ‹_›

-- Epi of g at ⊤ from H^1(X₁)=0 via LES + adj + separator
theorem epi_g_app_top_of_H1_vanishing
    {Z : TopCat.{u}}
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
    {X : TopCat.{u}}
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
      haveI := hG'
      exact ext_dimension_shift _ hSE_X (m + 1)
        (ih_push ip.shortComplex.X₃
          (sheafH_dimension_shift_X₃ ip.shortExact_shortComplex m))
        (FlasqueVanishing _ _ (m + 1))

-- The adjunction unit F → i_*(i^*F) is epi for closed immersions.
-- Proof: stalkwise surjective (identity on Z, maps to 0 outside Z).
-- Requires: stalkPushforward_iso_of_isInducing + stalk of i_*G = 0 outside Z.
-- epi via surjective on stalks
theorem epi_unit_of_closedImmersion
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
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
    exact fun b => ⟨0, by
      rw [pushforward_closedIncl_stalk_eq_zero hZ _ hxZ b]; exact map_zero _⟩

/-- The short exact sequence `0 → ker(η) → F → i_*(i^*F) → 0` from a closed immersion,
    where `η` is the pullback-pushforward adjunction unit and `i : Z ↪ X` is the
    inclusion of a closed subset. -/
noncomputable def closedImmersionSES
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  let i := TopCat.closedIncl hZ
  let η := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).unit.app F
  ShortComplex.mk (kernel.ι η) η (kernel.condition η)

theorem closedImmersionSES_shortExact
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (closedImmersionSES Z hZ F).ShortExact := by
  delta closedImmersionSES
  haveI := epi_unit_of_closedImmersion Z hZ F
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)) inferInstance inferInstance

/-- Vanishing for a sheaf supported on the complement of an open V, via closed-immersion SES.
    Given:
    - C is a sheaf on irreducible Noetherian X
    - V ≠ ⊥ is an open with n > dim Vᶜ
    - IH gives vanishing on all spaces of smaller dimension
    - Stalks of C vanish at all points of V (the `hStalksOnV` hypothesis)
    Concludes H^n(C) = 0 by building the SES on Y = Vᶜ. -/
theorem closedComplementVanishing
    {X : TopCat.{u}} [NoetherianSpace X] [IrreducibleSpace X]
    (V : Opens X) (hV : V ≠ ⊥)
    (C : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (ih : VanishingIH.{u} (topologicalKrullDim X))
    (hn : ↑n > topologicalKrullDim (Set.compl (V : Set X)))
    (hStalksOnV : ∀ x ∈ V,
      ∀ (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj C.val), a = 0) :
    Subsingleton (Sheaf.H C n) := by
  set Y := (V : Set X)ᶜ
  have hYcl : IsClosed Y := V.2.isClosed_compl
  have hY_dim_lt : topologicalKrullDim Y < topologicalKrullDim X :=
    topologicalKrullDim_lt_of_isIrreducible_of_isClosed hYcl
      (Set.compl_ne_univ.mpr (Set.nonempty_iff_ne_empty.mpr (Opens.coe_eq_empty.not.mpr hV)))
      (lt_of_lt_of_le hn le_top)
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
    (PushforwardHVanishing Y hYcl _ n (@ih (TopCat.of Y) _ n _ hY_dim_lt hn))
