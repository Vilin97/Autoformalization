import Aristotle.GrothendieckVanishing.main.CohomologyAPI
import Aristotle.GrothendieckVanishing.main.FlasqueCohomology

/-!
  ClosedImmersionCohomology.lean — Closed immersion cohomology infrastructure

  Provides:
  1. `closedIncl_pushforward_preservesEpis/Monos` (pushforward preserves epis/monos)
  2. `closedIncl_pushforward_shortExact` (pushforward preserves ShortExact)
  3. `PushforwardHIso` / `PushforwardHVanishing` (pushforward preserves cohomology)
  4. `epi_unit_of_closedImmersion` (adjunction unit is epi)
  5. `closedImmersionSES` (short exact sequence from closed immersion)

  Depends on CohomologyAPI.lean for LES-facing `Sheaf.H` wrappers and on
  FlasqueCohomology.lean for `FlasqueVanishing`. FlasqueVanishing.lean supplies
  `IsFlasqueSheaf` and `isFlasque_of_injective`.
-/

set_option linter.unusedSimpArgs false

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

/-- The induction hypothesis for Grothendieck vanishing: vanishing holds for all
    sheaf-valued presheaves on all spaces of strictly smaller Krull dimension than X. -/
abbrev VanishingIH (dimX : WithBot ℕ∞) : Prop :=
  ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
    (m : ℕ) {G : TopCat.Presheaf AddCommGrpCat.{u} Y} (hG : G.IsSheaf),
    topologicalKrullDim Y < dimX →
    m > topologicalKrullDim Y →
    Subsingleton (Sheaf.H (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} Y) m)

/-! ## Building blocks for the closed-open decomposition

ReducibleVanishing and IrreduciblePosVanishing require two building blocks:

1. PushforwardHIso: pushforward along closed immersion preserves cohomology
   (adjunction + mono preservation + exactness of i_*)
2. closedImmersionSES: the adjunction unit F -> i_*(i^*F) gives a short exact sequence
-/

/-- Stalks of a pushforward along a closed inclusion vanish outside the closed set:
    if `x ∉ s`, every element of `stalk(i_*(G), x)` is zero. -/
theorem pushforward_closedIncl_stalk_eq_zero
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {G : TopCat.Presheaf AddCommGrpCat.{u} (TopCat.of s)} (hG : G.IsSheaf)
    {x : X} (hx : x ∉ s)
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).obj G)) :
    a = 0 := by
  let Gsh : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s) := ⟨G, hG⟩
  let F' := (TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).obj G
  obtain ⟨U, hxU, sU, rfl⟩ := F'.germ_exist x a
  let W : Opens X := U ⊓ ⟨sᶜ, hs.isOpen_compl⟩
  have hW_le : W ≤ ⟨sᶜ, hs.isOpen_compl⟩ := inf_le_right
  haveI : Subsingleton (F'.obj (op W)) := AddCommGrpCat.subsingleton_of_isZero (by
    change IsZero (G.obj (op ((Opens.map (TopCat.closedIncl hs)).obj W)))
    rw [TopCat.closedIncl_map_eq_bot_of_le_compl hs hW_le]
    exact Gsh.isTerminalOfEmpty.isZero)
  rw [← TopCat.Presheaf.germ_res_apply F'
    (homOfLE (show W ≤ U from inf_le_left)) x ⟨hxU, hx⟩ sU]
  simp [Subsingleton.eq_zero (ConcreteCategory.hom (F'.map (homOfLE (show W ≤ U from
    inf_le_left)).op) sU)]

/-- Pushforward along a closed immersion preserves epis: if `f : F ⟶ G` is epi in
    presheaves on the closed subspace, then `i_*(f)` is epi in sheaves on the ambient
    space whenever `f` is locally surjective.
    Proof: stalkwise surjectivity (identity on the closed set, zero outside). -/
theorem epi_pushforward_map_closedIncl_of_locallySurjective
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {F G : TopCat.Presheaf AddCommGrpCat.{u} (TopCat.of s)}
    (hF : F.IsSheaf) (hG : G.IsSheaf)
    (f : F ⟶ G)
    (hf_loc : TopCat.Presheaf.IsLocallySurjective f) :
    Epi ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).map (show
        (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)) ⟶
          (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)) from
            Sheaf.Hom.mk f)) := by
  let fsh : (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)) ⟶
      (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)) := Sheaf.Hom.mk f
  letI : Balanced (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := balanced_of_strongEpiCategory
  change Epi ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).map fsh)
  rw [← Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u}
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).map fsh)]
  change TopCat.Presheaf.IsLocallySurjective
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).map fsh).val
  rw [TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks]
  intro x; by_cases hx : (x : X) ∈ s
  · let z : TopCat.of s := ⟨x, hx⟩
    haveI : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map f) :=
      (AddCommGrpCat.epi_iff_surjective _).mpr
        (((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
            (T := f)).mp hf_loc) z)
    have hnat : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
        ((TopCat.closedIncl hs) z)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).map f) ≫
      TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} (TopCat.closedIncl hs) G z =
    TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} (TopCat.closedIncl hs) F z ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map f := by
      apply TopCat.Presheaf.stalk_hom_ext; intro U hU
      rw [TopCat.Presheaf.stalkFunctor_map_germ_assoc,
        TopCat.Presheaf.stalkPushforward_germ,
        TopCat.Presheaf.stalkPushforward_germ_assoc,
        TopCat.Presheaf.stalkFunctor_map_germ]; rfl
    apply (AddCommGrpCat.epi_iff_surjective _).mp
    change Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
        ((TopCat.closedIncl hs) z)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).map f))
    rw [← epi_comp_iff_of_isIso _ (TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hs) G z), hnat]
    exact epi_comp _ _
  · intro b
    rw [pushforward_closedIncl_stalk_eq_zero (hs := hs) (G := G) hG hx b]
    exact ⟨0, AddMonoidHom.map_zero _⟩

/-- Wrapper around `epi_pushforward_map_closedIncl_of_locallySurjective`: an epi of
    sheaves on the closed subspace pushes forward to an epi on the ambient space. -/
theorem epi_pushforward_map_closedIncl
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {F G : TopCat.Presheaf AddCommGrpCat.{u} (TopCat.of s)}
    (hF : F.IsSheaf) (hG : G.IsSheaf)
    (f : F ⟶ G)
    (hf : Epi (show (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)) ⟶
        (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)) from
          Sheaf.Hom.mk f)) :
    Epi ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).map (show
        (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)) ⟶
          (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)) from
            Sheaf.Hom.mk f)) := by
  let fsh : (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)) ⟶
      (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)) := Sheaf.Hom.mk f
  letI : Epi fsh := by
    simpa [fsh] using hf
  letI : Balanced (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := balanced_of_strongEpiCategory
  have hf_loc : TopCat.Presheaf.IsLocallySurjective f := by
    simpa [fsh] using
      (show Sheaf.IsLocallySurjective fsh from
        (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} fsh).mpr inferInstance)
  simpa [fsh] using
    epi_pushforward_map_closedIncl_of_locallySurjective
      (hs := hs) (F := F) (G := G) hF hG f hf_loc

instance closedIncl_pushforward_preservesEpis
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).PreservesEpimorphisms where
  preserves {F G} f hf := by
    letI : Epi f := hf
    letI : Balanced (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := balanced_of_strongEpiCategory
    have hf_loc : TopCat.Presheaf.IsLocallySurjective f.val := by
      simpa using
        (show Sheaf.IsLocallySurjective f from
          (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} f).mpr inferInstance)
    simpa using epi_pushforward_map_closedIncl_of_locallySurjective
      (hs := hs) (F := F.val) (G := G.val) F.cond G.cond f.val hf_loc

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

-- Pushforward along closed immersion preserves sheaf cohomology.
-- Proof by induction: n=0 via sections, n=1 via the cokernel model of H¹,
-- n≥2 via source/target dimension-shift isomorphisms and the induction hypothesis on X₃.
noncomputable def PushforwardHIso
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    {G : TopCat.Presheaf AddCommGrpCat.{u} (TopCat.of Z)} (hG : G.IsSheaf)
    (n : ℕ) :
    AddCommGrpCat.of (Sheaf.H (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)) n) ≅
      AddCommGrpCat.of (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hZ)).obj (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z))) n) := by
  let Gsh : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z) := ⟨G, hG⟩
  let i := TopCat.closedIncl hZ
  suffices ∀ (m : ℕ) (G' : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)),
      AddCommGrpCat.of (Sheaf.H G' m) ≅
        AddCommGrpCat.of (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G') m) from
    this n Gsh
  intro m; induction m with
  | zero =>
    intro G'
    let F' := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G'
    let topIso : G'.val.obj (op ⊤) ≅ F'.val.obj (op ⊤) := eqToIso (by
      change G'.val.obj (op ⊤) = G'.val.obj (op ((Opens.map i).obj ⊤))
      rw [Opens.map_top])
    exact (sheafH0NatIsoSections (X := TopCat.of Z)).app G' ≪≫
      topIso ≪≫ ((sheafH0NatIsoSections (X := X)).app F').symm
  | succ k ih_push =>
    intro G'
    classical
    let ip : InjectivePresentation G' := Classical.choice (EnoughInjectives.presentation G')
    let S := ip.shortComplex
    let SX := S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i)
    have hSE_X : SX.ShortExact :=
      closedIncl_pushforward_shortExact hZ ip.shortExact_shortComplex
    haveI : IsFlasqueSheaf SX.X₂ := by
      constructor; intro U V j
      change Epi (S.X₂.val.map ((Opens.map i).op.map j.op))
      exact IsFlasqueSheaf.epi_map ((Opens.map i).map j)
    cases k with
    | zero =>
      let hH1_src :
          cokernel (S.g.val.app (op ⊤)) ≅ AddCommGrpCat.of (Sheaf.H G' 1) := by
        simpa [S] using
          sheafH1_cokernel_iso_of_subsingleton_middle ip.shortExact_shortComplex
            (Ext.subsingleton_of_injective _ _ 0)
      let hH1_tgt :
          cokernel (S.g.val.app (op ⊤)) ≅ AddCommGrpCat.of (Sheaf.H SX.X₁ 1) := by
        simpa [S, SX, Opens.map_top i] using
          sheafH1_cokernel_iso_of_subsingleton_middle hSE_X
            (inferInstance : Subsingleton (Sheaf.H SX.X₂ 1))
      exact hH1_src.symm ≪≫ hH1_tgt
    | succ m =>
      let hShift_src :
          AddCommGrpCat.of (Sheaf.H S.X₃ (m + 1)) ≅
            AddCommGrpCat.of (Sheaf.H G' (m + 2)) := by
        simpa [S] using
          sheafH_extClassIso_of_subsingleton_middle ip.shortExact_shortComplex (m + 1)
            (Ext.subsingleton_of_injective _ _ m)
            (Ext.subsingleton_of_injective _ _ (m + 1))
      let hShift_tgt :
          AddCommGrpCat.of (Sheaf.H SX.X₃ (m + 1)) ≅
            AddCommGrpCat.of (Sheaf.H SX.X₁ (m + 2)) :=
        sheafH_extClassIso_of_subsingleton_middle hSE_X (m + 1)
          (inferInstance : Subsingleton (Sheaf.H SX.X₂ (m + 1)))
          (inferInstance : Subsingleton (Sheaf.H SX.X₂ (m + 2)))
      exact hShift_src.symm ≪≫ ih_push S.X₃ ≪≫ hShift_tgt

theorem PushforwardHVanishing
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    {G : TopCat.Presheaf AddCommGrpCat.{u} (TopCat.of Z)} (hG : G.IsSheaf)
    (n : ℕ) (h : Subsingleton (Sheaf.H (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)) n)) :
    Subsingleton (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hZ)).obj (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z))) n) := by
  let e :
      Sheaf.H (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)) n ≃
        Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
          (TopCat.closedIncl hZ)).obj (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z))) n :=
    Equiv.ofBijective (ConcreteCategory.hom (PushforwardHIso Z hZ hG n).hom)
      (ConcreteCategory.bijective_of_isIso (PushforwardHIso Z hZ hG n).hom)
  exact (e.subsingleton_congr).mp h

-- The adjunction unit F → i_*(i^*F) is epi for closed immersions.
-- Proof: stalkwise surjective (identity on Z, maps to 0 outside Z).
-- Requires: stalkPushforward_iso_of_isInducing + stalk of i_*G = 0 outside Z.
-- epi via surjective on stalks
theorem epi_unit_of_closedImmersion
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf) :
    Epi ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
      (TopCat.closedIncl hZ)).unit.app (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) := by
  let i := TopCat.closedIncl hZ
  let Fsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F, hF⟩
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i
  rw [← Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} (adj.unit.app Fsh),
    show Sheaf.IsLocallySurjective (adj.unit.app Fsh) =
      TopCat.Presheaf.IsLocallySurjective (adj.unit.app Fsh).val from rfl,
    TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks]
  intro x; by_cases hxZ : (x : X) ∈ Z
  · -- x ∈ Z: stalk map is surjective (it's an iso)
    haveI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
        ((TopCat.closedIncl hZ) ⟨x, hxZ⟩)).map (adj.unit.app Fsh).val) := by
      simpa [Fsh] using
        (TopCat.closedIncl_unit_stalk_isIso (C := AddCommGrpCat.{u})
          (hs := hZ) (F := F) hF ⟨x, hxZ⟩)
    exact (ConcreteCategory.bijective_of_isIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} ((TopCat.closedIncl hZ) ⟨x, hxZ⟩)).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
          (TopCat.closedIncl hZ)).unit.app Fsh).val)).2
  · -- x ∉ Z: target stalk is 0 (pushforward has zero stalk outside closed Z)
    exact fun b => ⟨0, by
      rw [pushforward_closedIncl_stalk_eq_zero
        (hs := hZ)
        (G := ((TopCat.Sheaf.pullback AddCommGrpCat.{u} i).obj Fsh).val)
        (((TopCat.Sheaf.pullback AddCommGrpCat.{u} i).obj Fsh).cond)
        hxZ b]
      exact map_zero _⟩

/-- The short exact sequence `0 → ker(η) → F → i_*(i^*F) → 0` from a closed immersion,
    where `η` is the pullback-pushforward adjunction unit and `i : Z ↪ X` is the
    inclusion of a closed subset. -/
noncomputable def closedImmersionSES
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  let i := TopCat.closedIncl hZ
  let Fsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F, hF⟩
  let η := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).unit.app Fsh
  ShortComplex.mk (kernel.ι η) η (kernel.condition η)

theorem closedImmersionSES_shortExact
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf) :
    (closedImmersionSES (Z := Z) (hZ := hZ) (F := F) hF).ShortExact := by
  unfold closedImmersionSES
  haveI := epi_unit_of_closedImmersion (Z := Z) (hZ := hZ) (F := F) hF
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
    {C : TopCat.Presheaf AddCommGrpCat.{u} X} (hC : C.IsSheaf) (n : ℕ)
    (ih : VanishingIH.{u} (topologicalKrullDim X))
    (hn : ↑n > topologicalKrullDim (Set.compl (V : Set X)))
    (hStalksOnV : ∀ x ∈ V,
      ∀ (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj C), a = 0) :
    Subsingleton (Sheaf.H (⟨C, hC⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) n) := by
  let Csh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨C, hC⟩
  set Y := (V : Set X)ᶜ
  have hYcl : IsClosed Y := V.2.isClosed_compl
  have hY_dim_lt : topologicalKrullDim Y < topologicalKrullDim X :=
    topologicalKrullDim_lt_of_isIrreducible_of_isClosed_of_lt_coe_nat hYcl
      (Set.compl_ne_univ.mpr (Set.nonempty_iff_ne_empty.mpr (Opens.coe_eq_empty.not.mpr hV)))
      hn
  let i := TopCat.closedIncl hYcl
  let CY := ((TopCat.Sheaf.pullback AddCommGrpCat.{u} i).obj Csh)
  let S := closedImmersionSES (Z := Y) (hZ := hYcl) (F := C) hC
  have hSE := closedImmersionSES_shortExact (Z := Y) (hZ := hYcl) (F := C) hC
  have hSX₁_zero : IsZero S.X₁ := by
    have hSX₁_zero' : IsZero ((⟨S.X₁.val, S.X₁.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) :=
      sheaf_isZero_of_zero_stalks X S.X₁.cond (fun x a => by
        by_cases hxY : x ∈ Y
        · haveI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.g.val) := by
            simpa [S, closedImmersionSES, i, Csh] using
              (TopCat.closedIncl_unit_stalk_isIso (C := AddCommGrpCat.{u})
                (hs := hYcl) (F := C) hC ⟨x, hxY⟩)
          exact stalk_zero_of_ses_g_iso hSE x inferInstance a
        · exact stalk_zero_of_shortExact_kernel hSE x
            (fun b => hStalksOnV x (by rwa [Set.mem_compl_iff, not_not] at hxY) b) a)
    simpa using hSX₁_zero'
  exact subsingleton_sheafH_of_shortExact_middle hSE n
    (_root_.sheafH_subsingleton_of_isZero S.X₁ hSX₁_zero n)
    (by
      let e : Sheaf.H CY n ≃ Sheaf.H S.X₃ n := by
        simpa [S, closedImmersionSES, i, CY] using
          Equiv.ofBijective
            (ConcreteCategory.hom (PushforwardHIso Y hYcl CY.cond n).hom)
            (ConcreteCategory.bijective_of_isIso (PushforwardHIso Y hYcl CY.cond n).hom)
      exact (e.subsingleton_congr).mp
        (ih (TopCat.of Y) n (G := CY.val) CY.cond hY_dim_lt hn))
