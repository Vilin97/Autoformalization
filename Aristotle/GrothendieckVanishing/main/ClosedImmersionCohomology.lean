import Aristotle.GrothendieckVanishing.main.CohomologyAPI
import Aristotle.GrothendieckVanishing.main.FlasqueCohomology

/-!
  ClosedImmersionCohomology.lean — Closed immersion cohomology infrastructure

  Provides:
  1. `closedIncl_pushforward_preservesEpis/Monos` (pushforward preserves epis/monos)
  2. `closedIncl_pushforward_shortExact` (pushforward preserves ShortExact)
  3. `PushforwardHVanishing` (pushforward preserves cohomological vanishing)
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

1. PushforwardHVanishing: pushforward along closed immersion preserves vanishing
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
  have hW_bot : (Opens.map (TopCat.closedIncl hs)).obj W = ⊥ :=
    le_antisymm (fun ⟨_, hy⟩ h => absurd hy h.2) bot_le
  haveI : Subsingleton (F'.obj (op W)) := AddCommGrpCat.subsingleton_of_isZero (by
    change IsZero (G.obj (op ((Opens.map (TopCat.closedIncl hs)).obj W)))
    rw [hW_bot]; exact Gsh.isTerminalOfEmpty.isZero)
  rw [← TopCat.Presheaf.germ_res_apply F'
    (homOfLE (show W ≤ U from inf_le_left)) x ⟨hxU, hx⟩ sU]
  simp [Subsingleton.eq_zero (ConcreteCategory.hom (F'.map (homOfLE (show W ≤ U from
    inf_le_left)).op) sU)]

/-- Pushforward along a closed immersion preserves epis: if `f : F ⟶ G` is epi in
    sheaves on the closed subspace, then `i_*(f)` is epi in sheaves on the ambient space.
    Proof: stalkwise surjectivity (identity on the closed set, zero outside). -/
theorem epi_pushforward_map_closedIncl
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {F G : TopCat.Presheaf AddCommGrpCat.{u} (TopCat.of s)}
    (hF : F.IsSheaf) (hG : G.IsSheaf)
    (f : (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s)) ⟶
      (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of s))) [Epi f] :
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
    haveI : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map f.val) :=
      (AddCommGrpCat.epi_iff_surjective _).mpr
        (((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
            (T := f.val)).mp
          ((Sheaf.isLocallySurjective_iff_epi'
              AddCommGrpCat.{u} _).mpr inferInstance)) z)
    have hnat : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
        (ConcreteCategory.hom (TopCat.closedIncl hs) z)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} (TopCat.closedIncl hs)).map f.val) ≫
      TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} (TopCat.closedIncl hs) G z =
    TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} (TopCat.closedIncl hs) F z ≫
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
        (TopCat.closedIncl hs) G z), hnat]
    exact epi_comp _ _
  · intro b
    rw [pushforward_closedIncl_stalk_eq_zero (hs := hs) (G := G) hG hx b]
    exact ⟨0, AddMonoidHom.map_zero _⟩

instance closedIncl_pushforward_preservesEpis
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hs)).PreservesEpimorphisms where
  preserves {F G} f hf := by
    letI : Epi f := hf
    simpa using epi_pushforward_map_closedIncl
      (hs := hs) (F := F.val) (G := G.val) F.cond G.cond f

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

-- Pushforward along closed immersion preserves cohomological vanishing.
-- Proof by induction: n=0 via sections, n=1 via Ext^0 surjectivity, n≥2 via LES dimension shift.
theorem PushforwardHVanishing
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    {G : TopCat.Presheaf AddCommGrpCat.{u} (TopCat.of Z)} (hG : G.IsSheaf)
    (n : ℕ) (h : Subsingleton (Sheaf.H (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)) n)) :
    Subsingleton (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.closedIncl hZ)).obj (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z))) n) := by
  let Gsh : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z) := ⟨G, hG⟩
  let i := TopCat.closedIncl hZ
  suffices ∀ (m : ℕ) (G' : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)),
      Subsingleton (Sheaf.H G' m) →
      Subsingleton (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G') m) from
    this n Gsh h
  intro m; induction m with
  | zero =>
    intro G' hG'
    let F' := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G'
    have hsec : Subsingleton (G'.val.obj (op ⊤)) := by
      letI := hG'; exact (sheafH0EquivSections G').toEquiv.subsingleton_congr.mp ‹_›
    have hobj : F'.val.obj (op ⊤) = G'.val.obj (op ⊤) := by
      change G'.val.obj (op ((Opens.map i).obj ⊤)) = G'.val.obj (op ⊤)
      rw [Opens.map_top]
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
      exact sheafH_subsingleton_H1_of_flasque_of_epi_app_top_map i
        ip.shortExact_shortComplex hSE_X (Opens.map_top i) hG'
    | succ m =>
      haveI := hG'
      haveI : Subsingleton (Sheaf.H
          ((ip.shortComplex.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i)).X₃) (m + 1)) :=
        ih_push ip.shortComplex.X₃ (sheafH_dimension_shift_X₃ ip.shortExact_shortComplex m)
      haveI : Subsingleton (Sheaf.H
          ((ip.shortComplex.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i)).X₂) (m + 2)) :=
        FlasqueVanishing _ _ (m + 1)
      exact sheafH_dimension_shift_of_both hSE_X (m + 1)

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
    haveI := TopCat.closedIncl_unit_stalk_isIso hZ Fsh ⟨x, hxZ⟩
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
    topologicalKrullDim_lt_of_isIrreducible_of_isClosed hYcl
      (Set.compl_ne_univ.mpr (Set.nonempty_iff_ne_empty.mpr (Opens.coe_eq_empty.not.mpr hV)))
      (lt_of_lt_of_le hn le_top)
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
              (TopCat.closedIncl_unit_stalk_isIso hYcl Csh ⟨x, hxY⟩)
          exact stalk_zero_of_ses_g_iso hSE x inferInstance a
        · exact stalk_zero_of_shortExact_kernel hSE x
            (fun b => hStalksOnV x (by rwa [Set.mem_compl_iff, not_not] at hxY) b) a)
    simpa using hSX₁_zero'
  exact subsingleton_sheafH_of_shortExact_middle hSE n
    (_root_.sheafH_subsingleton_of_isZero S.X₁ hSX₁_zero n)
    (by
      simpa [S, closedImmersionSES, i, CY] using
        (PushforwardHVanishing Y hYcl
          (G := CY.val) CY.cond n
          (ih (TopCat.of Y) n (G := CY.val) CY.cond hY_dim_lt hn)))
