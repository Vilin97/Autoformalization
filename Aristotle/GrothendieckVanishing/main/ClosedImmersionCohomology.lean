import Aristotle.GrothendieckVanishing.main.ClosedImmersion
import Aristotle.GrothendieckVanishing.main.CohomologyAPI
import Aristotle.GrothendieckVanishing.main.FlasqueCohomology

/-!
  ClosedImmersionCohomology.lean — Closed immersion cohomology infrastructure

  Provides:
  1. `PushforwardHIso` / `PushforwardHVanishing` (pushforward preserves cohomology)
  2. `epi_unit_of_closedImmersion` (adjunction unit is epi)
  3. `closedImmersionSES` (short exact sequence from closed immersion)

  Depends on `ClosedImmersion.lean` for the closed-inclusion pushforward exactness API,
  on `CohomologyAPI.lean` for LES-facing `Sheaf.H` wrappers, and on
  `FlasqueCohomology.lean` for `FlasqueVanishing`. `FlasqueVanishing.lean` supplies
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

1. PushforwardHIso: pushforward along closed immersion preserves cohomology,
   using the pushforward exactness API from `ClosedImmersion.lean`
2. closedImmersionSES: the adjunction unit F -> i_*(i^*F) gives a short exact sequence
-/

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
  let closedIncl := TopCat.closedIncl hZ
  suffices ∀ (m : ℕ) (G' : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z)),
      AddCommGrpCat.of (Sheaf.H G' m) ≅
        AddCommGrpCat.of (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} closedIncl).obj G') m) from
    this n Gsh
  intro m; induction m with
  | zero =>
    intro G'
    let F' := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} closedIncl).obj G'
    let topIso : G'.val.obj (op ⊤) ≅ F'.val.obj (op ⊤) := eqToIso (by
      change G'.val.obj (op ⊤) = G'.val.obj (op ((Opens.map closedIncl).obj ⊤))
      rw [Opens.map_top])
    exact (sheafH0NatIsoSections (X := TopCat.of Z)).app G' ≪≫
      topIso ≪≫ ((sheafH0NatIsoSections (X := X)).app F').symm
  | succ k ih_push =>
    intro G'
    classical
    let ip : InjectivePresentation G' := Classical.choice (EnoughInjectives.presentation G')
    let S := ip.shortComplex
    let SX := S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} closedIncl)
    have hSE_X : SX.ShortExact :=
      closedIncl_pushforward_shortExact hZ ip.shortExact_shortComplex
    haveI : IsFlasqueSheaf SX.X₂ := by
      constructor; intro U V j
      change Epi (S.X₂.val.map ((Opens.map closedIncl).op.map j.op))
      exact IsFlasqueSheaf.epi_map ((Opens.map closedIncl).map j)
    cases k with
    | zero =>
      let hH1_src :
          cokernel (S.g.val.app (op ⊤)) ≅ AddCommGrpCat.of (Sheaf.H G' 1) := by
        simpa [S] using
          sheafH1_cokernel_iso_of_subsingleton_middle_presheaf
            S.X₁.cond S.X₂.cond S.X₃.cond
            (f := S.f.val) (g := S.g.val)
            (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
            (by simpa [S] using ip.shortExact_shortComplex)
            (by simpa [S] using (Ext.subsingleton_of_injective _ _ 0 :
              Subsingleton (Sheaf.H S.X₂ 1)))
      let hH1_tgt :
          cokernel (S.g.val.app (op ⊤)) ≅ AddCommGrpCat.of (Sheaf.H SX.X₁ 1) := by
        simpa [S, SX, Opens.map_top closedIncl] using
          sheafH1_cokernel_iso_of_subsingleton_middle_presheaf
            SX.X₁.cond SX.X₂.cond SX.X₃.cond
            (f := SX.f.val) (g := SX.g.val)
            (show SX.f.val ≫ SX.g.val = 0 from congrArg Sheaf.Hom.val SX.zero)
            (by simpa [SX] using hSE_X)
            (by simpa [SX] using (inferInstance : Subsingleton (Sheaf.H SX.X₂ 1)))
      exact hH1_src.symm ≪≫ hH1_tgt
    | succ m =>
      let hShift_src :
          AddCommGrpCat.of (Sheaf.H S.X₃ (m + 1)) ≅
            AddCommGrpCat.of (Sheaf.H G' (m + 2)) := by
        simpa [S] using
          sheafH_extClassIso_of_subsingleton_middle_presheaf
            S.X₁.cond S.X₂.cond S.X₃.cond
            (f := S.f.val) (g := S.g.val)
            (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
            (by simpa [S] using ip.shortExact_shortComplex)
            (m + 1)
            (by simpa [S] using
              (Ext.subsingleton_of_injective _ _ m : Subsingleton (Sheaf.H S.X₂ (m + 1))))
            (by simpa [S] using
              (Ext.subsingleton_of_injective _ _ (m + 1) :
                Subsingleton (Sheaf.H S.X₂ (m + 2))))
      let hShift_tgt :
          AddCommGrpCat.of (Sheaf.H SX.X₃ (m + 1)) ≅
            AddCommGrpCat.of (Sheaf.H SX.X₁ (m + 2)) := by
        simpa [SX] using
          sheafH_extClassIso_of_subsingleton_middle_presheaf
            SX.X₁.cond SX.X₂.cond SX.X₃.cond
            (f := SX.f.val) (g := SX.g.val)
            (show SX.f.val ≫ SX.g.val = 0 from congrArg Sheaf.Hom.val SX.zero)
            (by simpa [SX] using hSE_X)
            (m + 1)
            (by simpa [SX] using
              (inferInstance : Subsingleton (Sheaf.H SX.X₂ (m + 1))))
            (by simpa [SX] using
              (inferInstance : Subsingleton (Sheaf.H SX.X₂ (m + 2))))
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
  let closedIncl := TopCat.closedIncl hZ
  let Fsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F, hF⟩
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} closedIncl
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
        (G := ((TopCat.Sheaf.pullback AddCommGrpCat.{u} closedIncl).obj Fsh).val)
        (((TopCat.Sheaf.pullback AddCommGrpCat.{u} closedIncl).obj Fsh).cond)
        hxZ b]
      exact map_zero _⟩

/-- The short exact sequence `0 → ker(η) → F → i_*(i^*F) → 0` from a closed immersion,
    where `η` is the pullback-pushforward adjunction unit and `i : Z ↪ X` is the
    inclusion of a closed subset. -/
noncomputable def closedImmersionSES
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  let closedIncl := TopCat.closedIncl hZ
  let Fsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F, hF⟩
  let η := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} closedIncl).unit.app Fsh
  ShortComplex.mk (kernel.ι η) η (kernel.condition η)

theorem closedImmersionSES_shortExact
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf) :
    (closedImmersionSES (Z := Z) (hZ := hZ) (F := F) hF).ShortExact := by
  unfold closedImmersionSES
  haveI := epi_unit_of_closedImmersion (Z := Z) (hZ := hZ) (F := F) hF
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)) inferInstance inferInstance

/-- Closed-immersion presheaf wrapper: if the kernel term of the closed-immersion
short exact sequence and the pullback to the closed subset have subsingleton
cohomology in degree `n`, then so does the ambient sheaf. -/
theorem subsingleton_sheafH_of_closedImmersion_middle_presheaf
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf) (n : ℕ)
    (h₁ : Subsingleton
      (Sheaf.H ((closedImmersionSES (Z := Z) (hZ := hZ) (F := F) hF).X₁) n))
    (h₃ : Subsingleton
      (Sheaf.H
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (TopCat.closedIncl hZ)).obj
          (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n)) :
    Subsingleton (Sheaf.H (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) n) := by
  let closedIncl := TopCat.closedIncl hZ
  let Fsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F, hF⟩
  let FZ := ((TopCat.Sheaf.pullback AddCommGrpCat.{u} closedIncl).obj Fsh)
  let S := closedImmersionSES (Z := Z) (hZ := hZ) (F := F) hF
  have hSE := closedImmersionSES_shortExact (Z := Z) (hZ := hZ) (F := F) hF
  have h₁' : Subsingleton (Sheaf.H S.X₁ n) := by
    simpa [S] using h₁
  have h₃' : Subsingleton (Sheaf.H FZ n) := by
    simpa [closedIncl, Fsh, FZ] using h₃
  have hPush : Subsingleton (Sheaf.H S.X₃ n) := by
    simpa [S, closedImmersionSES, closedIncl, Fsh, FZ] using
      PushforwardHVanishing Z hZ FZ.cond n h₃'
  haveI : Mono S.f := hSE.mono_f
  haveI : Mono S.f.val := by
    exact (Sheaf.Hom.mono_iff_presheaf_mono
      (J := Opens.grothendieckTopology X) (D := AddCommGrpCat.{u}) S.f).1 inferInstance
  have hCok :
      Subsingleton
        (Sheaf.H (cokernel (show S.X₁ ⟶ Fsh from Sheaf.Hom.mk S.f.val)) n) := by
    let fsh : S.X₁ ⟶ Fsh := Sheaf.Hom.mk S.f.val
    have hfsh : fsh = S.f := rfl
    have hfshg : fsh ≫ S.g = 0 := by
      change S.f ≫ S.g = 0
      exact S.zero
    let hSgCok : IsColimit (CokernelCofork.ofπ S.g hfshg) := by
      simpa [hfsh, hfshg] using hSE.gIsCokernel
    let e :=
      (sheafCohomologyFunctor X n).mapIso
        ((cokernelIsCokernel fsh).coconePointUniqueUpToIso
          hSgCok)
    haveI :
        Subsingleton ↑((sheafCohomologyFunctor X n).obj
          (CokernelCofork.ofπ S.g hfshg).pt) := by
      simpa [sheafCohomologyFunctor_obj] using hPush
    exact ⟨fun a b => by
      apply (ConcreteCategory.bijective_of_isIso e.hom).1
      exact Subsingleton.elim _ _⟩
  simpa [Fsh] using
    subsingleton_sheafH_of_shortExact_middle_presheaf
      (F := S.X₁.val) (G := F) S.X₁.cond hF S.f.val n h₁' hCok

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
  have hY_dim_lt_top : topologicalKrullDim Y < ⊤ :=
    topologicalKrullDim_lt_top_of_lt_nat (by simpa [gt_iff_lt] using hn)
  have hY_dim_lt : topologicalKrullDim Y < topologicalKrullDim X :=
    topologicalKrullDim_lt_of_isIrreducible_of_isClosed hYcl
      (Set.compl_ne_univ.mpr (Set.nonempty_iff_ne_empty.mpr (Opens.coe_eq_empty.not.mpr hV)))
      hY_dim_lt_top
  let closedIncl := TopCat.closedIncl hYcl
  let CY := ((TopCat.Sheaf.pullback AddCommGrpCat.{u} closedIncl).obj Csh)
  let S := closedImmersionSES (Z := Y) (hZ := hYcl) (F := C) hC
  have hSE := closedImmersionSES_shortExact (Z := Y) (hZ := hYcl) (F := C) hC
  have hSX₁_zero : IsZero S.X₁ := by
    have hSX₁_zero' : IsZero ((⟨S.X₁.val, S.X₁.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) :=
      sheaf_isZero_of_zero_stalks X S.X₁.cond (fun x a => by
        by_cases hxY : x ∈ Y
        · haveI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.g.val) := by
            simpa [S, closedImmersionSES, closedIncl, Csh] using
              (TopCat.closedIncl_unit_stalk_isIso (C := AddCommGrpCat.{u})
                (hs := hYcl) (F := C) hC ⟨x, hxY⟩)
          exact stalk_zero_of_ses_g_iso_presheaf
            S.X₁.cond S.X₂.cond S.X₃.cond
            (f := S.f.val) (g := S.g.val)
            (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
            (by simpa [S] using hSE)
            x inferInstance a
        · exact stalk_zero_of_shortExact_kernel_presheaf
            S.X₁.cond S.X₂.cond S.X₃.cond
            (f := S.f.val) (g := S.g.val)
            (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
            (by simpa [S] using hSE)
            x
            (fun b => hStalksOnV x (by rwa [Set.mem_compl_iff, not_not] at hxY) b)
            a)
    simpa using hSX₁_zero'
  exact subsingleton_sheafH_of_closedImmersion_middle_presheaf
    (Z := Y) (hZ := hYcl) (F := C) hC n
    (by
      simpa [S] using sheafH_subsingleton_of_isZero_presheaf S.X₁.cond hSX₁_zero n)
    (by
      simpa [closedIncl, Csh, CY] using
        ih (TopCat.of Y) n (G := CY.val) CY.cond hY_dim_lt hn)
