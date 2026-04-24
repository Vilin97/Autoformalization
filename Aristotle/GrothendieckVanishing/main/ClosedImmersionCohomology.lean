import Aristotle.GrothendieckVanishing.main.ClosedImmersion
import Aristotle.GrothendieckVanishing.main.CohomologyAPI
import Aristotle.GrothendieckVanishing.main.FlasqueVanishing

/-!
  ClosedImmersionCohomology.lean — Closed immersion cohomology infrastructure

  Provides:
  1. `PushforwardHIso` / `PushforwardHVanishing` (pushforward preserves cohomology)
  2. `subsingleton_sheafH_of_closedImmersion_middle_presheaf`

  Depends on `ClosedImmersion.lean` for the closed-inclusion pushforward exactness and
  adjunction-unit/SES API,
  on `CohomologyAPI.lean` for LES-facing `Sheaf.H` wrappers, and on
  `FlasqueVanishing.lean` for `FlasqueVanishing`, `IsFlasqueSheaf`, and
  `isFlasque_of_injective`.
-/

set_option linter.unusedSimpArgs false

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

/-! ## Closed-immersion cohomology consequences

This file starts at the cohomological layer. The closed-immersion stalk, exactness, and
adjunction-unit short exact sequence API now lives in `ClosedImmersion.lean`.
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
            (by simpa [S] using (sheafH_subsingleton_of_injective S.X₂ 0 :
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
              (sheafH_subsingleton_of_injective S.X₂ m :
                Subsingleton (Sheaf.H S.X₂ (m + 1))))
            (by simpa [S] using
              (sheafH_subsingleton_of_injective S.X₂ (m + 1) :
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
