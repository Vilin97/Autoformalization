import Aristotle.GrothendieckVanishing.main.ClosedImmersion
import Aristotle.GrothendieckVanishing.main.CohomologyAPI
import Aristotle.GrothendieckVanishing.main.FlasqueVanishing

/-!
  ClosedImmersionCohomology.lean — Closed immersion cohomology infrastructure

  Provides:
  1. `PushforwardHIso` (pushforward preserves cohomology by isomorphism)
  2. `subsingleton_sheafH_of_closedImmersion_middle`

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
    (G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z))
    (n : ℕ) :
    AddCommGrpCat.of (Sheaf.H G n) ≅
      AddCommGrpCat.of (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hZ)).obj G) n) := by
  let closedIncl := TopCat.closedIncl hZ
  revert G
  induction n with
  | zero =>
    intro G'
    let F' := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} closedIncl).obj G'
    exact (sheafH0NatIsoSections (X := TopCat.of Z)).app G' ≪≫
      eqToIso (by
        change G'.val.obj (op ⊤) = G'.val.obj (op ((Opens.map closedIncl).obj ⊤))
        rw [Opens.map_top]) ≪≫
      ((sheafH0NatIsoSections (X := X)).app F').symm
  | succ k ih_push =>
    intro G'
    classical
    let ip : InjectivePresentation G' := Classical.choice (EnoughInjectives.presentation G')
    let S := ip.shortComplex
    let SX := S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} closedIncl)
    have hSE_X : SX.ShortExact :=
      closedIncl_pushforward_shortExact hZ ip.shortExact_shortComplex
    have hFlasqueSX₂ : IsFlasqueSheaf SX.X₂ := fun j => by
      change Epi (S.X₂.val.map ((Opens.map closedIncl).op.map j.op))
      exact (isFlasque_of_injective S.X₂) ((Opens.map closedIncl).map j)
    have hSE : S.ShortExact := by simpa [S] using ip.shortExact_shortComplex
    have hSrcSub (r : ℕ) : Subsingleton (Sheaf.H S.X₂ (r + 1)) :=
      sheafH_subsingleton_of_injective S.X₂ r
    have hTgtSub (r : ℕ) : Subsingleton (Sheaf.H SX.X₂ (r + 1)) :=
      sheafH_subsingleton_of_flasque X SX.X₂ hFlasqueSX₂ r
    cases k with
    | zero =>
      exact
        (show cokernel (S.g.val.app (op ⊤)) ≅ AddCommGrpCat.of (Sheaf.H G' 1) from by
          simpa [S] using
            sheafH1_cokernel_iso_of_subsingleton_middle hSE (hSrcSub 0)).symm ≪≫
        (show cokernel (S.g.val.app (op ⊤)) ≅ AddCommGrpCat.of (Sheaf.H SX.X₁ 1) from by
          simpa [S, SX, Opens.map_top closedIncl] using
            sheafH1_cokernel_iso_of_subsingleton_middle hSE_X (hTgtSub 0))
    | succ m =>
      exact
        (show AddCommGrpCat.of (Sheaf.H S.X₃ (m + 1)) ≅
            AddCommGrpCat.of (Sheaf.H G' (m + 2)) from by
          simpa [S] using
            sheafH_succ_iso_of_subsingleton_middle hSE (m + 1) (hSrcSub m)
              (hSrcSub (m + 1))).symm ≪≫
        ih_push S.X₃ ≪≫
        (show AddCommGrpCat.of (Sheaf.H SX.X₃ (m + 1)) ≅
            AddCommGrpCat.of (Sheaf.H SX.X₁ (m + 2)) from by
          simpa [SX] using
            sheafH_succ_iso_of_subsingleton_middle hSE_X (m + 1) (hTgtSub m)
              (hTgtSub (m + 1)))

/-- Closed-immersion step: if the kernel term of the closed-immersion
short exact sequence and the pullback to the closed subset have subsingleton
cohomology in degree `n`, then so does the ambient sheaf. -/
theorem subsingleton_sheafH_of_closedImmersion_middle
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (h₁ : Subsingleton
      (Sheaf.H ((closedImmersionSES (Z := Z) (hZ := hZ) F).X₁) n))
    (h₃ : Subsingleton
      (Sheaf.H
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (TopCat.closedIncl hZ)).obj
          F) n)) :
    Subsingleton (Sheaf.H F n) := by
  let closedIncl := TopCat.closedIncl hZ
  let FZ := ((TopCat.Sheaf.pullback AddCommGrpCat.{u} closedIncl).obj F)
  let S := closedImmersionSES (Z := Z) (hZ := hZ) F
  have hSE := closedImmersionSES_shortExact (Z := Z) (hZ := hZ) F
  have h₁' : Subsingleton (Sheaf.H S.X₁ n) := by
    simpa [S] using h₁
  have h₃' : Subsingleton (Sheaf.H FZ n) := by
    simpa [closedIncl, FZ] using h₃
  have hPush : Subsingleton (Sheaf.H S.X₃ n) := by
    let e :
        Sheaf.H FZ n ≃
          Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} closedIncl).obj FZ) n :=
      Equiv.ofBijective (ConcreteCategory.hom (PushforwardHIso Z hZ FZ n).hom)
        (ConcreteCategory.bijective_of_isIso (PushforwardHIso Z hZ FZ n).hom)
    simpa [S, closedImmersionSES, closedIncl, FZ] using
      (e.subsingleton_congr).mp h₃'
  haveI : Mono S.f := hSE.mono_f
  have hCok : Subsingleton (Sheaf.H (cokernel S.f) n) := by
    let hSgCok : IsColimit (CokernelCofork.ofπ S.g S.zero) := hSE.gIsCokernel
    let e :=
      (sheafCohomologyFunctor X n).mapIso
        ((cokernelIsCokernel S.f).coconePointUniqueUpToIso hSgCok)
    haveI :
        Subsingleton ↑((sheafCohomologyFunctor X n).obj
          (CokernelCofork.ofπ S.g S.zero).pt) := by
      simpa [sheafCohomologyFunctor] using hPush
    exact ⟨fun a b => by
      apply (ConcreteCategory.bijective_of_isIso e.hom).1
      exact Subsingleton.elim _ _⟩
  simpa using
    subsingleton_sheafH_of_shortExact_middle S.f n h₁' hCok
