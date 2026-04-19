import Aristotle.GrothendieckVanishing.main.CohomologyAPI

/-!
# FlasqueCohomology — Cohomological vanishing for flasque sheaves

Provides:
* `FlasqueVanishing`: flasque sheaves have vanishing higher cohomology

General sheaf-cohomology API lives in `CohomologyAPI.lean`.
-/

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

/-- **Base case**: `H^1(F) = 0` for flasque `F`. -/
private theorem sheafH_one_of_flasque {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [IsFlasqueSheaf F] :
    Subsingleton (Sheaf.H F 1) := by
  obtain ⟨ip⟩ := EnoughInjectives.presentation F
  have hSE := ip.shortExact_shortComplex
  exact sheafH_subsingleton_H1_of_injective_of_epi_app_top hSE (by
      haveI : Epi ((Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
          ip.shortComplex.g) := by
        have h := epi_app_of_shortExact_flasque hSE ⊤
        exact @epi_of_epi_fac _ _ _ _ _ _ _ _ (epi_comp' h (IsIso.epi_of_iso _))
          ((Sheaf.ΓNatIsoSheafSections _ _ Limits.isTerminalTop).inv.naturality
            ip.shortComplex.g).symm
      have hfac := (Sheaf.ΓNatIsoSheafSections _ _ Limits.isTerminalTop).hom.naturality
        ip.shortComplex.g
      change Epi (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj (op ⊤)).map
        ip.shortComplex.g)
      haveI : Epi ((Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat).map ip.shortComplex.g ≫
          (Sheaf.ΓNatIsoSheafSections _ _ Limits.isTerminalTop).hom.app ip.shortComplex.X₃) :=
        epi_comp' (inferInstance : Epi ((Sheaf.Γ (Opens.grothendieckTopology X)
          AddCommGrpCat).map ip.shortComplex.g)) (IsIso.epi_of_iso _)
      exact epi_of_epi_fac hfac.symm)

/-- **Flasque sheaves have vanishing higher cohomology** (Nugent, PR #35790).

    The proof is by induction on `n`:
    - Base: `H^1(F) = 0` by `sheafH_one_of_flasque` (Ext LES + Zorn surjectivity).
    - Step: embed `F` into injective `I`, form `0 -> F -> I -> Q -> 0`.
      Since `I` is injective hence flasque, and `F` is flasque, `Q` is also flasque
      by `isFlasque_X₃_of_shortExact`. By dimension shifting, `H^{n+2}(F) = H^{n+1}(Q)`,
      and the latter vanishes by the induction hypothesis. -/
instance FlasqueVanishing (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [IsFlasqueSheaf F]
    (n : ℕ) :
    Subsingleton (Sheaf.H F (n + 1)) := by
  induction n generalizing F with
  | zero => exact sheafH_one_of_flasque F
  | succ n ih =>
    obtain ⟨ip⟩ := EnoughInjectives.presentation F
    have hSE := ip.shortExact_shortComplex
    haveI : IsFlasqueSheaf ip.shortComplex.X₃ := isFlasque_X₃_of_shortExact hSE
    haveI := ih ip.shortComplex.X₃
    exact sheafH_dimension_shift ip.shortExact_shortComplex (n + 1)
