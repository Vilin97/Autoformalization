import Aristotle.GrothendieckVanishing.main.CohomologyAPI

/-!
# FlasqueCohomology — Cohomological vanishing for flasque sheaves

Provides:
* `FlasqueVanishing`: flasque sheaves have vanishing higher cohomology

General sheaf-cohomology API lives in `CohomologyAPI.lean`.
-/

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

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
  | zero => exact sheafH_subsingleton_H1_of_flasque F
  | succ n ih =>
    obtain ⟨ip⟩ := EnoughInjectives.presentation F
    have hSE := ip.shortExact_shortComplex
    haveI : IsFlasqueSheaf ip.shortComplex.X₃ := isFlasque_X₃_of_shortExact hSE
    haveI := ih ip.shortComplex.X₃
    exact sheafH_dimension_shift ip.shortExact_shortComplex (n + 1)

/-- Presheaf-boundary form of `FlasqueVanishing`. -/
theorem sheafH_subsingleton_of_flasque_presheaf
    (X : TopCat.{u}) {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf)
    [IsFlasqueSheaf (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)]
    (n : ℕ) :
    Subsingleton (Sheaf.H (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) (n + 1)) := by
  simpa using
    (FlasqueVanishing X (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) n)
