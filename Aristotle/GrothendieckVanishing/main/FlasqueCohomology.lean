import Aristotle.GrothendieckVanishing.main.CohomologyAPI

/-!
# FlasqueCohomology — Cohomological vanishing for flasque sheaves

Provides:
* `sheafH_dimension_shift`: dimension shifting via short exact sequence with injective middle term
* `FlasqueVanishing`: flasque sheaves have vanishing higher cohomology

General cohomology API (`sheafH0EquivSections`, `subsingleton_of_addEquiv`) lives in
`CohomologyAPI.lean`.
-/

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

/-- **Dimension shifting** via short exact sequence with injective middle term.
    For `0 → X₁ → X₂ → X₃ → 0` with `X₂` injective, `Subsingleton (H X₃ n)`
    implies `Subsingleton (H X₁ (n+1))`. Thin wrapper over `ext_dimension_shift`. -/
theorem sheafH_dimension_shift {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    [Injective S.X₂] (n : ℕ)
    (hQ : Subsingleton (Sheaf.H S.X₃ n)) :
    Subsingleton (Sheaf.H S.X₁ (n + 1)) :=
  ext_dimension_shift _ hS n hQ (Ext.subsingleton_of_injective _ _ n)

/-- **Base case**: `H^1(F) = 0` for flasque `F`. -/
private theorem sheafH_one_of_flasque {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (h : IsFlasqueSheaf F) :
    Subsingleton (Sheaf.H F 1) := by
  obtain ⟨ip⟩ := EnoughInjectives.presentation F
  exact subsingleton_H1_via_surj _ ip.shortExact_shortComplex
    (Ext.subsingleton_of_injective _ _ 0) (ext_zero_map_surjective ip.shortExact_shortComplex h)

/-- **Flasque sheaves have vanishing higher cohomology** (Nugent, PR #35790).

    The proof is by induction on `n`:
    - Base: `H^1(F) = 0` by `sheafH_one_of_flasque` (Ext LES + Zorn surjectivity).
    - Step: embed `F` into injective `I`, form `0 -> F -> I -> Q -> 0`.
      Since `I` is injective hence flasque, and `F` is flasque, `Q` is also flasque
      by `isFlasque_X₃_of_shortExact`. By dimension shifting, `H^{n+2}(F) = H^{n+1}(Q)`,
      and the latter vanishes by the induction hypothesis. -/
theorem FlasqueVanishing (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (h : ∀ {U V : Opens X} (i : U ⟶ V), Epi (F.val.map i.op))
    (n : ℕ) :
    Subsingleton (Sheaf.H F (n + 1)) := by
  induction n generalizing F with
  | zero => exact sheafH_one_of_flasque F h
  | succ n ih =>
    obtain ⟨ip⟩ := EnoughInjectives.presentation F
    have hSE := ip.shortExact_shortComplex
    have hI_flasque : IsFlasqueSheaf ip.shortComplex.X₂ := isFlasque_of_injective _
    have hQ_flasque : IsFlasqueSheaf ip.shortComplex.X₃ :=
      isFlasque_X₃_of_shortExact hSE h hI_flasque
    exact sheafH_dimension_shift ip.shortExact_shortComplex (n + 1) (ih ip.shortComplex.X₃ hQ_flasque)
