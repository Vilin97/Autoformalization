import Aristotle.GrothendieckVanishing.main.CohomologyAPI

/-!
# FlasqueCohomology — Cohomological vanishing for flasque sheaves

Provides:
* `sheafH_dimension_shift`: dimension shifting via short exact sequence with injective middle term
* `FlasqueVanishing`: flasque sheaves have vanishing higher cohomology

General cohomology API (`sheafH0EquivSections`) lives in `CohomologyAPI.lean`.
-/

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

/-- **Dimension shifting** via short exact sequence with injective middle term.
    For `0 → X₁ → X₂ → X₃ → 0` with `X₂` injective, `Subsingleton (H X₃ n)`
    implies `Subsingleton (H X₁ (n+1))`. Thin wrapper over `ext_dimension_shift`. -/
theorem sheafH_dimension_shift {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    [Injective S.X₂] (n : ℕ)
    [Subsingleton (Sheaf.H S.X₃ n)] :
    Subsingleton (Sheaf.H S.X₁ (n + 1)) :=
  ext_dimension_shift _ hS n ‹_› (Ext.subsingleton_of_injective _ _ n)

/-- General dimension shifting at `Sheaf.H` level: both vanishing hypotheses are
    instance-implicit. More general than `sheafH_dimension_shift` (no `Injective` needed). -/
theorem sheafH_dimension_shift_of_both {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (Sheaf.H S.X₃ n)]
    [Subsingleton (Sheaf.H S.X₂ (n + 1))] :
    Subsingleton (Sheaf.H S.X₁ (n + 1)) :=
  ext_dimension_shift _ hS n ‹_› ‹_›

/-- Reverse dimension shift at `Sheaf.H` level with injective middle term:
    `Subsingleton (H X₁ (n+2))` implies `Subsingleton (H X₃ (n+1))`.
    Requires degree ≥ 1 since `Ext^0(Z, I)` is not necessarily trivial for injective `I`. -/
theorem sheafH_dimension_shift_X₃ {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    [Injective S.X₂] (n : ℕ)
    [Subsingleton (Sheaf.H S.X₁ (n + 2))] :
    Subsingleton (Sheaf.H S.X₃ (n + 1)) :=
  ext_dimension_shift_X₃ _ hS (n + 1) (Ext.subsingleton_of_injective _ _ n) ‹_›

/-- **Base case**: `H^1(F) = 0` for flasque `F`. -/
private theorem sheafH_one_of_flasque {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [IsFlasqueSheaf F] :
    Subsingleton (Sheaf.H F 1) := by
  obtain ⟨ip⟩ := EnoughInjectives.presentation F
  have hSE := ip.shortExact_shortComplex
  exact subsingleton_H1_via_surj _ hSE
    (Ext.subsingleton_of_injective _ _ 0) (fun y => by
      suffices ∃ ψ : _ ⟶ ip.shortComplex.X₂, ψ ≫ ip.shortComplex.g = Ext.addEquiv₀ y by
        obtain ⟨ψ, hψ⟩ := this
        exact ⟨Ext.mk₀ ψ, by rw [Ext.mk₀_comp_mk₀, hψ, Ext.mk₀_addEquiv₀_apply]⟩
      haveI : Epi ((Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
          ip.shortComplex.g) := by
        have h := epi_app_of_shortExact_flasque hSE ⊤
        exact @epi_of_epi_fac _ _ _ _ _ _ _ _ (epi_comp' h (IsIso.epi_of_iso _))
          ((Sheaf.ΓNatIsoSheafSections _ _ Limits.isTerminalTop).inv.naturality
            ip.shortComplex.g).symm
      let adj := constantSheafΓAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      exact ⟨(adj.homEquiv _ ip.shortComplex.X₂).symm (Projective.factorThru
        ((adj.homEquiv _ ip.shortComplex.X₃) (Ext.addEquiv₀ y))
        ((Sheaf.Γ _ _).map ip.shortComplex.g)), by
        apply (adj.homEquiv _ ip.shortComplex.X₃).injective
        rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
          Projective.factorThru_comp]⟩)

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
