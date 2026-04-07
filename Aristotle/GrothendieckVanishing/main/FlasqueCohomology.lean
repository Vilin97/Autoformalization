/-
  FlasqueCohomology.lean — Cohomological vanishing for flasque sheaves

  Provides:
  1. `sheafH0EquivSections`: H^0(F) ≃+ F(⊤) (sections on ⊤)
  2. `subsingleton_of_addEquiv`: transport subsingletons across additive equivalences
  3. `flasqueVanishing`: flasque sheaves have vanishing higher cohomology

  Split from FlasqueVanishing.lean (flasque infrastructure) for file size.
-/
import Aristotle.GrothendieckVanishing.main.FlasqueVanishing
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

/-- `Ext.addEquiv₀ (Ext.mk₀ f) = f`: round-trip through the Ext^0 ≃ Hom equivalence. -/
@[simp] lemma Ext.addEquiv₀_mk₀ {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y : C} (f : X ⟶ Y) : Ext.addEquiv₀ (Ext.mk₀ f) = f := by
  rw [show Ext.mk₀ f = Ext.addEquiv₀.symm f from by
    apply Ext.addEquiv₀.injective; simp,
    AddEquiv.apply_symm_apply]

/-- `H F 0` is equivalent to sections on `⊤`. -/
noncomputable def sheafH0EquivSections {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Sheaf.H F 0 ≃+ F.val.obj (op ⊤) := by
  refine AddEquiv.trans Ext.addEquiv₀ ?_
  refine AddEquiv.trans ?_ (TopCat.Sheaf.AddCommGrpCat.uliftZMultiplesAddEquiv _)
  exact (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat Limits.isTerminalTop).homAddEquiv _ F

/-- `sheafH0EquivSections` is natural in the sheaf: the square
    `H^0(F) →[comp(mk₀ f)] H^0(G) →[sections] Γ(G)` commutes with
    `H^0(F) →[sections] Γ(F) →[f.app ⊤] Γ(G)`. -/
lemma sheafH0EquivSections_natural {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (x : Sheaf.H F 0) :
    sheafH0EquivSections G (x.comp (Ext.mk₀ f) (add_zero 0)) =
    ConcreteCategory.hom (f.val.app (op ⊤)) (sheafH0EquivSections F x) := by
  rw [show x = Ext.mk₀ (Ext.addEquiv₀ x) from (Ext.mk₀_addEquiv₀_apply x).symm,
    Ext.mk₀_comp_mk₀]; simp only [sheafH0EquivSections, AddEquiv.trans_apply]
  erw [Ext.addEquiv₀_mk₀, Ext.addEquiv₀_mk₀, Adjunction.homEquiv_naturality_right]
  change _ = ConcreteCategory.hom (f.val.app (op ⊤))
    ((TopCat.Sheaf.AddCommGrpCat.uliftZMultiplesAddEquiv (F.val.obj (op ⊤)))
      (((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat
        Limits.isTerminalTop).homEquiv _ F) (Ext.addEquiv₀ x)))
  rfl

/-- Transport subsingletons across an additive equivalence. -/
theorem subsingleton_of_addEquiv {A B : Type*} [Add A] [Add B]
    (e : A ≃+ B) [Subsingleton A] : Subsingleton B :=
  ⟨fun x y => by simpa using congrArg e (Subsingleton.elim (e.symm x) (e.symm y))⟩

/-- **Dimension shifting** via injective presentation.
    For `0 -> F -> I -> Q -> 0` with `I` injective, `Subsingleton (H Q n)`
    implies `Subsingleton (H F (n+1))`. Uses the covariant Ext LES:
    `Ext(Z, Q, n) -> Ext(Z, F, n+1) -> Ext(Z, I, n+1) = 0`
    so every element of `Ext(Z, F, n+1)` lifts to `Ext(Z, Q, n)`. -/
theorem sheafH_dimension_shift {X : TopCat.{u}}
    {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (ip : InjectivePresentation F) (n : ℕ)
    (hQ : Subsingleton (Sheaf.H ip.shortComplex.X₃ n)) :
    Subsingleton (Sheaf.H F (n + 1)) := by
  have hSE := ip.shortExact_shortComplex
  constructor; intro a b
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ _ hSE a (Ext.eq_zero_of_injective _) rfl
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₁ _ hSE b (Ext.eq_zero_of_injective _) rfl
  rw [← hc, ← hd]; congr 1; exact @Subsingleton.elim _ hQ c d

/-- H^1 vanishing via Ext^0 surjectivity: if H^1(X₂)=0 and every Ext^0 element
    of X₃ lifts to X₂, then H^1(X₁)=0. Used in flasque, pushforward, and colimit proofs. -/
theorem subsingleton_H1_via_surj {C' : Type*} [Category C'] [Abelian C'] [HasExt C']
    (Z : C') {S : ShortComplex C'} (hSE : S.ShortExact)
    (hJ : Subsingleton (Ext Z S.X₂ 1))
    (h_surj : ∀ y : Ext Z S.X₃ 0,
      ∃ z : Ext Z S.X₂ 0, z.comp (Ext.mk₀ S.g) (add_zero 0) = y) :
    Subsingleton (Ext Z S.X₁ 1) := by
  constructor; intro a b
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ _ hSE a (@Subsingleton.elim _ hJ _ _) rfl
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₁ _ hSE b (@Subsingleton.elim _ hJ _ _) rfl
  obtain ⟨c', hc'⟩ := h_surj c; obtain ⟨d', hd'⟩ := h_surj d
  simp only [← hc, ← hd, ← hc', ← hd', Ext.comp_assoc_of_second_deg_zero _ (Ext.mk₀ S.g)
    hSE.extClass rfl, hSE.comp_extClass, Ext.comp_zero _ _ 1 1 rfl]

/-- **Base case**: `H^1(F) = 0` for flasque `F`. -/
theorem sheafH_one_of_flasque {X : TopCat.{u}}
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
theorem flasqueVanishing (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
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
    exact sheafH_dimension_shift ip (n + 1) (ih ip.shortComplex.X₃ hQ_flasque)
