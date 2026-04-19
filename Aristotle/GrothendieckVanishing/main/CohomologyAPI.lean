import Aristotle.GrothendieckVanishing.main.FlasqueVanishing

/-!
# Sheaf Cohomology API

Centralizes results about sheaf cohomology `Sheaf.H` and its underlying `Ext` groups
so that downstream files never need to unfold `Sheaf.H` or use `Ext` directly.

## Main results

* `ext_dimension_shift` / `ext_dimension_shift_X₃`: dimension shifting via Ext LES
* `Ext.subsingleton_of_isZero_tgt`: zero target ⟹ subsingleton Ext (general abelian category)
* `extClass_naturality`: naturality of the extension class
* `subsingleton_H1_via_surj`: H^1 vanishing via Ext^0 surjectivity
* `subsingleton_sheafH_of_shortExact_middle`: LES consequence for Sheaf.H
* `sheafH_subsingleton_of_isEmpty`: empty-space vanishing
* `sheaf_isZero_of_zero_stalks`: zero stalks imply zero sheaf
* `sheafH_subsingleton_of_isZero`: zero sheaf ⟹ subsingleton cohomology
* `stalk_zero_of_ses_g_iso`: stalk vanishing from SES with iso on `g`
* `stalk_zero_of_shortExact_kernel`: stalk vanishing from SES kernel
* `sheafH0EquivSections`: H^0(F) ≃+ F(⊤)
* `sheafH0EquivSections_natural`: naturality of the above
* `epi_app_top_of_subsingleton_sheafH1`: H^1 vanishing gives surjectivity on top sections
* `sheafH0_surj_of_epi_app_top`: surjectivity on top sections gives H^0 surjectivity
* `sheafH_subsingleton_H1_via_epi_app_top`: H^1 vanishing via surjective top sections
* `sheafH_subsingleton_H1_of_flasque`: flasque sheaves have vanishing `H¹`
* `sheafH_subsingleton_H1_of_flasque_of_epi_app_top`: flasque-middle-term `H¹` vanishing
-/

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

/-! ## Abstract Ext dimension shift helpers -/

section ExtDimShift
variable {C' : Type*} [Category C'] [Abelian C'] [HasExt C']

/-- Dimension shift for Ext via LES: given `0 → X₁ → X₂ → X₃ → 0` short exact,
    `Ext^n(Z, X₃) = 0` and `Ext^{n+1}(Z, X₂) = 0` imply `Ext^{n+1}(Z, X₁) = 0`. -/
theorem ext_dimension_shift (Z : C') {S : ShortComplex C'} (hS : S.ShortExact) (n : ℕ)
    (h₃ : Subsingleton (Ext Z S.X₃ n))
    (h₂ : Subsingleton (Ext Z S.X₂ (n + 1))) :
    Subsingleton (Ext Z S.X₁ (n + 1)) := by
  constructor; intro a b
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ _ hS a (@Subsingleton.elim _ h₂ _ _) rfl
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₁ _ hS b (@Subsingleton.elim _ h₂ _ _) rfl
  rw [← hc, ← hd, @Subsingleton.elim _ h₃ c d]

/-- Reverse dimension shift: `Ext^n(Z, X₂) = 0` and `Ext^{n+1}(Z, X₁) = 0` imply
    `Ext^n(Z, X₃) = 0`. Uses exactness at X₃ in the covariant LES. -/
theorem ext_dimension_shift_X₃ (Z : C') {S : ShortComplex C'} (hS : S.ShortExact) (n : ℕ)
    (h₂ : Subsingleton (Ext Z S.X₂ n))
    (h₁ : Subsingleton (Ext Z S.X₁ (n + 1))) :
    Subsingleton (Ext Z S.X₃ n) := by
  constructor; intro a b
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₃ _ hS a rfl (@Subsingleton.elim _ h₁ _ _)
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₃ _ hS b rfl (@Subsingleton.elim _ h₁ _ _)
  rw [← hc, ← hd, @Subsingleton.elim _ h₂ c d]

/-- Naturality of the extension class: given a morphism `φ : S₁ ⟶ S₂` of short exact sequences,
    the connecting homomorphism commutes with the induced maps on Ext groups.
    Proved via the triangulated category axiom TR3 (`complete_distinguished_triangle_morphism₁`),
    fullness/faithfulness of `singleFunctor`, and mono cancellation. -/
lemma extClass_naturality {S₁ S₂ : ShortComplex C'} (hS₁ : S₁.ShortExact)
    (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) :
    (Ext.mk₀ φ.τ₃).comp hS₂.extClass (zero_add 1) =
    hS₁.extClass.comp (Ext.mk₀ φ.τ₁) (add_zero 1) := by
  letI := HasDerivedCategory.standard C'
  ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, ShortComplex.ShortExact.extClass_hom]
  rw [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
  have comm₂ : hS₁.singleTriangle.mor₂ ≫ (DerivedCategory.singleFunctor C' 0).map φ.τ₃ =
      (DerivedCategory.singleFunctor C' 0).map φ.τ₂ ≫ hS₂.singleTriangle.mor₂ := by
    show (DerivedCategory.singleFunctor C' 0).map S₁.g ≫
      (DerivedCategory.singleFunctor C' 0).map φ.τ₃ =
      (DerivedCategory.singleFunctor C' 0).map φ.τ₂ ≫
      (DerivedCategory.singleFunctor C' 0).map S₂.g
    simp [← Functor.map_comp, φ.comm₂₃]
  obtain ⟨a', ha₁, ha₃⟩ := Pretriangulated.complete_distinguished_triangle_morphism₁
    hS₁.singleTriangle hS₂.singleTriangle
    hS₁.singleTriangle_distinguished hS₂.singleTriangle_distinguished
    ((DerivedCategory.singleFunctor C' 0).map φ.τ₂)
    ((DerivedCategory.singleFunctor C' 0).map φ.τ₃) comm₂
  simp only [ShortComplex.ShortExact.singleTriangle_mor₃] at ha₃
  rw [← ha₃]
  suffices a' = (DerivedCategory.singleFunctor C' 0).map φ.τ₁ by rw [this]; simp
  obtain ⟨a'', rfl⟩ := (DerivedCategory.singleFunctor C' 0).map_surjective a'
  congr 1
  have h : S₁.f ≫ φ.τ₂ = a'' ≫ S₂.f := by
    have := ha₁
    simp only [ShortComplex.ShortExact.singleTriangle_mor₁] at this
    rwa [← Functor.map_comp, ← Functor.map_comp,
      (DerivedCategory.singleFunctor C' 0).map_injective.eq_iff] at this
  haveI : Mono S₂.f := hS₂.mono_f
  exact (cancel_mono S₂.f).mp (by rw [← φ.comm₁₂.symm, h])

/-- If `Y` is zero in an abelian category, `Ext X Y n` is subsingleton for all `X`, `n`.
    Proof: `𝟙 Y = 0` because `Y` is zero, so `x = x ∘ mk₀(𝟙 Y) = x ∘ mk₀(0) = x ∘ 0 = 0`. -/
theorem Ext.subsingleton_of_isZero_tgt {X Y : C'} (hY : IsZero Y) (n : ℕ) :
    Subsingleton (Ext X Y n) :=
  ⟨fun a b => by
    have eq : ∀ x : Ext X Y n, x = 0 := fun x => by
      have h := Ext.comp_mk₀_id x
      rw [show (𝟙 Y : Y ⟶ Y) = 0 from hY.eq_of_src _ _, Ext.mk₀_zero] at h
      exact h.symm.trans (Ext.comp_zero x Y 0 n (add_zero n))
    exact (eq a).trans (eq b).symm⟩

end ExtDimShift

/-! ## Stalks and zero sheaves -/

/-- Naturality of the connecting map on sheaf cohomology for a morphism of short exact
    sequences. This packages `extClass_naturality` together with the two associativity
    rewrites needed to move between nested `comp` expressions and composition with the
    connecting class. -/
theorem sheafH_comp_extClass_naturality {X : TopCat.{u}}
    {S₁ S₂ : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n : ℕ)
    (y : Sheaf.H S₁.X₃ n) :
    (y.comp hS₁.extClass rfl).comp (Ext.mk₀ φ.τ₁) (add_zero (n + 1)) =
      (y.comp (Ext.mk₀ φ.τ₃) (add_zero n)).comp hS₂.extClass rfl := by
  rw [Ext.comp_assoc_of_third_deg_zero]
  rw [← extClass_naturality hS₁ hS₂ φ]
  rw [← Ext.comp_assoc_of_second_deg_zero]

/-- In a short exact sequence of sheaves, if `H^(n+1)(X₂)` is subsingleton then every
    `H^(n+1)(X₁)` class lifts along the connecting morphism from some `H^n(X₃)` class. -/
theorem sheafH_exists_preimage_extClass {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact) (n : ℕ)
    (h₂ : Subsingleton (Sheaf.H S.X₂ (n + 1)))
    (x : Sheaf.H S.X₁ (n + 1)) :
    ∃ y : Sheaf.H S.X₃ n, y.comp hS.extClass rfl = x := by
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _ hS x (@Subsingleton.elim _ h₂ _ _) rfl
  exact ⟨y, hy⟩

theorem sheaf_isZero_of_zero_stalks (X : TopCat.{u})
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hstalk : ∀ (x : X)
      (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj F.val), a = 0) :
    IsZero F := by
  have hZ : IsZero F.val := Functor.isZero F.val (fun ⟨U⟩ =>
    @AddCommGrpCat.isZero_of_subsingleton _
      ⟨fun s t => TopCat.Presheaf.section_ext F U s t fun x hx =>
        (hstalk x _).trans (hstalk x _).symm⟩)
  exact IsZero.mk
    (fun G => ⟨{ default := 0, uniq := fun f => Sheaf.Hom.ext (NatTrans.ext (funext
      fun U => (hZ.obj U).eq_zero_of_src (f.val.app U))) }⟩)
    (fun G => ⟨{ default := 0, uniq := fun f => Sheaf.Hom.ext (NatTrans.ext (funext
      fun U => (hZ.obj U).eq_zero_of_tgt (f.val.app U))) }⟩)

/-- If a sheaf is zero, then all its cohomology groups are subsingleton. -/
theorem sheafH_subsingleton_of_isZero {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (hF : IsZero F) (n : ℕ) :
    Subsingleton (Sheaf.H F n) :=
  Ext.subsingleton_of_isZero_tgt hF n

theorem stalk_zero_of_ses_g_iso
    {X : TopCat.{u}} {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hSE : S.ShortExact) (x : X)
    (hiso : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.g.val))
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj S.X₁.val) :
    a = 0 := by
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hf0 : T.map S.f.val = 0 := by
    have : T.map S.f.val ≫ T.map S.g.val = 0 := by
      rw [← T.map_comp, show S.f.val ≫ S.g.val = (S.f ≫ S.g).val from rfl, S.zero]
      change T.map ((sheafToPresheaf _ _).map (0 : S.X₁ ⟶ S.X₃)) = 0
      simp only [Functor.map_zero]
    rw [show T.map S.f.val = (T.map S.f.val ≫ T.map S.g.val) ≫ inv (T.map S.g.val)
      from by simp, this, zero_comp]
  haveI : Mono S.f := hSE.mono_f
  haveI := TopCat.Presheaf.stalkFunctor_preserves_mono (C := AddCommGrpCat.{u}) (X := X) x
  exact (AddCommGrpCat.mono_iff_injective _).mp
    (Functor.map_mono (TopCat.Sheaf.forget _ _ ⋙ T) S.f)
    (show ConcreteCategory.hom (T.map S.f.val) a = ConcreteCategory.hom (T.map S.f.val) 0
      by simp [hf0])

/-- In a short exact sequence `X₁ → X₂ → X₃`, if all stalks of `X₂` at `x` vanish, then
    all stalks of `X₁` at `x` vanish (by mono-injectivity of `f`). -/
theorem stalk_zero_of_shortExact_kernel
    {X : TopCat.{u}} {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hSE : S.ShortExact) (x : X)
    (hX₂ : ∀ (b : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj S.X₂.val), b = 0)
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj S.X₁.val) :
    a = 0 := by
  haveI : Mono S.f := hSE.mono_f
  haveI := TopCat.Presheaf.stalkFunctor_preserves_mono (C := AddCommGrpCat.{u}) (X := X) x
  exact (AddCommGrpCat.mono_iff_injective _).mp (Functor.map_mono
    (TopCat.Sheaf.forget _ _ ⋙ TopCat.Presheaf.stalkFunctor _ x) S.f)
    ((hX₂ _).trans (map_zero _).symm)

/-! ## H⁰ ≅ Sections -/

/-- `H F 0` is equivalent to sections on `⊤`. -/
noncomputable def sheafH0EquivSections {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Sheaf.H F 0 ≃+ F.val.obj (op ⊤) :=
  Ext.addEquiv₀.trans
    (((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat
        Limits.isTerminalTop).homAddEquiv _ F).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _))

/-- Naturality of `sheafH0EquivSections`: composing `x` with `mk₀ f` at degree 0
    corresponds to applying `f.app(⊤)` at the sections level. -/
lemma sheafH0EquivSections_natural {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (x : Sheaf.H F 0) :
    sheafH0EquivSections G (x.comp (Ext.mk₀ f) (add_zero 0)) =
    ConcreteCategory.hom (f.val.app (op ⊤)) (sheafH0EquivSections F x) := by
  conv_lhs => rw [show x = Ext.mk₀ (Ext.addEquiv₀ x) from
    (Ext.mk₀_addEquiv₀_apply x).symm, Ext.mk₀_comp_mk₀]
  unfold sheafH0EquivSections
  simp only [AddEquiv.trans_apply]
  have key : Ext.addEquiv₀ (Ext.mk₀ (Ext.addEquiv₀ x ≫ f)) = Ext.addEquiv₀ x ≫ f :=
    Ext.addEquiv₀.apply_symm_apply _
  erw [Adjunction.homAddEquiv_apply, Adjunction.homAddEquiv_apply, key,
    Adjunction.homEquiv_naturality_right, Adjunction.homAddEquiv_apply]
  rfl

/-- In a short exact sequence of sheaves, `H¹(X₁)=0` implies the map on global sections
    `X₂(⊤) → X₃(⊤)` is surjective. This packages the `H⁰/H¹` segment of the LES using
    `sheafH0EquivSections`. -/
theorem epi_app_top_of_subsingleton_sheafH1 {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hSE : S.ShortExact)
    (h₁ : Subsingleton (Sheaf.H S.X₁ 1)) :
    Epi (S.g.val.app (op ⊤)) := by
  rw [AddCommGrpCat.epi_iff_surjective]
  intro r
  let y : Sheaf.H S.X₃ 0 := (sheafH0EquivSections S.X₃).symm r
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ _ hSE y rfl
    (@Subsingleton.elim _ h₁ _ _)
  refine ⟨sheafH0EquivSections S.X₂ z, ?_⟩
  rw [← sheafH0EquivSections_natural, hz]
  simp [y]

/-- If `f.app (op ⊤)` is surjective on sections, then every `H⁰` class of the target
    lifts along `f`. This is the `H⁰`-surjectivity input used by
    `sheafH_subsingleton_H1_via_surj`. -/
theorem sheafH0_surj_of_epi_app_top {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (hf : Epi (f.val.app (op ⊤))) :
    ∀ y : Sheaf.H G 0, ∃ z : Sheaf.H F 0, z.comp (Ext.mk₀ f) (add_zero 0) = y := by
  intro y
  obtain ⟨s, hs⟩ := (AddCommGrpCat.epi_iff_surjective _).mp hf (sheafH0EquivSections G y)
  refine ⟨(sheafH0EquivSections F).symm s, ?_⟩
  apply (sheafH0EquivSections G).injective
  rw [sheafH0EquivSections_natural, AddEquiv.apply_symm_apply, hs]

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

/-- Sheaf-level wrapper for `subsingleton_H1_via_surj`: if `H¹(X₂)=0` and every `H⁰`
    class on `X₃` lifts along `g`, then `H¹(X₁)=0`. -/
theorem sheafH_subsingleton_H1_via_surj {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hSE : S.ShortExact)
    (h₂ : Subsingleton (Sheaf.H S.X₂ 1))
    (h_surj : ∀ y : Sheaf.H S.X₃ 0,
      ∃ z : Sheaf.H S.X₂ 0, z.comp (Ext.mk₀ S.g) (add_zero 0) = y) :
    Subsingleton (Sheaf.H S.X₁ 1) :=
  subsingleton_H1_via_surj _ hSE h₂ h_surj

/-- Sheaf-level `H¹` vanishing criterion from surjective top sections:
    if `H¹(X₂)=0` and `g.app(⊤)` is epi in a short exact sequence
    `0 → X₁ → X₂ → X₃ → 0`, then `H¹(X₁)=0`. -/
theorem sheafH_subsingleton_H1_via_epi_app_top {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hSE : S.ShortExact)
    (h₂ : Subsingleton (Sheaf.H S.X₂ 1))
    (hg : Epi (S.g.val.app (op ⊤))) :
    Subsingleton (Sheaf.H S.X₁ 1) :=
  sheafH_subsingleton_H1_via_surj hSE h₂ (sheafH0_surj_of_epi_app_top _ hg)

/-- Sheaf-level `H¹` vanishing criterion with injective middle term:
    if `X₂` is injective and `g.app(⊤)` is epi in a short exact sequence
    `0 → X₁ → X₂ → X₃ → 0`, then `H¹(X₁)=0`. -/
theorem sheafH_subsingleton_H1_of_injective_of_epi_app_top {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hSE : S.ShortExact)
    [Injective S.X₂]
    (hg : Epi (S.g.val.app (op ⊤))) :
    Subsingleton (Sheaf.H S.X₁ 1) :=
  sheafH_subsingleton_H1_via_epi_app_top hSE (Ext.subsingleton_of_injective _ _ 0) hg

/-- Flasque sheaves have vanishing `H¹`. This isolates the base case of flasque
    cohomological vanishing in the general sheaf-cohomology API. -/
theorem sheafH_subsingleton_H1_of_flasque {X : TopCat.{u}}
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

/-- Sheaf-level `H¹` vanishing criterion with flasque middle term:
    if `X₂` is flasque and `g.app(⊤)` is epi in a short exact sequence
    `0 → X₁ → X₂ → X₃ → 0`, then `H¹(X₁)=0`. -/
theorem sheafH_subsingleton_H1_of_flasque_of_epi_app_top {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hSE : S.ShortExact)
    [IsFlasqueSheaf S.X₂]
    (hg : Epi (S.g.val.app (op ⊤))) :
    Subsingleton (Sheaf.H S.X₁ 1) :=
  sheafH_subsingleton_H1_via_epi_app_top hSE (sheafH_subsingleton_H1_of_flasque S.X₂) hg

/-- Sheaf-level `H¹` vanishing criterion for a pushed-forward short exact sequence:
    if the mapped middle term is flasque and the source sequence has `H¹(X₁)=0`,
    then `H¹` vanishes on the mapped kernel, provided the caller supplies the
    identification of `f⁻¹(⊤)` with `⊤`. -/
theorem sheafH_subsingleton_H1_of_flasque_of_epi_app_top_map {X Y : TopCat.{u}}
    (f : X ⟶ Y)
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hSE : S.ShortExact)
    (hSE_map : (S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)).ShortExact)
    [IsFlasqueSheaf ((S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)).X₂)]
    (h_top : (Opens.map f).obj ⊤ = ⊤)
    (h₁ : Subsingleton (Sheaf.H S.X₁ 1)) :
    Subsingleton (Sheaf.H ((S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)).X₁) 1) := by
  refine sheafH_subsingleton_H1_of_flasque_of_epi_app_top
    (S := S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f))
    (hSE := hSE_map)
    ?_
  change Epi (S.g.val.app (op ((Opens.map f).obj ⊤)))
  rw [h_top]
  exact epi_app_top_of_subsingleton_sheafH1 hSE h₁

/-- General dimension shifting at `Sheaf.H` level: if `H^n(X₃)=0` and `H^(n+1)(X₂)=0`
    in a short exact sequence `0 → X₁ → X₂ → X₃ → 0`, then `H^(n+1)(X₁)=0`. -/
theorem sheafH_dimension_shift_of_both {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (Sheaf.H S.X₃ n)]
    [Subsingleton (Sheaf.H S.X₂ (n + 1))] :
    Subsingleton (Sheaf.H S.X₁ (n + 1)) :=
  ext_dimension_shift _ hS n ‹_› ‹_›

/-- Dimension shifting at `Sheaf.H` level with injective middle term:
    if `X₂` is injective and `H^n(X₃)=0`, then `H^(n+1)(X₁)=0`. -/
theorem sheafH_dimension_shift {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    [Injective S.X₂] (n : ℕ)
    [Subsingleton (Sheaf.H S.X₃ n)] :
    Subsingleton (Sheaf.H S.X₁ (n + 1)) :=
  ext_dimension_shift _ hS n ‹_› (Ext.subsingleton_of_injective _ _ n)

/-- Reverse dimension shift at `Sheaf.H` level with injective middle term:
    `Subsingleton (H X₁ (n+2))` implies `Subsingleton (H X₃ (n+1))`.
    Requires degree at least `1`, since `Ext^0(Z, I)` need not vanish for injective `I`. -/
theorem sheafH_dimension_shift_X₃ {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    [Injective S.X₂] (n : ℕ)
    [Subsingleton (Sheaf.H S.X₁ (n + 2))] :
    Subsingleton (Sheaf.H S.X₃ (n + 1)) :=
  ext_dimension_shift_X₃ _ hS (n + 1) (Ext.subsingleton_of_injective _ _ n) ‹_›

-- If both ends of a short exact sequence have vanishing H^n, so does the middle.
theorem subsingleton_sheafH_of_shortExact_middle {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (n : ℕ)
    (h₁ : Subsingleton (Sheaf.H S.X₁ n))
    (h₃ : Subsingleton (Sheaf.H S.X₃ n)) :
    Subsingleton (Sheaf.H S.X₂ n) := by
  constructor; intro a b
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₂ _ hS a
    (@Subsingleton.elim _ ((add_zero n) ▸ h₃) _ _)
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₂ _ hS b
    (@Subsingleton.elim _ ((add_zero n) ▸ h₃) _ _)
  rw [← hc, ← hd, @Subsingleton.elim _ h₁ c d]

/-- On an empty space, all sheaf cohomology groups are subsingleton.
    Proof: when X is empty, all stalks are vacuously zero, so the sheaf is zero,
    and zero sheaves have subsingleton cohomology in all degrees. -/
instance sheafH_subsingleton_of_isEmpty {X : TopCat.{u}} [IsEmpty X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Subsingleton (Sheaf.H F n) :=
  sheafH_subsingleton_of_isZero F
    (sheaf_isZero_of_zero_stalks X F (fun x _ => (IsEmpty.false x).elim)) n

/-! ## Sheaf Cohomology Functor -/

/-- The sheaf cohomology functor `H^n : Sheaf(X, Ab) ⥤ Ab`, defined as the covariant
    Ext functor `Ext^n(ℤ_X, −)` where `ℤ_X` is the constant sheaf of integers. -/
noncomputable def sheafCohomologyFunctor (X : TopCat.{u}) (n : ℕ) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  extFunctorObj ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))) n

noncomputable instance sheafCohomologyFunctor_additive (X : TopCat.{u}) (n : ℕ) :
    (sheafCohomologyFunctor X n).Additive :=
  inferInstanceAs (extFunctorObj _ n).Additive

@[simp]
theorem sheafCohomologyFunctor_obj (X : TopCat.{u}) (n : ℕ)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (sheafCohomologyFunctor X n).obj F = AddCommGrpCat.of (Sheaf.H F n) := rfl

@[simp]
theorem sheafCohomologyFunctor_map_apply (X : TopCat.{u}) (n : ℕ)
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (x : Sheaf.H F n) :
    ConcreteCategory.hom ((sheafCohomologyFunctor X n).map f) x =
    x.comp (Ext.mk₀ f) (add_zero n) := rfl
