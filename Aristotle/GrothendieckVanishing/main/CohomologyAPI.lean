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
* `subsingleton_sheafH_of_shortExact_middle_presheaf`: presheaf-boundary middle-term wrapper
* `sheafH_subsingleton_of_isEmpty`: empty-space vanishing
* `sheafH_subsingleton_of_isEmpty_presheaf`: presheaf-boundary empty-space vanishing
* `sheaf_isZero_of_zero_stalks`: zero stalks imply zero sheaf
* `sheafH_subsingleton_of_isZero`: zero sheaf ⟹ subsingleton cohomology
* `sheafH_subsingleton_of_isZero_presheaf`: presheaf-boundary wrapper for the same fact
* `stalk_zero_of_ses_g_iso`: stalk vanishing from SES with iso on `g`
* `stalk_zero_of_shortExact_kernel`: stalk vanishing from SES kernel
* `sheafH0EquivSections`: H^0(F) ≃+ F(⊤)
* `sheafH0EquivSections_natural`: naturality of the above
* `sheafH1_cokernel_iso_of_subsingleton_middle`: `H¹(X₁)` as the cokernel of
  `X₂(⊤) → X₃(⊤)` when `H¹(X₂)=0`
* `sheafH1_cokernel_iso_of_subsingleton_middle_presheaf`: presheaf-boundary wrapper for
  the same `H¹` cokernel identification
* `sheafH1_cokernel_iso_of_subsingleton_middle_presheaf_natural`: presheaf-boundary
  naturality for the same `H¹` cokernel identification
* `sheafH_extClassIso_of_subsingleton_middle_presheaf`: presheaf-boundary wrapper for
  the higher-degree connecting isomorphism
* `sheafH_extClassIso_of_subsingleton_middle_presheaf_natural`: presheaf-boundary
  naturality for the same connecting isomorphism
* `epi_app_top_of_subsingleton_sheafH1_presheaf`: presheaf-boundary H^1 vanishing gives
  surjectivity on top sections
* `epi_app_top_of_subsingleton_sheafH1`: sheaf-level wrapper for the same fact
* `sheafH0_surj_of_epi_app_top_presheaf`: presheaf-boundary surjectivity on top sections
  gives H^0 surjectivity
* `sheafH0_surj_of_epi_app_top`: sheaf-level wrapper for the same fact
* `sheafH_subsingleton_H1_via_surj_presheaf`: presheaf-boundary H^1 vanishing via
  H^0-surjectivity
* `sheafH_subsingleton_H1_via_epi_app_top_presheaf`: presheaf-boundary H^1 vanishing via
  surjective top sections
* `sheafH_subsingleton_H1_via_epi_app_top`: sheaf-level wrapper for the same fact
* `sheafH_subsingleton_H1_of_injective_of_epi_app_top_presheaf`: presheaf-boundary
  injective-middle-term `H¹` vanishing
* `sheafH_subsingleton_H1_of_flasque`: flasque sheaves have vanishing `H¹`
* `sheafH_subsingleton_H1_of_flasque_presheaf`: presheaf-boundary wrapper for the same fact
* `sheafH_subsingleton_H1_of_flasque_of_epi_app_top_presheaf`: presheaf-boundary
  flasque-middle-term `H¹` vanishing
* `sheafH_subsingleton_H1_of_flasque_of_epi_app_top`: flasque-middle-term `H¹` vanishing
* `sheafH_subsingleton_H1_of_flasque_of_epi_app_top_map_presheaf`: presheaf-boundary
  pushed-forward flasque-middle-term `H¹` vanishing
* `sheafH_dimension_shift_of_both_presheaf`: presheaf-boundary forward dimension shift
  for short exact sequences
* `sheafH_dimension_shift_of_mono_presheaf`: presheaf-boundary forward dimension shift
* `sheafH_dimension_shift_presheaf`: presheaf-boundary forward dimension shift with
  injective middle term
* `sheafH_dimension_shift_X₃_of_both_presheaf`: presheaf-boundary reverse dimension shift
  for short exact sequences
* `sheafH_dimension_shift_X₃_of_locallySurjective_presheaf`: presheaf-boundary reverse
  dimension shift for locally surjective morphisms
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

/-- If the middle cohomology groups in degrees `n` and `n + 1` are subsingleton, then the
    connecting morphism `Ext^n(Z, X₃) → Ext^(n+1)(Z, X₁)` is bijective. -/
theorem extClass_postcomp_bijective_of_subsingleton_middle
    (Z : C') {S : ShortComplex C'} (hS : S.ShortExact) (n : ℕ)
    (h₂n : Subsingleton (Ext Z S.X₂ n))
    (h₂succ : Subsingleton (Ext Z S.X₂ (n + 1))) :
    Function.Bijective (hS.extClass.postcomp Z (rfl : n + 1 = n + 1)) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have hzero : (x - y).comp hS.extClass rfl = 0 := by
      change (hS.extClass.postcomp Z (rfl : n + 1 = n + 1)) (x - y) = 0
      rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ Z hS (x - y) rfl hzero
    have hz0 : z = 0 := Subsingleton.elim _ _
    apply sub_eq_zero.mp
    rw [← hz, hz0, Ext.zero_comp]
  · intro x
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ Z hS x
      (@Subsingleton.elim _ h₂succ _ _) rfl
    exact ⟨y, hy⟩

/-- The connecting morphism in the covariant long exact sequence as an additive equivalence,
    assuming the middle cohomology groups in degrees `n` and `n + 1` vanish. -/
noncomputable def extClass_postcompAddEquiv_of_subsingleton_middle
    (Z : C') {S : ShortComplex C'} (hS : S.ShortExact) (n : ℕ)
    (h₂n : Subsingleton (Ext Z S.X₂ n))
    (h₂succ : Subsingleton (Ext Z S.X₂ (n + 1))) :
    Ext Z S.X₃ n ≃+ Ext Z S.X₁ (n + 1) :=
  AddEquiv.ofBijective (hS.extClass.postcomp Z (rfl : n + 1 = n + 1))
    (extClass_postcomp_bijective_of_subsingleton_middle Z hS n h₂n h₂succ)

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
    {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf)
    (hstalk : ∀ (x : X)
      (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj F), a = 0) :
    IsZero ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) := by
  let Fsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F, hF⟩
  have hZ : IsZero F := Functor.isZero F (fun ⟨U⟩ =>
    @AddCommGrpCat.isZero_of_subsingleton _
      ⟨fun s t => by
        apply hF.section_ext
        intro x hx
        obtain ⟨W, hxW, iU, iV, hEq⟩ := F.germ_eq x hx hx s t
          ((hstalk x _).trans (hstalk x _).symm)
        rw [Subsingleton.elim iU iV] at hEq
        have hWU : W ≤ U := leOfHom iV
        rw [Subsingleton.elim iV (homOfLE hWU)] at hEq
        exact ⟨W, hWU, hxW, hEq⟩⟩)
  have hFsh : IsZero Fsh := by
    exact IsZero.mk
      (fun G => ⟨{ default := 0, uniq := fun f => Sheaf.Hom.ext (NatTrans.ext (funext
        fun U => (hZ.obj U).eq_zero_of_src (f.val.app U))) }⟩)
      (fun G => ⟨{ default := 0, uniq := fun f => Sheaf.Hom.ext (NatTrans.ext (funext
        fun U => (hZ.obj U).eq_zero_of_tgt (f.val.app U))) }⟩)
  simpa [Fsh] using hFsh

/-- If a sheaf is zero, then all its cohomology groups are subsingleton. -/
theorem sheafH_subsingleton_of_isZero {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (hF : IsZero F) (n : ℕ) :
    Subsingleton (Sheaf.H F n) :=
  Ext.subsingleton_of_isZero_tgt hF n

/-- Presheaf-boundary wrapper for `sheafH_subsingleton_of_isZero`: if a presheaf is a
    sheaf and the induced bundled sheaf is zero, then its cohomology is subsingleton in
    every degree. -/
theorem sheafH_subsingleton_of_isZero_presheaf {X : TopCat.{u}}
    {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf)
    (hzero : IsZero ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))) (n : ℕ) :
    Subsingleton (Sheaf.H ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n) := by
  simpa using
    (sheafH_subsingleton_of_isZero
      (F := (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) (hF := hzero) (n := n))

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

/-- If `S.g` is a cokernel of `S.f`, then at any point where the stalk map of `f`
is epi, the stalk of `S.X₃` vanishes. -/
theorem stalk_zero_of_g_is_cokernel_of_stalk_epi
    {X : TopCat.{u}} {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hg : IsColimit (CokernelCofork.ofπ S.g S.zero)) (x : X)
    (hepi : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.f.val))
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj S.X₃.val) :
    a = 0 := by
  let T : TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
    TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  haveI : ∀ U : Opens X, Decidable (x ∈ U) := fun _ => Classical.dec _
  haveI : T.IsLeftAdjoint :=
    (stalkSkyscraperSheafAdjunction (C := AddCommGrpCat.{u}) (X := X) (p₀ := x)).isLeftAdjoint
  haveI : Epi (T.map S.f) := by
    simpa [T] using hepi
  have hzero_map : T.map S.f ≫ T.map S.g = 0 := by
    rw [← T.map_comp, S.zero, Functor.map_zero]
  have hcolim : IsColimit (CokernelCofork.ofπ (T.map S.g) hzero_map) := by
    simpa [T, hzero_map] using CokernelCofork.mapIsColimit _ hg T
  have hzero : IsZero (T.obj S.X₃) := CokernelCofork.IsColimit.isZero_of_epi hcolim
  haveI := AddCommGrpCat.subsingleton_of_isZero hzero
  change T.obj S.X₃ at a
  change (a : T.obj S.X₃) = 0
  exact Subsingleton.elim _ _

/-- Short exact sequence version of `stalk_zero_of_g_is_cokernel_of_stalk_epi`. -/
theorem stalk_zero_of_shortExact_cokernel
    {X : TopCat.{u}} {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hSE : S.ShortExact) (x : X)
    (hepi : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.f.val))
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj S.X₃.val) :
    a = 0 :=
  stalk_zero_of_g_is_cokernel_of_stalk_epi hSE.gIsCokernel x hepi a

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

/-- If `H¹(X₂)=0` in a short exact sequence `0 → X₁ → X₂ → X₃ → 0`, then `H¹(X₁)` is the
    cokernel of the map on top sections `X₂(⊤) → X₃(⊤)`. -/
noncomputable def sheafH1_cokernel_iso_of_subsingleton_middle {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    (h₂ : Subsingleton (Sheaf.H S.X₂ 1)) :
    cokernel (S.g.val.app (op ⊤)) ≅ AddCommGrpCat.of (Sheaf.H S.X₁ 1) := by
  let δ : S.X₃.val.obj (op ⊤) ⟶ AddCommGrpCat.of (Sheaf.H S.X₁ 1) :=
    AddCommGrpCat.ofHom <|
      AddMonoidHom.mk'
        (fun t => ((sheafH0EquivSections S.X₃).symm t).comp hS.extClass rfl)
        (by
          intro a b
          change (((sheafH0EquivSections S.X₃).symm (a + b)).comp hS.extClass rfl) =
            (((sheafH0EquivSections S.X₃).symm a).comp hS.extClass rfl) +
              (((sheafH0EquivSections S.X₃).symm b).comp hS.extClass rfl)
          rw [map_add, Ext.add_comp])
  have hδ : S.g.val.app (op ⊤) ≫ δ = 0 := by
    ext s
    let y : Sheaf.H S.X₂ 0 := (sheafH0EquivSections S.X₂).symm s
    have hy :
        y.comp (Ext.mk₀ S.g) (add_zero 0) =
          (sheafH0EquivSections S.X₃).symm
            (ConcreteCategory.hom (S.g.val.app (op ⊤)) s) := by
      apply (sheafH0EquivSections S.X₃).injective
      rw [sheafH0EquivSections_natural, AddEquiv.apply_symm_apply]
      exact (AddEquiv.apply_symm_apply (sheafH0EquivSections S.X₃)
        (ConcreteCategory.hom (S.g.val.app (op ⊤)) s)).symm
    change (((sheafH0EquivSections S.X₃).symm
        (ConcreteCategory.hom (S.g.val.app (op ⊤)) s)).comp hS.extClass rfl) = 0
    rw [← hy, Ext.comp_assoc_of_second_deg_zero _ (Ext.mk₀ S.g) hS.extClass rfl,
      hS.comp_extClass, Ext.comp_zero _ _ 1 1 rfl]
  let πH : cokernel (S.g.val.app (op ⊤)) ⟶ AddCommGrpCat.of (Sheaf.H S.X₁ 1) :=
    cokernel.desc _ δ hδ
  have hπH_epi : Epi πH := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro x
    obtain ⟨y, hy⟩ := sheafH_exists_preimage_extClass hS 0 h₂ x
    refine ⟨ConcreteCategory.hom (cokernel.π (S.g.val.app (op ⊤)))
      (sheafH0EquivSections S.X₃ y), ?_⟩
    simpa [πH, δ] using hy
  have hπH_mono : Mono πH := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro a b hab
    obtain ⟨sa, hsa⟩ := (AddCommGrpCat.epi_iff_surjective
      (cokernel.π (S.g.val.app (op ⊤)))).mp inferInstance a
    obtain ⟨sb, hsb⟩ := (AddCommGrpCat.epi_iff_surjective
      (cokernel.π (S.g.val.app (op ⊤)))).mp inferInstance b
    rw [← hsa, ← hsb] at hab ⊢
    have hab' :
        (((sheafH0EquivSections S.X₃).symm sa).comp hS.extClass rfl) =
          (((sheafH0EquivSections S.X₃).symm sb).comp hS.extClass rfl) := by
      simpa [πH, δ] using hab
    have hzero :
        ((((sheafH0EquivSections S.X₃).symm (sa - sb)).comp hS.extClass rfl) : Sheaf.H S.X₁ 1) = 0 := by
      have hsub :
          ((((sheafH0EquivSections S.X₃).symm sa).comp hS.extClass rfl) -
              (((sheafH0EquivSections S.X₃).symm sb).comp hS.extClass rfl)) = 0 := by
        rw [sub_eq_zero]
        exact hab'
      rw [map_sub, sub_eq_add_neg, Ext.add_comp, Ext.neg_comp]
      simpa [sub_eq_add_neg] using hsub
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ _ hS
      ((sheafH0EquivSections S.X₃).symm (sa - sb)) rfl hzero
    have hy_sec :
        ConcreteCategory.hom (S.g.val.app (op ⊤))
            (sheafH0EquivSections S.X₂ y) =
          sa - sb := by
      simpa [hy] using
        (sheafH0EquivSections_natural (f := S.g) (x := y)).symm
    change ConcreteCategory.hom (cokernel.π (S.g.val.app (op ⊤))) sa =
      ConcreteCategory.hom (cokernel.π (S.g.val.app (op ⊤))) sb
    rw [← sub_eq_zero]
    have hq :
        ConcreteCategory.hom (cokernel.π (S.g.val.app (op ⊤))) (sa - sb) = 0 := by
      rw [← hy_sec]
      change ConcreteCategory.hom
        ((S.g.val.app (op ⊤)) ≫ cokernel.π (S.g.val.app (op ⊤)))
        (sheafH0EquivSections S.X₂ y) = 0
      rw [cokernel.condition]
      simp
    simpa [map_sub] using hq
  haveI : IsIso πH := isIso_of_mono_of_epi πH
  exact asIso πH

/-- Presheaf-boundary wrapper for `sheafH1_cokernel_iso_of_subsingleton_middle`: if
`0 → F₁ → F₂ → F₃ → 0` is short exact after bundling the presheaves as sheaves and
`H¹(F₂)=0`, then `H¹(F₁)` is the cokernel of `g.app(⊤)`. -/
noncomputable def sheafH1_cokernel_iso_of_subsingleton_middle_presheaf {X : TopCat.{u}}
    {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    (h₁ : F₁.IsSheaf) (h₂ : F₂.IsSheaf) (h₃ : F₃.IsSheaf)
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃} (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk
      (X₁ := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₂ := (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₃ := (⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (Sheaf.Hom.mk f)
      (Sheaf.Hom.mk g)
      (by
        apply Sheaf.Hom.ext
        simpa using hfg)).ShortExact)
    (h₂H : Subsingleton (Sheaf.H ((⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) 1)) :
    cokernel (g.app (op ⊤)) ≅
      AddCommGrpCat.of (Sheaf.H ((⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) 1) := by
  let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) := ShortComplex.mk
    (X₁ := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₂ := (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₃ := (⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (Sheaf.Hom.mk f)
    (Sheaf.Hom.mk g)
    (by
      apply Sheaf.Hom.ext
      simpa using hfg)
  have hS' : S.ShortExact := by
    simpa [S] using hS
  have h₂H' : Subsingleton (Sheaf.H S.X₂ 1) := by
    simpa [S] using h₂H
  simpa [S] using sheafH1_cokernel_iso_of_subsingleton_middle (S := S) hS' h₂H'

@[simp] theorem sheafH1_cokernel_iso_of_subsingleton_middle_hom_π {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    (h₂ : Subsingleton (Sheaf.H S.X₂ 1)) (s : S.X₃.val.obj (op ⊤)) :
    ConcreteCategory.hom
        ((sheafH1_cokernel_iso_of_subsingleton_middle hS h₂).hom)
        (ConcreteCategory.hom (cokernel.π (S.g.val.app (op ⊤))) s) =
      ((sheafH0EquivSections S.X₃).symm s).comp hS.extClass rfl := by
  simp [sheafH1_cokernel_iso_of_subsingleton_middle]

/-- Naturality of `sheafH1_cokernel_iso_of_subsingleton_middle` for a morphism of short exact
    sequences. -/
theorem sheafH1_cokernel_iso_of_subsingleton_middle_natural {X : TopCat.{u}}
    {S₁ S₂ : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂)
    (h₁₂ : Subsingleton (Sheaf.H S₁.X₂ 1))
    (h₂₂ : Subsingleton (Sheaf.H S₂.X₂ 1)) :
    cokernel.map (S₁.g.val.app (op ⊤)) (S₂.g.val.app (op ⊤))
        (φ.τ₂.val.app (op ⊤)) (φ.τ₃.val.app (op ⊤))
        (by
          simpa using congrArg
            (fun α : S₁.X₂ ⟶ S₂.X₃ => α.val.app (op ⊤)) φ.comm₂₃.symm) ≫
      (sheafH1_cokernel_iso_of_subsingleton_middle hS₂ h₂₂).hom =
    (sheafH1_cokernel_iso_of_subsingleton_middle hS₁ h₁₂).hom ≫
      AddCommGrpCat.ofHom
        (AddMonoidHom.mk'
          (fun t => t.comp (Ext.mk₀ φ.τ₁) (add_zero 1))
          (by
            intro a b
            change ((a + b).comp (Ext.mk₀ φ.τ₁) (add_zero 1)) =
              (a.comp (Ext.mk₀ φ.τ₁) (add_zero 1)) + (b.comp (Ext.mk₀ φ.τ₁) (add_zero 1))
            rw [Ext.add_comp])) := by
  apply (cancel_epi (cokernel.π (S₁.g.val.app (op ⊤)))).mp
  rw [cokernel.π_desc_assoc, Category.assoc]
  ext s
  have hs :
      (((sheafH0EquivSections S₁.X₃).symm s).comp (Ext.mk₀ φ.τ₃) (add_zero 0)) =
        (sheafH0EquivSections S₂.X₃).symm
          (ConcreteCategory.hom (φ.τ₃.val.app (op ⊤)) s) := by
    apply (sheafH0EquivSections S₂.X₃).injective
    rw [sheafH0EquivSections_natural, AddEquiv.apply_symm_apply]
    exact (AddEquiv.apply_symm_apply (sheafH0EquivSections S₂.X₃)
      (ConcreteCategory.hom (φ.τ₃.val.app (op ⊤)) s)).symm
  change ConcreteCategory.hom
      (cokernel.π (S₂.g.val.app (op ⊤)) ≫
        (sheafH1_cokernel_iso_of_subsingleton_middle hS₂ h₂₂).hom)
      (ConcreteCategory.hom (φ.τ₃.val.app (op ⊤)) s) =
    ConcreteCategory.hom
      ((sheafH1_cokernel_iso_of_subsingleton_middle hS₁ h₁₂).hom ≫
        AddCommGrpCat.ofHom
          (AddMonoidHom.mk'
            (fun t => t.comp (Ext.mk₀ φ.τ₁) (add_zero 1))
            (by
              intro a b
              change ((a + b).comp (Ext.mk₀ φ.τ₁) (add_zero 1)) =
                (a.comp (Ext.mk₀ φ.τ₁) (add_zero 1)) + (b.comp (Ext.mk₀ φ.τ₁) (add_zero 1))
              rw [Ext.add_comp])))
      (ConcreteCategory.hom (cokernel.π (S₁.g.val.app (op ⊤))) s)
  simp only [ConcreteCategory.comp_apply]
  rw [sheafH1_cokernel_iso_of_subsingleton_middle_hom_π,
    sheafH1_cokernel_iso_of_subsingleton_middle_hom_π]
  change (((sheafH0EquivSections S₂.X₃).symm
        (ConcreteCategory.hom (φ.τ₃.val.app (op ⊤)) s)).comp hS₂.extClass rfl) =
      ((((sheafH0EquivSections S₁.X₃).symm s).comp hS₁.extClass rfl).comp
        (Ext.mk₀ φ.τ₁) (add_zero 1))
  rw [← hs]
  exact (sheafH_comp_extClass_naturality hS₁ hS₂ φ 0
    ((sheafH0EquivSections S₁.X₃).symm s)).symm

/-- Presheaf-boundary `H¹`-vanishing criterion for surjective top sections:
    if `0 → F₁ → F₂ → F₃ → 0` is short exact after bundling the presheaves as sheaves
    and `H¹(F₁)=0`, then `g.app(⊤)` is epi. -/
theorem epi_app_top_of_subsingleton_sheafH1_presheaf {X : TopCat.{u}}
    {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    (h₁ : F₁.IsSheaf) (h₂ : F₂.IsSheaf) (h₃ : F₃.IsSheaf)
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃} (hfg : f ≫ g = 0)
    (hSE : (ShortComplex.mk
      (X₁ := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₂ := (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₃ := (⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (Sheaf.Hom.mk f)
      (Sheaf.Hom.mk g)
      (by
        apply Sheaf.Hom.ext
        simpa using hfg)).ShortExact)
    (h₁H : Subsingleton (Sheaf.H ((⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) 1)) :
    Epi (g.app (op ⊤)) := by
  let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) := ShortComplex.mk
    (X₁ := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₂ := (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₃ := (⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (Sheaf.Hom.mk f)
    (Sheaf.Hom.mk g)
    (by
      apply Sheaf.Hom.ext
      simpa using hfg)
  have hS : S.ShortExact := by
    simpa [S] using hSE
  have h₁' : Subsingleton (Sheaf.H S.X₁ 1) := by
    simpa [S] using h₁H
  change Epi (S.g.val.app (op ⊤))
  rw [AddCommGrpCat.epi_iff_surjective]
  intro r
  let y : Sheaf.H S.X₃ 0 := (sheafH0EquivSections S.X₃).symm r
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ _ hS y rfl
    (@Subsingleton.elim _ h₁' _ _)
  refine ⟨sheafH0EquivSections S.X₂ z, ?_⟩
  rw [← sheafH0EquivSections_natural, hz]
  simp [y]

/-- Sheaf-level wrapper for `epi_app_top_of_subsingleton_sheafH1_presheaf`. -/
theorem epi_app_top_of_subsingleton_sheafH1 {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hSE : S.ShortExact)
    (h₁ : Subsingleton (Sheaf.H S.X₁ 1)) :
    Epi (S.g.val.app (op ⊤)) := by
  simpa using epi_app_top_of_subsingleton_sheafH1_presheaf
    (F₁ := S.X₁.val) (F₂ := S.X₂.val) (F₃ := S.X₃.val)
    S.X₁.cond S.X₂.cond S.X₃.cond
    (f := S.f.val) (g := S.g.val)
    (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
    (by simpa using hSE)
    (by simpa using h₁)

/-- Presheaf-boundary `H⁰`-surjectivity from surjective top sections:
    if `f.app (op ⊤)` is surjective on sections, then every `H⁰` class of the target
    lifts along the bundled sheaf morphism `Sheaf.Hom.mk f`. -/
theorem sheafH0_surj_of_epi_app_top_presheaf {X : TopCat.{u}}
    {F G : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf) (hG : G.IsSheaf)
    (f : F ⟶ G) (hf : Epi (f.app (op ⊤))) :
    ∀ y : Sheaf.H ((⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) 0,
      ∃ z : Sheaf.H ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) 0,
        z.comp (Ext.mk₀ (Sheaf.Hom.mk f)) (add_zero 0) = y := by
  let Fsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F, hF⟩
  let Gsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨G, hG⟩
  intro y
  obtain ⟨s, hs⟩ := (AddCommGrpCat.epi_iff_surjective _).mp hf (sheafH0EquivSections Gsh y)
  refine ⟨(sheafH0EquivSections Fsh).symm s, ?_⟩
  apply (sheafH0EquivSections Gsh).injective
  rw [sheafH0EquivSections_natural, AddEquiv.apply_symm_apply, hs]

/-- Sheaf-level wrapper for `sheafH0_surj_of_epi_app_top_presheaf`. -/
theorem sheafH0_surj_of_epi_app_top {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (hf : Epi (f.val.app (op ⊤))) :
    ∀ y : Sheaf.H G 0, ∃ z : Sheaf.H F 0, z.comp (Ext.mk₀ f) (add_zero 0) = y := by
  simpa using sheafH0_surj_of_epi_app_top_presheaf
    (F := F.val) (G := G.val) F.cond G.cond f.val (by simpa using hf)

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
theorem sheafH_subsingleton_H1_via_surj_presheaf {X : TopCat.{u}}
    {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    (h₁ : F₁.IsSheaf) (h₂ : F₂.IsSheaf) (h₃ : F₃.IsSheaf)
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃} (hfg : f ≫ g = 0)
    (hSE : (ShortComplex.mk
      (X₁ := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₂ := (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₃ := (⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (Sheaf.Hom.mk f)
      (Sheaf.Hom.mk g)
      (by
        apply Sheaf.Hom.ext
        simpa using hfg)).ShortExact)
    (h₂H : Subsingleton (Sheaf.H ((⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) 1))
    (h_surj : ∀ y : Sheaf.H ((⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) 0,
      ∃ z : Sheaf.H ((⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) 0,
        z.comp (Ext.mk₀ (Sheaf.Hom.mk g)) (add_zero 0) = y) :
    Subsingleton (Sheaf.H ((⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) 1) := by
  let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) := ShortComplex.mk
    (X₁ := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₂ := (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₃ := (⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (Sheaf.Hom.mk f)
    (Sheaf.Hom.mk g)
    (by
      apply Sheaf.Hom.ext
      simpa using hfg)
  have hS : S.ShortExact := by
    simpa [S] using hSE
  have h₂' : Subsingleton (Sheaf.H S.X₂ 1) := by
    simpa [S] using h₂H
  have h_surj' : ∀ y : Sheaf.H S.X₃ 0,
      ∃ z : Sheaf.H S.X₂ 0, z.comp (Ext.mk₀ S.g) (add_zero 0) = y := by
    simpa [S] using h_surj
  simpa [S] using subsingleton_H1_via_surj _ hS h₂' h_surj'

/-- Sheaf-level wrapper for `sheafH_subsingleton_H1_via_surj_presheaf`: if `H¹(X₂)=0`
    and every `H⁰` class on `X₃` lifts along `g`, then `H¹(X₁)=0`. -/
theorem sheafH_subsingleton_H1_via_surj {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hSE : S.ShortExact)
    (h₂ : Subsingleton (Sheaf.H S.X₂ 1))
    (h_surj : ∀ y : Sheaf.H S.X₃ 0,
      ∃ z : Sheaf.H S.X₂ 0, z.comp (Ext.mk₀ S.g) (add_zero 0) = y) :
    Subsingleton (Sheaf.H S.X₁ 1) := by
  simpa using sheafH_subsingleton_H1_via_surj_presheaf
    (F₁ := S.X₁.val) (F₂ := S.X₂.val) (F₃ := S.X₃.val)
    S.X₁.cond S.X₂.cond S.X₃.cond
    (f := S.f.val) (g := S.g.val)
    (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
    (by simpa using hSE)
    (by simpa using h₂)
    (by simpa using h_surj)

/-- Presheaf-boundary `H¹` vanishing criterion from surjective top sections:
    if `0 → F₁ → F₂ → F₃ → 0` is short exact after bundling the presheaves as sheaves,
    `H¹(F₂)=0`, and `g.app(⊤)` is epi, then `H¹(F₁)=0`. -/
theorem sheafH_subsingleton_H1_via_epi_app_top_presheaf {X : TopCat.{u}}
    {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    (h₁ : F₁.IsSheaf) (h₂ : F₂.IsSheaf) (h₃ : F₃.IsSheaf)
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃} (hfg : f ≫ g = 0)
    (hSE : (ShortComplex.mk
      (X₁ := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₂ := (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₃ := (⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (Sheaf.Hom.mk f)
      (Sheaf.Hom.mk g)
      (by
        apply Sheaf.Hom.ext
        simpa using hfg)).ShortExact)
    (h₂H : Subsingleton (Sheaf.H ((⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) 1))
    (hg : Epi (g.app (op ⊤))) :
    Subsingleton (Sheaf.H ((⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) 1) := by
  simpa using sheafH_subsingleton_H1_via_surj_presheaf
    (F₁ := F₁) (F₂ := F₂) (F₃ := F₃)
    h₁ h₂ h₃ hfg hSE h₂H
    (sheafH0_surj_of_epi_app_top_presheaf (F := F₂) (G := F₃) h₂ h₃ g hg)

/-- Sheaf-level `H¹` vanishing criterion from surjective top sections:
    if `H¹(X₂)=0` and `g.app(⊤)` is epi in a short exact sequence
    `0 → X₁ → X₂ → X₃ → 0`, then `H¹(X₁)=0`. -/
theorem sheafH_subsingleton_H1_via_epi_app_top {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hSE : S.ShortExact)
    (h₂ : Subsingleton (Sheaf.H S.X₂ 1))
    (hg : Epi (S.g.val.app (op ⊤))) :
    Subsingleton (Sheaf.H S.X₁ 1) := by
  simpa using sheafH_subsingleton_H1_via_epi_app_top_presheaf
    (F₁ := S.X₁.val) (F₂ := S.X₂.val) (F₃ := S.X₃.val)
    S.X₁.cond S.X₂.cond S.X₃.cond
    (f := S.f.val) (g := S.g.val)
    (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
    (by simpa using hSE)
    (by simpa using h₂)
    (by simpa using hg)

/-- Presheaf-boundary `H¹` vanishing criterion with injective middle term:
    if `0 → F₁ → F₂ → F₃ → 0` is short exact after bundling the presheaves as sheaves,
    `⟨F₂, h₂⟩` is injective, and `g.app(⊤)` is epi, then `H¹(F₁)=0`. -/
theorem sheafH_subsingleton_H1_of_injective_of_epi_app_top_presheaf {X : TopCat.{u}}
    {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    (h₁ : F₁.IsSheaf) (h₂ : F₂.IsSheaf) (h₃ : F₃.IsSheaf)
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃} (hfg : f ≫ g = 0)
    (hSE : (ShortComplex.mk
      (X₁ := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₂ := (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₃ := (⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (Sheaf.Hom.mk f)
      (Sheaf.Hom.mk g)
      (by
        apply Sheaf.Hom.ext
        simpa using hfg)).ShortExact)
    [Injective ((⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))]
    (hg : Epi (g.app (op ⊤))) :
    Subsingleton (Sheaf.H ((⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) 1) := by
  simpa using sheafH_subsingleton_H1_via_epi_app_top_presheaf
    (F₁ := F₁) (F₂ := F₂) (F₃ := F₃)
    h₁ h₂ h₃ hfg hSE
    (Ext.subsingleton_of_injective _ _ 0)
    hg

/-- Sheaf-level `H¹` vanishing criterion with injective middle term:
    if `X₂` is injective and `g.app(⊤)` is epi in a short exact sequence
    `0 → X₁ → X₂ → X₃ → 0`, then `H¹(X₁)=0`. -/
theorem sheafH_subsingleton_H1_of_injective_of_epi_app_top {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hSE : S.ShortExact)
    [Injective S.X₂]
    (hg : Epi (S.g.val.app (op ⊤))) :
    Subsingleton (Sheaf.H S.X₁ 1) := by
  letI : Injective ((⟨S.X₂.val, S.X₂.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) := by
    simpa using (inferInstance : Injective S.X₂)
  simpa using sheafH_subsingleton_H1_of_injective_of_epi_app_top_presheaf
    (F₁ := S.X₁.val) (F₂ := S.X₂.val) (F₃ := S.X₃.val)
    S.X₁.cond S.X₂.cond S.X₃.cond
    (f := S.f.val) (g := S.g.val)
    (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
    (by simpa using hSE)
    (by simpa using hg)

/-- Presheaf-boundary wrapper for `sheafH_subsingleton_H1_of_flasque`: if a presheaf is a
    sheaf and the induced bundled sheaf is flasque, then its `H¹` is subsingleton. -/
theorem sheafH_subsingleton_H1_of_flasque_presheaf {X : TopCat.{u}}
    {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf)
    [IsFlasqueSheaf ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))] :
    Subsingleton (Sheaf.H ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) 1) := by
  let Fsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F, hF⟩
  obtain ⟨ip⟩ := EnoughInjectives.presentation Fsh
  let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) := ip.shortComplex
  letI : Injective ((⟨S.X₂.val, S.X₂.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) := by
    simpa [S] using (inferInstance : Injective S.X₂)
  have hSE :
      (ShortComplex.mk
        (X₁ := (⟨S.X₁.val, S.X₁.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
        (X₂ := (⟨S.X₂.val, S.X₂.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
        (X₃ := (⟨S.X₃.val, S.X₃.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
        (Sheaf.Hom.mk S.f.val)
        (Sheaf.Hom.mk S.g.val)
        (by
          apply Sheaf.Hom.ext
          exact congrArg Sheaf.Hom.val S.zero)).ShortExact := by
    simpa [S] using ip.shortExact_shortComplex
  have hg : Epi (S.g.val.app (op ⊤)) := by
    letI : IsFlasqueSheaf ((⟨S.X₁.val, S.X₁.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) := by
      simpa [Fsh, S] using (inferInstance : IsFlasqueSheaf Fsh)
    simpa [S] using epi_app_of_shortExact_flasque_presheaf
      S.X₁.cond S.X₂.cond S.X₃.cond
      (f := S.f.val) (g := S.g.val)
      (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
      hSE ⊤
  simpa [Fsh, S] using sheafH_subsingleton_H1_of_injective_of_epi_app_top_presheaf
    (F₁ := S.X₁.val) (F₂ := S.X₂.val) (F₃ := S.X₃.val)
    S.X₁.cond S.X₂.cond S.X₃.cond
    (f := S.f.val) (g := S.g.val)
    (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
    hSE hg

/-- Flasque sheaves have vanishing `H¹`. This isolates the base case of flasque
    cohomological vanishing in the general sheaf-cohomology API. -/
theorem sheafH_subsingleton_H1_of_flasque {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) [IsFlasqueSheaf F] :
    Subsingleton (Sheaf.H F 1) := by
  let Fsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F.val, F.cond⟩
  letI : IsFlasqueSheaf Fsh := by
    simpa [Fsh] using (inferInstance : IsFlasqueSheaf F)
  simpa [Fsh] using
    (sheafH_subsingleton_H1_of_flasque_presheaf (X := X) (F := F.val) F.cond)

/-- Presheaf-boundary `H¹` vanishing criterion with flasque middle term:
    if `0 → F₁ → F₂ → F₃ → 0` is short exact after bundling the presheaves as sheaves,
    `⟨F₂, h₂⟩` is flasque, and `g.app(⊤)` is epi, then `H¹(F₁)=0`. -/
theorem sheafH_subsingleton_H1_of_flasque_of_epi_app_top_presheaf {X : TopCat.{u}}
    {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    (h₁ : F₁.IsSheaf) (h₂ : F₂.IsSheaf) (h₃ : F₃.IsSheaf)
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃} (hfg : f ≫ g = 0)
    (hSE : (ShortComplex.mk
      (X₁ := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₂ := (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₃ := (⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (Sheaf.Hom.mk f)
      (Sheaf.Hom.mk g)
      (by
        apply Sheaf.Hom.ext
        simpa using hfg)).ShortExact)
    [IsFlasqueSheaf ((⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))]
    (hg : Epi (g.app (op ⊤))) :
    Subsingleton (Sheaf.H ((⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) 1) := by
  simpa using sheafH_subsingleton_H1_via_epi_app_top_presheaf
    (F₁ := F₁) (F₂ := F₂) (F₃ := F₃)
    h₁ h₂ h₃ hfg hSE
    (sheafH_subsingleton_H1_of_flasque_presheaf (F := F₂) h₂)
    hg

/-- Sheaf-level `H¹` vanishing criterion with flasque middle term:
    if `X₂` is flasque and `g.app(⊤)` is epi in a short exact sequence
    `0 → X₁ → X₂ → X₃ → 0`, then `H¹(X₁)=0`. -/
theorem sheafH_subsingleton_H1_of_flasque_of_epi_app_top {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hSE : S.ShortExact)
    [IsFlasqueSheaf S.X₂]
    (hg : Epi (S.g.val.app (op ⊤))) :
    Subsingleton (Sheaf.H S.X₁ 1) := by
  letI : IsFlasqueSheaf ((⟨S.X₂.val, S.X₂.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) := by
    simpa using (inferInstance : IsFlasqueSheaf S.X₂)
  simpa using sheafH_subsingleton_H1_of_flasque_of_epi_app_top_presheaf
    (F₁ := S.X₁.val) (F₂ := S.X₂.val) (F₃ := S.X₃.val)
    S.X₁.cond S.X₂.cond S.X₃.cond
    (f := S.f.val) (g := S.g.val)
    (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
    (by simpa using hSE)
    (by simpa using hg)

/-- Presheaf-boundary `H¹` vanishing criterion for a pushed-forward short exact sequence:
    if the pushed-forward middle term is flasque and the source sequence has `H¹(F₁)=0`,
    then the pushed-forward kernel has vanishing `H¹`, provided the caller supplies the
    identification of `i⁻¹(⊤)` with `⊤`. -/
theorem sheafH_subsingleton_H1_of_flasque_of_epi_app_top_map_presheaf {X Y : TopCat.{u}}
    (i : X ⟶ Y)
    {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    (h₁ : F₁.IsSheaf) (h₂ : F₂.IsSheaf) (h₃ : F₃.IsSheaf)
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃} (hfg : f ≫ g = 0)
    (hSE : (ShortComplex.mk
      (X₁ := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₂ := (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₃ := (⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (Sheaf.Hom.mk f)
      (Sheaf.Hom.mk g)
      (by
        apply Sheaf.Hom.ext
        simpa using hfg)).ShortExact)
    (hSE_map : (ShortComplex.mk
      (X₁ := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj
        ((⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)))
      (X₂ := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj
        ((⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)))
      (X₃ := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj
        ((⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)))
      (Sheaf.Hom.mk ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).map f))
      (Sheaf.Hom.mk ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).map g))
      (by
        apply Sheaf.Hom.ext
        simpa using congrArg ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).map) hfg)
      ).ShortExact)
    [IsFlasqueSheaf ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj
      ((⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)))]
    (h_top : (Opens.map i).obj ⊤ = ⊤)
    (h₁H : Subsingleton (Sheaf.H ((⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) 1)) :
    Subsingleton (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj
      ((⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))) 1) := by
  let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) := ShortComplex.mk
    (X₁ := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₂ := (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₃ := (⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (Sheaf.Hom.mk f)
    (Sheaf.Hom.mk g)
    (by
      apply Sheaf.Hom.ext
      simpa using hfg)
  let T := S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i)
  letI : IsFlasqueSheaf ((⟨T.X₂.val, T.X₂.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} Y)) := by
    simpa [S, T] using
      (inferInstance : IsFlasqueSheaf ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj
        ((⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))))
  simpa [S, T] using sheafH_subsingleton_H1_of_flasque_of_epi_app_top_presheaf
    (F₁ := T.X₁.val) (F₂ := T.X₂.val) (F₃ := T.X₃.val)
    T.X₁.cond T.X₂.cond T.X₃.cond
    (f := T.f.val) (g := T.g.val)
    (show T.f.val ≫ T.g.val = 0 from congrArg Sheaf.Hom.val T.zero)
    (by simpa [S, T] using hSE_map)
    (by
      change Epi (g.app (op ((Opens.map i).obj ⊤)))
      rw [h_top]
      exact epi_app_top_of_subsingleton_sheafH1_presheaf
        (F₁ := F₁) (F₂ := F₂) (F₃ := F₃)
        h₁ h₂ h₃ hfg hSE h₁H)

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
  letI : IsFlasqueSheaf ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj
      ((⟨S.X₂.val, S.X₂.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))) := by
    simpa using (inferInstance :
      IsFlasqueSheaf ((S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)).X₂))
  simpa using sheafH_subsingleton_H1_of_flasque_of_epi_app_top_map_presheaf
    (i := f)
    (F₁ := S.X₁.val) (F₂ := S.X₂.val) (F₃ := S.X₃.val)
    S.X₁.cond S.X₂.cond S.X₃.cond
    (f := S.f.val) (g := S.g.val)
    (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
    (by simpa using hSE)
    (by simpa using hSE_map)
    h_top
    (by simpa using h₁)

/-- General dimension shifting at `Sheaf.H` level: if `H^n(X₃)=0` and `H^(n+1)(X₂)=0`
    in a short exact sequence `0 → X₁ → X₂ → X₃ → 0`, then `H^(n+1)(X₁)=0`. -/
theorem sheafH_dimension_shift_of_both {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (Sheaf.H S.X₃ n)]
    [Subsingleton (Sheaf.H S.X₂ (n + 1))] :
    Subsingleton (Sheaf.H S.X₁ (n + 1)) :=
  ext_dimension_shift _ hS n ‹_› ‹_›

/-- Presheaf-boundary forward dimension shift for a short exact sequence:
    if `0 → F₁ → F₂ → F₃ → 0` is short exact after bundling the presheaves as sheaves,
    `H^n(F₃)=0`, and `H^(n+1)(F₂)=0`, then `H^(n+1)(F₁)=0`. -/
theorem sheafH_dimension_shift_of_both_presheaf {X : TopCat.{u}}
    {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    (h₁ : F₁.IsSheaf) (h₂ : F₂.IsSheaf) (h₃ : F₃.IsSheaf)
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃} (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk
      (X₁ := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₂ := (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₃ := (⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (Sheaf.Hom.mk f)
      (Sheaf.Hom.mk g)
      (by
        apply Sheaf.Hom.ext
        simpa using hfg)).ShortExact)
    (n : ℕ)
    (h₃H : Subsingleton (Sheaf.H ((⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n))
    (h₂H : Subsingleton (Sheaf.H ((⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) (n + 1))) :
    Subsingleton (Sheaf.H ((⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) (n + 1)) := by
  let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) := ShortComplex.mk
    (X₁ := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₂ := (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₃ := (⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (Sheaf.Hom.mk f)
    (Sheaf.Hom.mk g)
    (by
      apply Sheaf.Hom.ext
      simpa using hfg)
  have hS' : S.ShortExact := by
    simpa [S] using hS
  haveI : Subsingleton (Sheaf.H S.X₃ n) := by
    simpa [S] using h₃H
  haveI : Subsingleton (Sheaf.H S.X₂ (n + 1)) := by
    simpa [S] using h₂H
  simpa [S] using sheafH_dimension_shift_of_both (S := S) hS' n

/-- Presheaf-boundary forward dimension shift for a monomorphism:
    if `f : F ⟶ G` is mono between sheaf-valued presheaves, the cokernel sheaf of
    `Sheaf.Hom.mk f` has subsingleton `H^n`, and `G` has subsingleton `H^(n+1)`,
    then `F` has subsingleton `H^(n+1)`. -/
theorem sheafH_dimension_shift_of_mono_presheaf {X : TopCat.{u}}
    {F G : TopCat.Presheaf AddCommGrpCat.{u} X}
    (hF : F.IsSheaf) (hG : G.IsSheaf)
    (f : F ⟶ G) [Mono f] (n : ℕ)
    (h₃ : Subsingleton (Sheaf.H (cokernel (show
      (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) ⟶
        (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) from
          Sheaf.Hom.mk f)) n))
    (h₂ : Subsingleton (Sheaf.H ((⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) (n + 1))) :
    Subsingleton (Sheaf.H ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) (n + 1)) := by
  let fsh : (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) ⟶
      (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) := Sheaf.Hom.mk f
  haveI : Mono fsh := by
    exact (Sheaf.Hom.mono_iff_presheaf_mono
      (J := Opens.grothendieckTopology X) (D := AddCommGrpCat.{u}) fsh).2 inferInstance
  let S := ShortComplex.mk fsh (cokernel.π fsh) (cokernel.condition fsh)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel fsh))
    inferInstance inferInstance
  haveI : Subsingleton (Sheaf.H S.X₃ n) := by
    simpa [S, fsh] using h₃
  haveI : Subsingleton (Sheaf.H S.X₂ (n + 1)) := by
    simpa [S] using h₂
  simpa [S] using sheafH_dimension_shift_of_both (S := S) hS n

/-- Dimension shifting at `Sheaf.H` level with injective middle term:
    if `X₂` is injective and `H^n(X₃)=0`, then `H^(n+1)(X₁)=0`. -/
theorem sheafH_dimension_shift {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    [Injective S.X₂] (n : ℕ)
    [Subsingleton (Sheaf.H S.X₃ n)] :
    Subsingleton (Sheaf.H S.X₁ (n + 1)) :=
  ext_dimension_shift _ hS n ‹_› (Ext.subsingleton_of_injective _ _ n)

/-- Presheaf-boundary dimension shifting with injective middle term:
    if `0 → F₁ → F₂ → F₃ → 0` is short exact after bundling the presheaves as sheaves,
    `⟨F₂, h₂⟩` is injective, and `H^n(F₃)=0`, then `H^(n+1)(F₁)=0`. -/
theorem sheafH_dimension_shift_presheaf {X : TopCat.{u}}
    {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    (h₁ : F₁.IsSheaf) (h₂ : F₂.IsSheaf) (h₃ : F₃.IsSheaf)
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃} (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk
      (X₁ := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₂ := (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₃ := (⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (Sheaf.Hom.mk f)
      (Sheaf.Hom.mk g)
      (by
        apply Sheaf.Hom.ext
        simpa using hfg)).ShortExact)
    [Injective ((⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))]
    (n : ℕ)
    (h₃H : Subsingleton (Sheaf.H ((⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n)) :
    Subsingleton (Sheaf.H ((⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) (n + 1)) := by
  let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) := ShortComplex.mk
    (X₁ := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₂ := (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₃ := (⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (Sheaf.Hom.mk f)
    (Sheaf.Hom.mk g)
    (by
      apply Sheaf.Hom.ext
      simpa using hfg)
  have hS' : S.ShortExact := by
    simpa [S] using hS
  letI : Injective S.X₂ := by
    simpa [S] using
      (inferInstance : Injective ((⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)))
  haveI : Subsingleton (Sheaf.H S.X₃ n) := by
    simpa [S] using h₃H
  simpa [S] using sheafH_dimension_shift (S := S) hS' n

/-- Reverse dimension shift at `Sheaf.H` level with injective middle term:
    `Subsingleton (H X₁ (n+2))` implies `Subsingleton (H X₃ (n+1))`.
    Requires degree at least `1`, since `Ext^0(Z, I)` need not vanish for injective `I`. -/
theorem sheafH_dimension_shift_X₃ {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    [Injective S.X₂] (n : ℕ)
    [Subsingleton (Sheaf.H S.X₁ (n + 2))] :
    Subsingleton (Sheaf.H S.X₃ (n + 1)) :=
  ext_dimension_shift_X₃ _ hS (n + 1) (Ext.subsingleton_of_injective _ _ n) ‹_›

/-- Reverse dimension shift at `Sheaf.H` level: if `H^n(X₂)=0` and `H^(n+1)(X₁)=0`
    in a short exact sequence `0 → X₁ → X₂ → X₃ → 0`, then `H^n(X₃)=0`. -/
theorem sheafH_dimension_shift_X₃_of_both {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (Sheaf.H S.X₂ n)]
    [Subsingleton (Sheaf.H S.X₁ (n + 1))] :
    Subsingleton (Sheaf.H S.X₃ n) :=
  ext_dimension_shift_X₃ _ hS n ‹_› ‹_›

/-- Presheaf-boundary reverse dimension shift for a short exact sequence:
    if `0 → F₁ → F₂ → F₃ → 0` is short exact after bundling the presheaves as sheaves,
    `H^n(F₂)=0`, and `H^(n+1)(F₁)=0`, then `H^n(F₃)=0`. -/
theorem sheafH_dimension_shift_X₃_of_both_presheaf {X : TopCat.{u}}
    {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    (h₁ : F₁.IsSheaf) (h₂ : F₂.IsSheaf) (h₃ : F₃.IsSheaf)
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃} (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk
      (X₁ := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₂ := (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₃ := (⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (Sheaf.Hom.mk f)
      (Sheaf.Hom.mk g)
      (by
        apply Sheaf.Hom.ext
        simpa using hfg)).ShortExact)
    (n : ℕ)
    (h₂H : Subsingleton (Sheaf.H ((⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n))
    (h₁H : Subsingleton (Sheaf.H ((⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) (n + 1))) :
    Subsingleton (Sheaf.H ((⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n) := by
  let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) := ShortComplex.mk
    (X₁ := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₂ := (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₃ := (⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (Sheaf.Hom.mk f)
    (Sheaf.Hom.mk g)
    (by
      apply Sheaf.Hom.ext
      simpa using hfg)
  have hS' : S.ShortExact := by
    simpa [S] using hS
  haveI : Subsingleton (Sheaf.H S.X₂ n) := by
    simpa [S] using h₂H
  haveI : Subsingleton (Sheaf.H S.X₁ (n + 1)) := by
    simpa [S] using h₁H
  simpa [S] using sheafH_dimension_shift_X₃_of_both (S := S) hS' n

/-- Presheaf-boundary reverse dimension shift for a locally surjective morphism:
    if `f : F ⟶ G` is locally surjective, `H^n(F)` is subsingleton, and
    `H^(n+1)(kernel (Sheaf.Hom.mk f))` is subsingleton, then `H^n(G)` is subsingleton. -/
theorem sheafH_dimension_shift_X₃_of_locallySurjective_presheaf {X : TopCat.{u}}
    {F G : TopCat.Presheaf AddCommGrpCat.{u} X}
    (hF : F.IsSheaf) (hG : G.IsSheaf)
    (f : F ⟶ G) (hf : TopCat.Presheaf.IsLocallySurjective f) (n : ℕ)
    (h₂ : Subsingleton (Sheaf.H ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n))
    (h₁ : Subsingleton (Sheaf.H
      (kernel (Sheaf.Hom.mk f :
        (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) ⟶
          (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)))
      (n + 1))) :
    Subsingleton (Sheaf.H ((⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n) := by
  let fsh : (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) ⟶
      (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) := Sheaf.Hom.mk f
  letI : Balanced (CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) := balanced_of_strongEpiCategory
  haveI : Epi fsh := by
    rw [← Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} fsh]
    simpa [fsh] using hf
  let S := ShortComplex.mk (kernel.ι fsh) fsh (kernel.condition fsh)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel fsh)) inferInstance inferInstance
  haveI : Subsingleton (Sheaf.H S.X₂ n) := by
    simpa [S, fsh] using h₂
  haveI : Subsingleton (Sheaf.H S.X₁ (n + 1)) := by
    simpa [S, fsh] using h₁
  simpa [S, fsh] using sheafH_dimension_shift_X₃_of_both (S := S) hS n

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

/-- Presheaf-boundary wrapper for `subsingleton_sheafH_of_shortExact_middle`: if
`f : F ⟶ G` is mono between sheaf-valued presheaves, and the cohomology of `F`
and of the cokernel sheaf of `Sheaf.Hom.mk f` are subsingleton in degree `n`,
then so is the cohomology of `G`. -/
theorem subsingleton_sheafH_of_shortExact_middle_presheaf {X : TopCat.{u}}
    {F G : TopCat.Presheaf AddCommGrpCat.{u} X}
    (hF : F.IsSheaf) (hG : G.IsSheaf)
    (f : F ⟶ G) [Mono f] (n : ℕ)
    (h₁ : Subsingleton (Sheaf.H ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n))
    (h₃ : Subsingleton (Sheaf.H (cokernel (show
      (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) ⟶
        (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) from
          Sheaf.Hom.mk f)) n)) :
    Subsingleton (Sheaf.H ((⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n) := by
  let fsh : (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) ⟶
      (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) := Sheaf.Hom.mk f
  haveI : Mono fsh := by
    exact (Sheaf.Hom.mono_iff_presheaf_mono
      (J := Opens.grothendieckTopology X) (D := AddCommGrpCat.{u}) fsh).2 inferInstance
  let S := ShortComplex.mk fsh (cokernel.π fsh) (cokernel.condition fsh)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel fsh))
    inferInstance inferInstance
  have h₁' : Subsingleton (Sheaf.H S.X₁ n) := by
    simpa [S] using h₁
  have h₃' : Subsingleton (Sheaf.H S.X₃ n) := by
    simpa [S, fsh] using h₃
  simpa [S] using subsingleton_sheafH_of_shortExact_middle (S := S) hS n h₁' h₃'

/-- On an empty space, all sheaf cohomology groups are subsingleton.
    Proof: when X is empty, all stalks are vacuously zero, so the sheaf is zero,
    and zero sheaves have subsingleton cohomology in all degrees. -/
instance sheafH_subsingleton_of_isEmpty {X : TopCat.{u}} [IsEmpty X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Subsingleton (Sheaf.H F n) :=
  sheafH_subsingleton_of_isZero F
    (by
      have hF_zero : IsZero ((⟨F.val, F.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) :=
        sheaf_isZero_of_zero_stalks X F.cond (fun x _ => (IsEmpty.false x).elim)
      simpa using hF_zero) n

/-- Presheaf-boundary wrapper for empty-space vanishing: if `X` is empty and `F` is a
sheaf-valued presheaf, then the cohomology of the bundled sheaf `⟨F, hF⟩` is subsingleton
in every degree. -/
theorem sheafH_subsingleton_of_isEmpty_presheaf {X : TopCat.{u}} [IsEmpty X]
    {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf) (n : ℕ) :
    Subsingleton (Sheaf.H ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n) := by
  simpa using
    (sheafH_subsingleton_of_isEmpty
      (F := (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) (n := n))

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

/-- Presheaf-boundary naturality of
`sheafH1_cokernel_iso_of_subsingleton_middle_presheaf` for a morphism between two short
exact sequences of presheaves. -/
theorem sheafH1_cokernel_iso_of_subsingleton_middle_presheaf_natural {X : TopCat.{u}}
    {F₁₁ F₁₂ F₁₃ F₂₁ F₂₂ F₂₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    (h₁₁ : F₁₁.IsSheaf) (h₁₂ : F₁₂.IsSheaf) (h₁₃ : F₁₃.IsSheaf)
    (h₂₁ : F₂₁.IsSheaf) (h₂₂ : F₂₂.IsSheaf) (h₂₃ : F₂₃.IsSheaf)
    {f₁ : F₁₁ ⟶ F₁₂} {g₁ : F₁₂ ⟶ F₁₃} (hfg₁ : f₁ ≫ g₁ = 0)
    {f₂ : F₂₁ ⟶ F₂₂} {g₂ : F₂₂ ⟶ F₂₃} (hfg₂ : f₂ ≫ g₂ = 0)
    (hS₁ : (ShortComplex.mk
      (X₁ := (⟨F₁₁, h₁₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₂ := (⟨F₁₂, h₁₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₃ := (⟨F₁₃, h₁₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (Sheaf.Hom.mk f₁)
      (Sheaf.Hom.mk g₁)
      (by
        apply Sheaf.Hom.ext
        simpa using hfg₁)).ShortExact)
    (hS₂ : (ShortComplex.mk
      (X₁ := (⟨F₂₁, h₂₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₂ := (⟨F₂₂, h₂₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₃ := (⟨F₂₃, h₂₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (Sheaf.Hom.mk f₂)
      (Sheaf.Hom.mk g₂)
      (by
        apply Sheaf.Hom.ext
        simpa using hfg₂)).ShortExact)
    {τ₁ : F₁₁ ⟶ F₂₁} {τ₂ : F₁₂ ⟶ F₂₂} {τ₃ : F₁₃ ⟶ F₂₃}
    (hτ₁₂ : τ₁ ≫ f₂ = f₁ ≫ τ₂)
    (hτ₂₃ : τ₂ ≫ g₂ = g₁ ≫ τ₃)
    (h₁₂H : Subsingleton (Sheaf.H ((⟨F₁₂, h₁₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) 1))
    (h₂₂H : Subsingleton (Sheaf.H ((⟨F₂₂, h₂₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) 1)) :
    cokernel.map (g₁.app (op ⊤)) (g₂.app (op ⊤))
        (τ₂.app (op ⊤)) (τ₃.app (op ⊤))
        (by
          simpa using congrArg
            (fun α : F₁₂ ⟶ F₂₃ => α.app (op ⊤)) hτ₂₃.symm) ≫
      (sheafH1_cokernel_iso_of_subsingleton_middle_presheaf
        h₂₁ h₂₂ h₂₃ hfg₂ hS₂ h₂₂H).hom =
    (sheafH1_cokernel_iso_of_subsingleton_middle_presheaf
      h₁₁ h₁₂ h₁₃ hfg₁ hS₁ h₁₂H).hom ≫
      (sheafCohomologyFunctor X 1).map (Sheaf.Hom.mk τ₁) := by
  let S₁ : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) := ShortComplex.mk
    (X₁ := (⟨F₁₁, h₁₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₂ := (⟨F₁₂, h₁₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₃ := (⟨F₁₃, h₁₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (Sheaf.Hom.mk f₁)
    (Sheaf.Hom.mk g₁)
    (by
      apply Sheaf.Hom.ext
      simpa using hfg₁)
  let S₂ : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) := ShortComplex.mk
    (X₁ := (⟨F₂₁, h₂₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₂ := (⟨F₂₂, h₂₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₃ := (⟨F₂₃, h₂₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (Sheaf.Hom.mk f₂)
    (Sheaf.Hom.mk g₂)
    (by
      apply Sheaf.Hom.ext
      simpa using hfg₂)
  let φ : S₁ ⟶ S₂ := ShortComplex.homMk
    (Sheaf.Hom.mk τ₁)
    (Sheaf.Hom.mk τ₂)
    (Sheaf.Hom.mk τ₃)
    (by
      apply Sheaf.Hom.ext
      simpa using hτ₁₂)
    (by
      apply Sheaf.Hom.ext
      simpa using hτ₂₃)
  have hS₁' : S₁.ShortExact := by
    simpa [S₁] using hS₁
  have hS₂' : S₂.ShortExact := by
    simpa [S₂] using hS₂
  have h₁₂H' : Subsingleton (Sheaf.H S₁.X₂ 1) := by
    simpa [S₁] using h₁₂H
  have h₂₂H' : Subsingleton (Sheaf.H S₂.X₂ 1) := by
    simpa [S₂] using h₂₂H
  simpa [S₁, S₂, φ] using
    (sheafH1_cokernel_iso_of_subsingleton_middle_natural
      (S₁ := S₁) (S₂ := S₂) hS₁' hS₂' φ h₁₂H' h₂₂H')

/-- The degree-`0` sheaf cohomology functor is naturally isomorphic to taking sections on `⊤`. -/
noncomputable def sheafH0NatIsoSections {X : TopCat.{u}} :
    sheafCohomologyFunctor X 0 ≅
      sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤) :=
  NatIso.ofComponents (fun F => (sheafH0EquivSections F).toAddCommGrpIso) fun f => by
    ext x
    simpa [sheafCohomologyFunctor_map_apply] using
      (sheafH0EquivSections_natural (f := f) (x := x))

@[simp] theorem sheafH0NatIsoSections_hom_app {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (x : Sheaf.H F 0) :
    ConcreteCategory.hom ((sheafH0NatIsoSections (X := X)).hom.app F) x =
      sheafH0EquivSections F x := rfl

@[simp] theorem sheafH0NatIsoSections_inv_app {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (x : ToType (F.val.obj (op ⊤))) :
    ConcreteCategory.hom ((sheafH0NatIsoSections (X := X)).inv.app F) x =
      (sheafH0EquivSections F).symm x := rfl

/-- Functor-level naturality of the connecting morphism on sheaf cohomology. This is the
    `sheafCohomologyFunctor`-packaged form of `sheafH_comp_extClass_naturality`. -/
theorem sheafCohomologyFunctor_map_extClass_naturality {X : TopCat.{u}}
    {S₁ S₂ : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n : ℕ)
    (y : Sheaf.H S₁.X₃ n) :
    ConcreteCategory.hom ((sheafCohomologyFunctor X (n + 1)).map φ.τ₁)
      (y.comp hS₁.extClass rfl) =
    (ConcreteCategory.hom ((sheafCohomologyFunctor X n).map φ.τ₃) y).comp hS₂.extClass rfl := by
  rw [sheafCohomologyFunctor_map_apply, sheafCohomologyFunctor_map_apply]
  exact sheafH_comp_extClass_naturality hS₁ hS₂ φ n y

/-- If `y` maps to `z` on the `X₃` side of a morphism of short exact sequences, then the
    corresponding extension class of `y` maps to the extension class of `z` on the `X₁`
    side. This packages `sheafCohomologyFunctor_map_extClass_naturality` with the
    downstream rewrite by the known `X₃`-side equality. -/
theorem sheafCohomologyFunctor_map_extClass_of_map_eq {X : TopCat.{u}}
    {S₁ S₂ : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n : ℕ)
    {y : Sheaf.H S₁.X₃ n} {z : Sheaf.H S₂.X₃ n}
    (hy : ConcreteCategory.hom ((sheafCohomologyFunctor X n).map φ.τ₃) y = z) :
    ConcreteCategory.hom ((sheafCohomologyFunctor X (n + 1)).map φ.τ₁)
      (y.comp hS₁.extClass rfl) =
    z.comp hS₂.extClass rfl := by
  rw [sheafCohomologyFunctor_map_extClass_naturality hS₁ hS₂ φ n y, hy]

/-- The sheaf-cohomology connecting morphism as an additive equivalence, assuming the middle
    sheaf cohomology groups in degrees `n` and `n + 1` are subsingleton. -/
noncomputable def sheafH_extClassAddEquiv_of_subsingleton_middle {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact) (n : ℕ)
    (h₂n : Subsingleton (Sheaf.H S.X₂ n))
    (h₂succ : Subsingleton (Sheaf.H S.X₂ (n + 1))) :
    Sheaf.H S.X₃ n ≃+ Sheaf.H S.X₁ (n + 1) :=
  extClass_postcompAddEquiv_of_subsingleton_middle _ hS n h₂n h₂succ

/-- The sheaf-cohomology connecting morphism as an `AddCommGrpCat` isomorphism, assuming the
    middle sheaf cohomology groups in degrees `n` and `n + 1` are subsingleton. -/
noncomputable def sheafH_extClassIso_of_subsingleton_middle {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact) (n : ℕ)
    (h₂n : Subsingleton (Sheaf.H S.X₂ n))
    (h₂succ : Subsingleton (Sheaf.H S.X₂ (n + 1))) :
    AddCommGrpCat.of (Sheaf.H S.X₃ n) ≅ AddCommGrpCat.of (Sheaf.H S.X₁ (n + 1)) :=
  (sheafH_extClassAddEquiv_of_subsingleton_middle hS n h₂n h₂succ).toAddCommGrpIso

@[simp] theorem sheafH_extClassIso_of_subsingleton_middle_hom_apply {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact) (n : ℕ)
    (h₂n : Subsingleton (Sheaf.H S.X₂ n))
    (h₂succ : Subsingleton (Sheaf.H S.X₂ (n + 1)))
    (y : Sheaf.H S.X₃ n) :
    ConcreteCategory.hom
        ((sheafH_extClassIso_of_subsingleton_middle hS n h₂n h₂succ).hom) y =
      y.comp hS.extClass rfl := by
  rfl

/-- Presheaf-boundary wrapper for `sheafH_extClassIso_of_subsingleton_middle`: if
`0 → F₁ → F₂ → F₃ → 0` is short exact after bundling the presheaves as sheaves and the
middle cohomology groups in degrees `n` and `n + 1` are subsingleton, then the connecting
morphism induces an isomorphism `H^n(F₃) ≅ H^(n+1)(F₁)`. -/
noncomputable def sheafH_extClassIso_of_subsingleton_middle_presheaf {X : TopCat.{u}}
    {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    (h₁ : F₁.IsSheaf) (h₂ : F₂.IsSheaf) (h₃ : F₃.IsSheaf)
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃} (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk
      (X₁ := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₂ := (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₃ := (⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (Sheaf.Hom.mk f)
      (Sheaf.Hom.mk g)
      (by
        apply Sheaf.Hom.ext
        simpa using hfg)).ShortExact)
    (n : ℕ)
    (h₂n : Subsingleton (Sheaf.H ((⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n))
    (h₂succ : Subsingleton (Sheaf.H ((⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) (n + 1))) :
    AddCommGrpCat.of (Sheaf.H ((⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n) ≅
      AddCommGrpCat.of (Sheaf.H ((⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) (n + 1)) := by
  let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) := ShortComplex.mk
    (X₁ := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₂ := (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₃ := (⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (Sheaf.Hom.mk f)
    (Sheaf.Hom.mk g)
    (by
      apply Sheaf.Hom.ext
      simpa using hfg)
  have hS' : S.ShortExact := by
    simpa [S] using hS
  have h₂n' : Subsingleton (Sheaf.H S.X₂ n) := by
    simpa [S] using h₂n
  have h₂succ' : Subsingleton (Sheaf.H S.X₂ (n + 1)) := by
    simpa [S] using h₂succ
  simpa [S] using
    sheafH_extClassIso_of_subsingleton_middle (S := S) hS' n h₂n' h₂succ'

/-- Naturality of the sheaf-level connecting isomorphism for morphisms of short exact
    sequences, under the corresponding middle-degree vanishing hypotheses. -/
theorem sheafH_extClassIso_of_subsingleton_middle_natural {X : TopCat.{u}}
    {S₁ S₂ : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n : ℕ)
    (h₁₂n : Subsingleton (Sheaf.H S₁.X₂ n))
    (h₁₂succ : Subsingleton (Sheaf.H S₁.X₂ (n + 1)))
    (h₂₂n : Subsingleton (Sheaf.H S₂.X₂ n))
    (h₂₂succ : Subsingleton (Sheaf.H S₂.X₂ (n + 1))) :
    (sheafH_extClassIso_of_subsingleton_middle hS₁ n h₁₂n h₁₂succ).hom ≫
        (sheafCohomologyFunctor X (n + 1)).map φ.τ₁ =
      (sheafCohomologyFunctor X n).map φ.τ₃ ≫
        (sheafH_extClassIso_of_subsingleton_middle hS₂ n h₂₂n h₂₂succ).hom := by
  ext y
  simpa [sheafH_extClassIso_of_subsingleton_middle_hom_apply] using
    (sheafCohomologyFunctor_map_extClass_naturality hS₁ hS₂ φ n y)

/-- Presheaf-boundary naturality of `sheafH_extClassIso_of_subsingleton_middle_presheaf`
    for a morphism between two short exact sequences of presheaves. -/
theorem sheafH_extClassIso_of_subsingleton_middle_presheaf_natural {X : TopCat.{u}}
    {F₁₁ F₁₂ F₁₃ F₂₁ F₂₂ F₂₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    (h₁₁ : F₁₁.IsSheaf) (h₁₂ : F₁₂.IsSheaf) (h₁₃ : F₁₃.IsSheaf)
    (h₂₁ : F₂₁.IsSheaf) (h₂₂ : F₂₂.IsSheaf) (h₂₃ : F₂₃.IsSheaf)
    {f₁ : F₁₁ ⟶ F₁₂} {g₁ : F₁₂ ⟶ F₁₃} (hfg₁ : f₁ ≫ g₁ = 0)
    {f₂ : F₂₁ ⟶ F₂₂} {g₂ : F₂₂ ⟶ F₂₃} (hfg₂ : f₂ ≫ g₂ = 0)
    (hS₁ : (ShortComplex.mk
      (X₁ := (⟨F₁₁, h₁₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₂ := (⟨F₁₂, h₁₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₃ := (⟨F₁₃, h₁₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (Sheaf.Hom.mk f₁)
      (Sheaf.Hom.mk g₁)
      (by
        apply Sheaf.Hom.ext
        simpa using hfg₁)).ShortExact)
    (hS₂ : (ShortComplex.mk
      (X₁ := (⟨F₂₁, h₂₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₂ := (⟨F₂₂, h₂₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (X₃ := (⟨F₂₃, h₂₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
      (Sheaf.Hom.mk f₂)
      (Sheaf.Hom.mk g₂)
      (by
        apply Sheaf.Hom.ext
        simpa using hfg₂)).ShortExact)
    {τ₁ : F₁₁ ⟶ F₂₁} {τ₂ : F₁₂ ⟶ F₂₂} {τ₃ : F₁₃ ⟶ F₂₃}
    (hτ₁₂ : τ₁ ≫ f₂ = f₁ ≫ τ₂)
    (hτ₂₃ : τ₂ ≫ g₂ = g₁ ≫ τ₃)
    (n : ℕ)
    (h₁₂n : Subsingleton (Sheaf.H ((⟨F₁₂, h₁₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n))
    (h₁₂succ : Subsingleton (Sheaf.H ((⟨F₁₂, h₁₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) (n + 1)))
    (h₂₂n : Subsingleton (Sheaf.H ((⟨F₂₂, h₂₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n))
    (h₂₂succ : Subsingleton (Sheaf.H ((⟨F₂₂, h₂₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) (n + 1))) :
    (sheafH_extClassIso_of_subsingleton_middle_presheaf
        h₁₁ h₁₂ h₁₃ hfg₁ hS₁ n h₁₂n h₁₂succ).hom ≫
        (sheafCohomologyFunctor X (n + 1)).map (Sheaf.Hom.mk τ₁) =
      (sheafCohomologyFunctor X n).map (Sheaf.Hom.mk τ₃) ≫
        (sheafH_extClassIso_of_subsingleton_middle_presheaf
          h₂₁ h₂₂ h₂₃ hfg₂ hS₂ n h₂₂n h₂₂succ).hom := by
  let S₁ : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) := ShortComplex.mk
    (X₁ := (⟨F₁₁, h₁₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₂ := (⟨F₁₂, h₁₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₃ := (⟨F₁₃, h₁₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (Sheaf.Hom.mk f₁)
    (Sheaf.Hom.mk g₁)
    (by
      apply Sheaf.Hom.ext
      simpa using hfg₁)
  let S₂ : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) := ShortComplex.mk
    (X₁ := (⟨F₂₁, h₂₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₂ := (⟨F₂₂, h₂₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₃ := (⟨F₂₃, h₂₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (Sheaf.Hom.mk f₂)
    (Sheaf.Hom.mk g₂)
    (by
      apply Sheaf.Hom.ext
      simpa using hfg₂)
  let φ : S₁ ⟶ S₂ := ShortComplex.homMk
    (Sheaf.Hom.mk τ₁)
    (Sheaf.Hom.mk τ₂)
    (Sheaf.Hom.mk τ₃)
    (by
      apply Sheaf.Hom.ext
      simpa using hτ₁₂)
    (by
      apply Sheaf.Hom.ext
      simpa using hτ₂₃)
  have hS₁' : S₁.ShortExact := by
    simpa [S₁] using hS₁
  have hS₂' : S₂.ShortExact := by
    simpa [S₂] using hS₂
  have h₁₂n' : Subsingleton (Sheaf.H S₁.X₂ n) := by
    simpa [S₁] using h₁₂n
  have h₁₂succ' : Subsingleton (Sheaf.H S₁.X₂ (n + 1)) := by
    simpa [S₁] using h₁₂succ
  have h₂₂n' : Subsingleton (Sheaf.H S₂.X₂ n) := by
    simpa [S₂] using h₂₂n
  have h₂₂succ' : Subsingleton (Sheaf.H S₂.X₂ (n + 1)) := by
    simpa [S₂] using h₂₂succ
  simpa [S₁, S₂, φ] using
    (sheafH_extClassIso_of_subsingleton_middle_natural
      (S₁ := S₁) (S₂ := S₂) hS₁' hS₂' φ n h₁₂n' h₁₂succ' h₂₂n' h₂₂succ')
