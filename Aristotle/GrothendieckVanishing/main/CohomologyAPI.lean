import Mathlib
import Aristotle.GrothendieckVanishing.main.ClosedImmersion
import Aristotle.GrothendieckVanishing.main.ULiftInt

/-!
# Sheaf Cohomology API

Centralizes results about sheaf cohomology `Sheaf.H`, keeping the underlying `Ext`
calculations internal so downstream files never need to unfold `Sheaf.H` directly.

## Main results

* `subsingleton_sheafH_of_shortExact_middle_presheaf`: presheaf-boundary middle-term wrapper
* `sheafH_subsingleton_of_isEmpty_presheaf`: presheaf-boundary empty-space vanishing
* `sheafH_subsingleton_of_isEmpty`: sheaf-level wrapper for empty-space vanishing
* `sheaf_isZero_of_zero_stalks`: zero stalks imply zero sheaf
* `sheafH_subsingleton_of_isZero_presheaf`: presheaf-boundary zero-sheaf vanishing
* `stalk_zero_of_ses_g_iso_presheaf`: presheaf-boundary stalk vanishing from SES with iso
  on `g`
* `stalk_zero_of_shortExact_kernel_presheaf`: presheaf-boundary stalk vanishing from SES
  kernel
* `stalk_zero_of_g_is_cokernel_of_stalk_epi_presheaf`: presheaf-boundary stalk
  vanishing from a cokernel and stalk-epi hypothesis
* `cokernel_stalk_zero_of_stalk_surj`: actual-cokernel specialization of the same stalk
  vanishing under stalk-surjectivity
* `stalk_zero_of_shortExact_cokernel_presheaf`: presheaf-boundary short exact
  specialization of the same cokernel stalk vanishing
* `sheafH_exists_preimage_extClass_presheaf`: presheaf-boundary wrapper for lifting
  cohomology classes through the connecting morphism
* `sheafH0EquivSections_presheaf`: presheaf-boundary wrapper for `H^0(F) ≃+ F(⊤)`
* `sheafH0EquivSections_presheaf_natural`: presheaf-boundary naturality of the above
* `sheafH1_cokernel_iso_of_subsingleton_middle_presheaf`: presheaf-boundary form of the
  `H¹` cokernel identification
* `sheafH1_cokernel_iso_of_subsingleton_middle_presheaf_natural`: presheaf-boundary
  naturality for the same `H¹` cokernel identification
* `sheafH_extClassAddEquiv_of_subsingleton_middle_presheaf`: presheaf-boundary additive
  equivalence for the higher-degree connecting morphism
* `sheafH_extClassIso_of_subsingleton_middle_presheaf`: presheaf-boundary form of the
  higher-degree connecting isomorphism
* `sheafH_extClassIso_of_subsingleton_middle_presheaf_natural`: presheaf-boundary
  naturality for the same connecting isomorphism
* `epi_app_top_of_subsingleton_sheafH1_presheaf`: presheaf-boundary H^1 vanishing gives
  surjectivity on top sections
* `sheafH0_surj_of_epi_app_top_presheaf`: presheaf-boundary surjectivity on top sections
  gives H^0 surjectivity
* `sheafH_subsingleton_H1_via_surj_presheaf`: presheaf-boundary H^1 vanishing via
  H^0-surjectivity
* `sheafH_subsingleton_H1_via_epi_app_top_presheaf`: presheaf-boundary H^1 vanishing via
  surjective top sections
* `sheafH_subsingleton_of_injective`: positive-degree cohomology of an injective sheaf
  is subsingleton
* `sheafH_subsingleton_H1_of_injective_of_epi_app_top_presheaf`: presheaf-boundary
  injective-middle-term `H¹` vanishing
* `sheafH_dimension_shift_of_both_presheaf`: presheaf-boundary forward dimension shift
  for short exact sequences
* `sheafH_dimension_shift_of_mono_presheaf`: presheaf-boundary forward dimension shift
* `sheafH_dimension_shift_presheaf`: presheaf-boundary forward dimension shift with
  injective middle term
* `sheafH_dimension_shift_X₃_presheaf`: presheaf-boundary reverse dimension shift with
  injective middle term
* `sheafH_dimension_shift_X₃_of_both_presheaf`: presheaf-boundary reverse dimension shift
  for short exact sequences
* `sheafH_dimension_shift_X₃_of_locallySurjective_presheaf`: presheaf-boundary reverse
  dimension shift for locally surjective morphisms
-/

universe w' w v u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

instance : HasSeparator AddCommGrpCat.{u} where
  hasSeparator := by
    use AddCommGrpCat.of (ULift ℤ)
    intro A B f g h
    simp_all only [ObjectProperty.singleton_iff, AddCommGrpCat.ext_iff,
      AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply, forall_eq',
      ULift.forall]
    intro x
    specialize h (AddCommGrpCat.ofHom
      (AddMonoidHom.mk' (fun y => y • x) fun y z => by simp only [add_smul])) 1
    aesop

instance : IsGrothendieckAbelian.{u} AddCommGrpCat.{u} where

instance (X : TopCat.{u}) : IsGrothendieckAbelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (IsGrothendieckAbelian (CategoryTheory.Sheaf _ _))

instance {C : Type*} [Category C] {D : Type*} [Category D] [Preadditive D] :
    (Functor.const Cᵒᵖ : D ⥤ Cᵒᵖ ⥤ D).Additive where

instance {C : Type*} [Category C] [Preadditive C] {X : TopCat.{u}} :
    Preadditive (TopCat.Presheaf C X) := by
  delta TopCat.Presheaf
  infer_instance

instance {X : TopCat.{u}} :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive :=
  inferInstanceAs ((Functor.const (Opens X)ᵒᵖ ⋙
    presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive)

/-! ## Projective ULift ℤ in AddCommGrpCat -/

/-- `ULift ℤ` is projective in `AddCommGrpCat` (via the equivalence with `ModuleCat ℤ`). -/
noncomputable instance ulift_int_projective :
    Projective (AddCommGrpCat.of (ULift.{u} ℤ)) := by
  set e := (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).asEquivalence with he
  have : e.inverse.PreservesEpimorphisms :=
    ⟨fun f _ => e.symm.functor.map_epi f⟩
  have hp := e.toAdjunction.map_projective _
    (inferInstance : Projective (ModuleCat.of ℤ (ULift.{u} ℤ)))
  simp only [he, Functor.asEquivalence, ModuleCat.forget₂_obj] at hp
  exact hp

noncomputable instance sheafHasExt (X : TopCat.{u}) :
    HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  hasExt_of_enoughInjectives _

/-! ## Internal Ext helpers -/

section ExtDimShift
variable {C' : Type*} [Category C'] [Abelian C'] [HasExt C']

/-- Dimension shift for Ext via LES: given `0 → X₁ → X₂ → X₃ → 0` short exact,
    `Ext^n(Z, X₃) = 0` and `Ext^{n+1}(Z, X₂) = 0` imply `Ext^{n+1}(Z, X₁) = 0`. -/
private theorem ext_dimension_shift (Z : C') {S : ShortComplex C'} (hS : S.ShortExact) (n : ℕ)
    (h₃ : Subsingleton (Ext Z S.X₃ n))
    (h₂ : Subsingleton (Ext Z S.X₂ (n + 1))) :
    Subsingleton (Ext Z S.X₁ (n + 1)) := by
  constructor; intro a b
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ _ hS a (@Subsingleton.elim _ h₂ _ _) rfl
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₁ _ hS b (@Subsingleton.elim _ h₂ _ _) rfl
  rw [← hc, ← hd, @Subsingleton.elim _ h₃ c d]

/-- Reverse dimension shift: `Ext^n(Z, X₂) = 0` and `Ext^{n+1}(Z, X₁) = 0` imply
    `Ext^n(Z, X₃) = 0`. Uses exactness at X₃ in the covariant LES. -/
private theorem ext_dimension_shift_X₃ (Z : C') {S : ShortComplex C'} (hS : S.ShortExact) (n : ℕ)
    (h₂ : Subsingleton (Ext Z S.X₂ n))
    (h₁ : Subsingleton (Ext Z S.X₁ (n + 1))) :
    Subsingleton (Ext Z S.X₃ n) := by
  constructor; intro a b
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₃ _ hS a rfl (@Subsingleton.elim _ h₁ _ _)
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₃ _ hS b rfl (@Subsingleton.elim _ h₁ _ _)
  rw [← hc, ← hd, @Subsingleton.elim _ h₂ c d]

/-- If the middle cohomology groups in degrees `n` and `n + 1` are subsingleton, then the
    connecting morphism `Ext^n(Z, X₃) → Ext^(n+1)(Z, X₁)` is bijective. -/
private theorem extClass_postcomp_bijective_of_subsingleton_middle
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
private noncomputable def extClass_postcompAddEquiv_of_subsingleton_middle
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
private lemma extClass_naturality {S₁ S₂ : ShortComplex C'} (hS₁ : S₁.ShortExact)
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

/-- Internal helper: if `Y` is zero in an abelian category, `Ext X Y n` is subsingleton
    for all `X`, `n`.
    Proof: `𝟙 Y = 0` because `Y` is zero, so `x = x ∘ mk₀(𝟙 Y) = x ∘ mk₀(0) = x ∘ 0 = 0`. -/
private theorem ext_subsingleton_of_isZero_tgt {X Y : C'} (hY : IsZero Y) (n : ℕ) :
    Subsingleton (Ext X Y n) :=
  ⟨fun a b => by
    have eq : ∀ x : Ext X Y n, x = 0 := fun x => by
      have h := Ext.comp_mk₀_id x
      rw [show (𝟙 Y : Y ⟶ Y) = 0 from hY.eq_of_src _ _, Ext.mk₀_zero] at h
      exact h.symm.trans (Ext.comp_zero x Y 0 n (add_zero n))
    exact (eq a).trans (eq b).symm⟩

end ExtDimShift

/-! ## Stalks and zero sheaves -/

/-- Presheaf-boundary naturality of the connecting map on sheaf cohomology for a morphism
    of short exact sequences of presheaves. This packages the underlying extension-class
    naturality calculation with the associativity rewrites needed to move between nested
    `comp` expressions and composition with the connecting class. -/
private theorem sheafH_comp_extClass_naturality_presheaf {X : TopCat.{u}}
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
    (y : Sheaf.H ((⟨F₁₃, h₁₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n) :
    (y.comp hS₁.extClass rfl).comp (Ext.mk₀ (Sheaf.Hom.mk τ₁)) (add_zero (n + 1)) =
      (y.comp (Ext.mk₀ (Sheaf.Hom.mk τ₃)) (add_zero n)).comp hS₂.extClass rfl := by
  let φ :
      ShortComplex.mk
        (X₁ := (⟨F₁₁, h₁₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
        (X₂ := (⟨F₁₂, h₁₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
        (X₃ := (⟨F₁₃, h₁₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
        (Sheaf.Hom.mk f₁)
        (Sheaf.Hom.mk g₁)
        (by
          apply Sheaf.Hom.ext
          simpa using hfg₁) ⟶
      ShortComplex.mk
        (X₁ := (⟨F₂₁, h₂₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
        (X₂ := (⟨F₂₂, h₂₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
        (X₃ := (⟨F₂₃, h₂₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
        (Sheaf.Hom.mk f₂)
        (Sheaf.Hom.mk g₂)
        (by
          apply Sheaf.Hom.ext
          simpa using hfg₂) := ShortComplex.homMk
    (Sheaf.Hom.mk τ₁)
    (Sheaf.Hom.mk τ₂)
    (Sheaf.Hom.mk τ₃)
    (by
      apply Sheaf.Hom.ext
      simpa using hτ₁₂)
    (by
      apply Sheaf.Hom.ext
      simpa using hτ₂₃)
  have hcomp :
      y.comp (hS₁.extClass.comp (Ext.mk₀ (Sheaf.Hom.mk τ₁)) (add_zero 1)) rfl =
        y.comp ((Ext.mk₀ (Sheaf.Hom.mk τ₃)).comp hS₂.extClass (zero_add 1)) rfl := by
    exact congrArg (fun t => y.comp t rfl) (extClass_naturality hS₁ hS₂ φ).symm
  simpa [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_second_deg_zero] using hcomp

/-- If `0 → F₁ → F₂ → F₃ → 0` is short exact after bundling the presheaves as sheaves and
`H^(n+1)(F₂)` is subsingleton, then every `H^(n+1)(F₁)` class comes from some `H^n(F₃)`
class via the connecting morphism. -/
theorem sheafH_exists_preimage_extClass_presheaf {X : TopCat.{u}}
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
    (h₂H : Subsingleton (Sheaf.H ((⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) (n + 1)))
    (x : Sheaf.H ((⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) (n + 1)) :
    ∃ y : Sheaf.H ((⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n,
      y.comp hS.extClass rfl = x := by
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
  have h₂' : Subsingleton (Sheaf.H S.X₂ (n + 1)) := by
    simpa [S] using h₂H
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ _ hS' x (@Subsingleton.elim _ h₂' _ _) rfl
  exact ⟨y, by simpa [S] using hy⟩

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

/-- If a presheaf is a sheaf and the induced bundled sheaf is zero, then its cohomology is
    subsingleton in every degree. -/
theorem sheafH_subsingleton_of_isZero_presheaf {X : TopCat.{u}}
    {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf)
    (hzero : IsZero ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))) (n : ℕ) :
    Subsingleton (Sheaf.H ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n) :=
  ext_subsingleton_of_isZero_tgt hzero n

/-- Presheaf-boundary stalk vanishing: if `0 → F₁ → F₂ → F₃ → 0` is short exact after
bundling the presheaves as sheaves, and the stalk map of `g` at `x` is an isomorphism,
then the stalk of `F₁` at `x` vanishes. -/
theorem stalk_zero_of_ses_g_iso_presheaf
    {X : TopCat.{u}}
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
    (x : X)
    (hiso : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map g))
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj F₁) :
    a = 0 := by
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
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let fsh :
      (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) ⟶
        (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) := Sheaf.Hom.mk f
  have hfsh_mono : Mono fsh := by
    simpa [S, fsh] using hS'.mono_f
  have hf_mono : Mono f := by
    exact (Sheaf.Hom.mono_iff_presheaf_mono
      (J := Opens.grothendieckTopology X) (D := AddCommGrpCat.{u}) fsh).1 hfsh_mono
  haveI : Mono fsh := by
    exact (Sheaf.Hom.mono_iff_presheaf_mono
      (J := Opens.grothendieckTopology X) (D := AddCommGrpCat.{u}) fsh).2 hf_mono
  haveI := TopCat.Presheaf.stalkFunctor_preserves_mono (C := AddCommGrpCat.{u}) (X := X) x
  have hTf_mono : Mono (T.map f) := by
    simpa [T, fsh] using (Functor.map_mono (TopCat.Sheaf.forget _ _ ⋙ T) fsh)
  have hf0 : T.map f = 0 := by
    have : T.map f ≫ T.map g = 0 := by
      rw [← T.map_comp, hfg, Functor.map_zero]
    rw [show T.map f = (T.map f ≫ T.map g) ≫ inv (T.map g) by simp, this, zero_comp]
  exact (AddCommGrpCat.mono_iff_injective _).mp hTf_mono
    (show ConcreteCategory.hom (T.map f) a = ConcreteCategory.hom (T.map f) 0 by simp [hf0])

/-- In a short exact sequence `X₁ → X₂ → X₃`, if all stalks of `X₂` at `x` vanish, then
    all stalks of `X₁` at `x` vanish (by mono-injectivity of `f`). -/
theorem stalk_zero_of_shortExact_kernel_presheaf
    {X : TopCat.{u}}
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
    (x : X)
    (hX₂ : ∀ (b : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj F₂), b = 0)
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj F₁) :
    a = 0 := by
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
  let T := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let fsh :
      (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) ⟶
        (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) := Sheaf.Hom.mk f
  have hfsh_mono : Mono fsh := by
    simpa [S, fsh] using hS'.mono_f
  have hf_mono : Mono f := by
    exact (Sheaf.Hom.mono_iff_presheaf_mono
      (J := Opens.grothendieckTopology X) (D := AddCommGrpCat.{u}) fsh).1 hfsh_mono
  haveI : Mono fsh := by
    exact (Sheaf.Hom.mono_iff_presheaf_mono
      (J := Opens.grothendieckTopology X) (D := AddCommGrpCat.{u}) fsh).2 hf_mono
  haveI := TopCat.Presheaf.stalkFunctor_preserves_mono (C := AddCommGrpCat.{u}) (X := X) x
  have hTf_mono : Mono (T.map f) := by
    simpa [T, fsh] using (Functor.map_mono (TopCat.Sheaf.forget _ _ ⋙ T) fsh)
  exact (AddCommGrpCat.mono_iff_injective _).mp hTf_mono
    ((hX₂ _).trans (map_zero _).symm)

/-- Presheaf-boundary stalk vanishing: if `g` is a cokernel of `f` after bundling the
presheaves as sheaves, and the stalk map of `f` at `x` is epi, then the stalk of `F₃`
at `x` vanishes. -/
theorem stalk_zero_of_g_is_cokernel_of_stalk_epi_presheaf
    {X : TopCat.{u}}
    {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
    (h₁ : F₁.IsSheaf) (h₂ : F₂.IsSheaf) (h₃ : F₃.IsSheaf)
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃} (hfg : f ≫ g = 0)
    (hg : let S := (ShortComplex.mk
        (X₁ := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
        (X₂ := (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
        (X₃ := (⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
        (Sheaf.Hom.mk f)
        (Sheaf.Hom.mk g)
        (by
          apply Sheaf.Hom.ext
          simpa using hfg)
      : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)); IsColimit (CokernelCofork.ofπ S.g S.zero))
    (x : X)
    (hepi : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f))
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj F₃) :
    a = 0 := by
  let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) := ShortComplex.mk
    (X₁ := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₂ := (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (X₃ := (⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))
    (Sheaf.Hom.mk f)
    (Sheaf.Hom.mk g)
    (by
      apply Sheaf.Hom.ext
      simpa using hfg)
  have hg' : IsColimit (CokernelCofork.ofπ S.g S.zero) := by
    simpa [S] using hg
  let T : TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
    TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  haveI : ∀ U : Opens X, Decidable (x ∈ U) := fun _ => Classical.dec _
  haveI : T.IsLeftAdjoint :=
    (stalkSkyscraperSheafAdjunction (C := AddCommGrpCat.{u}) (X := X) (p₀ := x)).isLeftAdjoint
  haveI : Epi (T.map S.f) := by
    simpa [T, S] using hepi
  have hzero_map : T.map S.f ≫ T.map S.g = 0 := by
    rw [← T.map_comp, S.zero, Functor.map_zero]
  have hcolim : IsColimit (CokernelCofork.ofπ (T.map S.g) hzero_map) := by
    simpa [T, hzero_map] using CokernelCofork.mapIsColimit _ hg' T
  have hzero : IsZero (T.obj S.X₃) := CokernelCofork.IsColimit.isZero_of_epi hcolim
  haveI := AddCommGrpCat.subsingleton_of_isZero hzero
  change T.obj S.X₃ at a
  change (a : T.obj S.X₃) = 0
  exact Subsingleton.elim _ _

/-- Actual-cokernel specialization of
`stalk_zero_of_g_is_cokernel_of_stalk_epi_presheaf`: if the stalk map of `f` at `x`
is surjective, then the stalk of `cokernel f` at `x` vanishes. -/
theorem cokernel_stalk_zero_of_stalk_surj
    {X : TopCat.{u}}
    {F G : TopCat.Presheaf AddCommGrpCat.{u} X}
    (hF : F.IsSheaf) (hG : G.IsSheaf)
    (f : CategoryTheory.NatTrans F G) (x : X)
    (hf : Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f)))
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      (Limits.cokernel (show (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) ⟶
        (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) from Sheaf.Hom.mk f)).val) :
    a = 0 := by
  let fsh : (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) ⟶
      (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) := Sheaf.Hom.mk f
  have hepi : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f) := by
    simpa using (AddCommGrpCat.epi_iff_surjective _).mpr hf
  simpa [fsh] using stalk_zero_of_g_is_cokernel_of_stalk_epi_presheaf
    (F₁ := F)
    (F₂ := G)
    (F₃ := (Limits.cokernel fsh).val)
    hF
    hG
    (Limits.cokernel fsh).cond
    (f := f)
    (g := (Limits.cokernel.π fsh).val)
    (show f ≫ (Limits.cokernel.π fsh).val = 0 by
      ext U s
      change ConcreteCategory.hom (((fsh ≫ Limits.cokernel.π fsh).val.app U)) s = 0
      have happ :
          (((fsh ≫ Limits.cokernel.π fsh).val).app U) =
            NatTrans.app
              (0 : (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X).val ⟶
                (Limits.cokernel fsh).val) U := by
        exact NatTrans.congr_app
          (congrArg (fun α => α.val) (Limits.cokernel.condition fsh))
          U
      rw [happ]
      simp)
    (by simpa [fsh] using (cokernelIsCokernel fsh))
    x
    hepi
    a

/-- Presheaf-boundary short exact sequence version of
`stalk_zero_of_g_is_cokernel_of_stalk_epi_presheaf`. -/
theorem stalk_zero_of_shortExact_cokernel_presheaf
    {X : TopCat.{u}}
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
    (x : X)
    (hepi : Epi ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f))
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj F₃) :
    a = 0 := by
  exact stalk_zero_of_g_is_cokernel_of_stalk_epi_presheaf
    (F₁ := F₁) (F₂ := F₂) (F₃ := F₃)
    h₁ h₂ h₃
    (f := f) (g := g) hfg
    (hg := by simpa using hS.gIsCokernel)
    x hepi a

/-! ## H⁰ ≅ Sections -/

/-- If `F` is a sheaf, then `H F 0` is equivalent to sections on `⊤`. -/
noncomputable def sheafH0EquivSections_presheaf {X : TopCat.{u}}
    {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf) :
    Sheaf.H ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) 0 ≃+ F.obj (op ⊤) :=
  Ext.addEquiv₀.trans
    (((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat
        Limits.isTerminalTop).homAddEquiv _ ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _))

/-- Presheaf-boundary naturality of `sheafH0EquivSections_presheaf`: composing `x`
    with `mk₀ (Sheaf.Hom.mk f)` at degree 0 corresponds to applying `f.app(⊤)` on
    sections. -/
lemma sheafH0EquivSections_presheaf_natural {X : TopCat.{u}}
    {F G : TopCat.Presheaf AddCommGrpCat.{u} X}
    (hF : F.IsSheaf) (hG : G.IsSheaf) (f : F ⟶ G)
    (x : Sheaf.H ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) 0) :
    sheafH0EquivSections_presheaf hG
      (x.comp (Ext.mk₀ (Sheaf.Hom.mk f)) (add_zero 0)) =
    ConcreteCategory.hom (f.app (op ⊤)) (sheafH0EquivSections_presheaf hF x) := by
  let Fsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F, hF⟩
  let Gsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨G, hG⟩
  let fsh : Fsh ⟶ Gsh := Sheaf.Hom.mk f
  conv_lhs => rw [show x = Ext.mk₀ (Ext.addEquiv₀ x) from
    (Ext.mk₀_addEquiv₀_apply x).symm, Ext.mk₀_comp_mk₀]
  unfold sheafH0EquivSections_presheaf
  simp only [AddEquiv.trans_apply]
  have key :
      Ext.addEquiv₀ (Ext.mk₀ (Ext.addEquiv₀ x ≫ fsh)) = Ext.addEquiv₀ x ≫ fsh :=
    by
      change Ext.addEquiv₀ (Ext.addEquiv₀.symm (Ext.addEquiv₀ x ≫ fsh)) = Ext.addEquiv₀ x ≫ fsh
      simpa using Ext.addEquiv₀.apply_symm_apply (Ext.addEquiv₀ x ≫ fsh)
  erw [Adjunction.homAddEquiv_apply, Adjunction.homAddEquiv_apply, key,
    Adjunction.homEquiv_naturality_right, Adjunction.homAddEquiv_apply]
  rfl

set_option maxHeartbeats 800000 in
/-- Presheaf-boundary form of `H¹(X₁)` as the cokernel of top sections: if
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
  let F₁sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F₁, h₁⟩
  let F₂sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F₂, h₂⟩
  let F₃sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F₃, h₃⟩
  let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) := ShortComplex.mk
    (X₁ := F₁sh)
    (X₂ := F₂sh)
    (X₃ := F₃sh)
    (Sheaf.Hom.mk f)
    (Sheaf.Hom.mk g)
    (by
      apply Sheaf.Hom.ext
      simpa using hfg)
  have hS' : S.ShortExact := by
    simpa [S, F₁sh, F₂sh, F₃sh] using hS
  change cokernel (S.g.val.app (op ⊤)) ≅ AddCommGrpCat.of (Sheaf.H S.X₁ 1)
  let δ : S.X₃.val.obj (op ⊤) ⟶ AddCommGrpCat.of (Sheaf.H S.X₁ 1) :=
    AddCommGrpCat.ofHom <|
      AddMonoidHom.mk'
        (fun t => ((sheafH0EquivSections_presheaf h₃).symm t).comp hS'.extClass rfl)
        (by
          intro a b
          change
            (((sheafH0EquivSections_presheaf h₃).symm (a + b)).comp hS'.extClass rfl) =
              (((sheafH0EquivSections_presheaf h₃).symm a).comp hS'.extClass rfl) +
                (((sheafH0EquivSections_presheaf h₃).symm b).comp hS'.extClass rfl)
          rw [map_add, Ext.add_comp])
  have hδ : S.g.val.app (op ⊤) ≫ δ = 0 := by
    ext s
    let y : Sheaf.H S.X₂ 0 :=
      (sheafH0EquivSections_presheaf h₂).symm s
    have hy :
        y.comp (Ext.mk₀ S.g) (add_zero 0) =
          (sheafH0EquivSections_presheaf h₃).symm
            (ConcreteCategory.hom (S.g.val.app (op ⊤)) s) := by
      apply (sheafH0EquivSections_presheaf h₃).injective
      rw [sheafH0EquivSections_presheaf_natural, AddEquiv.apply_symm_apply]
      exact (AddEquiv.apply_symm_apply (sheafH0EquivSections_presheaf h₃)
        (ConcreteCategory.hom (S.g.val.app (op ⊤)) s)).symm
    change (((sheafH0EquivSections_presheaf h₃).symm
        (ConcreteCategory.hom (S.g.val.app (op ⊤)) s)).comp hS'.extClass rfl) = 0
    rw [← hy, Ext.comp_assoc_of_second_deg_zero _ (Ext.mk₀ S.g) hS'.extClass rfl,
      hS'.comp_extClass, Ext.comp_zero _ _ 1 1 rfl]
  let πH : cokernel (S.g.val.app (op ⊤)) ⟶ AddCommGrpCat.of (Sheaf.H S.X₁ 1) :=
    cokernel.desc _ δ hδ
  have hπH_epi : Epi πH := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro x
    obtain ⟨y, hy⟩ := sheafH_exists_preimage_extClass_presheaf
      h₁ h₂ h₃ hfg hS 0 h₂H x
    have hy' : y.comp hS'.extClass rfl = x := by
      simpa [S, F₁sh, F₂sh, F₃sh] using hy
    refine ⟨ConcreteCategory.hom (cokernel.π (S.g.val.app (op ⊤)))
      (sheafH0EquivSections_presheaf h₃ y), ?_⟩
    simpa [πH, δ] using hy'
  have hπH_mono : Mono πH := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro a b hab
    obtain ⟨sa, hsa⟩ := (AddCommGrpCat.epi_iff_surjective
      (cokernel.π (S.g.val.app (op ⊤)))).mp inferInstance a
    obtain ⟨sb, hsb⟩ := (AddCommGrpCat.epi_iff_surjective
      (cokernel.π (S.g.val.app (op ⊤)))).mp inferInstance b
    rw [← hsa, ← hsb] at hab ⊢
    have hab' :
        (((sheafH0EquivSections_presheaf h₃).symm sa).comp hS'.extClass rfl) =
          (((sheafH0EquivSections_presheaf h₃).symm sb).comp hS'.extClass rfl) := by
      simpa [πH, δ] using hab
    have hzero :
        ((((sheafH0EquivSections_presheaf h₃).symm (sa - sb)).comp hS'.extClass rfl) :
            Sheaf.H S.X₁ 1) = 0 := by
      have hsub :
          ((((sheafH0EquivSections_presheaf h₃).symm sa).comp hS'.extClass rfl) -
              (((sheafH0EquivSections_presheaf h₃).symm sb).comp hS'.extClass rfl)) = 0 := by
        rw [sub_eq_zero]
        exact hab'
      rw [map_sub, sub_eq_add_neg, Ext.add_comp, Ext.neg_comp]
      simpa [sub_eq_add_neg] using hsub
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ _ hS'
      ((sheafH0EquivSections_presheaf h₃).symm (sa - sb)) rfl hzero
    have hy_sec :
        ConcreteCategory.hom (S.g.val.app (op ⊤))
            (sheafH0EquivSections_presheaf h₂ y) =
          sa - sb := by
      exact (sheafH0EquivSections_presheaf_natural h₂ h₃ (f := g) (x := y)).symm.trans <|
        by
          simpa using congrArg (sheafH0EquivSections_presheaf h₃) hy
    change ConcreteCategory.hom (cokernel.π (S.g.val.app (op ⊤))) sa =
      ConcreteCategory.hom (cokernel.π (S.g.val.app (op ⊤))) sb
    rw [← sub_eq_zero]
    have hq :
        ConcreteCategory.hom (cokernel.π (S.g.val.app (op ⊤))) (sa - sb) = 0 := by
      rw [← hy_sec]
      change ConcreteCategory.hom
        (S.g.val.app (op ⊤) ≫ cokernel.π (S.g.val.app (op ⊤)))
        (sheafH0EquivSections_presheaf h₂ y) = 0
      rw [cokernel.condition]
      simp
    simpa [map_sub] using hq
  haveI : IsIso πH := isIso_of_mono_of_epi πH
  exact asIso πH

@[simp] theorem sheafH1_cokernel_iso_of_subsingleton_middle_presheaf_hom_π {X : TopCat.{u}}
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
    (h₂H : Subsingleton (Sheaf.H ((⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) 1))
    (s : F₃.obj (op ⊤)) :
    ConcreteCategory.hom
        ((sheafH1_cokernel_iso_of_subsingleton_middle_presheaf h₁ h₂ h₃ hfg hS h₂H).hom)
        (ConcreteCategory.hom (cokernel.π (g.app (op ⊤))) s) =
      ((sheafH0EquivSections_presheaf h₃).symm s).comp hS.extClass rfl := by
  simp [sheafH1_cokernel_iso_of_subsingleton_middle_presheaf]

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
  let y : Sheaf.H S.X₃ 0 := (sheafH0EquivSections_presheaf h₃).symm r
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ _ hS y rfl
    (@Subsingleton.elim _ h₁' _ _)
  refine ⟨sheafH0EquivSections_presheaf h₂ z, ?_⟩
  rw [← sheafH0EquivSections_presheaf_natural h₂ h₃ (f := g), hz]
  simp [y]

/-- Presheaf-boundary `H⁰`-surjectivity from surjective top sections:
    if `f.app (op ⊤)` is surjective on sections, then every `H⁰` class of the target
    lifts along the bundled sheaf morphism `Sheaf.Hom.mk f`. -/
theorem sheafH0_surj_of_epi_app_top_presheaf {X : TopCat.{u}}
    {F G : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf) (hG : G.IsSheaf)
    (f : F ⟶ G) (hf : Epi (f.app (op ⊤))) :
    ∀ y : Sheaf.H ((⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) 0,
      ∃ z : Sheaf.H ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) 0,
        z.comp (Ext.mk₀ (Sheaf.Hom.mk f)) (add_zero 0) = y := by
  intro y
  obtain ⟨s, hs⟩ := (AddCommGrpCat.epi_iff_surjective _).mp hf
    (sheafH0EquivSections_presheaf hG y)
  refine ⟨(sheafH0EquivSections_presheaf hF).symm s, ?_⟩
  apply (sheafH0EquivSections_presheaf hG).injective
  rw [sheafH0EquivSections_presheaf_natural hF hG (f := f), AddEquiv.apply_symm_apply, hs]

/-- Internal helper for `H^1` vanishing via degree-zero surjectivity. -/
private theorem subsingleton_H1_via_surj {C' : Type*} [Category C'] [Abelian C'] [HasExt C']
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

/-- Presheaf-boundary `H¹` vanishing via `H⁰`-surjectivity: if `H¹(X₂)=0` and every
    `H⁰` class on `X₃` lifts along `g`, then `H¹(X₁)=0`. -/
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

/-- Positive-degree cohomology of an injective sheaf is subsingleton. -/
theorem sheafH_subsingleton_of_injective
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (I : Sheaf J AddCommGrpCat.{w}) [Injective I] (n : ℕ) :
    Subsingleton (Sheaf.H I (n + 1)) := by
  simpa [Sheaf.H] using
    (Ext.subsingleton_of_injective
      ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))) I n)

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
  have h₃H' : Subsingleton (Sheaf.H S.X₃ n) := by
    simpa [S] using h₃H
  have h₂H' : Subsingleton (Sheaf.H S.X₂ (n + 1)) := by
    simpa [S] using h₂H
  simpa [S] using ext_dimension_shift _ hS' n h₃H' h₂H'

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
  simpa [S, fsh] using
    (sheafH_dimension_shift_of_both_presheaf
      (F₁ := S.X₁.val) (F₂ := S.X₂.val) (F₃ := S.X₃.val)
      S.X₁.cond S.X₂.cond S.X₃.cond
      (f := S.f.val) (g := S.g.val)
      (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
      (by simpa [S] using hS)
      n
      (by simpa [S, fsh] using h₃)
      (by simpa [S] using h₂))

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
  have h₃H' : Subsingleton (Sheaf.H S.X₃ n) := by
    simpa [S] using h₃H
  simpa [S] using
    ext_dimension_shift _ hS' n h₃H' (Ext.subsingleton_of_injective _ _ n)

/-- Presheaf-boundary reverse dimension shift with injective middle term:
    if `0 → F₁ → F₂ → F₃ → 0` is short exact after bundling the presheaves as sheaves,
    `⟨F₂, h₂⟩` is injective, and `H^(n+2)(F₁)=0`, then `H^(n+1)(F₃)=0`.
    Requires degree at least `1`, since `Ext^0(Z, I)` need not vanish for injective `I`. -/
theorem sheafH_dimension_shift_X₃_presheaf {X : TopCat.{u}}
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
    (h₁H : Subsingleton (Sheaf.H ((⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) (n + 2))) :
    Subsingleton (Sheaf.H ((⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) (n + 1)) := by
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
  have h₁H' : Subsingleton (Sheaf.H S.X₁ (n + 2)) := by
    simpa [S] using h₁H
  simpa [S] using
    ext_dimension_shift_X₃ _ hS' (n + 1) (Ext.subsingleton_of_injective _ _ n) h₁H'

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
  have h₂H' : Subsingleton (Sheaf.H S.X₂ n) := by
    simpa [S] using h₂H
  have h₁H' : Subsingleton (Sheaf.H S.X₁ (n + 1)) := by
    simpa [S] using h₁H
  simpa [S] using ext_dimension_shift_X₃ _ hS' n h₂H' h₁H'

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
  simpa [S, fsh] using
    (sheafH_dimension_shift_X₃_of_both_presheaf
      (F₁ := S.X₁.val) (F₂ := S.X₂.val) (F₃ := S.X₃.val)
      S.X₁.cond S.X₂.cond S.X₃.cond
      (f := S.f.val) (g := S.g.val)
      (show S.f.val ≫ S.g.val = 0 from congrArg Sheaf.Hom.val S.zero)
      (by simpa [S] using hS)
      n
      (by simpa [S, fsh] using h₂)
      (by simpa [S, fsh] using h₁))

/-- If `X` is empty and `F` is a sheaf-valued presheaf, then the cohomology of the bundled
sheaf `⟨F, hF⟩` is subsingleton in every degree. -/
theorem sheafH_subsingleton_of_isEmpty_presheaf {X : TopCat.{u}} [IsEmpty X]
    {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf) (n : ℕ) :
    Subsingleton (Sheaf.H ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n) := by
  have hzero : IsZero ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) :=
    sheaf_isZero_of_zero_stalks X hF (fun x _ => (IsEmpty.false x).elim)
  exact sheafH_subsingleton_of_isZero_presheaf hF hzero n

/-- On an empty space, all sheaf cohomology groups are subsingleton.
    Proof: when X is empty, all stalks are vacuously zero, so the sheaf is zero,
    and zero sheaves have subsingleton cohomology in all degrees. -/
instance sheafH_subsingleton_of_isEmpty {X : TopCat.{u}} [IsEmpty X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Subsingleton (Sheaf.H F n) := by
  simpa using
    (sheafH_subsingleton_of_isEmpty_presheaf (F := F.val) (hF := F.cond) (n := n))

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

-- If both ends of a short exact sequence have vanishing H^n, so does the middle.
/-- Presheaf-boundary middle-term cohomology vanishing: if `f : F ⟶ G` is mono between
sheaf-valued presheaves, and the cohomology of `F` and of the cokernel sheaf of
`Sheaf.Hom.mk f` are subsingleton in degree `n`, then so is the cohomology of `G`. -/
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
  constructor
  intro a b
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₂ _ hS a
    (@Subsingleton.elim _ ((add_zero n) ▸ h₃') _ _)
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₂ _ hS b
    (@Subsingleton.elim _ ((add_zero n) ▸ h₃') _ _)
  rw [← hc, ← hd, @Subsingleton.elim _ h₁' c d]

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
  apply (cancel_epi (cokernel.π (g₁.app (op ⊤)))).mp
  rw [cokernel.π_desc_assoc, Category.assoc]
  ext s
  have hs :
      (((sheafH0EquivSections_presheaf h₁₃).symm s).comp
          (Ext.mk₀ (Sheaf.Hom.mk τ₃)) (add_zero 0)) =
        (sheafH0EquivSections_presheaf h₂₃).symm
          (ConcreteCategory.hom (τ₃.app (op ⊤)) s) := by
    apply (sheafH0EquivSections_presheaf h₂₃).injective
    rw [sheafH0EquivSections_presheaf_natural, AddEquiv.apply_symm_apply]
    exact (AddEquiv.apply_symm_apply (sheafH0EquivSections_presheaf h₂₃)
      (ConcreteCategory.hom (τ₃.app (op ⊤)) s)).symm
  change ConcreteCategory.hom
      (cokernel.π (g₂.app (op ⊤)) ≫
        (sheafH1_cokernel_iso_of_subsingleton_middle_presheaf
          h₂₁ h₂₂ h₂₃ hfg₂ hS₂ h₂₂H).hom)
      (ConcreteCategory.hom (τ₃.app (op ⊤)) s) =
    ConcreteCategory.hom
      ((sheafH1_cokernel_iso_of_subsingleton_middle_presheaf
          h₁₁ h₁₂ h₁₃ hfg₁ hS₁ h₁₂H).hom ≫
        (sheafCohomologyFunctor X 1).map (Sheaf.Hom.mk τ₁))
      (ConcreteCategory.hom (cokernel.π (g₁.app (op ⊤))) s)
  simp only [ConcreteCategory.comp_apply]
  rw [sheafH1_cokernel_iso_of_subsingleton_middle_presheaf_hom_π,
    sheafH1_cokernel_iso_of_subsingleton_middle_presheaf_hom_π]
  change (((sheafH0EquivSections_presheaf h₂₃).symm
        (ConcreteCategory.hom (τ₃.app (op ⊤)) s)).comp hS₂.extClass rfl) =
      ((((sheafH0EquivSections_presheaf h₁₃).symm s).comp hS₁.extClass rfl).comp
        (Ext.mk₀ (Sheaf.Hom.mk τ₁)) (add_zero 1))
  rw [← hs]
  simpa using
    (sheafH_comp_extClass_naturality_presheaf
      h₁₁ h₁₂ h₁₃ h₂₁ h₂₂ h₂₃ hfg₁ hfg₂ hS₁ hS₂ hτ₁₂ hτ₂₃ 0
      ((sheafH0EquivSections_presheaf h₁₃).symm s)).symm

/-- The degree-`0` sheaf cohomology functor is naturally isomorphic to taking sections on `⊤`. -/
noncomputable def sheafH0NatIsoSections {X : TopCat.{u}} :
    sheafCohomologyFunctor X 0 ≅
      sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤) :=
  NatIso.ofComponents (fun F => (sheafH0EquivSections_presheaf F.cond).toAddCommGrpIso)
    fun {F G} f => by
    ext x
    simpa [sheafCohomologyFunctor_map_apply] using
      (sheafH0EquivSections_presheaf_natural
        (F := F.val) (G := G.val) F.cond G.cond (f := f.val) (x := x))

@[simp] theorem sheafH0NatIsoSections_hom_app {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (x : Sheaf.H F 0) :
    ConcreteCategory.hom ((sheafH0NatIsoSections (X := X)).hom.app F) x =
      sheafH0EquivSections_presheaf F.cond x := rfl

@[simp] theorem sheafH0NatIsoSections_inv_app {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (x : ToType (F.val.obj (op ⊤))) :
    ConcreteCategory.hom ((sheafH0NatIsoSections (X := X)).inv.app F) x =
      (sheafH0EquivSections_presheaf F.cond).symm x := rfl

/-- Functor-level naturality of the connecting morphism on sheaf cohomology. This is the
    `sheafCohomologyFunctor`-packaged form of
    `sheafH_comp_extClass_naturality_presheaf`. -/
theorem sheafCohomologyFunctor_map_extClass_naturality_presheaf {X : TopCat.{u}}
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
    (y : Sheaf.H ((⟨F₁₃, h₁₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n) :
    ConcreteCategory.hom
        ((sheafCohomologyFunctor X (n + 1)).map (Sheaf.Hom.mk τ₁))
      (y.comp hS₁.extClass rfl) =
    (ConcreteCategory.hom ((sheafCohomologyFunctor X n).map (Sheaf.Hom.mk τ₃)) y).comp
      hS₂.extClass rfl := by
  rw [sheafCohomologyFunctor_map_apply, sheafCohomologyFunctor_map_apply]
  exact sheafH_comp_extClass_naturality_presheaf
    h₁₁ h₁₂ h₁₃ h₂₁ h₂₂ h₂₃ hfg₁ hfg₂ hS₁ hS₂ hτ₁₂ hτ₂₃ n y

/-- If `y` maps to `z` on the `X₃` side of a morphism of short exact sequences, then the
    corresponding extension class of `y` maps to the extension class of `z` on the `X₁`
    side. This packages `sheafCohomologyFunctor_map_extClass_naturality_presheaf` with the
    downstream rewrite by the known `X₃`-side equality. -/
theorem sheafCohomologyFunctor_map_extClass_of_map_eq_presheaf {X : TopCat.{u}}
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
    {y : Sheaf.H ((⟨F₁₃, h₁₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n}
    {z : Sheaf.H ((⟨F₂₃, h₂₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n}
    (hy : ConcreteCategory.hom ((sheafCohomologyFunctor X n).map (Sheaf.Hom.mk τ₃)) y = z) :
    ConcreteCategory.hom ((sheafCohomologyFunctor X (n + 1)).map (Sheaf.Hom.mk τ₁))
      (y.comp hS₁.extClass rfl) =
    z.comp hS₂.extClass rfl := by
  rw [sheafCohomologyFunctor_map_extClass_naturality_presheaf
    h₁₁ h₁₂ h₁₃ h₂₁ h₂₂ h₂₃ hfg₁ hfg₂ hS₁ hS₂ hτ₁₂ hτ₂₃ n y, hy]

/-- Presheaf-boundary form of the higher-degree connecting additive equivalence: if
`0 → F₁ → F₂ → F₃ → 0` is short exact after bundling the presheaves as sheaves and the
middle cohomology groups in degrees `n` and `n + 1` are subsingleton, then the connecting
morphism induces an additive equivalence `H^n(F₃) ≃+ H^(n+1)(F₁)`. -/
noncomputable def sheafH_extClassAddEquiv_of_subsingleton_middle_presheaf {X : TopCat.{u}}
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
    Sheaf.H ((⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n ≃+
      Sheaf.H ((⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) (n + 1) := by
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
  simpa [S] using extClass_postcompAddEquiv_of_subsingleton_middle _ hS' n h₂n' h₂succ'

@[simp] theorem sheafH_extClassAddEquiv_of_subsingleton_middle_presheaf_apply
    {X : TopCat.{u}} {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}
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
    (h₂succ : Subsingleton (Sheaf.H ((⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) (n + 1)))
    (y : Sheaf.H ((⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n) :
    sheafH_extClassAddEquiv_of_subsingleton_middle_presheaf
        h₁ h₂ h₃ hfg hS n h₂n h₂succ y =
      y.comp hS.extClass rfl := by
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
  change (extClass_postcompAddEquiv_of_subsingleton_middle _ hS' n h₂n' h₂succ') y =
      y.comp hS.extClass rfl
  have hh : hS' = hS := by
    apply Subsingleton.elim
  subst hh
  rfl

/-- Presheaf-boundary form of the higher-degree connecting isomorphism: if
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
      AddCommGrpCat.of (Sheaf.H ((⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) (n + 1)) :=
  (sheafH_extClassAddEquiv_of_subsingleton_middle_presheaf
    h₁ h₂ h₃ hfg hS n h₂n h₂succ).toAddCommGrpIso

@[simp] theorem sheafH_extClassIso_of_subsingleton_middle_presheaf_hom_apply {X : TopCat.{u}}
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
    (h₂succ : Subsingleton (Sheaf.H ((⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) (n + 1)))
    (y : Sheaf.H ((⟨F₃, h₃⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n) :
    ConcreteCategory.hom
        ((sheafH_extClassIso_of_subsingleton_middle_presheaf
            h₁ h₂ h₃ hfg hS n h₂n h₂succ).hom) y =
      y.comp hS.extClass rfl := by
  change sheafH_extClassAddEquiv_of_subsingleton_middle_presheaf
      h₁ h₂ h₃ hfg hS n h₂n h₂succ y = y.comp hS.extClass rfl
  exact sheafH_extClassAddEquiv_of_subsingleton_middle_presheaf_apply
    h₁ h₂ h₃ hfg hS n h₂n h₂succ y

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
  ext y
  simpa [ConcreteCategory.comp_apply,
    sheafH_extClassIso_of_subsingleton_middle_presheaf_hom_apply] using
    (sheafCohomologyFunctor_map_extClass_naturality_presheaf
      h₁₁ h₁₂ h₁₃ h₂₁ h₂₂ h₂₃ hfg₁ hfg₂ hS₁ hS₂ hτ₁₂ hτ₂₃ n y)
