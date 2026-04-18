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
* `sheafH0EquivSections`: H^0(F) ≃+ F(⊤)
* `sheafH0EquivSections_natural`: naturality of the above
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

/-! ## H⁰ ≅ Sections -/

/-- `H F 0` is equivalent to sections on `⊤`. -/
noncomputable def sheafH0EquivSections {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Sheaf.H F 0 ≃+ F.val.obj (op ⊤) := by
  refine AddEquiv.trans Ext.addEquiv₀ ?_
  refine AddEquiv.trans ?_ (TopCat.Sheaf.AddCommGrpCat.uliftZMultiplesAddEquiv _)
  exact (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat Limits.isTerminalTop).homAddEquiv _ F

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
  Ext.subsingleton_of_isZero_tgt
    (sheaf_isZero_of_zero_stalks X F (fun x _ => (IsEmpty.false x).elim)) n
