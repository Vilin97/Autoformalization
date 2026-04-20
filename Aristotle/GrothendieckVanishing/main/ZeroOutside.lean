import Mathlib

/-!
  ZeroOutside.lean — Extension-by-zero presheaf and sheaf machinery

  Provides:
  - `zeroOutside`: presheaf that is `F` on opens contained in `U` and zero elsewhere
  - `constZ`: constant presheaf with value `ULift ℤ`
  - `zeroOutsideInt`: sheafified extension-by-zero of `constZ` on an open `U`
  - `sHom`: section-hom from a section `s ∈ F(U)` to a presheaf/sheaf morphism
  - `generator`: canonical generator of `(constZ.zeroOutside U).obj (op U)`
  - `familyGeneratorMap`: coproduct map from a family of `zeroOutsideInt`
-/

universe u

open CategoryTheory TopologicalSpace Limits Opposite

noncomputable section

namespace AddCommGrpCat

theorem uliftZMultiplesHom_add (G : Type u) [AddCommGroup G] (x y : G) :
    (uliftZMultiplesHom G) (x + y) = ((uliftZMultiplesHom G) x) + ((uliftZMultiplesHom G) y) := by
  ext
  simp_all only [uliftZMultiplesHom_apply_apply, smul_add, AddMonoidHom.add_apply]

/-- The additive equivalence `(ULift ℤ ⟶ G) ≃+ G`. -/
def uliftZMultiplesAddEquiv (G : AddCommGrpCat.{u}) :
    (AddCommGrpCat.of (ULift ℤ) ⟶ G) ≃+ G :=
  AddEquiv.trans
    (@AddCommGrpCat.homAddEquiv (AddCommGrpCat.of (ULift ℤ)) G)
    (AddEquiv.mk' (uliftZMultiplesHom G) (uliftZMultiplesHom_add G)).symm

end AddCommGrpCat

namespace TopCat

namespace Sheaf

instance (X : TopCat.{u}) : Abelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (Abelian (CategoryTheory.Sheaf _ _))

end Sheaf

namespace Presheaf

open ZeroObject ConcreteCategory

section

variable {C : Type*} [Category C] [HasZeroObject C] {X : TopCat.{u}}
    (U : Opens X) (F : Presheaf C X)

open Classical in
@[simps]
def zeroOutside : Presheaf C X where
  obj W := if (unop W) ≤ U then F.obj W else 0
  map {W Y} i :=
    if h : (unop W) ≤ U then
      eqToHom (by grind) ≫ F.map i ≫ eqToHom (by rw [if_pos (le_trans (leOfHom i.unop) h)])
    else ((if_neg h).symm.ndrec (isZero_zero C)).to_ _
  map_id W := by
    split_ifs with h
    · simp
    · apply IsZero.to_eq
  map_comp {W Y Z} iWY iYZ := by
    split_ifs with h
    · have : unop Y ≤ U := le_trans (leOfHom iWY.unop) h
      have : unop Z ≤ U := le_trans (leOfHom iYZ.unop) this
      simp_all
    · apply IsZero.to_eq

variable {U F}

lemma zeroOutside_isZero {W : Opens X} (h : ¬ W ≤ U) :
    IsZero ((zeroOutside U F).obj (op W)) := by
  simp [zeroOutside, h, isZero_zero C]

lemma zeroOutside_le {W : Opens X} (h : W ≤ U) :
    (zeroOutside U F).obj (op W) = F.obj (op W) := by
  simp [zeroOutside, h]

/-- `zeroOutside ⊤ F ≅ F`: zero-outside on the whole space is the identity. -/
def zeroOutside_top_iso : zeroOutside (⊤ : Opens X) F ≅ F :=
  NatIso.ofComponents
    (fun W => eqToIso (zeroOutside_le (le_top : unop W ≤ ⊤)))
    (fun {W Y} i => by simp [zeroOutside, le_top])

variable {V : Opens X} (h : V ≤ U)

open Classical in
@[simps]
def zeroOutside_openHom [HasPullbacks C] : zeroOutside V F ⟶ zeroOutside U F where
  app W := if hW : (unop W) ≤ V then
      eqToHom (by rw [zeroOutside_le hW, zeroOutside_le (le_trans hW h)])
    else (zeroOutside_isZero (F := F) hW).to_ _
  naturality {W Y} i := by
    by_cases hWV : (unop W) ≤ V
    · have hYV : unop Y ≤ V := le_trans (leOfHom i.unop) hWV
      have hYU : unop Y ≤ U := le_trans hYV h
      have hWU : unop W ≤ U := le_trans hWV h
      simp [zeroOutside, hWV, hYV, hWU, hYU]
    · apply (zeroOutside_isZero (F := F) hWV).eq_of_src

instance zeroOutside_hom_mono [HasPullbacks C] : Mono (zeroOutside_openHom (F := F) h) := by
  erw [NatTrans.mono_iff_mono_app]
  intro W; by_cases hWV : (unop W) ≤ V
  · have : unop W ≤ U := le_trans hWV h
    simp [zeroOutside_openHom, hWV, this, IsIso.mono_of_iso]
  · simp [zeroOutside_openHom, hWV, zeroOutside_isZero (F := F) hWV, IsZero.mono, isZero_zero C]

end

open AddCommGrpCat

abbrev constZ {X : TopCat.{u}} : Presheaf AddCommGrpCat.{u} X :=
  (Functor.const _).obj (AddCommGrpCat.of (ULift ℤ))

namespace zeroOutside

variable {X : TopCat.{u}} (U : Opens X)

@[simp] theorem uliftZMultiplesAddEquiv_symm_apply (G : AddCommGrpCat.{u}) (x : G) (n : ULift ℤ) :
    AddCommGrpCat.Hom.hom ((AddCommGrpCat.uliftZMultiplesAddEquiv G).symm x) n =
      (n.down : ℤ) • x := rfl

def generator : (constZ.zeroOutside U).obj (op U) :=
  (eqToHom (by simp) : AddCommGrpCat.of (ULift ℤ) ⟶ (constZ.zeroOutside U).obj (op U)) 1

variable {U}

open Classical in
@[simps]
def sHom {F : Presheaf AddCommGrpCat.{u} X} (s : F.obj (op U)) :
    constZ.zeroOutside U ⟶ F where
  app {W} :=
    if h : (unop W) ≤ U then
      eqToHom (by simp_all) ≫
        (AddCommGrpCat.uliftZMultiplesAddEquiv (F.obj W)).symm
          (F.map (homOfLE h).op s)
    else 0
  naturality {W Y} i := by
    by_cases hWU : (unop W) ≤ U
    · have hYU : (unop Y) ≤ U := le_trans (leOfHom i.unop) hWU
      apply AddCommGrpCat.hom_ext
      ext z
      have hmap :
          F.map (homOfLE hYU).op s = F.map i (F.map (homOfLE hWU).op s) := by
        simpa [FunctorToTypes.map_comp_apply] using
          (congrArg (fun j => F.map j s) (Subsingleton.elim ((homOfLE hWU).op ≫ i)
            (homOfLE hYU).op)).symm
      have hObjW : (zeroOutside U constZ).obj W = AddCommGrpCat.of (ULift ℤ) := by
        simp [zeroOutside, hWU, constZ]
      let w : ULift ℤ :=
        (AddCommGrpCat.Hom.hom (eqToHom hObjW) z)
      have hz : (AddCommGrpCat.Hom.hom (eqToHom hObjW.symm)) w = z := by
        simp [w, ← comp_apply, eqToHom_trans]
      rw [← hz]
      simp [zeroOutside, hWU, hYU, w, hmap, constZ]
      rw [uliftZMultiplesAddEquiv_symm_apply, uliftZMultiplesAddEquiv_symm_apply]
      simpa [w, hmap] using
        (map_zsmul (AddCommGrpCat.Hom.hom (F.map i)) w.down (F.map (homOfLE hWU).op s)).symm
    · apply (zeroOutside_isZero (F := constZ) hWU).eq_of_src

theorem sHom_app_generator {F : Presheaf AddCommGrpCat.{u} X} (s : F.obj (op U)) :
    (sHom s).app (op U) (generator U) = s := by
  have hObjU : (zeroOutside U constZ).obj (op U) = AddCommGrpCat.of (ULift ℤ) := by
    simp [zeroOutside, constZ]
  have h1 :
      (AddCommGrpCat.Hom.hom (eqToHom hObjU))
          ((AddCommGrpCat.Hom.hom (eqToHom hObjU.symm)) (1 : ULift ℤ)) = (1 : ULift ℤ) := by
    simp [← comp_apply, eqToHom_trans]
  rw [show generator U =
    (eqToHom hObjU.symm : AddCommGrpCat.of (ULift ℤ) ⟶ (zeroOutside U constZ).obj (op U))
      (1 : ULift ℤ) by
      simp [generator, hObjU]]
  simp [sHom, zeroOutside_obj, zeroOutside, constZ]
  rw [uliftZMultiplesAddEquiv_symm_apply]
  change (((AddCommGrpCat.Hom.hom (eqToHom hObjU))
      ((AddCommGrpCat.Hom.hom (eqToHom hObjU.symm)) (1 : ULift ℤ))).down : ℤ) • s = s
  rw [congrArg ULift.down h1]
  simpa using one_zsmul s

end zeroOutside

end Presheaf

namespace Sheaf

open Presheaf

def zeroOutsideInt {X : TopCat.{u}} (U : Opens X) : Sheaf AddCommGrpCat.{u} X :=
  (presheafToSheaf _ _).obj (Presheaf.constZ.zeroOutside U)

namespace zeroOutsideInt

variable {X : TopCat.{u}} (U : Opens X)

def generator : (zeroOutsideInt U).presheaf.obj (op U) :=
  (toSheafify _ (Presheaf.constZ.zeroOutside U)).app (op U) (Presheaf.zeroOutside.generator U)

variable {U}

@[simps]
def openHom {X : TopCat.{u}} {V U : Opens X} (h : V ≤ U) :
    zeroOutsideInt V ⟶ zeroOutsideInt U where
  val := sheafifyMap _ (Presheaf.zeroOutside_openHom (F := Presheaf.constZ) h)

instance {X : TopCat.{u}} {V U : Opens X} (h : V ≤ U) : Mono (openHom h) := by
  have := Presheaf.zeroOutside_hom_mono
    (F := (Functor.const _).obj (AddCommGrpCat.of (ULift.{u, 0} ℤ))) h
  delta openHom
  apply Functor.map_mono (presheafToSheaf _ _)

@[simps]
def sHom {X : TopCat.{u}} {U : Opens X} {F : Sheaf AddCommGrpCat.{u} X}
    (s : F.presheaf.obj (op U)) : zeroOutsideInt U ⟶ F where
  val := sheafifyLift _ (Presheaf.zeroOutside.sHom s) F.cond

theorem sHom_app_generator {X : TopCat.{u}} {U : Opens X}
    {F : Sheaf AddCommGrpCat.{u} X} (s : F.presheaf.obj (op U)) :
    (sHom s).val.app (op U) (generator U) = s := by
  delta generator
  erw [sHom_val, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app, toSheafify_sheafifyLift]
  exact Presheaf.zeroOutside.sHom_app_generator s

theorem openHom_val_app_generator {X : TopCat.{u}} {V U : Opens X} (h : V ≤ U) :
    (openHom h).val.app (op V) (generator V) =
    (zeroOutsideInt U).val.map (homOfLE h).op (generator U) := by
  delta generator
  erw [openHom_val,
    ← ConcreteCategory.comp_apply
      ((CategoryTheory.toSheafify _ (Presheaf.constZ.zeroOutside V)).app (op V))
      ((CategoryTheory.sheafifyMap _ (Presheaf.zeroOutside_openHom (F := Presheaf.constZ) h)).app
        (op V)),
    ← NatTrans.comp_app (CategoryTheory.toSheafify _ (Presheaf.constZ.zeroOutside V))
      (CategoryTheory.sheafifyMap _ (Presheaf.zeroOutside_openHom (F := Presheaf.constZ) h)),
    ← CategoryTheory.toSheafify_naturality _ (Presheaf.zeroOutside_openHom (F := Presheaf.constZ) h),
    NatTrans.comp_app, ConcreteCategory.comp_apply,
    ← (CategoryTheory.toSheafify _ (Presheaf.constZ.zeroOutside U)).naturality_apply
      (homOfLE h).op (Presheaf.zeroOutside.generator U)]
  congr 1
  simp [Presheaf.zeroOutside.generator, Presheaf.zeroOutside_openHom, h,
    Presheaf.zeroOutside, Presheaf.constZ, ← ConcreteCategory.comp_apply, eqToHom_trans]

end zeroOutsideInt

open zeroOutsideInt

/-- For a family of morphisms into `F`, the universal map from their coproduct into `F`. -/
abbrev familyMap {C : Type*} [Category C] {X : TopCat.{u}} {ι : Type*}
    (G : ι → Sheaf C X) {F : Sheaf C X} (f : ∀ i, G i ⟶ F)
    [HasCoproduct G] :
    (∐ G) ⟶ F :=
  Sigma.desc f

/-- The image subsheaf generated by a family of morphisms into `F`. -/
abbrev familyImage {C : Type*} [Category C] {X : TopCat.{u}} {ι : Type*}
    (G : ι → Sheaf C X) {F : Sheaf C X} (f : ∀ i, G i ⟶ F)
    [HasCoproduct G] [HasImage (familyMap G f)] :
    Sheaf C X :=
  Limits.image (familyMap G f)

/-- The canonical inclusion of the image generated by a family of morphisms into `F`. -/
abbrev familyImageι {C : Type*} [Category C] {X : TopCat.{u}} {ι : Type*}
    (G : ι → Sheaf C X) {F : Sheaf C X} (f : ∀ i, G i ⟶ F)
    [HasCoproduct G] [HasImage (familyMap G f)] :
    familyImage G f ⟶ F :=
  Limits.image.ι (familyMap G f)

theorem familyImage_ι_eq {C : Type*} [Category C] {X : TopCat.{u}} {ι : Type*}
    (G : ι → Sheaf C X) {F : Sheaf C X} (f : ∀ i, G i ⟶ F)
    [HasCoproduct G] [HasImage (familyMap G f)] :
    familyImageι G f = Limits.image.ι (familyMap G f) := rfl

/-- For a family of local sections, the universal map from the coproduct of the corresponding
`zeroOutsideInt (U i)` into `F`. This packages the "generated by a family of sections"
construction used in Hartshorne Step 3. -/
abbrev familyGeneratorMap {X : TopCat.{u}} {ι : Type*}
    (U : ι → Opens X) {F : Sheaf AddCommGrpCat.{u} X}
    (s : ∀ i, F.presheaf.obj (op (U i)))
    [HasCoproduct fun i => zeroOutsideInt (U i)] :
    (∐ fun i => zeroOutsideInt (U i)) ⟶ F :=
  familyMap (fun i => zeroOutsideInt (U i)) (fun i => zeroOutsideInt.sHom (s i))

/-- The subsheaf of `F` generated by a family of local sections. -/
abbrev familyGeneratedSheaf {X : TopCat.{u}} {ι : Type*}
    (U : ι → Opens X) {F : Sheaf AddCommGrpCat.{u} X}
    (s : ∀ i, F.presheaf.obj (op (U i)))
    [HasCoproduct fun i => zeroOutsideInt (U i)] :
    Sheaf AddCommGrpCat.{u} X :=
  Limits.image (familyGeneratorMap U s)

/-- The canonical inclusion of the subsheaf generated by a family of sections into `F`. -/
abbrev familyGeneratedSheafι {X : TopCat.{u}} {ι : Type*}
    (U : ι → Opens X) {F : Sheaf AddCommGrpCat.{u} X}
    (s : ∀ i, F.presheaf.obj (op (U i)))
    [HasCoproduct fun i => zeroOutsideInt (U i)] :
    familyGeneratedSheaf U s ⟶ F :=
  Limits.image.ι (familyGeneratorMap U s)

theorem familyGeneratedSheaf_ι_eq {X : TopCat.{u}} {ι : Type*}
    (U : ι → Opens X) {F : Sheaf AddCommGrpCat.{u} X}
    (s : ∀ i, F.presheaf.obj (op (U i)))
    [HasCoproduct fun i => zeroOutsideInt (U i)] :
    familyGeneratedSheafι U s = Limits.image.ι (familyGeneratorMap U s) := rfl

-- SectionIndex, finsetGeneratedSheaf, and allSectionMap are in ZeroOutsideFinset.lean.

end Sheaf

end TopCat
