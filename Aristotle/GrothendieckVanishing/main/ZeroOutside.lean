import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Images
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Topology.Sheaves.Sheaf

universe u

open CategoryTheory TopologicalSpace Limits Opposite

noncomputable section

namespace TopCat

namespace Sheaf

/-- Category of sheaves of abelian groups on a topological space is abelian. -/
instance (X : TopCat.{u}) : Abelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (Abelian (CategoryTheory.Sheaf _ _))

/-- `uliftZMultiplesHom` preserves addition. -/
theorem AddCommGrpCat.uliftZMultiplesHom_add (G : Type u) [AddCommGroup G] (x y : G) :
    (uliftZMultiplesHom G) (x + y) = ((uliftZMultiplesHom G) x) + ((uliftZMultiplesHom G) y) := by
  ext
  simp_all only [uliftZMultiplesHom_apply_apply, smul_add, AddMonoidHom.add_apply]

/-- The additive equivalence `(ULift ℤ ⟶ G) ≃+ G`. -/
def AddCommGrpCat.uliftZMultiplesAddEquiv (G : AddCommGrpCat.{u}) :
    (AddCommGrpCat.of (ULift ℤ) ⟶ G) ≃+ G :=
  AddEquiv.trans
    (@AddCommGrpCat.homAddEquiv (AddCommGrpCat.of (ULift ℤ)) G)
    (AddEquiv.mk' (uliftZMultiplesHom G) (AddCommGrpCat.uliftZMultiplesHom_add G)).symm

end Sheaf

namespace Presheaf

open ZeroObject ConcreteCategory

section

variable {C : Type*} [Category C] [HasZeroObject C] {X : TopCat.{u}}
    (U : Opens X) (F : Presheaf C X)

open Classical in
/-- The extension-by-zero presheaf: agrees with `F` on opens contained in `U`,
and is zero elsewhere. -/
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

/-- The extension-by-zero presheaf is zero on opens not contained in `U`. -/
lemma zeroOutside_isZero {W : Opens X} (h : ¬ W ≤ U) :
    IsZero ((zeroOutside U F).obj (op W)) := by
  simp [zeroOutside, h, isZero_zero C]

/-- On opens contained in `U`, the extension-by-zero presheaf agrees with `F`. -/
lemma zeroOutside_le {W : Opens X} (h : W ≤ U) :
    (zeroOutside U F).obj (op W) = F.obj (op W) := by
  simp [zeroOutside, h]

variable {V : Opens X} (h : V ≤ U)

open Classical in
/-- The canonical inclusion `zeroOutside V F ⟶ zeroOutside U F` for `V ≤ U`. -/
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

/-- The canonical inclusion `zeroOutside_openHom` is a monomorphism. -/
instance zeroOutside_hom_mono [HasPullbacks C] : Mono (zeroOutside_openHom (F := F) h) := by
  erw [NatTrans.mono_iff_mono_app]
  intro W; by_cases hWV : (unop W) ≤ V
  · have : unop W ≤ U := le_trans hWV h
    simp [zeroOutside_openHom, hWV, this, IsIso.mono_of_iso]
  · simp [zeroOutside_openHom, hWV, zeroOutside_isZero (F := F) hWV, IsZero.mono, isZero_zero C]

end

open AddCommGrpCat

/-- The constant presheaf with value `ULift ℤ`. -/
abbrev constZ {X : TopCat.{u}} : Presheaf AddCommGrpCat.{u} X :=
  (Functor.const _).obj (AddCommGrpCat.of (ULift ℤ))

namespace zeroOutside

variable {X : TopCat.{u}} (U : Opens X)

@[simp] theorem hom_eqToHom_symm_hom_eqToHom {A B : AddCommGrpCat.{u}} (e : A = B) (x : A) :
    (AddCommGrpCat.Hom.hom (eqToHom e.symm)) ((AddCommGrpCat.Hom.hom (eqToHom e)) x) = x := by
  cases e; rfl

@[simp] theorem hom_eqToHom_hom_eqToHom_symm {A B : AddCommGrpCat.{u}} (e : A = B) (x : B) :
    (AddCommGrpCat.Hom.hom (eqToHom e)) ((AddCommGrpCat.Hom.hom (eqToHom e.symm)) x) = x := by
  cases e; rfl

@[simp] theorem hom_eqToHom_hom_eqToHom {A B C : AddCommGrpCat.{u}}
    (e₁ : A = B) (e₂ : B = C) (x : A) :
    (AddCommGrpCat.Hom.hom (eqToHom e₂)) ((AddCommGrpCat.Hom.hom (eqToHom e₁)) x) =
      (AddCommGrpCat.Hom.hom (eqToHom (e₁.trans e₂))) x := by
  cases e₁; cases e₂; rfl

@[simp] theorem uliftZMultiplesAddEquiv_symm_apply (G : AddCommGrpCat.{u}) (x : G) (n : ULift ℤ) :
    AddCommGrpCat.Hom.hom ((TopCat.Sheaf.AddCommGrpCat.uliftZMultiplesAddEquiv G).symm x) n =
      (n.down : ℤ) • x := rfl

/-- The distinguished generator `1 ∈ (constZ.zeroOutside U)(U) ≅ ULift ℤ`. -/
def generator : (constZ.zeroOutside U).obj (op U) :=
  (eqToHom (by simp) : AddCommGrpCat.of (ULift ℤ) ⟶ (constZ.zeroOutside U).obj (op U)) 1

variable {U}

open Classical in
/-- The presheaf morphism `constZ.zeroOutside U ⟶ F` determined by a section `s ∈ F(U)`,
sending the generator to `s` and extending by zero. -/
@[simps]
def sHom {F : Presheaf AddCommGrpCat.{u} X} (s : F.obj (op U)) :
    constZ.zeroOutside U ⟶ F where
  app {W} :=
    if h : (unop W) ≤ U then
      eqToHom (by simp_all) ≫
        (TopCat.Sheaf.AddCommGrpCat.uliftZMultiplesAddEquiv (F.obj W)).symm
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
        simpa [w] using hom_eqToHom_symm_hom_eqToHom (e := hObjW) z
      rw [← hz]
      simp [zeroOutside, hWU, hYU, w, hmap, constZ]
      rw [uliftZMultiplesAddEquiv_symm_apply, uliftZMultiplesAddEquiv_symm_apply]
      simpa [w, hmap] using
        (map_zsmul (AddCommGrpCat.Hom.hom (F.map i)) w.down (F.map (homOfLE hWU).op s)).symm
    · apply (zeroOutside_isZero (F := constZ) hWU).eq_of_src

/-- Evaluating `sHom s` at the generator recovers the section `s`. -/
theorem sHom_app_generator {F : Presheaf AddCommGrpCat.{u} X} (s : F.obj (op U)) :
    (sHom s).app (op U) (generator U) = s := by
  have hObjU : (zeroOutside U constZ).obj (op U) = AddCommGrpCat.of (ULift ℤ) := by
    simp [zeroOutside, constZ]
  have h1 :
      (AddCommGrpCat.Hom.hom (eqToHom hObjU))
          ((AddCommGrpCat.Hom.hom (eqToHom hObjU.symm)) (1 : ULift ℤ)) = (1 : ULift ℤ) := by
    simpa using hom_eqToHom_hom_eqToHom_symm (e := hObjU) (1 : ULift ℤ)
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

/-- The sheafification of `constZ.zeroOutside U`: the extension-by-zero sheaf of `ℤ`
supported on `U`. -/
def zeroOutsideInt {X : TopCat.{u}} (U : Opens X) : Sheaf AddCommGrpCat.{u} X :=
  (presheafToSheaf _ _).obj (Presheaf.constZ.zeroOutside U)

namespace zeroOutsideInt

variable {X : TopCat.{u}} (U : Opens X)

/-- The distinguished generator of the sheaf `zeroOutsideInt U` at the open `U`. -/
def generator : (zeroOutsideInt U).presheaf.obj (op U) :=
  (toSheafify _ (Presheaf.constZ.zeroOutside U)).app (op U) (Presheaf.zeroOutside.generator U)

variable {U}

/-- The canonical monomorphism `zeroOutsideInt V ⟶ zeroOutsideInt U` for `V ≤ U`. -/
@[simps]
def openHom {X : TopCat.{u}} {V U : Opens X} (h : V ≤ U) :
    zeroOutsideInt V ⟶ zeroOutsideInt U where
  val := sheafifyMap _ (Presheaf.zeroOutside_openHom (F := Presheaf.constZ) h)

/-- `openHom h` is a monomorphism. -/
instance {X : TopCat.{u}} {V U : Opens X} (h : V ≤ U) : Mono (openHom h) := by
  have := Presheaf.zeroOutside_hom_mono
    (F := (Functor.const _).obj (AddCommGrpCat.of (ULift.{u, 0} ℤ))) h
  delta openHom
  apply Functor.map_mono (presheafToSheaf _ _)

/-- The sheaf morphism `zeroOutsideInt U ⟶ F` determined by a section `s ∈ F(U)`. -/
@[simps]
def sHom {X : TopCat.{u}} {U : Opens X} {F : Sheaf AddCommGrpCat.{u} X}
    (s : F.presheaf.obj (op U)) : zeroOutsideInt U ⟶ F where
  val := sheafifyLift _ (Presheaf.zeroOutside.sHom s) F.cond

/-- Evaluating `sHom s` at the generator recovers the section `s`. -/
theorem sHom_app_generator {X : TopCat.{u}} {U : Opens X}
    {F : Sheaf AddCommGrpCat.{u} X} (s : F.presheaf.obj (op U)) :
    (sHom s).val.app (op U) (generator U) = s := by
  delta generator
  erw [sHom_val, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app, toSheafify_sheafifyLift]
  exact Presheaf.zeroOutside.sHom_app_generator s

end zeroOutsideInt

open zeroOutsideInt

/-- For a family of local sections, the universal map from the coproduct of the corresponding
`zeroOutsideInt (U i)` into `F`. This packages the "generated by a family of sections"
construction used in Hartshorne Step 3. -/
abbrev familyGeneratorMap {X : TopCat.{u}} {ι : Type*}
    (U : ι → Opens X) {F : Sheaf AddCommGrpCat.{u} X}
    (s : ∀ i, F.presheaf.obj (op (U i)))
    [HasCoproduct fun i => zeroOutsideInt (U i)] :
    (∐ fun i => zeroOutsideInt (U i)) ⟶ F :=
  Sigma.desc fun i => zeroOutsideInt.sHom (s i)

/-- The factor-through-image of `familyGeneratorMap` is always epi. -/
instance familyGeneratorMap_epi_to_image {X : TopCat.{u}} {ι : Type*}
    (U : ι → Opens X) {F : Sheaf AddCommGrpCat.{u} X}
    (s : ∀ i, F.presheaf.obj (op (U i)))
    [HasCoproduct fun i => zeroOutsideInt (U i)] :
    Epi (factorThruImage (familyGeneratorMap U s)) :=
  inferInstance

-- SectionIndex, finsetGeneratedSheaf, and allSectionMap are in ZeroOutsideFinset.lean.

end Sheaf

end TopCat
