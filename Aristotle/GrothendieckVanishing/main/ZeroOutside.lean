import Mathlib

universe u

open CategoryTheory TopologicalSpace Limits Opposite

noncomputable section

namespace TopCat

namespace Sheaf

theorem AddCommGrpCat.uliftZMultiplesHom_add (G : Type u) [AddCommGroup G] (x y : G) :
    (uliftZMultiplesHom G) (x + y) = ((uliftZMultiplesHom G) x) + ((uliftZMultiplesHom G) y) := by
  ext
  simp_all only [uliftZMultiplesHom_apply_apply, smul_add, AddMonoidHom.add_apply]

/-- The additive equivalence `(ULift ℤ ⟶ G) ≃+ G`. -/
def AddCommGrpCat.uliftZMultiplesAddEquiv (G : AddCommGrpCat.{u}) :
    (AddCommGrpCat.of (ULift ℤ) ⟶ G) ≃+ G := by
  exact AddEquiv.trans
    (@AddCommGrpCat.homAddEquiv (AddCommGrpCat.of (ULift ℤ)) G)
    (AddEquiv.mk' (uliftZMultiplesHom G) (AddCommGrpCat.uliftZMultiplesHom_add G)).symm

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
  intro W
  by_cases hWV : (unop W) ≤ V
  · have : unop W ≤ U := le_trans hWV h
    simp [zeroOutside_openHom, hWV, this, IsIso.mono_of_iso]
  · simp [zeroOutside_openHom, hWV, zeroOutside_isZero (F := F) hWV, IsZero.mono, isZero_zero C]

end

open AddCommGrpCat

abbrev constZ {X : TopCat.{u}} : Presheaf AddCommGrpCat.{u} X :=
  (Functor.const _).obj (AddCommGrpCat.of (ULift ℤ))

namespace zeroOutside

variable {X : TopCat.{u}} (U : Opens X)

@[simp] theorem hom_eqToHom_symm_hom_eqToHom {A B : AddCommGrpCat.{u}} (e : A = B) (x : A) :
    (AddCommGrpCat.Hom.hom (eqToHom e.symm)) ((AddCommGrpCat.Hom.hom (eqToHom e)) x) = x := by
  cases e
  rfl

@[simp] theorem hom_eqToHom_hom_eqToHom_symm {A B : AddCommGrpCat.{u}} (e : A = B) (x : B) :
    (AddCommGrpCat.Hom.hom (eqToHom e)) ((AddCommGrpCat.Hom.hom (eqToHom e.symm)) x) = x := by
  cases e
  rfl

@[simp] theorem hom_eqToHom_hom_eqToHom {A B C : AddCommGrpCat.{u}}
    (e₁ : A = B) (e₂ : B = C) (x : A) :
    (AddCommGrpCat.Hom.hom (eqToHom e₂)) ((AddCommGrpCat.Hom.hom (eqToHom e₁)) x) =
      (AddCommGrpCat.Hom.hom (eqToHom (e₁.trans e₂))) x := by
  cases e₁
  cases e₂
  rfl

@[simp] theorem uliftZMultiplesAddEquiv_symm_apply (G : AddCommGrpCat.{u}) (x : G) (n : ULift ℤ) :
    AddCommGrpCat.Hom.hom ((TopCat.Sheaf.AddCommGrpCat.uliftZMultiplesAddEquiv G).symm x) n =
      (n.down : ℤ) • x := by
  change (((zmultiplesHom ↑G) x).comp (AddEquiv.ulift : ULift ℤ ≃+ ℤ).toAddMonoidHom) n =
    (n.down : ℤ) • x
  rfl

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
        (TopCat.Sheaf.AddCommGrpCat.uliftZMultiplesAddEquiv (F.obj W)).symm
          (F.map (homOfLE h).op s)
    else 0
  naturality {W Y} i := by
    by_cases hWU : (unop W) ≤ U
    · have hYU : (unop Y) ≤ U := le_trans (leOfHom i.unop) hWU
      apply AddCommGrpCat.hom_ext
      ext z
      have hi : (homOfLE hWU).op ≫ i = (homOfLE hYU).op := by
        apply Subsingleton.elim
      have hmap :
          F.map (homOfLE hYU).op s = F.map i (F.map (homOfLE hWU).op s) := by
        simpa [FunctorToTypes.map_comp_apply] using
          (congrArg (fun j => F.map j s) hi).symm
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

theorem openHom_generator {V : Opens X} (h : V ≤ U) :
    (zeroOutside_openHom (F := constZ) h).app (op V) (generator V) =
      Presheaf.restrictOpen (F := constZ.zeroOutside U) (generator U) V h := by
  simp [generator, Presheaf.restrictOpen, Presheaf.restrict, ← comp_apply]

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

theorem openHom_generator {X : TopCat.{u}} {V U : Opens X} (h : V ≤ U) :
    (openHom h).val.app (op V) (generator V) =
      Presheaf.restrictOpen (F := (zeroOutsideInt U).presheaf) (generator U) V h := by
  simp only [openHom, generator, Presheaf.zeroOutside_obj, Functor.const_obj_obj]
  erw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, ← toSheafify_naturality,
    NatTrans.comp_app, ConcreteCategory.comp_apply, Presheaf.zeroOutside.openHom_generator,
    Presheaf.map_restrict]
  rfl

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

end zeroOutsideInt

open zeroOutsideInt

theorem epi_map_of_injective {X : TopCat.{u}} (I : Sheaf AddCommGrpCat.{u} X) [Injective I]
    {U V : Opens X} (h : V ≤ U) : Epi (I.presheaf.map (homOfLE h).op) := by
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  let f := Injective.factorThru (zeroOutsideInt.sHom s) (zeroOutsideInt.openHom h)
  refine ⟨f.val.app (op U) (zeroOutsideInt.generator U), ?_⟩
  change Presheaf.restrictOpen (F := I.presheaf)
      (f.val.app (op U) (zeroOutsideInt.generator U)) V h = s
  rw [← Presheaf.map_restrict, ← zeroOutsideInt.openHom_generator]
  change (zeroOutsideInt.openHom h ≫ f).val.app (op V) (zeroOutsideInt.generator V) = s
  rw [Injective.comp_factorThru, zeroOutsideInt.sHom_app_generator]

end Sheaf

end TopCat
