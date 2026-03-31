import Mathlib

universe u

open CategoryTheory TopologicalSpace Limits Opposite

noncomputable section

namespace TopCat

namespace Sheaf

instance (X : TopCat.{u}) : Abelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (Abelian (CategoryTheory.Sheaf _ _))

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

/-- A morphism out of `constZ.zeroOutside U` is determined by the image of the
distinguished generator over `U`. -/
theorem sHom_eq_of_app_generator {F : Presheaf AddCommGrpCat.{u} X}
    (f : constZ.zeroOutside U ⟶ F) :
    sHom (f.app (op U) (generator U)) = f := by
  apply NatTrans.ext
  funext W
  ext x
  by_cases hW : unop W ≤ U
  · let gW : (constZ.zeroOutside U).obj W :=
      Presheaf.restrictOpen (F := constZ.zeroOutside U) (generator U) (unop W) hW
    have hObjW : (zeroOutside U constZ).obj W = AddCommGrpCat.of (ULift ℤ) := by
      simp [zeroOutside, hW, constZ]
    let w : ULift ℤ := (AddCommGrpCat.Hom.hom (eqToHom hObjW) x)
    have hObjW₀ : (zeroOutside (unop W) constZ).obj W = AddCommGrpCat.of (ULift ℤ) := by
      simp [zeroOutside, constZ]
    have hmid : (zeroOutside (unop W) constZ).obj W = (zeroOutside U constZ).obj W := by
      rw [hObjW₀, hObjW]
    have hcollapse :
        (AddCommGrpCat.Hom.hom (eqToHom hmid))
            ((AddCommGrpCat.Hom.hom (eqToHom hObjW₀.symm)) (1 : ULift ℤ)) =
          (AddCommGrpCat.Hom.hom (eqToHom hObjW.symm)) (1 : ULift ℤ) := by
      have hcollapse' :
          (AddCommGrpCat.Hom.hom (eqToHom hmid))
              ((AddCommGrpCat.Hom.hom (eqToHom hObjW₀.symm)) (1 : ULift ℤ)) =
            (AddCommGrpCat.Hom.hom (eqToHom (hObjW₀.symm.trans hmid))) (1 : ULift ℤ) := by
        simpa using hom_eqToHom_hom_eqToHom hObjW₀.symm hmid (1 : ULift ℤ)
      have hsingle : hObjW₀.symm.trans hmid = hObjW.symm := by
        apply Subsingleton.elim
      simpa [hsingle] using hcollapse'
    have hgW_transport :
        gW = (eqToHom hObjW.symm :
          AddCommGrpCat.of (ULift ℤ) ⟶ (zeroOutside U constZ).obj W) (1 : ULift ℤ) := by
      calc
        gW = (zeroOutside_openHom (F := constZ) hW).app (op (unop W)) (generator (unop W)) := by
          simpa [gW] using (openHom_generator (U := U) (V := unop W) hW).symm
        _ = (eqToHom hObjW.symm :
            AddCommGrpCat.of (ULift ℤ) ⟶ (zeroOutside U constZ).obj W) (1 : ULift ℤ) := by
          simpa [generator, zeroOutside_openHom, zeroOutside, constZ, hW, hObjW₀, hmid] using
            hcollapse
    have hgW :
        (AddCommGrpCat.Hom.hom (eqToHom hObjW.symm)) (1 : ULift ℤ) = gW := by
      exact hgW_transport.symm
    have hw : w = (w.down : ℤ) • (1 : ULift ℤ) := by
      ext
      simp [w]
    have hx : x = (w.down : ℤ) • gW := by
      calc
        x = (AddCommGrpCat.Hom.hom (eqToHom hObjW.symm)) w := by
              simpa [w] using (hom_eqToHom_symm_hom_eqToHom (e := hObjW) x).symm
        _ = (w.down : ℤ) • (AddCommGrpCat.Hom.hom (eqToHom hObjW.symm)) (1 : ULift ℤ) := by
              rw [hw]
              simpa using
                (map_zsmul (AddCommGrpCat.Hom.hom (eqToHom hObjW.symm)) w.down (1 : ULift ℤ))
        _ = (w.down : ℤ) • gW := by rw [hgW]
    have hs_restrict :
        (sHom (f.app (op U) (generator U))).app W gW =
          F.map (homOfLE hW).op (f.app (op U) (generator U)) := by
      have hs_nat := congrArg (fun g => g (generator U))
        (NatTrans.naturality (sHom (f.app (op U) (generator U))) (homOfLE hW).op)
      have hs_nat' :
          (sHom (f.app (op U) (generator U))).app W gW =
            F.map (homOfLE hW).op
              ((sHom (f.app (op U) (generator U))).app (op U) (generator U)) := by
        simpa [gW, Presheaf.restrictOpen, Presheaf.restrict] using hs_nat
      rw [sHom_app_generator] at hs_nat'
      exact hs_nat'
    have hf_restrict :
        f.app W gW = F.map (homOfLE hW).op (f.app (op U) (generator U)) := by
      simpa [gW, Presheaf.restrictOpen, Presheaf.restrict] using
        (congrArg (fun g => g (generator U))
          (NatTrans.naturality f (homOfLE hW).op))
    calc
      (sHom (f.app (op U) (generator U))).app W x
          = (sHom (f.app (op U) (generator U))).app W ((w.down : ℤ) • gW) := by rw [hx]
      _ = (w.down : ℤ) • (sHom (f.app (op U) (generator U))).app W gW := by simp
      _ = (w.down : ℤ) • F.map (homOfLE hW).op (f.app (op U) (generator U)) := by
            rw [hs_restrict]
      _ = (w.down : ℤ) • f.app W gW := by rw [hf_restrict]
      _ = f.app W ((w.down : ℤ) • gW) := by simp
      _ = f.app W x := by rw [hx]
  · have hs : (sHom (f.app (op U) (generator U))).app W = 0 :=
        (zeroOutside_isZero (F := constZ) hW).eq_of_src _ _
    have hf : f.app W = 0 := (zeroOutside_isZero (F := constZ) hW).eq_of_src _ _
    rw [hs, hf]

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

/-- A morphism out of `zeroOutsideInt U` is determined by the image of the
distinguished generator over `U`. -/
theorem sHom_eq_of_app_generator {X : TopCat.{u}} {U : Opens X}
    {F : Sheaf AddCommGrpCat.{u} X} (f : zeroOutsideInt U ⟶ F) :
    sHom (f.val.app (op U) (generator U)) = f := by
  apply Sheaf.Hom.ext
  symm
  apply CategoryTheory.sheafifyLift_unique
  simpa [generator, Category.assoc, ConcreteCategory.comp_apply] using
    (Presheaf.zeroOutside.sHom_eq_of_app_generator
      (f := CategoryTheory.toSheafify _ (Presheaf.constZ.zeroOutside U) ≫ f.val)).symm

/-- Two morphisms out of `zeroOutsideInt U` agree as soon as they agree on the
distinguished generator over `U`. -/
theorem hom_ext_from_generator {X : TopCat.{u}} {U : Opens X}
    {F : Sheaf AddCommGrpCat.{u} X} (f g : zeroOutsideInt U ⟶ F)
    (h :
      f.val.app (op U) (generator U) =
        g.val.app (op U) (generator U)) :
    f = g := by
  rw [← sHom_eq_of_app_generator f, ← sHom_eq_of_app_generator g, h]

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

/-- The canonical map from `zeroOutsideInt U` to `F` associated to a section `s ∈ F(U)`. -/
abbrev singleGeneratorMap {X : TopCat.{u}} {U : Opens X}
    {F : Sheaf AddCommGrpCat.{u} X}
    (s : F.presheaf.obj (op U)) :
    zeroOutsideInt U ⟶ F :=
  zeroOutsideInt.sHom s

/-- The image of `singleGeneratorMap s`, viewed as the subsheaf of `F` generated by
the single local section `s`. -/
abbrev singleGeneratedSheaf {X : TopCat.{u}} {U : Opens X}
    {F : Sheaf AddCommGrpCat.{u} X}
    (s : F.presheaf.obj (op U)) :
    Sheaf AddCommGrpCat.{u} X :=
  Limits.image (singleGeneratorMap s)

instance singleGeneratorMap_epi_to_image {X : TopCat.{u}} {U : Opens X}
    {F : Sheaf AddCommGrpCat.{u} X}
    (s : F.presheaf.obj (op U)) :
    Epi (factorThruImage (singleGeneratorMap s)) :=
  inferInstance

/-- For a family of local sections, the universal map from the coproduct of the corresponding
`zeroOutsideInt (U i)` into `F`. This packages the "generated by a family of sections"
construction used in Hartshorne Step 3. -/
abbrev familyGeneratorMap {X : TopCat.{u}} {ι : Type*}
    (U : ι → Opens X) {F : Sheaf AddCommGrpCat.{u} X}
    (s : ∀ i, F.presheaf.obj (op (U i)))
    [HasCoproduct fun i => zeroOutsideInt (U i)] :
    (∐ fun i => zeroOutsideInt (U i)) ⟶ F :=
  Sigma.desc fun i => zeroOutsideInt.sHom (s i)

/-- The image of `familyGeneratorMap U s`, viewed as the subsheaf of `F` generated by
the chosen family of local sections. -/
abbrev familyGeneratedSheaf {X : TopCat.{u}} {ι : Type*}
    (U : ι → Opens X) {F : Sheaf AddCommGrpCat.{u} X}
    (s : ∀ i, F.presheaf.obj (op (U i)))
    [HasCoproduct fun i => zeroOutsideInt (U i)] :
    Sheaf AddCommGrpCat.{u} X :=
  Limits.image (familyGeneratorMap U s)

instance familyGeneratorMap_epi_to_image {X : TopCat.{u}} {ι : Type*}
    (U : ι → Opens X) {F : Sheaf AddCommGrpCat.{u} X}
    (s : ∀ i, F.presheaf.obj (op (U i)))
    [HasCoproduct fun i => zeroOutsideInt (U i)] :
    Epi (factorThruImage (familyGeneratorMap U s)) :=
  inferInstance

/-- The map from the `i`-th generator `zeroOutsideInt (U i)` into the subsheaf generated by
the family `(s i)`. -/
abbrev familyGeneratedSheafι {X : TopCat.{u}} {ι : Type*}
    (U : ι → Opens X) {F : Sheaf AddCommGrpCat.{u} X}
    (s : ∀ i, F.presheaf.obj (op (U i)))
    [HasCoproduct fun i => zeroOutsideInt (U i)] (i : ι) :
    zeroOutsideInt (U i) ⟶ familyGeneratedSheaf U s :=
  Sigma.ι (fun i => zeroOutsideInt (U i)) i ≫ factorThruImage (familyGeneratorMap U s)

/-- The local section of the generated subsheaf corresponding to the `i`-th generator. -/
abbrev familyGeneratedSection {X : TopCat.{u}} {ι : Type*}
    (U : ι → Opens X) {F : Sheaf AddCommGrpCat.{u} X}
    (s : ∀ i, F.presheaf.obj (op (U i)))
    [HasCoproduct fun i => zeroOutsideInt (U i)] (i : ι) :
    (familyGeneratedSheaf U s).presheaf.obj (op (U i)) :=
  (familyGeneratedSheafι U s i).val.app (op (U i)) (zeroOutsideInt.generator (U i))

@[reassoc]
theorem familyGeneratedSheafι_comp_image_ι {X : TopCat.{u}} {ι : Type*}
    (U : ι → Opens X) {F : Sheaf AddCommGrpCat.{u} X}
    (s : ∀ i, F.presheaf.obj (op (U i)))
    [HasCoproduct fun i => zeroOutsideInt (U i)] (i : ι) :
    familyGeneratedSheafι U s i ≫ image.ι (familyGeneratorMap U s) =
      zeroOutsideInt.sHom (s i) := by
  simp [familyGeneratedSheafι, familyGeneratorMap]

/-- Adjoin one extra open set to a family of opens. -/
abbrev adjoinGeneratorOpens {X : TopCat.{u}} {ι : Type*}
    (U : ι → Opens X) (U₀ : Opens X) :
    ι ⊕ Unit → Opens X
  | Sum.inl i => U i
  | Sum.inr _ => U₀

/-- Adjoin one extra local section to a family of local sections. -/
abbrev adjoinGeneratorSections {X : TopCat.{u}} {ι : Type*}
    {F : Sheaf AddCommGrpCat.{u} X}
    (U : ι → Opens X) (s : ∀ i, F.presheaf.obj (op (U i)))
    {U₀ : Opens X} (s₀ : F.presheaf.obj (op U₀)) :
    ∀ j : ι ⊕ Unit, F.presheaf.obj (op (adjoinGeneratorOpens U U₀ j))
  | Sum.inl i => s i
  | Sum.inr _ => s₀

/-- The canonical inclusion of the old coproduct into the coproduct after adjoining one
more generator. -/
abbrev oldToAdjoinCoproduct {X : TopCat.{u}} {ι : Type*}
    (U : ι → Opens X) (U₀ : Opens X)
    [HasCoproduct fun i => zeroOutsideInt (U i)]
    [HasCoproduct fun j : ι ⊕ Unit => zeroOutsideInt (adjoinGeneratorOpens U U₀ j)] :
    (∐ fun i => zeroOutsideInt (U i)) ⟶
      (∐ fun j : ι ⊕ Unit => zeroOutsideInt (adjoinGeneratorOpens U U₀ j)) :=
  Sigma.desc (fun i =>
    Sigma.ι (fun j : ι ⊕ Unit => zeroOutsideInt (adjoinGeneratorOpens U U₀ j)) (Sum.inl i))

@[reassoc]
theorem oldToAdjoinCoproduct_comp_familyGeneratorMap {X : TopCat.{u}} {ι : Type*}
    {F : Sheaf AddCommGrpCat.{u} X}
    (U : ι → Opens X) (s : ∀ i, F.presheaf.obj (op (U i)))
    (U₀ : Opens X) (s₀ : F.presheaf.obj (op U₀))
    [HasCoproduct fun i => zeroOutsideInt (U i)]
    [HasCoproduct fun j : ι ⊕ Unit => zeroOutsideInt (adjoinGeneratorOpens U U₀ j)] :
    oldToAdjoinCoproduct U U₀ ≫
        familyGeneratorMap (adjoinGeneratorOpens U U₀) (adjoinGeneratorSections U s s₀) =
      familyGeneratorMap U s := by
  ext i
  simp [oldToAdjoinCoproduct, familyGeneratorMap, adjoinGeneratorOpens, adjoinGeneratorSections]

/-- The canonical morphism from the subsheaf generated by a family to the subsheaf generated
after adjoining one extra section. This is the structural map used in induction on the number
of generators. -/
abbrev oldGeneratedToAdjoinGenerated {X : TopCat.{u}} {ι : Type*}
    {F : Sheaf AddCommGrpCat.{u} X}
    (U : ι → Opens X) (s : ∀ i, F.presheaf.obj (op (U i)))
    (U₀ : Opens X) (s₀ : F.presheaf.obj (op U₀))
    [HasCoproduct fun i => zeroOutsideInt (U i)]
    [HasCoproduct fun j : ι ⊕ Unit => zeroOutsideInt (adjoinGeneratorOpens U U₀ j)] :
    familyGeneratedSheaf U s ⟶
      familyGeneratedSheaf (adjoinGeneratorOpens U U₀) (adjoinGeneratorSections U s s₀) :=
  Limits.image.lift
    { I := familyGeneratedSheaf (adjoinGeneratorOpens U U₀) (adjoinGeneratorSections U s s₀)
      m := Limits.image.ι _
      e := oldToAdjoinCoproduct U U₀ ≫ factorThruImage
        (familyGeneratorMap (adjoinGeneratorOpens U U₀) (adjoinGeneratorSections U s s₀))
      fac := by
        rw [Category.assoc, Limits.image.fac, oldToAdjoinCoproduct_comp_familyGeneratorMap] }

@[reassoc]
theorem oldGeneratedToAdjoinGenerated_comp {X : TopCat.{u}} {ι : Type*}
    {F : Sheaf AddCommGrpCat.{u} X}
    (U : ι → Opens X) (s : ∀ i, F.presheaf.obj (op (U i)))
    (U₀ : Opens X) (s₀ : F.presheaf.obj (op U₀))
    [HasCoproduct fun i => zeroOutsideInt (U i)]
    [HasCoproduct fun j : ι ⊕ Unit => zeroOutsideInt (adjoinGeneratorOpens U U₀ j)] :
    oldGeneratedToAdjoinGenerated U s U₀ s₀ ≫
        Limits.image.ι (familyGeneratorMap (adjoinGeneratorOpens U U₀)
          (adjoinGeneratorSections U s s₀)) =
      Limits.image.ι (familyGeneratorMap U s) := by
  exact Limits.image.lift_fac _

instance oldGeneratedToAdjoinGenerated_mono {X : TopCat.{u}} {ι : Type*}
    {F : Sheaf AddCommGrpCat.{u} X}
    (U : ι → Opens X) (s : ∀ i, F.presheaf.obj (op (U i)))
    (U₀ : Opens X) (s₀ : F.presheaf.obj (op U₀))
    [HasCoproduct fun i => zeroOutsideInt (U i)]
    [HasCoproduct fun j : ι ⊕ Unit => zeroOutsideInt (adjoinGeneratorOpens U U₀ j)] :
    Mono (oldGeneratedToAdjoinGenerated U s U₀ s₀) := by
  let m := image.ι (familyGeneratorMap (adjoinGeneratorOpens U U₀) (adjoinGeneratorSections U s s₀))
  haveI : Mono m := inferInstance
  exact mono_of_mono_fac (oldGeneratedToAdjoinGenerated_comp U s U₀ s₀)

lemma old_familyGeneratedSheafι_comp_oldGeneratedToAdjoinGenerated {X : TopCat.{u}} {ι : Type*}
    {F : Sheaf AddCommGrpCat.{u} X}
    (U : ι → Opens X) (s : ∀ i, F.presheaf.obj (op (U i)))
    (U₀ : Opens X) (s₀ : F.presheaf.obj (op U₀))
    [HasCoproduct fun i => zeroOutsideInt (U i)]
    [HasCoproduct fun j : ι ⊕ Unit => zeroOutsideInt (adjoinGeneratorOpens U U₀ j)]
    (i : ι) :
    familyGeneratedSheafι U s i ≫ oldGeneratedToAdjoinGenerated U s U₀ s₀ =
      familyGeneratedSheafι (adjoinGeneratorOpens U U₀) (adjoinGeneratorSections U s s₀)
        (Sum.inl i) := by
  apply (cancel_mono (image.ι (familyGeneratorMap (adjoinGeneratorOpens U U₀)
    (adjoinGeneratorSections U s s₀)))).1
  rw [Category.assoc, oldGeneratedToAdjoinGenerated_comp]
  rw [familyGeneratedSheafι_comp_image_ι]
  rw [familyGeneratedSheafι_comp_image_ι]

/-- The projection from the enlarged coproduct onto the newly adjoined generator, killing the
old summands. -/
abbrev adjoinGeneratorProjection {X : TopCat.{u}} {ι : Type*}
    (U : ι → Opens X) (U₀ : Opens X)
    [HasCoproduct fun j : ι ⊕ Unit => zeroOutsideInt (adjoinGeneratorOpens U U₀ j)] :
    (∐ fun j : ι ⊕ Unit => zeroOutsideInt (adjoinGeneratorOpens U U₀ j)) ⟶ zeroOutsideInt U₀ :=
  Sigma.desc fun
    | Sum.inl _ => 0
    | Sum.inr _ => 𝟙 _

/-- After adjoining one generator, the quotient by the old generated subsheaf is generated by the
new section alone. -/
abbrev adjoinedGeneratorToCokernel {X : TopCat.{u}} {ι : Type*}
    {F : Sheaf AddCommGrpCat.{u} X}
    (U : ι → Opens X) (s : ∀ i, F.presheaf.obj (op (U i)))
    (U₀ : Opens X) (s₀ : F.presheaf.obj (op U₀))
    [HasCoproduct fun i => zeroOutsideInt (U i)]
    [HasCoproduct fun j : ι ⊕ Unit => zeroOutsideInt (adjoinGeneratorOpens U U₀ j)] :
    zeroOutsideInt U₀ ⟶ cokernel (oldGeneratedToAdjoinGenerated U s U₀ s₀) :=
  familyGeneratedSheafι (adjoinGeneratorOpens U U₀) (adjoinGeneratorSections U s s₀) (Sum.inr ()) ≫
    cokernel.π (oldGeneratedToAdjoinGenerated U s U₀ s₀)

@[reassoc]
theorem adjoinGeneratorProjection_comp_adjoinedGeneratorToCokernel {X : TopCat.{u}} {ι : Type*}
    {F : Sheaf AddCommGrpCat.{u} X}
    (U : ι → Opens X) (s : ∀ i, F.presheaf.obj (op (U i)))
    (U₀ : Opens X) (s₀ : F.presheaf.obj (op U₀))
    [HasCoproduct fun i => zeroOutsideInt (U i)]
    [HasCoproduct fun j : ι ⊕ Unit => zeroOutsideInt (adjoinGeneratorOpens U U₀ j)] :
    adjoinGeneratorProjection U U₀ ≫ adjoinedGeneratorToCokernel U s U₀ s₀ =
      factorThruImage (familyGeneratorMap (adjoinGeneratorOpens U U₀) (adjoinGeneratorSections U s s₀)) ≫
        cokernel.π (oldGeneratedToAdjoinGenerated U s U₀ s₀) := by
  ext j
  cases j with
  | inl i =>
      simp [adjoinGeneratorProjection]
      calc
        0 = Sigma.ι (fun i => zeroOutsideInt (U i)) i ≫ factorThruImage (familyGeneratorMap U s) ≫
            0 := by simp
        _ = familyGeneratedSheafι U s i ≫ oldGeneratedToAdjoinGenerated U s U₀ s₀ ≫
            cokernel.π (oldGeneratedToAdjoinGenerated U s U₀ s₀) := by
              simp [familyGeneratedSheafι, Category.assoc]
        _ = familyGeneratedSheafι (adjoinGeneratorOpens U U₀) (adjoinGeneratorSections U s s₀)
            (Sum.inl i) ≫ cokernel.π (oldGeneratedToAdjoinGenerated U s U₀ s₀) := by
              rw [← Category.assoc, old_familyGeneratedSheafι_comp_oldGeneratedToAdjoinGenerated]
        _ = Sigma.ι (fun j => zeroOutsideInt (adjoinGeneratorOpens U U₀ j)) (Sum.inl i) ≫
            factorThruImage (familyGeneratorMap (adjoinGeneratorOpens U U₀)
              (adjoinGeneratorSections U s s₀)) ≫
            cokernel.π (oldGeneratedToAdjoinGenerated U s U₀ s₀) := by
              simp [familyGeneratedSheafι]
  | inr u =>
      cases u
      simp [adjoinGeneratorProjection, adjoinedGeneratorToCokernel, familyGeneratedSheafι,
        Category.assoc]

instance adjoinedGeneratorToCokernel_epi {X : TopCat.{u}} {ι : Type*}
    {F : Sheaf AddCommGrpCat.{u} X}
    (U : ι → Opens X) (s : ∀ i, F.presheaf.obj (op (U i)))
    (U₀ : Opens X) (s₀ : F.presheaf.obj (op U₀))
    [HasCoproduct fun i => zeroOutsideInt (U i)]
    [HasCoproduct fun j : ι ⊕ Unit => zeroOutsideInt (adjoinGeneratorOpens U U₀ j)] :
    Epi (adjoinedGeneratorToCokernel U s U₀ s₀) := by
  exact epi_of_epi_fac (adjoinGeneratorProjection_comp_adjoinedGeneratorToCokernel U s U₀ s₀)

/-- The short complex attached to adjoining one generator. -/
abbrev adjoinGeneratorShortComplex {X : TopCat.{u}} {ι : Type*}
    {F : Sheaf AddCommGrpCat.{u} X}
    (U : ι → Opens X) (s : ∀ i, F.presheaf.obj (op (U i)))
    (U₀ : Opens X) (s₀ : F.presheaf.obj (op U₀))
    [HasCoproduct fun i => zeroOutsideInt (U i)]
    [HasCoproduct fun j : ι ⊕ Unit => zeroOutsideInt (adjoinGeneratorOpens U U₀ j)] :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (oldGeneratedToAdjoinGenerated U s U₀ s₀)
    (cokernel.π (oldGeneratedToAdjoinGenerated U s U₀ s₀))
    (cokernel.condition _)

theorem adjoinGeneratorShortComplex_exact {X : TopCat.{u}} {ι : Type*}
    {F : Sheaf AddCommGrpCat.{u} X}
    (U : ι → Opens X) (s : ∀ i, F.presheaf.obj (op (U i)))
    (U₀ : Opens X) (s₀ : F.presheaf.obj (op U₀))
    [HasCoproduct fun i => zeroOutsideInt (U i)]
    [HasCoproduct fun j : ι ⊕ Unit => zeroOutsideInt (adjoinGeneratorOpens U U₀ j)] :
    (adjoinGeneratorShortComplex U s U₀ s₀).Exact := by
  exact ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)

theorem adjoinGeneratorShortComplex_shortExact {X : TopCat.{u}} {ι : Type*}
    {F : Sheaf AddCommGrpCat.{u} X}
    (U : ι → Opens X) (s : ∀ i, F.presheaf.obj (op (U i)))
    (U₀ : Opens X) (s₀ : F.presheaf.obj (op U₀))
    [HasCoproduct fun i => zeroOutsideInt (U i)]
    [HasCoproduct fun j : ι ⊕ Unit => zeroOutsideInt (adjoinGeneratorOpens U U₀ j)] :
    (adjoinGeneratorShortComplex U s U₀ s₀).ShortExact where
  mono_f := inferInstance
  exact := adjoinGeneratorShortComplex_exact U s U₀ s₀
  epi_g := inferInstance

/-- In an abelian category, the image of an epimorphism is canonically isomorphic to its target. -/
abbrev isoToImageOfEpi {X : TopCat.{u}} {A B : Sheaf AddCommGrpCat.{u} X}
    (f : A ⟶ B) [Epi f] : image f ≅ B := by
  haveI : Epi (image.ι f) := epi_of_epi_fac (image.fac f)
  haveI : IsIso (image.ι f) := isIso_of_mono_of_epi (image.ι f)
  exact asIso (image.ι f)

/-- The quotient obtained by adjoining one extra section is canonically a one-generator image of
`zeroOutsideInt U₀`. -/
abbrev adjoinedGeneratorCokernelIso {X : TopCat.{u}} {ι : Type*}
    {F : Sheaf AddCommGrpCat.{u} X}
    (U : ι → Opens X) (s : ∀ i, F.presheaf.obj (op (U i)))
    (U₀ : Opens X) (s₀ : F.presheaf.obj (op U₀))
    [HasCoproduct fun i => zeroOutsideInt (U i)]
    [HasCoproduct fun j : ι ⊕ Unit => zeroOutsideInt (adjoinGeneratorOpens U U₀ j)] :
    image (adjoinedGeneratorToCokernel U s U₀ s₀) ≅
      cokernel (oldGeneratedToAdjoinGenerated U s U₀ s₀) :=
  isoToImageOfEpi (adjoinedGeneratorToCokernel U s U₀ s₀)

/-- If a family of local sections generates `F` epimorphically, then the corresponding generated
subsheaf is canonically isomorphic to `F`. -/
abbrev familyGeneratedSheafIsoOfEpi {X : TopCat.{u}} {ι : Type*}
    (U : ι → Opens X) {F : Sheaf AddCommGrpCat.{u} X}
    (s : ∀ i, F.presheaf.obj (op (U i)))
    [HasCoproduct fun i => zeroOutsideInt (U i)]
    [Epi (familyGeneratorMap U s)] : familyGeneratedSheaf U s ≅ F :=
  isoToImageOfEpi (familyGeneratorMap U s)

/-- Indexing type for all local sections of a sheaf. -/
abbrev SectionIndex {X : TopCat.{u}}
    (F : Sheaf AddCommGrpCat.{u} X) :=
  Σ U : Opens X, F.presheaf.obj (op U)

/-- The canonical map attached to a finite set of local sections. -/
abbrev finsetGeneratorMap {X : TopCat.{u}}
    {F : Sheaf AddCommGrpCat.{u} X}
    (S : Finset (SectionIndex F))
    [HasCoproduct fun σ : {σ // σ ∈ S} => zeroOutsideInt σ.1.1] :
    (∐ fun σ : {σ // σ ∈ S} => zeroOutsideInt σ.1.1) ⟶ F :=
  familyGeneratorMap (fun σ : {σ // σ ∈ S} => σ.1.1) (fun σ => σ.1.2)

/-- The subsheaf of `F` generated by a finite set of local sections. -/
abbrev finsetGeneratedSheaf {X : TopCat.{u}}
    {F : Sheaf AddCommGrpCat.{u} X}
    (S : Finset (SectionIndex F))
    [HasCoproduct fun σ : {σ // σ ∈ S} => zeroOutsideInt σ.1.1] :
    Sheaf AddCommGrpCat.{u} X :=
  Limits.image (finsetGeneratorMap S)

instance finsetGeneratorMap_epi_to_image {X : TopCat.{u}}
    {F : Sheaf AddCommGrpCat.{u} X}
    (S : Finset (SectionIndex F))
    [HasCoproduct fun σ : {σ // σ ∈ S} => zeroOutsideInt σ.1.1] :
    Epi (factorThruImage (finsetGeneratorMap S)) :=
  inferInstance

/-- If a finite set of local sections generates `F` epimorphically, then the corresponding
finite generated subsheaf is canonically isomorphic to `F`. -/
abbrev finsetGeneratedSheafIsoOfEpi {X : TopCat.{u}}
    {F : Sheaf AddCommGrpCat.{u} X}
    (S : Finset (SectionIndex F))
    [HasCoproduct fun σ : {σ // σ ∈ S} => zeroOutsideInt σ.1.1]
    [Epi (finsetGeneratorMap S)] : finsetGeneratedSheaf S ≅ F :=
  isoToImageOfEpi (finsetGeneratorMap S)

/-- The canonical map from the coproduct of all `zeroOutsideInt U` indexed by local sections
of `F` onto `F`. This is the formal Step 3A starting point for building finitely generated
subsheaves via images of smaller subcoproducts. -/
abbrev allSectionMap {X : TopCat.{u}}
    (F : Sheaf AddCommGrpCat.{u} X)
    [HasCoproduct (fun σ : SectionIndex F => zeroOutsideInt σ.1)] :
    (∐ fun σ : SectionIndex F => zeroOutsideInt σ.1) ⟶ F :=
  Sigma.desc (fun σ => zeroOutsideInt.sHom σ.2)

set_option synthInstance.maxHeartbeats 40000 in
instance allSectionMap_epi {X : TopCat.{u}}
    (F : Sheaf AddCommGrpCat.{u} X)
    [HasCoproduct (fun σ : SectionIndex F => zeroOutsideInt σ.1)] :
    Epi (allSectionMap F) := by
  letI : Balanced (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    inferInstance
  rw [← Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat]
  change TopCat.Presheaf.IsLocallySurjective (allSectionMap F).val
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U t x hx
  refine ⟨U, 𝟙 U, ?_, hx⟩
  refine ⟨(Sigma.ι (fun σ : SectionIndex F => zeroOutsideInt σ.1) ⟨U, t⟩).val.app
      (op U) (zeroOutsideInt.generator U), ?_⟩
  change (((Sigma.ι (fun σ : SectionIndex F => zeroOutsideInt σ.1) ⟨U, t⟩) ≫
      allSectionMap F).val.app (op U) (zeroOutsideInt.generator U)) =
    TopCat.Presheaf.restrict t (𝟙 U)
  rw [Sigma.ι_desc, zeroOutsideInt.sHom_app_generator]
  change t = TopCat.Presheaf.restrict t (𝟙 U)
  symm
  change F.presheaf.map (𝟙 (Opposite.op U)) t = t
  simp

end Sheaf

end TopCat
