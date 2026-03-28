import Aristotle.GrothendieckVanishing.main.Setup
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Topology.Sheaves.Stalks

open CategoryTheory TopologicalSpace Opposite Limits

universe u

namespace CodexScratch

noncomputable def closedIncl {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) : TopCat.of s ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, hs.isClosedEmbedding_subtypeVal.continuous⟩

theorem locallyInjective_stalkFunctor_map_injective
    {X : TopCat.{u}} {F G : X.Presheaf AddCommGrpCat} (T : F ⟶ G)
    [CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) T] :
    ∀ x : X, Function.Injective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map T) := by
  intro x s t hst
  obtain ⟨U, hxU, sU, rfl⟩ := F.germ_exist x s
  obtain ⟨V, hxV, sV, hsV⟩ := F.germ_exist x t
  rw [← hsV] at hst ⊢
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, TopCat.Presheaf.stalkFunctor_map_germ_apply] at hst
  obtain ⟨W, hxW, iWU, iWV, hEq⟩ := G.germ_eq x hxU hxV _ _ hst
  have hEqWU :
      T.app (Opposite.op W) (F.map iWU.op sU) =
        G.map iWU.op (T.app (Opposite.op U) sU) := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, T.naturality]
  have hEqWV :
      T.app (Opposite.op W) (F.map iWV.op sV) =
        G.map iWV.op (T.app (Opposite.op V) sV) := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, T.naturality]
  have hEq' :
      T.app (Opposite.op W) (F.map iWU.op sU) =
        T.app (Opposite.op W) (F.map iWV.op sV) := by
    rw [hEqWU, hEqWV]
    exact hEq
  have hloc := CategoryTheory.Presheaf.equalizerSieve_mem
    (J := Opens.grothendieckTopology X) (φ := T)
    (x := F.map iWU.op sU) (y := F.map iWV.op sV) hEq'
  rw [Opens.grothendieckTopology] at hloc
  rcases hloc x hxW with ⟨Z, iZW, hEqZ, hxZ⟩
  apply F.germ_ext Z hxZ (iZW ≫ iWU) (iZW ≫ iWV)
  simpa using hEqZ

theorem stalkFunctor_map_iso_toSheafify
    {X : TopCat.{u}} (P : X.Presheaf AddCommGrpCat) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · exact locallyInjective_stalkFunctor_map_injective
      (T := CategoryTheory.toSheafify (Opens.grothendieckTopology X) P) x
  · have hls :
        TopCat.Presheaf.IsLocallySurjective
          (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P) := by
        dsimp [TopCat.Presheaf.IsLocallySurjective]
        infer_instance
    exact
      ((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
        (T := CategoryTheory.toSheafify (Opens.grothendieckTopology X) P)).mp hls) x

theorem closedIncl_counit_isIso
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    (F : TopCat.Sheaf AddCommGrpCat (TopCat.of s)) :
    IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat (closedIncl hs)).counit.app F) := by
  sorry

end CodexScratch

namespace TopCat

open Opposite
open scoped AlgebraicGeometry

lemma Presheaf.restrict_sum {X : TopCat.{u}} {U V : Opens X}
    {F : Presheaf AddCommGrpCat X} (h : V ≤ U) (s t : F.obj (op U)) :
    (s + t) |_ V = s |_ V + t |_ V := by
  delta Presheaf.restrictOpen Presheaf.restrict
  cat_disch

namespace Sheaf

noncomputable section

open CategoryTheory.Abelian

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

instance {C : Type*} [Category C] {D : Type*} [Category D] [Preadditive D] :
    (Functor.const Cᵒᵖ : D ⥤ Cᵒᵖ ⥤ D).Additive where

instance {X : TopCat.{u}} :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive := by
  show ((Functor.const (Opens X)ᵒᵖ) ⋙
    presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive
  infer_instance

instance (X : TopCat.{u}) :
    HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  hasExt_of_enoughInjectives _

/-- The cohomology of a sheaf of abelian groups in degree `n`. -/
abbrev H {X : TopCat.{u}} (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) : Type u :=
  CategoryTheory.Sheaf.H F n

/-- Given a morphism `𝓕 ⟶ 𝓖`, we get an induced morphism on cohomology. -/
noncomputable def H.map {X : TopCat.{u}} {F G : Sheaf AddCommGrpCat X} (f : F ⟶ G) (n : ℕ) :
    H F n →+ H G n :=
  ((Abelian.Ext.mk₀ f).postcomp
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj (AddCommGrpCat.of (ULift ℤ)))
    (add_zero n))

instance {X : TopCat.{u}} (F : Sheaf AddCommGrpCat X) {n : ℕ} [Injective F] :
    Subsingleton (H F (n + 1)) :=
  Abelian.Ext.subsingleton_of_injective _ _ _

/-- `H F 0` is equivalent to taking global sections. -/
noncomputable def H.equiv₀ {X : TopCat.{u}} (F : Sheaf AddCommGrpCat X) :
    H F 0 ≃+ F.val.obj (op ⊤) := by
  refine AddEquiv.trans Abelian.Ext.addEquiv₀ ?_
  refine AddEquiv.trans ?_ (AddCommGrpCat.uliftZMultiplesAddEquiv _)
  exact (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat Limits.isTerminalTop).homAddEquiv _ F

lemma H.map_apply {X : TopCat.{u}} {F G : Sheaf AddCommGrpCat X}
    (f : F ⟶ G) {n : ℕ} (x : H F n) :
    H.map f n x = x.comp (Abelian.Ext.mk₀ f) (add_zero n) := rfl

@[simp]
lemma H.map_id_apply {X : TopCat.{u}} {F : Sheaf AddCommGrpCat X} {n : ℕ} (x : H F n) :
    H.map (𝟙 F) n x = x := by
  simp [H.map_apply]

lemma H.map_comp_apply {X : TopCat.{u}} {F G G' : Sheaf AddCommGrpCat X}
    {n : ℕ} (f : F ⟶ G) (g : G ⟶ G') (x : H F n) :
    H.map (f ≫ g) n x = H.map g n (H.map f n x) := by
  simp [H.map_apply]

attribute [local simp] H.map_comp_apply in
/-- The connecting homomorphism in the long exact sequence on sheaf cohomology. -/
noncomputable def H.connectingHom {X : TopCat.{u}}
    {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    (n₀ : ℕ) (n₁ : ℕ := n₀ + 1) (h : n₀ + 1 = n₁ := by omega) :
    H S.X₃ n₀ →+ H S.X₁ n₁ :=
  hS.extClass.postcomp _ h

namespace H

/-- The long exact sequence on sheaf cohomology attached to a short exact sequence. -/
noncomputable def longSequence {X : TopCat.{u}}
    {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    (n₀ : ℕ) (n₁ : ℕ := n₀ + 1) (h : n₀ + 1 = n₁ := by omega) :
    ComposableArrows AddCommGrpCat.{u} 5 :=
  ComposableArrows.mk₅
    (AddCommGrpCat.ofHom (H.map S.f n₀))
    (AddCommGrpCat.ofHom (H.map S.g n₀))
    (AddCommGrpCat.ofHom (H.connectingHom hS n₀ n₁ h))
    (AddCommGrpCat.ofHom (H.map S.f n₁))
    (AddCommGrpCat.ofHom (H.map S.g n₁))

theorem longSequence_exact {X : TopCat.{u}}
    {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    (n₀ : ℕ) (n₁ : ℕ := n₀ + 1) (h : n₀ + 1 = n₁ := by omega) :
    (longSequence hS n₀ n₁ h).Exact :=
  Abelian.Ext.covariantSequence_exact _ hS n₀ n₁ h

lemma longSequence_exact₁' {X : TopCat.{u}}
    {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    (n₀ : ℕ) (n₁ : ℕ := n₀ + 1) (h : n₀ + 1 = n₁ := by omega) :
    (ShortComplex.mk (AddCommGrpCat.ofHom (H.connectingHom hS n₀ n₁ h))
      (AddCommGrpCat.ofHom (H.map S.f n₁)) (by
      convert ((longSequence_exact hS n₀ n₁ h).sc 2).zero)).Exact := by
  convert (longSequence_exact hS n₀ n₁ h).exact 2

lemma longSequence_exact₃' {X : TopCat.{u}}
    {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    (n₀ : ℕ) (n₁ : ℕ := n₀ + 1) (h : n₀ + 1 = n₁ := by omega) :
    (ShortComplex.mk (AddCommGrpCat.ofHom (H.map S.g n₀))
      (AddCommGrpCat.ofHom (H.connectingHom hS n₀ n₁ h)) (by
      convert ((longSequence_exact hS n₀ n₁ h).sc 1).zero)).Exact := by
  convert (longSequence_exact hS n₀ n₁ h).exact 1

lemma longSequence_exact₂' {X : TopCat.{u}}
    {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk (AddCommGrpCat.ofHom (H.map S.f n))
      (AddCommGrpCat.ofHom (H.map S.g n)) (by
      convert ((longSequence_exact hS n).sc 0).zero)).Exact := by
  convert (longSequence_exact hS n).exact 0

lemma map_comp_map_zero {X : TopCat.{u}}
    {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    (n : ℕ) (x₁ : H S.X₁ n) :
    H.map S.g n (H.map S.f n x₁) = 0 := by
  have hz :
      AddCommGrpCat.ofHom (H.map S.f n) ≫ AddCommGrpCat.ofHom (H.map S.g n) = 0 :=
    ((longSequence_exact hS n).sc 0).zero
  change
    (ConcreteCategory.hom
      (AddCommGrpCat.ofHom (H.map S.f n) ≫ AddCommGrpCat.ofHom (H.map S.g n))) x₁ = 0
  simpa [hz]

lemma map_comp_connectingHom_zero {X : TopCat.{u}}
    {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    (n₀ : ℕ) (n₁ : ℕ := n₀ + 1) (h : n₀ + 1 = n₁ := by omega) (x₂ : H S.X₂ n₀) :
    H.connectingHom hS n₀ n₁ h (H.map S.g n₀ x₂) = 0 := by
  have hz : AddCommGrpCat.ofHom (H.map S.g n₀) ≫ AddCommGrpCat.ofHom (H.connectingHom hS n₀ n₁ h) = 0 :=
    ((longSequence_exact hS n₀ n₁ h).sc 1).zero
  change
    (ConcreteCategory.hom
      (AddCommGrpCat.ofHom (H.map S.g n₀) ≫
        AddCommGrpCat.ofHom (H.connectingHom hS n₀ n₁ h))) x₂ = 0
  simpa [hz]

lemma connectingHom_comp_map_zero {X : TopCat.{u}}
    {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    (n₀ : ℕ) (n₁ : ℕ := n₀ + 1) (h : n₀ + 1 = n₁ := by omega) (x₃ : H S.X₃ n₀) :
    H.map S.f n₁ (H.connectingHom hS n₀ n₁ h x₃) = 0 := by
  have hz : AddCommGrpCat.ofHom (H.connectingHom hS n₀ n₁ h) ≫ AddCommGrpCat.ofHom (H.map S.f n₁) = 0 :=
    ((longSequence_exact hS n₀ n₁ h).sc 2).zero
  change
    (ConcreteCategory.hom
      (AddCommGrpCat.ofHom (H.connectingHom hS n₀ n₁ h) ≫
        AddCommGrpCat.ofHom (H.map S.f n₁))) x₃ = 0
  simpa [hz]

lemma longSequence_exact₂ {X : TopCat.{u}}
    {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    (n : ℕ) (x₂ : H S.X₂ n) (hx₂ : H.map S.g n x₂ = 0) :
    ∃ x₁ : H S.X₁ n, H.map S.f n x₁ = x₂ := by
  have hExact := longSequence_exact₂' hS n
  rw [ShortComplex.ab_exact_iff] at hExact
  exact hExact x₂ hx₂

lemma longSequence_exact₃ {X : TopCat.{u}}
    {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    (n₀ : ℕ) (n₁ : ℕ := n₀ + 1) (h : n₀ + 1 = n₁ := by omega)
    (x₃ : H S.X₃ n₀) (hx₃ : H.connectingHom hS n₀ n₁ h x₃ = 0) :
    ∃ x₂ : H S.X₂ n₀, H.map S.g n₀ x₂ = x₃ := by
  have hExact := longSequence_exact₃' hS n₀ n₁ h
  rw [ShortComplex.ab_exact_iff] at hExact
  exact hExact x₃ hx₃

lemma longSequence_exact₁ {X : TopCat.{u}}
    {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    (n₀ : ℕ) (n₁ : ℕ := n₀ + 1) (h : n₀ + 1 = n₁ := by omega)
    (x₁ : H S.X₁ n₁) (hx₁ : H.map S.f n₁ x₁ = 0) :
    ∃ x₃ : H S.X₃ n₀, H.connectingHom hS n₀ n₁ h x₃ = x₁ := by
  have hExact := longSequence_exact₁' hS n₀ n₁ h
  rw [ShortComplex.ab_exact_iff] at hExact
  exact hExact x₁ hx₁

end H

end

end Sheaf

end TopCat

noncomputable section

namespace TopCat

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
    sorry

theorem sHom_app_generator {F : Presheaf AddCommGrpCat.{u} X} (s : F.obj (op U)) :
    (sHom s).app (op U) (generator U) = s := by
  simp [sHom, generator, ← ConcreteCategory.comp_apply,
    TopCat.Sheaf.AddCommGrpCat.uliftZMultiplesAddEquiv, AddCommGrpCat.homAddEquiv,
    AddEquiv.mk', uliftZMultiplesHom]
  exact show (((zmultiplesHom ↑(F.obj (op U))) s).comp
      (AddEquiv.toAddMonoidHom (AddEquiv.ulift : ULift.{u, 0} ℤ ≃+ ℤ))) (1 : ULift ℤ) = s from by
    change ((1 : ℤ) • s) = s
    simp

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
