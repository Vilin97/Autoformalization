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

/-!
  ClosedImmersion.lean — Closed inclusion API and stalk results

  Provides:
  - `closedIncl`: closed inclusion `s ↪ X` as a morphism in `TopCat`
  - `closedIncl_isClosedEmbedding`, `closedIncl_isInducing`: basic properties
  - `stalkFunctor_map_iso_toSheafify`: stalk of sheafification map is an iso
  - `closedIncl_counit_isIso_presheaf`: presheaf-boundary counit iso for closed subspace
  - `closedIncl_counit_isIso`: pushforward–pullback counit is an iso on closed subspace
  - `closedIncl_unit_stalk_isIso`: adjunction unit is a stalk iso at points in the subspace
-/

open CategoryTheory TopologicalSpace Opposite Limits

universe u

noncomputable section

namespace TopCat

/-- Closed inclusion `s ↪ X` as a morphism in `TopCat`. -/
def closedIncl {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) : TopCat.of s ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, hs.isClosedEmbedding_subtypeVal.continuous⟩

@[simp]
theorem coe_closedIncl {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) :
    (closedIncl hs : s → X) = Subtype.val := rfl

lemma closedIncl_isClosedEmbedding {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) :
    Topology.IsClosedEmbedding (closedIncl hs) :=
  hs.isClosedEmbedding_subtypeVal

lemma closedIncl_isInducing {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) :
    Topology.IsInducing (closedIncl hs) :=
  (closedIncl_isClosedEmbedding hs).isInducing

theorem closedIncl_map_eq_bot_of_le_compl {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {U : Opens X} (hU : U ≤ ⟨sᶜ, hs.isOpen_compl⟩) :
    (Opens.map (closedIncl hs)).obj U = ⊥ := by
  ext x
  constructor
  · intro hx
    exact False.elim (hU hx x.2)
  · intro hx
    simp at hx

instance closedIncl_stalkPushforward_isIso {X : TopCat.{u}} {s : Set X} {hs : IsClosed s}
    {C : Type*} [Category.{u} C] [HasColimits C]
    {F : (TopCat.of s).Presheaf C} {x : TopCat.of s} :
    IsIso (Presheaf.stalkPushforward C (closedIncl hs) F x) :=
  Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
    C (closedIncl_isInducing hs) F x

lemma opensMap_range_isBasis_of_isInducing {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : Topology.IsInducing f) :
    Opens.IsBasis (Set.range (Opens.map f).obj) := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  refine ⟨U, ?_, hx, le_rfl⟩
  refine ⟨hf.functorObj U, ?_⟩
  simpa using hf.map_functorObj U

lemma opensMap_isCoverDense_of_isInducing {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : Topology.IsInducing f) :
    (Opens.map f).IsCoverDense (Opens.grothendieckTopology X) := by
  rw [TopCat.Opens.coverDense_iff_isBasis]
  exact opensMap_range_isBasis_of_isInducing hf

instance opensMap_isLocallyFull {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (Opens.map f).IsLocallyFull (Opens.grothendieckTopology X) where
  functorPushforward_imageSieve_mem := by
    intro U V i
    rw [Opens.grothendieckTopology]
    intro x hx
    refine ⟨(Opens.map f).obj (U ⊓ V), (Opens.map f).map (Opens.infLELeft U V), ?_, ?_⟩
    · refine ⟨U ⊓ V, Opens.infLELeft U V, 𝟙 _, ?_, by simp⟩
      refine ⟨Opens.infLERight U V, ?_⟩
      exact Subsingleton.elim _ _
    · exact ⟨hx, i.le hx⟩

theorem locallyInjective_stalkFunctor_map_injective
    {C : Type*} [Category.{u} C] [HasColimits C]
    {FC : C → C → Type*} {CC : C → Type u}
    [∀ (X Y : C), FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [PreservesFilteredColimits (forget C)]
    {X : TopCat.{u}} {F G : X.Presheaf C} (T : F ⟶ G)
    [CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) T] :
    ∀ x : X, Function.Injective ((TopCat.Presheaf.stalkFunctor C x).map T) := by
  intro x s t hst
  obtain ⟨U, hxU, sU, rfl⟩ := F.germ_exist x s
  obtain ⟨V, hxV, sV, hsV⟩ := F.germ_exist x t
  rw [← hsV] at hst ⊢
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, TopCat.Presheaf.stalkFunctor_map_germ_apply] at hst
  obtain ⟨W, hxW, iWU, iWV, hEq⟩ := G.germ_eq x hxU hxV _ _ hst
  have hnat (Y : Opens X) (iWY : W ⟶ Y) (sY : CC (F.obj (op Y))) :
      T.app (op W) (F.map iWY.op sY) = G.map iWY.op (T.app (op Y) sY) := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, T.naturality]
  have hEq' : T.app (op W) (F.map iWU.op sU) =
      T.app (op W) (F.map iWV.op sV) := by rw [hnat _ iWU, hnat _ iWV]; exact hEq
  have hloc := CategoryTheory.Presheaf.equalizerSieve_mem
    (J := Opens.grothendieckTopology X) (φ := T)
    (x := F.map iWU.op sU) (y := F.map iWV.op sV) hEq'
  rw [Opens.grothendieckTopology] at hloc
  rcases hloc x hxW with ⟨Z, iZW, hEqZ, hxZ⟩
  apply F.germ_ext Z hxZ (iZW ≫ iWU) (iZW ≫ iWV)
  simpa using hEqZ

theorem stalkFunctor_map_iso_toSheafify
    {C : Type*} [Category.{u} C] [HasColimits C]
    {FC : C → C → Type*} {CC : C → Type u}
    [∀ (X Y : C), FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [PreservesFilteredColimits (forget C)]
    [(forget C).ReflectsIsomorphisms]
    {X : TopCat.{u}} [HasWeakSheafify (Opens.grothendieckTopology X) C]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective C]
    (P : X.Presheaf C) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor C x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · exact locallyInjective_stalkFunctor_map_injective
      (T := CategoryTheory.toSheafify (Opens.grothendieckTopology X) P) x
  · have hls : TopCat.Presheaf.IsLocallySurjective
          (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P) := by
        dsimp [TopCat.Presheaf.IsLocallySurjective]; infer_instance
    exact
      ((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
        (T := CategoryTheory.toSheafify (Opens.grothendieckTopology X) P)).mp hls) x

theorem closedIncl_counit_isIso_presheaf
    {C : Type*} [Category.{u} C]
    {FC : C → C → Type*} {CC : C → Type u}
    [∀ (X Y : C), FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (forget C)]
    [PreservesFilteredColimits (forget C)]
    [(forget C).ReflectsIsomorphisms]
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {F : TopCat.Presheaf C (TopCat.of s)} (hF : F.IsSheaf) :
    IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction C (closedIncl hs)).counit.app
      (⟨F, hF⟩ : TopCat.Sheaf C (TopCat.of s))) := by
  let Fsh : TopCat.Sheaf C (TopCat.of s) := ⟨F, hF⟩
  change IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction C (closedIncl hs)).counit.app Fsh)
  letI : (Opens.map (closedIncl hs)).IsCoverDense
      (Opens.grothendieckTopology (TopCat.of s)) :=
    opensMap_isCoverDense_of_isInducing (closedIncl_isInducing hs)
  letI : (Opens.map (closedIncl hs)).IsLocallyFull
      (Opens.grothendieckTopology (TopCat.of s)) :=
    opensMap_isLocallyFull (closedIncl hs)
  letI : (Opens.map (closedIncl hs)).IsContinuous
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology (TopCat.of s)) :=
    CategoryTheory.Functor.IsCoverDense.isContinuous
      (J := Opens.grothendieckTopology X)
      (K := Opens.grothendieckTopology (TopCat.of s))
      (G := Opens.map (closedIncl hs))
      (coverPreserving_opens_map (closedIncl hs))
  haveI : (TopCat.Sheaf.pushforward C (closedIncl hs)).Full := by
    simpa [TopCat.Sheaf.pushforward] using
      (CategoryTheory.Functor.IsCoverDense.full_sheafPushforwardContinuous
        (J := Opens.grothendieckTopology X)
        (K := Opens.grothendieckTopology (TopCat.of s))
        (G := Opens.map (closedIncl hs)) :
          ((Opens.map (closedIncl hs)).sheafPushforwardContinuous
            C (Opens.grothendieckTopology X)
            (Opens.grothendieckTopology (TopCat.of s))).Full)
  haveI : (TopCat.Sheaf.pushforward C (closedIncl hs)).Faithful := by
    simpa [TopCat.Sheaf.pushforward] using
      (CategoryTheory.Functor.IsCoverDense.faithful_sheafPushforwardContinuous
        (J := Opens.grothendieckTopology X)
        (K := Opens.grothendieckTopology (TopCat.of s))
        (G := Opens.map (closedIncl hs)) :
          ((Opens.map (closedIncl hs)).sheafPushforwardContinuous
            C (Opens.grothendieckTopology X)
            (Opens.grothendieckTopology (TopCat.of s))).Faithful)
  infer_instance

theorem closedIncl_counit_isIso
    {C : Type*} [Category.{u} C]
    {FC : C → C → Type*} {CC : C → Type u}
    [∀ (X Y : C), FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (forget C)]
    [PreservesFilteredColimits (forget C)]
    [(forget C).ReflectsIsomorphisms]
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    (F : TopCat.Sheaf C (TopCat.of s)) :
    IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction C (closedIncl hs)).counit.app F) := by
  simpa using
    (closedIncl_counit_isIso_presheaf (C := C) (hs := hs) (F := F.val) F.cond)

-- Stalk pullback hom naturality
lemma stalkPullbackHom_naturality
    {C : Type*} [Category C] [HasColimits C]
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    {F G : Y.Presheaf C} (α : F ⟶ G) (x : ↑X) :
    (Presheaf.stalkFunctor C (ConcreteCategory.hom f x)).map α ≫
      Presheaf.stalkPullbackHom C f G x =
    Presheaf.stalkPullbackHom C f F x ≫
      (Presheaf.stalkFunctor C x).map
        ((Presheaf.pullback C f).map α) := by
  apply Presheaf.stalk_hom_ext; intro U hU
  simp only [Presheaf.stalkFunctor_map_germ_assoc, Presheaf.germ_stalkPullbackHom,
    Presheaf.germ_stalkPullbackHom_assoc, Presheaf.stalkFunctor_map_germ]
  have key : α.app (Opposite.op U) ≫
      ((Presheaf.pushforwardPullbackAdjunction C f).unit.app G).app (Opposite.op U) =
    ((Presheaf.pushforwardPullbackAdjunction C f).unit.app F).app (Opposite.op U) ≫
      ((Presheaf.pullback C f).map α).app
        (Opposite.op ((TopologicalSpace.Opens.map f).obj U)) := by
    have h := congr_arg (fun β => NatTrans.app β (Opposite.op U))
      ((Presheaf.pushforwardPullbackAdjunction C f).unit.naturality α)
    simpa only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] using h
  rw [← CategoryTheory.Category.assoc, key, CategoryTheory.Category.assoc]

-- Unit stalk is iso for closed immersions.
-- Proof chain: triangle identity → pullback.map(η) iso → pullbackIso naturality
-- → toSheafify naturality → stalkPullbackHom_naturality → η stalk iso
theorem closedIncl_unit_stalk_isIso
    {C : Type*} [Category.{u} C]
    {FC : C → C → Type*} {CC : C → Type u}
    [∀ (X Y : C), FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC]
    [HasColimits C] [HasLimits C]
    [PreservesLimits (forget C)]
    [PreservesFilteredColimits (forget C)]
    [(forget C).ReflectsIsomorphisms]
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    {F : TopCat.Presheaf C X} (hF : F.IsSheaf) (x : TopCat.of s) :
    IsIso ((Presheaf.stalkFunctor C ((closedIncl hs) x)).map
      ((Sheaf.pullbackPushforwardAdjunction C (closedIncl hs)).unit.app
        (⟨F, hF⟩ : TopCat.Sheaf C X)).val) := by
  let Fsh : TopCat.Sheaf C X := ⟨F, hF⟩
  -- Use the triangle identity + counit iso
  let adj := Sheaf.pullbackPushforwardAdjunction C (closedIncl hs)
  let pb := Sheaf.pullback C (closedIncl hs)
  let η := adj.unit.app Fsh
  haveI : IsIso (adj.counit.app (pb.obj Fsh)) := by
    simpa using
      (closedIncl_counit_isIso_presheaf (C := C) (hs := hs)
        (F := (pb.obj Fsh).val) (pb.obj Fsh).cond)
  haveI : IsIso (pb.map η) := by
    have htri : pb.map η ≫ adj.counit.app (pb.obj Fsh) = 𝟙 _ :=
      adj.left_triangle_components Fsh
    rw [show pb.map η = inv (adj.counit.app (pb.obj Fsh)) from by
      apply (cancel_mono (adj.counit.app (pb.obj Fsh))).mp; simp [htri]]
    infer_instance
  -- Step 2: val stalk of pb.map(η) is iso
  haveI : IsIso (pb.map η).val := by
    show IsIso (sheafToPresheaf _ _ |>.map (pb.map η)); infer_instance
  let Tz := Presheaf.stalkFunctor C x
  -- Step 3: pullbackIso naturality
  let pi := Sheaf.pullbackIso C (closedIncl hs)
  let piF := pi.hom.app Fsh
  let piT := pi.hom.app ((Sheaf.pushforward C (closedIncl hs)).obj (pb.obj Fsh))
  haveI : IsIso piF.val := by show IsIso ((sheafToPresheaf _ _).map piF); infer_instance
  haveI : IsIso piT.val := by show IsIso ((sheafToPresheaf _ _).map piT); infer_instance
  have hnat : (pb.map η).val ≫ piT.val = piF.val ≫
      (presheafToSheaf _ _ |>.map ((Presheaf.pullback C (closedIncl hs)).map η.val)).val :=
    congr_arg Sheaf.Hom.val (pi.hom.naturality η)
  have hnat_stalk := congr_arg Tz.map hnat
  simp only [Functor.map_comp] at hnat_stalk
  -- Step 4: presheafToSheaf.map(pull.map(η.val)).val stalk is iso
  haveI : IsIso (Tz.map
      (presheafToSheaf _ _ |>.map ((Presheaf.pullback C (closedIncl hs)).map η.val)).val) :=
    IsIso.of_isIso_fac_left hnat_stalk.symm
  -- Step 5: toSheafify naturality → pull.map(η.val) stalk is iso
  let K := Opens.grothendieckTopology (TopCat.of s)
  let P₁ := (Presheaf.pullback C (closedIncl hs)).obj F
  let P₂ := (Presheaf.pullback C (closedIncl hs)).obj
    ((Sheaf.pushforward C (closedIncl hs)).obj (pb.obj Fsh)).val
  have hts : Tz.map ((Presheaf.pullback C (closedIncl hs)).map η.val) ≫
      Tz.map (CategoryTheory.toSheafify K P₂) =
    Tz.map (CategoryTheory.toSheafify K P₁) ≫ Tz.map
      (presheafToSheaf K C |>.map
        ((Presheaf.pullback C (closedIncl hs)).map η.val)).val := by
    rw [← Functor.map_comp, ← Functor.map_comp]; congr 1
    exact CategoryTheory.toSheafify_naturality K _
  haveI : IsIso (Tz.map (CategoryTheory.toSheafify K P₁)) := stalkFunctor_map_iso_toSheafify P₁ x
  haveI : IsIso (Tz.map (CategoryTheory.toSheafify K P₂)) := stalkFunctor_map_iso_toSheafify P₂ x
  haveI : IsIso (Tz.map ((Presheaf.pullback C (closedIncl hs)).map η.val)) :=
    IsIso.of_isIso_fac_right hts
  -- Step 6: stalkPull_nat → η.val stalk is iso
  haveI : IsIso (Presheaf.stalkPullbackHom C (closedIncl hs)
      ((𝟭 (Sheaf C X)).obj Fsh).val x) := by
    simpa using
      (Presheaf.stalkPullbackIso C (closedIncl hs) ((𝟭 (Sheaf C X)).obj Fsh).val x).isIso_hom
  haveI : IsIso (Presheaf.stalkPullbackHom C (closedIncl hs)
      ((pb ⋙ Sheaf.pushforward C (closedIncl hs)).obj Fsh).val x) :=
    (Presheaf.stalkPullbackIso C (closedIncl hs)
      ((pb ⋙ Sheaf.pushforward C (closedIncl hs)).obj Fsh).val x).isIso_hom
  exact IsIso.of_isIso_fac_right (stalkPullbackHom_naturality (closedIncl hs) η.val x)

end TopCat
