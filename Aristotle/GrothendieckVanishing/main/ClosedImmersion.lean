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

noncomputable section

namespace TopCat

/-- Closed inclusion `s ↪ X` as a morphism in `TopCat`. -/
def closedIncl {X : TopCat.{u}} {s : Set X} (hs : IsClosed s) : TopCat.of s ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, hs.isClosedEmbedding_subtypeVal.continuous⟩

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

theorem closedIncl_presheaf_counit_stalk_comp
    {C : Type*} [Category C] [HasColimits C]
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    (F : TopCat.Presheaf C (TopCat.of s)) (x : TopCat.of s) :
    (TopCat.Presheaf.stalkPullbackIso C (closedIncl hs)
      ((TopCat.Presheaf.pushforward C (closedIncl hs)).obj F) x).hom ≫
      (TopCat.Presheaf.stalkFunctor C x).map
        ((TopCat.Presheaf.pushforwardPullbackAdjunction C
          (closedIncl hs)).counit.app F) =
      F.stalkPushforward C (closedIncl hs) x := by
  apply TopCat.Presheaf.stalk_hom_ext; intro U hU
  change ((TopCat.Presheaf.pushforward C (closedIncl hs)).obj F).germ U
      ((closedIncl hs) x) hU ≫
        TopCat.Presheaf.stalkPullbackHom C (closedIncl hs)
          ((TopCat.Presheaf.pushforward C (closedIncl hs)).obj F) x ≫
        (TopCat.Presheaf.stalkFunctor C x).map
          ((TopCat.Presheaf.pushforwardPullbackAdjunction C
            (closedIncl hs)).counit.app F) =
      ((TopCat.Presheaf.pushforward C (closedIncl hs)).obj F).germ U
        ((closedIncl hs) x) hU ≫ F.stalkPushforward C (closedIncl hs) x
  rw [TopCat.Presheaf.germ_stalkPullbackHom_assoc, TopCat.Presheaf.stalkFunctor_map_germ,
    TopCat.Presheaf.stalkPushforward_germ]
  have htri :=
    CategoryTheory.Functor.lanUnit_app_app_lanAdjunction_counit_app_app
      ((TopologicalSpace.Opens.map (closedIncl hs)).op) F (op U)
  have htri' :
      ((TopCat.Presheaf.pushforwardPullbackAdjunction C (closedIncl hs)).unit.app
            ((TopCat.Presheaf.pushforward C (closedIncl hs)).obj F)).app (op U) ≫
        ((TopCat.Presheaf.pushforwardPullbackAdjunction C
            (closedIncl hs)).counit.app F).app
          (op ((Opens.map (closedIncl hs)).obj U)) =
      𝟙 (F.obj (op ((Opens.map (closedIncl hs)).obj U))) := by
    simpa [TopCat.Presheaf.pushforwardPullbackAdjunction, TopCat.Presheaf.pushforward] using htri
  rw [← Category.assoc, htri']; simp

private theorem closedIncl_counit_val_eq_sheafifyLift
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
    let K := Opens.grothendieckTopology (TopCat.of s)
    let _ : (Opens.map (closedIncl hs)).IsContinuous (Opens.grothendieckTopology X) K :=
      Functor.isContinuous_of_coverPreserving
        (compatiblePreserving_opens_map (closedIncl hs))
        (coverPreserving_opens_map (closedIncl hs))
    (((CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (G := Opens.map (closedIncl hs)) C
        (Opens.grothendieckTopology X) K).counit.app F).val) =
      CategoryTheory.sheafifyLift K
        ((TopCat.Presheaf.pushforwardPullbackAdjunction C (closedIncl hs)).counit.app F.val)
        F.cond := by
  intro K _
  let P : (TopCat.of s).Presheaf C :=
    (TopCat.Presheaf.pullback C (closedIncl hs)).obj
      ((TopCat.Presheaf.pushforward C (closedIncl hs)).obj F.val)
  let η := (TopCat.Presheaf.pushforwardPullbackAdjunction C (closedIncl hs)).counit.app F.val
  let Q := ((Opens.map (closedIncl hs)).sheafPushforwardContinuous C
      (Opens.grothendieckTopology X) K).obj F
  let adj₀ := (((Opens.map (closedIncl hs)).op.lanAdjunction C).comp
      (CategoryTheory.sheafificationAdjunction K C))
  have hraw :=
    CategoryTheory.Adjunction.map_restrictFullyFaithful_counit_app
      (adj := adj₀)
      (hiC := fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) C)
      (hiD := Functor.FullyFaithful.id _)
      (L := CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback
        (Opens.map (closedIncl hs)) C (Opens.grothendieckTopology X) K)
      (R := (Opens.map (closedIncl hs)).sheafPushforwardContinuous
        C (Opens.grothendieckTopology X) K)
      (comm1 := Iso.refl _)
      (comm2 := Iso.refl _)
      F
  apply CategoryTheory.sheafifyLift_unique
  have hcomp := congrArg (fun f => CategoryTheory.toSheafify K P ≫ f.val) hraw
  have hcomp' :
      CategoryTheory.toSheafify K P ≫
          (((CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (G := Opens.map (closedIncl hs)) C
              (Opens.grothendieckTopology X) K).counit.app F).val) =
        CategoryTheory.toSheafify K P ≫
          (𝟙 ((CategoryTheory.presheafToSheaf K C).obj
            ((Opens.map (closedIncl hs)).op.lan.obj Q.val)).val) ≫
          CategoryTheory.sheafifyLift K
            (((Opens.map (closedIncl hs)).op.lan.map
                (𝟙 ((Opens.map (closedIncl hs)).op ⋙ F.val))) ≫
              ((Opens.map (closedIncl hs)).op.lanAdjunction C).counit.app F.val)
            F.cond := by
    simpa [adj₀, Q, P, TopCat.Presheaf.pushforward, TopCat.Sheaf.pushforward,
      CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
      CategoryTheory.Adjunction.comp_counit_app,
      CategoryTheory.sheafificationAdjunction_counit_app_val,
      CategoryTheory.sheafifyMap_sheafifyLift, Category.id_comp, Category.comp_id] using hcomp
  have hlan_id :
      (Opens.map (closedIncl hs)).op.lan.map (𝟙 ((Opens.map (closedIncl hs)).op ⋙ F.val)) =
        𝟙 ((Opens.map (closedIncl hs)).op.lan.obj ((Opens.map (closedIncl hs)).op ⋙ F.val)) := by
    simp
  calc
    CategoryTheory.toSheafify K P ≫
        (((CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (G := Opens.map (closedIncl hs)) C
            (Opens.grothendieckTopology X) K).counit.app F).val) =
      CategoryTheory.toSheafify K P ≫
        (𝟙 ((CategoryTheory.presheafToSheaf K C).obj
          ((Opens.map (closedIncl hs)).op.lan.obj Q.val)).val) ≫
        CategoryTheory.sheafifyLift K
          (((Opens.map (closedIncl hs)).op.lan.map
              (𝟙 ((Opens.map (closedIncl hs)).op ⋙ F.val))) ≫
            ((Opens.map (closedIncl hs)).op.lanAdjunction C).counit.app F.val)
          F.cond := hcomp'
    _ =
      ((Opens.map (closedIncl hs)).op.lan.map (𝟙 ((Opens.map (closedIncl hs)).op ⋙ F.val))) ≫
        ((Opens.map (closedIncl hs)).op.lanAdjunction C).counit.app F.val := by
        erw [Category.id_comp]
        exact CategoryTheory.toSheafify_sheafifyLift K
            (((Opens.map (closedIncl hs)).op.lan.map
                (𝟙 ((Opens.map (closedIncl hs)).op ⋙ F.val))) ≫
              ((Opens.map (closedIncl hs)).op.lanAdjunction C).counit.app F.val)
            F.cond
    _ =
      ((Opens.map (closedIncl hs)).op.lanAdjunction C).counit.app F.val := by
        rw [hlan_id, Category.id_comp]
    _ = η := by
        simp [η, TopCat.Presheaf.pushforwardPullbackAdjunction, TopCat.Presheaf.pullback]

private theorem closedIncl_sheafAdj_counit_isIso
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
    let K := Opens.grothendieckTopology (TopCat.of s)
    let _ : (Opens.map (closedIncl hs)).IsContinuous (Opens.grothendieckTopology X) K :=
      Functor.isContinuous_of_coverPreserving
        (compatiblePreserving_opens_map (closedIncl hs))
        (coverPreserving_opens_map (closedIncl hs))
    IsIso ((CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (G := Opens.map (closedIncl hs)) C
      (Opens.grothendieckTopology X) K).counit.app F) := by
  intro K _
  haveI : HasWeakSheafify K C := inferInstance
  haveI : K.WEqualsLocallyBijective C := inferInstance
  let P : (TopCat.of s).Presheaf C :=
    (TopCat.Presheaf.pullback C (closedIncl hs)).obj
      ((TopCat.Presheaf.pushforward C (closedIncl hs)).obj F.val)
  let η := (TopCat.Presheaf.pushforwardPullbackAdjunction C (closedIncl hs)).counit.app F.val
  have hval := closedIncl_counit_val_eq_sheafifyLift hs F
  have hstalk :
      ∀ x : TopCat.of s,
        IsIso ((TopCat.Presheaf.stalkFunctor C x).map
          ((CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (G := Opens.map (closedIncl hs)) C
            (Opens.grothendieckTopology X) K).counit.app F).val) := by
    intro x; rw [hval]
    let T := TopCat.Presheaf.stalkFunctor (X := TopCat.of s) C x
    have hcomp0 :
        CategoryTheory.toSheafify K P ≫ CategoryTheory.sheafifyLift K η F.cond = η :=
      CategoryTheory.toSheafify_sheafifyLift K η F.cond
    haveI : IsIso (T.map (CategoryTheory.toSheafify K P)) :=
      stalkFunctor_map_iso_toSheafify P x
    haveI : IsIso (T.map η) := by
      dsimp [η]
      let e :=
        TopCat.Presheaf.stalkPullbackIso C (closedIncl hs)
          ((TopCat.Presheaf.pushforward C (closedIncl hs)).obj F.val) x
      have hη_eq :
          T.map ((TopCat.Presheaf.pushforwardPullbackAdjunction C
            (closedIncl hs)).counit.app F.val) =
            e.inv ≫ TopCat.Presheaf.stalkPushforward C
              (closedIncl hs) F.val x := by
        conv_lhs => rw [← e.inv_hom_id_assoc (T.map _)]
        rw [closedIncl_presheaf_counit_stalk_comp hs F.val x]
      rw [hη_eq]
      haveI := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        (f := closedIncl hs) C hs.isClosedEmbedding_subtypeVal.isInducing F.val x
      infer_instance
    have hsheafifyLift_eq :
        T.map (CategoryTheory.sheafifyLift K η F.cond) =
          inv (T.map (CategoryTheory.toSheafify K P)) ≫ T.map η := by
      conv_lhs => rw [← IsIso.inv_hom_id_assoc (T.map (CategoryTheory.toSheafify K P))
        (T.map (CategoryTheory.sheafifyLift K η F.cond))]
      rw [← Functor.map_comp, hcomp0]
    rw [hsheafifyLift_eq]; infer_instance
  letI (x : TopCat.of s) := hstalk x
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
    (f := (CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (G := Opens.map (closedIncl hs)) C
      (Opens.grothendieckTopology X) K).counit.app F)

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
  let K := Opens.grothendieckTopology (TopCat.of s)
  let _ : (Opens.map (closedIncl hs)).IsContinuous (Opens.grothendieckTopology X) K :=
    Functor.isContinuous_of_coverPreserving
      (compatiblePreserving_opens_map (closedIncl hs))
      (coverPreserving_opens_map (closedIncl hs))
  haveI := closedIncl_sheafAdj_counit_isIso hs F
  have hcompare :
      (TopCat.Sheaf.pullbackIso C (closedIncl hs)).hom.app
          ((TopCat.Sheaf.pushforward C (closedIncl hs)).obj F) ≫
        (CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (G := Opens.map (closedIncl hs)) C
          (Opens.grothendieckTopology X) K).counit.app F =
      (TopCat.Sheaf.pullbackPushforwardAdjunction C (closedIncl hs)).counit.app F := by
    convert
      (CategoryTheory.Adjunction.leftAdjointUniq_hom_app_counit
        (TopCat.Sheaf.pullbackPushforwardAdjunction C (closedIncl hs))
        (CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (G := Opens.map (closedIncl hs)) C
          (Opens.grothendieckTopology X) K) F) using 1
  rw [← hcompare]; infer_instance

-- Stalk pullback hom naturality
private lemma stalkPull_nat
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
-- → toSheafify naturality → stalkPull_nat → η stalk iso
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
    (F : TopCat.Sheaf C X) (x : TopCat.of s) :
    IsIso ((Presheaf.stalkFunctor C ((closedIncl hs) x)).map
      ((Sheaf.pullbackPushforwardAdjunction C (closedIncl hs)).unit.app F).val) := by
  -- Use the triangle identity + counit iso
  let adj := Sheaf.pullbackPushforwardAdjunction C (closedIncl hs)
  let pb := Sheaf.pullback C (closedIncl hs)
  let η := adj.unit.app F
  haveI : IsIso (adj.counit.app (pb.obj F)) := closedIncl_counit_isIso hs (pb.obj F)
  haveI : IsIso (pb.map η) := by
    have htri : pb.map η ≫ adj.counit.app (pb.obj F) = 𝟙 _ := adj.left_triangle_components F
    rw [show pb.map η = inv (adj.counit.app (pb.obj F)) from by
      apply (cancel_mono (adj.counit.app (pb.obj F))).mp; simp [htri]]; infer_instance
  -- Step 2: val stalk of pb.map(η) is iso
  haveI : IsIso (pb.map η).val := by
    show IsIso (sheafToPresheaf _ _ |>.map (pb.map η)); infer_instance
  let Tz := Presheaf.stalkFunctor C x
  -- Step 3: pullbackIso naturality
  let pi := Sheaf.pullbackIso C (closedIncl hs)
  let piF := pi.hom.app F
  let piT := pi.hom.app ((Sheaf.pushforward C (closedIncl hs)).obj (pb.obj F))
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
  let P₁ := (Presheaf.pullback C (closedIncl hs)).obj F.val
  let P₂ := (Presheaf.pullback C (closedIncl hs)).obj
    ((Sheaf.pushforward C (closedIncl hs)).obj (pb.obj F)).val
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
      ((𝟭 _).obj F).val x) :=
    (Presheaf.stalkPullbackIso C (closedIncl hs) ((𝟭 _).obj F).val x).isIso_hom
  haveI : IsIso (Presheaf.stalkPullbackHom C (closedIncl hs)
      ((pb ⋙ Sheaf.pushforward C (closedIncl hs)).obj F).val x) :=
    (Presheaf.stalkPullbackIso C (closedIncl hs)
      ((pb ⋙ Sheaf.pushforward C (closedIncl hs)).obj F).val x).isIso_hom
  exact IsIso.of_isIso_fac_right (stalkPull_nat (closedIncl hs) η.val x)

end TopCat
