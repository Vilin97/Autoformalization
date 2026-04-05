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
    {X : TopCat.{u}} {F G : X.Presheaf AddCommGrpCat} (T : F ⟶ G)
    [CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) T] :
    ∀ x : X, Function.Injective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map T) := by
  intro x s t hst
  obtain ⟨U, hxU, sU, rfl⟩ := F.germ_exist x s
  obtain ⟨V, hxV, sV, hsV⟩ := F.germ_exist x t
  rw [← hsV] at hst ⊢
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, TopCat.Presheaf.stalkFunctor_map_germ_apply] at hst
  obtain ⟨W, hxW, iWU, iWV, hEq⟩ := G.germ_eq x hxU hxV _ _ hst
  have hnat (Y : Opens X) (iWY : W ⟶ Y) (sY : F.obj (op Y)) :
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

theorem closedIncl_presheaf_counit_stalk_comp
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    (F : TopCat.Presheaf AddCommGrpCat (TopCat.of s)) (x : TopCat.of s) :
    (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat (closedIncl hs)
      ((TopCat.Presheaf.pushforward AddCommGrpCat (closedIncl hs)).obj F) x).hom ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((TopCat.Presheaf.pushforwardPullbackAdjunction AddCommGrpCat
          (closedIncl hs)).counit.app F) =
      F.stalkPushforward AddCommGrpCat (closedIncl hs) x := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hU
  change ((TopCat.Presheaf.pushforward AddCommGrpCat (closedIncl hs)).obj F).germ U
      ((closedIncl hs) x) hU ≫
        TopCat.Presheaf.stalkPullbackHom AddCommGrpCat (closedIncl hs)
          ((TopCat.Presheaf.pushforward AddCommGrpCat (closedIncl hs)).obj F) x ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((TopCat.Presheaf.pushforwardPullbackAdjunction AddCommGrpCat
            (closedIncl hs)).counit.app F) =
      ((TopCat.Presheaf.pushforward AddCommGrpCat (closedIncl hs)).obj F).germ U
        ((closedIncl hs) x) hU ≫ F.stalkPushforward AddCommGrpCat (closedIncl hs) x
  rw [TopCat.Presheaf.germ_stalkPullbackHom_assoc]
  rw [TopCat.Presheaf.stalkFunctor_map_germ]
  rw [TopCat.Presheaf.stalkPushforward_germ]
  have htri :=
    CategoryTheory.Functor.lanUnit_app_app_lanAdjunction_counit_app_app
      ((TopologicalSpace.Opens.map (closedIncl hs)).op) F (op U)
  have htri' :
      ((TopCat.Presheaf.pushforwardPullbackAdjunction AddCommGrpCat (closedIncl hs)).unit.app
            ((TopCat.Presheaf.pushforward AddCommGrpCat (closedIncl hs)).obj F)).app (op U) ≫
        ((TopCat.Presheaf.pushforwardPullbackAdjunction AddCommGrpCat
            (closedIncl hs)).counit.app F).app
          (op ((Opens.map (closedIncl hs)).obj U)) =
      𝟙 (F.obj (op ((Opens.map (closedIncl hs)).obj U))) := by
    simpa [TopCat.Presheaf.pushforwardPullbackAdjunction, TopCat.Presheaf.pushforward] using htri
  rw [← Category.assoc, htri']; simp

theorem closedIncl_counit_isIso
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    (F : TopCat.Sheaf AddCommGrpCat (TopCat.of s)) :
    IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat (closedIncl hs)).counit.app F) := by
  let K := Opens.grothendieckTopology (TopCat.of s)
  let _ :
      (Opens.map (closedIncl hs)).IsContinuous (Opens.grothendieckTopology X) K :=
    Functor.isContinuous_of_coverPreserving
      (compatiblePreserving_opens_map (closedIncl hs))
      (coverPreserving_opens_map (closedIncl hs))
  let P :=
    (TopCat.Presheaf.pullback AddCommGrpCat (closedIncl hs)).obj
      ((TopCat.Presheaf.pushforward AddCommGrpCat (closedIncl hs)).obj F.val)
  let η :=
    (TopCat.Presheaf.pushforwardPullbackAdjunction AddCommGrpCat (closedIncl hs)).counit.app F.val
  have hval :
      (((CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (G := Opens.map (closedIncl hs)) AddCommGrpCat
          (Opens.grothendieckTopology X) K).counit.app F).val) =
        CategoryTheory.sheafifyLift K η F.cond := by
    let Q :=
      ((Opens.map (closedIncl hs)).sheafPushforwardContinuous AddCommGrpCat
        (Opens.grothendieckTopology X) K).obj F
    let adj₀ :=
      (((Opens.map (closedIncl hs)).op.lanAdjunction AddCommGrpCat).comp
        (CategoryTheory.sheafificationAdjunction K AddCommGrpCat))
    have hraw :=
      CategoryTheory.Adjunction.map_restrictFullyFaithful_counit_app
        (adj := adj₀)
        (hiC := fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat)
        (hiD := Functor.FullyFaithful.id _)
        (L := CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback
          (Opens.map (closedIncl hs)) AddCommGrpCat (Opens.grothendieckTopology X) K)
        (R := (Opens.map (closedIncl hs)).sheafPushforwardContinuous
          AddCommGrpCat (Opens.grothendieckTopology X) K)
        (comm1 := Iso.refl _)
        (comm2 := Iso.refl _)
        F
    apply CategoryTheory.sheafifyLift_unique
    have hcomp :=
      congrArg (fun f => CategoryTheory.toSheafify K P ≫ f.val) hraw
    have hcomp' :
        CategoryTheory.toSheafify K P ≫
            (((CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                (G := Opens.map (closedIncl hs)) AddCommGrpCat
                (Opens.grothendieckTopology X) K).counit.app F).val) =
          CategoryTheory.toSheafify K P ≫
            (𝟙 ((CategoryTheory.presheafToSheaf K AddCommGrpCat).obj
              ((Opens.map (closedIncl hs)).op.lan.obj Q.val)).val) ≫
            CategoryTheory.sheafifyLift K
              (((Opens.map (closedIncl hs)).op.lan.map
                  (𝟙 ((Opens.map (closedIncl hs)).op ⋙ F.val))) ≫
                ((Opens.map (closedIncl hs)).op.lanAdjunction AddCommGrpCat).counit.app F.val)
              F.cond := by
      simpa [adj₀, Q, P, TopCat.Presheaf.pushforward, TopCat.Sheaf.pushforward,
        CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
        CategoryTheory.Adjunction.comp_counit_app,
        CategoryTheory.sheafificationAdjunction_counit_app_val,
        CategoryTheory.sheafifyMap_sheafifyLift, Category.id_comp, Category.comp_id] using hcomp
    have hlan_id :
        (Opens.map (closedIncl hs)).op.lan.map (𝟙 ((Opens.map (closedIncl hs)).op ⋙ F.val)) =
          𝟙 ((Opens.map (closedIncl hs)).op.lan.obj ((Opens.map (closedIncl hs)).op ⋙ F.val)) := by
      simp [Functor.map_id]
    calc
      CategoryTheory.toSheafify K P ≫
          (((CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (G := Opens.map (closedIncl hs)) AddCommGrpCat
              (Opens.grothendieckTopology X) K).counit.app F).val) =
        CategoryTheory.toSheafify K P ≫
          (𝟙 ((CategoryTheory.presheafToSheaf K AddCommGrpCat).obj
            ((Opens.map (closedIncl hs)).op.lan.obj Q.val)).val) ≫
          CategoryTheory.sheafifyLift K
            (((Opens.map (closedIncl hs)).op.lan.map
                (𝟙 ((Opens.map (closedIncl hs)).op ⋙ F.val))) ≫
              ((Opens.map (closedIncl hs)).op.lanAdjunction AddCommGrpCat).counit.app F.val)
            F.cond := hcomp'
      _ =
        ((Opens.map (closedIncl hs)).op.lan.map (𝟙 ((Opens.map (closedIncl hs)).op ⋙ F.val))) ≫
          ((Opens.map (closedIncl hs)).op.lanAdjunction AddCommGrpCat).counit.app F.val := by
          convert
            (CategoryTheory.toSheafify_sheafifyLift K
              (((Opens.map (closedIncl hs)).op.lan.map
                  (𝟙 ((Opens.map (closedIncl hs)).op ⋙ F.val))) ≫
                ((Opens.map (closedIncl hs)).op.lanAdjunction AddCommGrpCat).counit.app F.val)
              F.cond) using 1
      _ =
        ((Opens.map (closedIncl hs)).op.lanAdjunction AddCommGrpCat).counit.app F.val := by
          rw [hlan_id, Category.id_comp]
      _ = η := by
          simp [η, Q, TopCat.Presheaf.pushforwardPullbackAdjunction, TopCat.Presheaf.pullback,
            Functor.map_id]
  have hconstructed :
      IsIso ((CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (G := Opens.map (closedIncl hs)) AddCommGrpCat
        (Opens.grothendieckTopology X) K).counit.app F) := by
    have hstalk :
        ∀ x : TopCat.of s,
          IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
            ((CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (G := Opens.map (closedIncl hs)) AddCommGrpCat
              (Opens.grothendieckTopology X) K).counit.app F).val) := by
      intro x
      rw [hval]
      let T := TopCat.Presheaf.stalkFunctor (X := TopCat.of s) AddCommGrpCat x
      have hcomp0 :
          CategoryTheory.toSheafify K P ≫ CategoryTheory.sheafifyLift K η F.cond = η := by
        simp [P, CategoryTheory.toSheafify_sheafifyLift K η F.cond]
      haveI :
          IsIso (T.map (CategoryTheory.toSheafify K P)) :=
        stalkFunctor_map_iso_toSheafify P x
      haveI : IsIso (T.map η) := by
        dsimp [η]
        let e :=
          TopCat.Presheaf.stalkPullbackIso AddCommGrpCat (closedIncl hs)
            ((TopCat.Presheaf.pushforward AddCommGrpCat (closedIncl hs)).obj F.val) x
        have hη_eq :
            T.map ((TopCat.Presheaf.pushforwardPullbackAdjunction AddCommGrpCat
              (closedIncl hs)).counit.app F.val) =
              e.inv ≫ TopCat.Presheaf.stalkPushforward AddCommGrpCat
                (closedIncl hs) F.val x := by
          conv_lhs => rw [← e.inv_hom_id_assoc (T.map _)]
          rw [closedIncl_presheaf_counit_stalk_comp hs F.val x]
        rw [hη_eq]
        haveI := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
          (f := closedIncl hs) AddCommGrpCat hs.isClosedEmbedding_subtypeVal.isInducing F.val x
        infer_instance
      have hsheafifyLift_eq :
          T.map (CategoryTheory.sheafifyLift K η F.cond) =
            inv (T.map (CategoryTheory.toSheafify K P)) ≫ T.map η := by
        conv_lhs => rw [← IsIso.inv_hom_id_assoc (T.map (CategoryTheory.toSheafify K P))
          (T.map (CategoryTheory.sheafifyLift K η F.cond))]
        rw [← Functor.map_comp, hcomp0]
      rw [hsheafifyLift_eq]
      infer_instance
    letI (x : TopCat.of s) := hstalk x
    exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
      (f := (CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (G := Opens.map (closedIncl hs)) AddCommGrpCat
        (Opens.grothendieckTopology X) K).counit.app F)
  have hcompare :
      (TopCat.Sheaf.pullbackIso AddCommGrpCat (closedIncl hs)).hom.app
          ((TopCat.Sheaf.pushforward AddCommGrpCat (closedIncl hs)).obj F) ≫
        (CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (G := Opens.map (closedIncl hs)) AddCommGrpCat
          (Opens.grothendieckTopology X) K).counit.app F =
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat (closedIncl hs)).counit.app F := by
    convert
      (CategoryTheory.Adjunction.leftAdjointUniq_hom_app_counit
        (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat (closedIncl hs))
        (CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (G := Opens.map (closedIncl hs)) AddCommGrpCat
          (Opens.grothendieckTopology X) K) F) using 1
  rw [← hcompare]
  infer_instance

private lemma isIso_left {C : Type*} [CategoryTheory.Category C] {A B D : C}
    {f : A ⟶ B} {g : B ⟶ D} {h : A ⟶ D} [CategoryTheory.IsIso g] [CategoryTheory.IsIso h]
    (e : f ≫ g = h) : CategoryTheory.IsIso f := by
  rw [show f = h ≫ CategoryTheory.inv g from by simp [← e]]; infer_instance

private lemma isIso_right {C : Type*} [CategoryTheory.Category C] {A B D : C}
    {f : A ⟶ B} {g : B ⟶ D} {h : A ⟶ D} [CategoryTheory.IsIso f] [CategoryTheory.IsIso h]
    (e : f ≫ g = h) : CategoryTheory.IsIso g := by
  rw [show g = CategoryTheory.inv f ≫ h from by simp [← e]]; infer_instance

-- Stalk pullback hom naturality
private lemma stalkPull_nat {X Y : TopCat.{u}} (f : X ⟶ Y)
    {F G : Y.Presheaf AddCommGrpCat.{u}} (α : F ⟶ G) (x : ↑X) :
    (Presheaf.stalkFunctor AddCommGrpCat.{u} (ConcreteCategory.hom f x)).map α ≫
      Presheaf.stalkPullbackHom AddCommGrpCat f G x =
    Presheaf.stalkPullbackHom AddCommGrpCat f F x ≫
      (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((Presheaf.pullback AddCommGrpCat f).map α) := by
  apply Presheaf.stalk_hom_ext; intro U hU
  simp only [Presheaf.stalkFunctor_map_germ_assoc, Presheaf.germ_stalkPullbackHom,
    Presheaf.germ_stalkPullbackHom_assoc, Presheaf.stalkFunctor_map_germ]
  have key : α.app (Opposite.op U) ≫
      ((Presheaf.pushforwardPullbackAdjunction AddCommGrpCat f).unit.app G).app (Opposite.op U) =
    ((Presheaf.pushforwardPullbackAdjunction AddCommGrpCat f).unit.app F).app (Opposite.op U) ≫
      ((Presheaf.pullback AddCommGrpCat f).map α).app
        (Opposite.op ((TopologicalSpace.Opens.map f).obj U)) := by
    have h := congr_arg (fun β => NatTrans.app β (Opposite.op U))
      ((Presheaf.pushforwardPullbackAdjunction AddCommGrpCat f).unit.naturality α)
    simp only [CategoryTheory.Functor.id_obj, CategoryTheory.Functor.id_map,
      CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.comp_map] at h
    exact h
  rw [← CategoryTheory.Category.assoc, key, CategoryTheory.Category.assoc]

-- Unit stalk is iso for closed immersions.
-- Proof chain: triangle identity → pullback.map(η) iso → pullbackIso naturality
-- → toSheafify naturality → stalkPull_nat → η stalk iso
theorem closedIncl_unit_stalk_isIso
    {X : TopCat.{u}} {s : Set X} (hs : IsClosed s)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (x : TopCat.of s) :
    IsIso ((Presheaf.stalkFunctor AddCommGrpCat.{u} ((closedIncl hs) x)).map
      ((Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (closedIncl hs)).unit.app F).val) := by
  -- Use the triangle identity + counit iso
  let adj := Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (closedIncl hs)
  let pb := Sheaf.pullback AddCommGrpCat.{u} (closedIncl hs)
  let η := adj.unit.app F
  haveI : IsIso (adj.counit.app (pb.obj F)) := closedIncl_counit_isIso hs (pb.obj F)
  haveI : IsIso (pb.map η) := by
    have htri : pb.map η ≫ adj.counit.app (pb.obj F) = 𝟙 _ := adj.left_triangle_components F
    rw [show pb.map η = inv (adj.counit.app (pb.obj F)) from by
      apply (cancel_mono (adj.counit.app (pb.obj F))).mp; simp [htri]]
    infer_instance
  -- Step 2: val stalk of pb.map(η) is iso
  haveI : IsIso (pb.map η).val := by
    show IsIso (sheafToPresheaf _ _ |>.map (pb.map η)); infer_instance
  let Tz := Presheaf.stalkFunctor AddCommGrpCat.{u} x
  haveI : IsIso (Tz.map (pb.map η).val) := inferInstance
  -- Step 3: pullbackIso naturality
  let pi := Sheaf.pullbackIso AddCommGrpCat.{u} (closedIncl hs)
  let piF := pi.hom.app F
  let piT := pi.hom.app ((Sheaf.pushforward AddCommGrpCat (closedIncl hs)).obj (pb.obj F))
  haveI : IsIso piF.val := by show IsIso ((sheafToPresheaf _ _).map piF); infer_instance
  haveI : IsIso piT.val := by show IsIso ((sheafToPresheaf _ _).map piT); infer_instance
  haveI : IsIso (Tz.map piF.val) := inferInstance
  haveI : IsIso (Tz.map piT.val) := inferInstance
  have hnat : (pb.map η).val ≫ piT.val = piF.val ≫
      (presheafToSheaf _ _ |>.map ((Presheaf.pullback AddCommGrpCat (closedIncl hs)).map η.val)).val :=
    congr_arg Sheaf.Hom.val (pi.hom.naturality η)
  have hnat_stalk := congr_arg Tz.map hnat
  simp only [Functor.map_comp] at hnat_stalk
  haveI : IsIso (Tz.map (pb.map η).val ≫ Tz.map piT.val) := inferInstance
  -- Step 4: presheafToSheaf.map(pull.map(η.val)).val stalk is iso
  haveI : IsIso (Tz.map
      (presheafToSheaf _ _ |>.map ((Presheaf.pullback AddCommGrpCat (closedIncl hs)).map η.val)).val) :=
    isIso_right (e := hnat_stalk.symm)
  -- Step 5: toSheafify naturality → pull.map(η.val) stalk is iso
  let K := Opens.grothendieckTopology (TopCat.of s)
  let P₁ := (Presheaf.pullback AddCommGrpCat (closedIncl hs)).obj F.val
  let P₂ := (Presheaf.pullback AddCommGrpCat (closedIncl hs)).obj
    ((Sheaf.pushforward AddCommGrpCat (closedIncl hs)).obj (pb.obj F)).val
  have hts : Tz.map ((Presheaf.pullback AddCommGrpCat (closedIncl hs)).map η.val) ≫
      Tz.map (CategoryTheory.toSheafify K P₂) =
    Tz.map (CategoryTheory.toSheafify K P₁) ≫ Tz.map
      (presheafToSheaf K AddCommGrpCat.{u} |>.map
        ((Presheaf.pullback AddCommGrpCat (closedIncl hs)).map η.val)).val := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    exact CategoryTheory.toSheafify_naturality K _
  haveI : IsIso (Tz.map (CategoryTheory.toSheafify K P₁)) := stalkFunctor_map_iso_toSheafify P₁ x
  haveI : IsIso (Tz.map (CategoryTheory.toSheafify K P₂)) := stalkFunctor_map_iso_toSheafify P₂ x
  haveI : IsIso (Tz.map ((Presheaf.pullback AddCommGrpCat (closedIncl hs)).map η.val)) :=
    isIso_left (e := hts)
  -- Step 6: stalkPull_nat → η.val stalk is iso
  haveI : IsIso (Presheaf.stalkPullbackHom AddCommGrpCat (closedIncl hs)
      ((𝟭 _).obj F).val x) :=
    (Presheaf.stalkPullbackIso AddCommGrpCat (closedIncl hs) ((𝟭 _).obj F).val x).isIso_hom
  haveI : IsIso (Presheaf.stalkPullbackHom AddCommGrpCat (closedIncl hs)
      ((pb ⋙ Sheaf.pushforward AddCommGrpCat (closedIncl hs)).obj F).val x) :=
    (Presheaf.stalkPullbackIso AddCommGrpCat (closedIncl hs)
      ((pb ⋙ Sheaf.pushforward AddCommGrpCat (closedIncl hs)).obj F).val x).isIso_hom
  exact isIso_left (e := stalkPull_nat (closedIncl hs) η.val x)

end TopCat
