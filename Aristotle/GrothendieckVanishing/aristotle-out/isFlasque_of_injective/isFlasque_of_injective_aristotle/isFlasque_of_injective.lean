import Mathlib

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

/-- A sheaf of abelian groups is **flasque** if all restriction maps are epi.
    This is equivalent to surjectivity of restriction on sections. -/
def IsFlasqueSheaf {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X) : Prop :=
  ∀ {U V : Opens X} (i : U ⟶ V), Epi (F.val.map i.op)

noncomputable section

variable {X : TopCat.{u}}

/-- The "free abelian presheaf" on an open set U: sends V to the free abelian group
    on Hom(V, U). -/
def freeAbPresheaf (U : Opens X) : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  yoneda.obj U ⋙ AddCommGrpCat.free

/-- The "free abelian sheaf" on U: sheafification of the free abelian presheaf. -/
def freeAbSheaf (U : Opens X) : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (presheafToSheaf (Opens.grothendieckTopology (T := X)) AddCommGrpCat.{u}).obj (freeAbPresheaf U)

/-- The inclusion `i : U ⟶ V` induces a morphism of free abelian sheaves. -/
def freeAbSheafMap {U V : Opens X} (i : U ⟶ V) : freeAbSheaf U ⟶ freeAbSheaf V :=
  (presheafToSheaf (Opens.grothendieckTopology (T := X)) AddCommGrpCat.{u}).map
    (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free)

/-- Chain of adjunctions giving an equivalence between morphisms from the free abelian
    sheaf on U into a sheaf I and the sections I(U):
    1. Sheafification adjunction: `(Z_U ⟶ I) ≃ (freeAbPresheaf U ⟶ I.val)`
    2. Free–forgetful adjunction on functor categories
    3. Yoneda lemma -/
def freeAbSheafHomEquiv (U : Opens X) (I : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (freeAbSheaf U ⟶ I) ≃ (forget AddCommGrpCat).obj (I.val.obj (op U)) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology (T := X)) AddCommGrpCat.{u}).homEquiv
    (freeAbPresheaf U) I).trans <|
  ((AddCommGrpCat.adj.whiskerRight _).homEquiv (yoneda.obj U)
    (sheafToPresheaf _ _ |>.obj I)).trans <|
  yonedaEquiv

/-- The equivalence is natural: precomposition with `freeAbSheafMap` corresponds to
    the restriction map. -/
lemma freeAbSheafHomEquiv_naturality {U V : Opens X} (i : U ⟶ V)
    (I : TopCat.Sheaf AddCommGrpCat.{u} X) (f : freeAbSheaf V ⟶ I) :
    freeAbSheafHomEquiv U I (freeAbSheafMap i ≫ f) =
      (I.val.map i.op) (freeAbSheafHomEquiv V I f) := by
  simp [freeAbSheafHomEquiv, freeAbSheafMap]
  erw [Adjunction.homEquiv_naturality_left]
  erw [Adjunction.homEquiv_naturality_left]
  simp +decide [yonedaEquiv]
  convert (NatTrans.naturality
    ((Adjunction.whiskerRight (Opens X)ᵒᵖ AddCommGrpCat.adj).homEquiv (yoneda.obj V) I.val
      ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat).homEquiv
        (freeAbPresheaf V) I f))
    i.op) using 1
  constructor <;> intro h
  · exact (NatTrans.naturality
      ((Adjunction.whiskerRight (Opens ↑X)ᵒᵖ AddCommGrpCat.adj).homEquiv (yoneda.obj V) I.val
        ((sheafificationAdjunction (Opens.grothendieckTopology ↑X) AddCommGrpCat).homEquiv
          (freeAbPresheaf V) I f)) i.op)
  · convert congr_arg (fun g => g (𝟙 V)) h using 1

/-- The Yoneda map is mono (all morphisms in a thin category are mono). -/
instance yoneda_map_mono {U V : Opens X} (i : U ⟶ V) :
    Mono (yoneda.map i : yoneda.obj U ⟶ yoneda.obj V) := by
  constructor; aesop_cat

/-- The free abelian group functor preserves monomorphisms. -/
instance : Functor.PreservesMonomorphisms
    (AddCommGrpCat.free : Type u ⥤ AddCommGrpCat.{u}) :=
  AddCommGrpCat.instPreservesMonomorphismsFree

/-- `whiskerRight` with a mono-preserving functor preserves monos. -/
instance whiskerRight_mono {U V : Opens X} (i : U ⟶ V) :
    Mono (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free :
      freeAbPresheaf U ⟶ freeAbPresheaf V) :=
  instMonoFunctorWhiskerRightOfPreservesMonomorphisms (yoneda.map i) AddCommGrpCat.free

/-- The `freeAbSheafMap` is mono (sheafification preserves monos). -/
instance freeAbSheafMap_mono {U V : Opens X} (i : U ⟶ V) :
    Mono (freeAbSheafMap i) := by
  have : ∀ (F G : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{_}) (f : F ⟶ G),
      Mono f → Mono ((presheafToSheaf (Opens.grothendieckTopology (T := X))
        AddCommGrpCat).map f) := by
    intro F G f hf; exact Functor.map_mono _ f
  exact this _ _ _ (whiskerRight_mono i)

/-- **Injective sheaves are flasque.**

    For `U ⊆ V`, the free abelian sheaf construction gives a mono `Z_U ↪ Z_V` in the
    sheaf category. Since `I` is injective, `Hom(Z_V, I) → Hom(Z_U, I)` is surjective.
    Via the Yoneda-like identification `Hom(Z_U, F) ≅ F(U)`, this gives `I(V) → I(U)`
    surjective, hence epi. -/
theorem isFlasque_of_injective {X : TopCat.{u}}
    (I : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective I] : IsFlasqueSheaf I := by
  intro U V i
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  -- Lift s to a morphism g : freeAbSheaf U ⟶ I via the equivalence
  set g := (freeAbSheafHomEquiv U I).symm s
  -- Factor g through the mono freeAbSheafMap i using injectivity of I
  obtain ⟨h, hh⟩ : ∃ h : freeAbSheaf V ⟶ I, freeAbSheafMap i ≫ h = g :=
    Injective.factors g (freeAbSheafMap i)
  -- The lift through the equivalence gives the desired preimage
  refine ⟨freeAbSheafHomEquiv V I h, ?_⟩
  rw [← freeAbSheafHomEquiv_naturality i I h, hh]
  simp [g]

end
