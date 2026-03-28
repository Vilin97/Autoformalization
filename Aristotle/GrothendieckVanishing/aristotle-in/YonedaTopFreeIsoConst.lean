import Mathlib

universe u

open CategoryTheory Limits Opposite

variable {C : Type (u+1)} [Category.{u} C] [HasTerminal C]

/-- Hom(U, ⊤) is Unique for any U. -/
instance (U : C) : Unique (U ⟶ ⊤_ C) := uniqueToTerminal U

/-- Component isomorphism: FreeAbelianGroup (U ⟶ ⊤) ≅ ULift ℤ -/
noncomputable def freeHomTopIsoULiftInt (U : Cᵒᵖ) :
    AddCommGrpCat.of (FreeAbelianGroup (U.unop ⟶ ⊤_ C)) ≅
    AddCommGrpCat.of (ULift.{u} ℤ) :=
  AddCommGrpCat.ofHom
    ((FreeAbelianGroup.uniqueEquiv _).trans ULift.ringEquiv.symm.toAddEquiv).toAddMonoidHom
  |> sorry -- need to construct as an Iso, not just a Hom

/-- The presheaf `yoneda.obj ⊤ ⋙ AddCommGrpCat.free` is naturally isomorphic to the
    constant presheaf `(Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift ℤ))`.

    At each object U: yoneda.obj ⊤ evaluates to Hom(U, ⊤) which is Unique (singleton).
    FreeAbelianGroup on a Unique type is ℤ (via FreeAbelianGroup.uniqueEquiv).
    ULift ℤ ≅ ℤ (via ULift.ringEquiv).
    So both presheaves assign ℤ to every object.

    Naturality: both presheaves have identity restriction maps.
    - The constant presheaf has (Functor.const).map f = 𝟙 for any f.
    - yoneda.obj ⊤ ⋙ free has: free.map (yoneda.map f) = free.map (fun g => f.unop ≫ g).
      Since Hom(V, ⊤) and Hom(U, ⊤) are both Unique, the FreeAbelianGroup map is
      the identity (on ℤ). So up to the component isos, this is also 𝟙.

    Therefore the component isos assemble into a natural isomorphism. -/
noncomputable def yonedaTopFreeIsoConst :
    yoneda.obj (⊤_ C) ⋙ AddCommGrpCat.free ≅
      (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) := by
  sorry
