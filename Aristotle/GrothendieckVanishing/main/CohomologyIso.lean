/-
  CohomologyIso.lean — Identification H'(⊤, F) ≅ H(F)

  Proves that the cohomology presheaf evaluated at the terminal object equals
  global sheaf cohomology. This resolves a TODO from Mathlib's SheafCohomology/Basic.lean.

  Key result: yoneda.obj ⊤ ⋙ AddCommGrpCat.free ≅ const(ULift ℤ) as presheaves,
  so after sheafification: freeAbSheaf(yoneda ⊤) ≅ constantSheaf(ULift ℤ).
  Therefore Ext(freeAbSheaf(yoneda ⊤), F, n) ≅ Ext(constantSheaf Z, F, n),
  i.e., H'(⊤, F, n) ≅ H(F, n).
-/
import Aristotle.GrothendieckVanishing.main.Setup

universe u

open CategoryTheory TopologicalSpace Limits Opposite

variable {C : Type (u + 1)} [Category.{u} C] [HasTerminal C]

noncomputable instance instUniqueHomTerminal (U : C) : Unique (U ⟶ ⊤_ C) :=
  uniqueToTerminal U

noncomputable instance instUniqueYonedaTop (U : Cᵒᵖ) :
    Unique ((yoneda.obj (⊤_ C)).obj U) := by
  change Unique (U.unop ⟶ ⊤_ C); infer_instance

/-- FreeAbelianGroup.map on a function between Unique types preserves the
    component isomorphism. -/
private lemma freeAbelianGroup_map_unique_eq {α β : Type u} [Unique α] [Unique β]
    (f : α → β) (x : FreeAbelianGroup α) :
    ((FreeAbelianGroup.uniqueEquiv β).trans ULift.ringEquiv.symm.toAddEquiv)
      (FreeAbelianGroup.map f x) =
    ((FreeAbelianGroup.uniqueEquiv α).trans ULift.ringEquiv.symm.toAddEquiv) x := by
  induction x using FreeAbelianGroup.induction_on with
  | C0 => simp
  | C1 a =>
    simp only [AddEquiv.trans_apply, FreeAbelianGroup.map_of_apply]
    simp [FreeAbelianGroup.uniqueEquiv, Unique.eq_default a]
  | Cn _ ih => simp only [map_neg] at ih ⊢; rw [ih]
  | Cp _ _ hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]

/-- Component isomorphism: FreeAbelianGroup(Hom(U, ⊤)) ≅ ULift ℤ. -/
private noncomputable def yonedaTopFreeComponentIso (U : Cᵒᵖ) :
    (yoneda.obj (⊤_ C) ⋙ AddCommGrpCat.free).obj U ≅
    ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ))).obj U := by
  let e : FreeAbelianGroup ((yoneda.obj (⊤_ C)).obj U) ≃+ ULift.{u} ℤ :=
    (FreeAbelianGroup.uniqueEquiv _).trans ULift.ringEquiv.symm.toAddEquiv
  exact {
    hom := AddCommGrpCat.ofHom e.toAddMonoidHom
    inv := AddCommGrpCat.ofHom e.symm.toAddMonoidHom
    hom_inv_id := by ext x; simp [e]
    inv_hom_id := by ext x; simp [e]
  }

set_option maxHeartbeats 800000 in
-- NatIso.ofComponents needs extra heartbeats for the naturality verification
/-- The presheaf `yoneda.obj ⊤ ⋙ AddCommGrpCat.free` is naturally isomorphic to the
    constant presheaf with value `ULift ℤ`. Both assign ℤ (up to ULift) to every
    object, with identity restriction maps. -/
noncomputable def yonedaTopFreeIsoConst :
    yoneda.obj (⊤_ C) ⋙ AddCommGrpCat.free ≅
      (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  NatIso.ofComponents yonedaTopFreeComponentIso (by
    intro U V f
    ext x
    simp only [yonedaTopFreeComponentIso, Functor.comp_map, Functor.const_obj_map]
    exact freeAbelianGroup_map_unique_eq _ x)

/-- The free abelian sheaf on `yoneda.obj ⊤` is isomorphic to the constant sheaf.
    This follows from `yonedaTopFreeIsoConst` (presheaf iso) + sheafification preserves isos. -/
noncomputable def freeAbSheafTopIsoConstantSheaf
    [HasSheafify (J : GrothendieckTopology C) AddCommGrpCat.{u}] :
    (presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj (⊤_ C) ⋙ AddCommGrpCat.free) ≅
    (constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  (presheafToSheaf J AddCommGrpCat.{u}).mapIso yonedaTopFreeIsoConst

/-! ## Ext transport along isomorphisms -/

/-- Transport Ext along an isomorphism: Ext(B, F, n) ≃+ Ext(A, F, n) when A ≅ B.
    Uses the `extFunctor` bifunctor from Mathlib. -/
noncomputable def extAddEquivOfIso {D : Type*} [Category D] [Abelian D] [HasExt D]
    {A B F : D} (f : A ≅ B) (n : ℕ) :
    Abelian.Ext B F n ≃+ Abelian.Ext A F n where
  toFun := AddCommGrpCat.Hom.hom (((Abelian.extFunctor n).mapIso f.op).app F).hom
  invFun := AddCommGrpCat.Hom.hom (((Abelian.extFunctor n).mapIso f.op).app F).inv
  left_inv x := by
    change (AddCommGrpCat.Hom.hom
      ((((Abelian.extFunctor n).mapIso f.op).app F).hom ≫
       (((Abelian.extFunctor n).mapIso f.op).app F).inv)) x = x
    rw [(((Abelian.extFunctor n).mapIso f.op).app F).hom_inv_id]; rfl
  right_inv x := by
    change (AddCommGrpCat.Hom.hom
      ((((Abelian.extFunctor n).mapIso f.op).app F).inv ≫
       (((Abelian.extFunctor n).mapIso f.op).app F).hom)) x = x
    rw [(((Abelian.extFunctor n).mapIso f.op).app F).inv_hom_id]; rfl
  map_add' := map_add _

/-! ## H'(⊤) ≅ H -/

/-- **H'(⊤, F, n) ≅ H(F, n)**: the cohomology presheaf at the terminal object
    equals global sheaf cohomology.

    This resolves the TODO in Mathlib's SheafCohomology/Basic.lean.

    Chain: freeAbSheafTopIsoConstantSheaf (sheaf iso) → extAddEquivOfIso (Ext transport)
    gives Ext(freeAbSheaf(yoneda ⊤), F, n) ≃+ Ext(constantSheaf Z, F, n)
    i.e., H'(⊤, F, n) ≃+ H(F, n). -/
noncomputable def cohomologyPresheafTopEquiv
    [HasSheafify J AddCommGrpCat.{u}]
    [HasExt (Sheaf J AddCommGrpCat.{u})]
    (F : Sheaf J AddCommGrpCat.{u}) (n : ℕ) :
    Abelian.Ext ((presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj (⊤_ C) ⋙ AddCommGrpCat.free)) F n ≃+
    Sheaf.H F n :=
  (extAddEquivOfIso freeAbSheafTopIsoConstantSheaf n).symm
