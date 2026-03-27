import Mathlib

universe u

open CategoryTheory TopologicalSpace Limits

instance : HasSeparator AddCommGrpCat.{u} where
  hasSeparator := by
    use AddCommGrpCat.of (ULift ℤ)
    intro A B f g h; simp_all only [ObjectProperty.singleton_iff, AddCommGrpCat.ext_iff,
      AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply, forall_eq',
      ULift.forall]
    intro x; specialize h (AddCommGrpCat.ofHom
      (AddMonoidHom.mk' (fun y => y • x) fun y z => by simp only [add_smul])) 1; aesop

instance : IsGrothendieckAbelian.{u} AddCommGrpCat.{u} where

instance (X : TopCat.{u}) : Abelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (Abelian (CategoryTheory.Sheaf _ _))

instance (X : TopCat.{u}) : IsGrothendieckAbelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (IsGrothendieckAbelian (CategoryTheory.Sheaf _ _))

set_option synthInstance.maxHeartbeats 80000

/-! ## Helper lemmas for sheaf cohomology vanishing -/

/-- For the empty presieve, the sheaf condition forces the presheaf value to be subsingleton.
    This is because the empty family of elements is vacuously compatible, any element is
    vacuously an amalgamation, and uniqueness forces at most one element. -/
private lemma subsingleton_of_isSheafFor_empty
    {C : Type*} [Category C] {U : C} {P : Cᵒᵖ ⥤ Type*}
    (h : Presieve.IsSheafFor P (⊥ : Presieve U)) :
    Subsingleton (P.obj (Opposite.op U)) := by
  constructor; intro a b
  have hemp : Presieve.FamilyOfElements P (⊥ : Presieve U) := fun _ _ hf => absurd hf id
  obtain ⟨t, _, huniq⟩ := h hemp (fun _ _ _ _ _ _ _ hf => absurd hf id)
  exact (huniq a (fun _ _ hf => absurd hf id)).trans (huniq b (fun _ _ hf => absurd hf id)).symm

/-- If the endomorphism monoid of an abelian group is subsingleton (meaning id = 0),
    then the group is trivial: for all g, g = id(g) = 0(g) = 0. -/
private lemma addCommGrpCat_subsingleton_of_end_subsingleton
    (G : AddCommGrpCat.{u}) (h : Subsingleton (G ⟶ G)) :
    Subsingleton G := by
  have : ∀ (g : G), g = 0 := by
    intro g
    have := AddCommGrpCat.ext_iff.mp (Subsingleton.elim (𝟙 G : G ⟶ G) 0) g
    simp at this; exact this
  exact ⟨fun a b => (this a).trans (this b).symm⟩

/-- Ext of an IsZero object with anything is subsingleton, since a zero object
    has projective dimension 0. -/
private lemma ext_subsingleton_of_isZero {C : Type*} [Category C] [Abelian C] [HasExt C]
    (X : C) (hX : IsZero X) (Y : C) (n : ℕ) :
    Subsingleton (Abelian.Ext X Y n) := by
  have : HasProjectiveDimensionLT X 0 := (hasProjectiveDimensionLT_zero_iff_isZero X).mpr hX
  exact HasProjectiveDimensionLT.subsingleton X 0 n (Nat.zero_le n) Y

/-! ## Empty space case -/

/-- On the empty space, every sheaf of abelian groups is a zero object.

    On the empty space, the empty sieve (⊥ : Sieve U) covers every open U
    (vacuously, since there are no points). The sheaf condition for this
    sieve forces Hom(E, F(U)) to be subsingleton for all E. Taking E = F(U)
    shows End(F(U)) is subsingleton, so id_{F(U)} = 0, meaning F(U) is trivial.
    Since all presheaf values are trivial, F is a zero object. -/
lemma sheaf_isZero_of_isEmpty (X : TopCat.{u}) [hE : IsEmpty X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    IsZero F := by
  -- For any E and U, Hom(E, F(U)) is subsingleton (via empty sieve sheaf condition)
  have hom_sub : ∀ (E : AddCommGrpCat.{u}) (U : Opens X),
      Subsingleton (E ⟶ F.val.obj (Opposite.op U)) := by
    intro E U
    have hmem : (⊥ : Sieve U) ∈ Opens.grothendieckTopology X U := by
      rw [Opens.grothendieckTopology]; intro x; exact IsEmpty.elim hE x
    have hsf := (F.cond E) (⊥ : Sieve U) hmem
    rw [show (⊥ : Sieve U).arrows = ⊥ from rfl] at hsf
    exact subsingleton_of_isSheafFor_empty hsf
  -- F(U) is subsingleton (id = 0 argument)
  have val_sub : ∀ (U : Opens X), Subsingleton (F.val.obj (Opposite.op U)) :=
    fun U => addCommGrpCat_subsingleton_of_end_subsingleton _ (hom_sub _ U)
  -- Each F(U) is IsZero in AddCommGrpCat
  have val_isZero : ∀ (U : (Opens X)ᵒᵖ), IsZero (F.val.obj U) := by
    intro ⟨U⟩; exact @AddCommGrpCat.isZero_of_subsingleton _ (val_sub U)
  -- F is IsZero in the sheaf category (unique morphisms to/from any G)
  apply IsZero.mk
  · intro G; exact ⟨{
      default := 0
      uniq := fun f => by
        apply Sheaf.Hom.ext; apply NatTrans.ext; funext U
        exact (val_isZero U).eq_zero_of_src (f.val.app U) }⟩
  · intro G; exact ⟨{
      default := 0
      uniq := fun f => by
        apply Sheaf.Hom.ext; apply NatTrans.ext; funext U
        exact (val_isZero U).eq_zero_of_tgt (f.val.app U) }⟩

/-- On the empty space, sheaf cohomology is trivially subsingleton
    (since the constant sheaf is zero, and Ext from zero is zero). -/
lemma sheaf_H_subsingleton_of_isEmpty
    (X : TopCat.{u}) [IsEmpty X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) : Subsingleton (Sheaf.H F n) :=
  ext_subsingleton_of_isZero _ (sheaf_isZero_of_isEmpty X _) F n

/-! ## The reducible case

The reducible case (X nonempty, not irreducible, ≥ 2 irreducible components) requires
infrastructure not yet available in Mathlib:

1. **Extension by zero / closed-open SES**: For Y ⊆ X closed and U = X \ Y open,
   the short exact sequence 0 → j_!F|_U → F → i_*F|_Y → 0 of sheaves on X.
   The functors j_! (extension by zero from U) and i_* (pushforward from Y)
   are not formalized for the sheaf cohomology setup.

2. **Lemma 2.10 (Hartshorne)**: H^i(X, i_*G) ≅ H^i(Y, G) for a closed
   inclusion i : Y → X. This relates Ext in the sheaf category on X to Ext
   in the sheaf category on the subspace Y.

3. **Sheaf.H vs Ext(ℤ[⊤], F, n)**: The identification of sheaf cohomology
   Sheaf.H F n (defined as Ext from the constant sheaf) with
   Ext(ℤ[⊤], F, n) (Ext from the free abelian sheaf on the terminal open).
   This is listed as a TODO in Mathlib's SheafCohomology/Basic.lean.

The proof strategy (Hartshorne III.2.7 Step 1) is:
- Induction on the number k of irreducible components of X
- For k ≥ 2: pick component Y₁, let Z = Y₂ ∪ ... ∪ Yₖ
- Use the SES 0 → j_!(F|_U) → F → i_*(F|_{Y₁}) → 0 where U = X \ Y₁
- The covariant Ext LES gives: H^n(X, j_!F|_U) → H^n(X, F) → H^n(Y₁, F|_{Y₁})
- H^n(Y₁, F|_{Y₁}) = 0 by ih_irred (Y₁ is irreducible, dim Y₁ ≤ dim X)
- H^n(X, j_!F|_U) = 0 by relating to the closure Z (fewer components)
-/
lemma sheaf_H_subsingleton_of_reducible
    (X : TopCat.{u}) [TopologicalSpace.NoetherianSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hNotIrred : ¬ IrreducibleSpace X) [Nonempty X]
    (ih_irred : ∀ (Y : TopCat.{u}) [TopologicalSpace.NoetherianSpace Y]
      [IrreducibleSpace Y] (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y ≤ topologicalKrullDim X →
      n > topologicalKrullDim Y → Subsingleton (Sheaf.H G n)) :
    Subsingleton (Sheaf.H F n) := by
  sorry

/-! ## Main theorem -/

/-- Reduction from general Noetherian spaces to irreducible ones (Hartshorne III.2.7 Step 1).

    If cohomological vanishing H^n(Y, G) = 0 holds for all irreducible Noetherian spaces Y
    with dim Y ≤ dim X and n > dim Y, then it holds for X.

    The proof handles three cases:
    1. **Empty X**: All sheaves on the empty space are zero objects (the empty sieve covers
       every open, forcing all presheaf values to be trivial), so Ext from the zero constant
       sheaf vanishes.
    2. **Irreducible X**: Apply `ih_irred` directly with Y = X, dim X ≤ dim X.
    3. **Reducible X**: (Requires infrastructure not yet in Mathlib — see documentation
       on `sheaf_H_subsingleton_of_reducible`.) Uses induction on the number of irreducible
       components via the closed-open short exact sequence and the Ext long exact sequence. -/
theorem grothendieck_vanishing_of_irreducible
    (X : TopCat.{u}) [TopologicalSpace.NoetherianSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (ih_irred : ∀ (Y : TopCat.{u}) [TopologicalSpace.NoetherianSpace Y]
      [IrreducibleSpace Y] (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y ≤ topologicalKrullDim X →
      n > topologicalKrullDim Y → Subsingleton (Sheaf.H G n)) :
    Subsingleton (Sheaf.H F n) := by
  -- Case split: is X empty, irreducible, or reducible?
  by_cases hEmpty : IsEmpty X
  · -- X is empty: the constant sheaf is zero, so Ext vanishes
    exact sheaf_H_subsingleton_of_isEmpty X F n
  · rw [not_isEmpty_iff] at hEmpty
    by_cases hIrred : IrreducibleSpace X
    · -- X is irreducible: apply ih_irred directly with Y = X
      exact @ih_irred X _ hIrred F le_rfl hn
    · -- X is not irreducible: use induction on irreducible components
      exact sheaf_H_subsingleton_of_reducible X n hn F hIrred ih_irred
