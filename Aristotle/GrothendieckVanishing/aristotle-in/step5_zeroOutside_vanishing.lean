/-
  Step 5 of Hartshorne III.2.7: Vanishing for Z_U (extension by zero of constant sheaf).

  Goal: H^m(X, Z_U) = 0 for m > dim X, where Z_U = zeroOutsideInt U.

  Proof: Use the SES  0 → Z_U → Z_X → Z_Y → 0  where:
  - Z_X = constant sheaf on X (flasque on irreducible X → H^m = 0)
  - Z_Y = pushforward of constant sheaf from Y = X\U
  - dim Y < dim X (since X is irreducible and Y is proper closed)
  - H^{m-1}(X, Z_Y) = 0 by IH + PushforwardHVanishing

  Sub-lemmas needed:
  1. zeroOutsideInt ⊤ ≅ constant sheaf (or a map between them)
  2. The cokernel of zeroOutsideInt U → zeroOutsideInt ⊤ relates to i_*(Z_Y)
  3. The SES is ShortExact
  4. The LES argument combining FlasqueVanishing + IH

  For sub-lemma 1: zeroOutsideInt ⊤ is the sheafification of the presheaf that
  assigns Z to every open (since every open ≤ ⊤). This is the constant sheaf.

  For sub-lemma 2: the cokernel has zero stalks on U and stalks ≅ Z on Y = X\U.
  This matches i_*(Z_Y) = pushforward of constant sheaf from Y.
-/
import Mathlib

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

instance : HasSeparator AddCommGrpCat.{u} where
  hasSeparator := by
    use AddCommGrpCat.of (ULift ℤ)
    intro A B f g h
    simp_all only [ObjectProperty.singleton_iff, AddCommGrpCat.ext_iff,
      AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply, forall_eq',
      ULift.forall]
    intro x
    specialize h (AddCommGrpCat.ofHom
      (AddMonoidHom.mk' (fun y => y • x) fun y z => by simp only [add_smul])) 1
    aesop

instance : IsGrothendieckAbelian.{u} AddCommGrpCat.{u} where

instance (X : TopCat.{u}) : Abelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (Abelian (CategoryTheory.Sheaf _ _))

instance (X : TopCat.{u}) : IsGrothendieckAbelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (IsGrothendieckAbelian (CategoryTheory.Sheaf _ _))

/-- The constant sheaf Z' on X. -/
noncomputable abbrev constantSheafZ (X : TopCat.{u}) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift ℤ))

/-- Sheaf cohomology H^n(X, F) = Ext^n(Z', F). -/
noncomputable abbrev Sheaf.H' {X : TopCat.{u}}
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :=
  Ext (constantSheafZ X) F n

/-- Step 5: The extension-by-zero sheaf Z_U has vanishing cohomology
    H^m(X, Z_U) = 0 for m > dim X on an irreducible Noetherian space.

    Proof sketch:
    1. Form the SES: 0 → Z_U → Z_X → cokernel → 0
       where Z_U = zeroOutsideInt U, Z_X = constant sheaf
    2. The cokernel has zero stalks on U and constant stalks on Y = X\U
    3. H^m(Z_X) = 0 by FlasqueVanishing (constant sheaf is flasque on irreducible X)
    4. H^{m-1}(cokernel) = 0 by PushforwardHVanishing + IH (dim Y < dim X)
    5. LES gives H^m(Z_U) = 0

    Key Mathlib API:
    - TopCat.Sheaf.zeroOutsideInt U : the extension by zero
    - TopCat.Sheaf.zeroOutsideInt.openHom : inclusion Z_V → Z_U for V ≤ U (mono)
    - presheafToSheaf, sheafifyMap : sheafification functors
    - Ext.covariant_sequence_exact₂ : LES for Ext in second variable
    - constantSheaf, constantSheafAdj : constant sheaf and its adjunction
-/
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 80000 in
theorem zeroOutsideInt_cohomology_vanishing
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X]
    (U : Opens X) (hU : U ≠ ⊥)
    (n : ℕ) (hn : n ≥ 1)
    -- The constant sheaf on irreducible X has vanishing H^n for n ≥ 1
    (hconst : ∀ (m : ℕ), Subsingleton (Sheaf.H' (constantSheafZ X) (m + 1)))
    -- IH: vanishing on all spaces of strictly smaller dimension
    (ih : ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
      (G : TopCat.Sheaf AddCommGrpCat.{u} Y) (m : ℕ),
      topologicalKrullDim Y < topologicalKrullDim X →
      (m : WithBot ℕ∞) > topologicalKrullDim Y →
      Subsingleton (Sheaf.H' G m)) :
    Subsingleton (Sheaf.H' (TopCat.Sheaf.zeroOutsideInt U) n) := by
  sorry
