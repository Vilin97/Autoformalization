import Mathlib

universe u

open CategoryTheory TopologicalSpace Limits Order

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

/-! ## Helper lemmas -/

/-- If `x < n` in `WithBot ℕ∞` for a natural number `n`, then either `x = ⊥` or
`x = ↑↑d` for some natural number `d < n`. -/
lemma WithBot.ENat.lt_nat_cases (x : WithBot ℕ∞) (n : ℕ) (h : x < (n : WithBot ℕ∞)) :
    x = ⊥ ∨ ∃ d : ℕ, x = ↑(d : ℕ∞) ∧ d < n := by
  rcases x with _ | y
  · left; rfl
  · right
    have hy : y < (n : ℕ∞) := by
      change (y : WithBot ℕ∞) < (n : WithBot ℕ∞) at h
      exact WithBot.coe_lt_coe.mp h
    have hfin : y ≠ ⊤ := ne_top_of_lt hy
    lift y to ℕ using hfin with d
    rw [ENat.coe_lt_coe] at hy
    exact ⟨d, rfl, hy⟩

/-- On an empty topological space, every open set is the bottom element (empty set). -/
instance Opens.subsingleton_of_isEmpty {X : Type*} [TopologicalSpace X] [IsEmpty X] :
    Subsingleton (Opens X) := by
  constructor; intro U V; ext x; exact IsEmpty.elim ‹IsEmpty X› x

/-- In any abelian category with `HasExt`, `Abelian.Ext` from a zero object is
subsingleton in every degree. This follows from the fact that `Ext.mk₀ (𝟙 X)` acts
as the identity on `Ext(X, Y, n)` via composition, and when `X` is zero, `𝟙 X = 0`,
so `mk₀ 0 = 0` and composition with zero gives zero. -/
lemma Abelian.Ext.subsingleton_of_isZero {C : Type*} [Category C] [Abelian C]
    [HasExt C] {X : C} (hX : IsZero X) (Y : C) (n : ℕ) :
    Subsingleton (Abelian.Ext X Y n) := by
  constructor
  intro a b
  have hid : (𝟙 X : X ⟶ X) = 0 := hX.eq_of_src _ _
  have hmk0 : Abelian.Ext.mk₀ (0 : X ⟶ X) = (0 : Abelian.Ext X X 0) := by
    have h := Abelian.Ext.mk₀_add (0 : X ⟶ X) (0 : X ⟶ X)
    simp only [add_zero] at h
    have : Abelian.Ext.mk₀ (0 : X ⟶ X) + Abelian.Ext.mk₀ (0 : X ⟶ X) =
           Abelian.Ext.mk₀ (0 : X ⟶ X) + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel this
  calc a = (Abelian.Ext.mk₀ (𝟙 X)).comp a (zero_add n) := (Abelian.Ext.mk₀_id_comp a).symm
    _ = (0 : Abelian.Ext X X 0).comp a (zero_add n) := by rw [hid, hmk0]
    _ = 0 := Abelian.Ext.zero_comp X 0 a n (zero_add n)
    _ = (0 : Abelian.Ext X X 0).comp b (zero_add n) :=
        (Abelian.Ext.zero_comp X 0 b n (zero_add n)).symm
    _ = (Abelian.Ext.mk₀ (𝟙 X)).comp b (zero_add n) := by rw [hid, hmk0]
    _ = b := Abelian.Ext.mk₀_id_comp b

/-- On an empty topological space (`IsEmpty X`), every sheaf of abelian groups is
the zero object. This is because the only open set is `⊥` (the empty set), and
`TopCat.Sheaf.isTerminalOfEmpty` shows that `F.val.obj (op ⊥)` is terminal for any
sheaf `F`. In an abelian category, terminal implies zero (`IsTerminal.isZero`),
so `𝟙 F = 0` follows from the fact that every component is zero. -/
lemma TopCat.Sheaf.isZero_of_isEmpty (X : TopCat.{u}) [IsEmpty X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  apply Sheaf.Hom.ext
  apply NatTrans.ext
  funext U
  have hU : U = Opposite.op ⊥ := Subsingleton.elim _ _
  subst hU
  have hterm := TopCat.Sheaf.isTerminalOfEmpty F
  exact hterm.isZero.eq_of_src _ _

/-! ## Grothendieck's Vanishing Theorem

We prove Grothendieck's vanishing theorem: for a Noetherian topological space X of
topological Krull dimension d, the sheaf cohomology H^n(X, F) = 0 for all sheaves F
of abelian groups and all n > d.

### Structure of the Proof

The main theorem `FlasqueVanishing` reduces to two cases:

1. **Empty space** (`topologicalKrullDim X = ⊥`): Handled by
   `sheafCohomology_subsingleton_of_empty_dim`, which uses
   `TopCat.Sheaf.isZero_of_isEmpty` (sheaves on empty spaces are zero) and
   `Abelian.Ext.subsingleton_of_isZero` (Ext from zero is trivial). ✓ Fully proved.

2. **Finite dimension** (`topologicalKrullDim X = ↑↑d` for `d : ℕ`): Handled by
   `grothendieck_vanishing_nat`. This is the core of the theorem and requires the
   **extension by zero functor j_!** which is not available in Mathlib.

### Missing Infrastructure: Extension by Zero (j_!)

The inductive step of Grothendieck's vanishing theorem (Hartshorne III.2.7) requires
the short exact sequence `0 → j_!(F|_U) → F → i_*(F|_Z) → 0` where:
- `Z ⊂ X` is a proper closed subset
- `U = X \ Z` is the open complement  
- `i : Z ↪ X` and `j : U ↪ X` are the inclusions
- `j_!` is the extension by zero (left adjoint of restriction `j*`)

**This functor j_! is not in Mathlib.** Without it, the key exact sequence cannot be
constructed, and the Noetherian induction on dimension cannot be carried out.

Alternative approaches that also require missing infrastructure:
- Čech-to-derived spectral sequence (not in Mathlib)
- Direct limit approach via Hartshorne Prop 2.9 (not in Mathlib)
- Sections with support / local cohomology (not in Mathlib)
- Flasque → injective: FALSE (ℤ on a point is flasque but not injective)
-/

/-- **Key vanishing lemma (requires j_! — extension by zero, not in Mathlib).**

For a Noetherian topological space X of topological Krull dimension ≤ d,
the sheaf cohomology H^n(X, F) = 0 for all sheaves F and all n > d.

The standard proof proceeds by strong induction on `d`:

**Base case (d = 0):** A Noetherian space of dim 0 is a finite discrete space.
On a discrete space, Γ is exact, so all higher cohomology vanishes.

**Inductive step (d ≥ 1):** Uses the SES `0 → j_!(F|_U) → F → i_*(F|_Z) → 0`
for a proper closed Z ⊊ X with open complement U = X \ Z.
The Ext LES (`Abelian.Ext.covariantSequence_exact`) gives vanishing by induction.

**This step requires j_! (extension by zero), which is not in Mathlib.** -/
lemma grothendieck_vanishing_nat (X : TopCat.{u}) [NoetherianSpace X]
    (d : ℕ) (hd : topologicalKrullDim X ≤ ↑↑d)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) (hn : n > d) :
    Subsingleton (Sheaf.H F n) := by
  sorry

/-- **Vanishing of sheaf cohomology on the empty space.**

When `topologicalKrullDim X = ⊥`, the space has no irreducible closed subsets.
For Noetherian X, this means X is empty (every nonempty Noetherian space has
irreducible components, and hence irreducible closed subsets). On the empty space,
every sheaf is the zero object, so Ext from the constant sheaf (which is also zero)
vanishes in all degrees. -/
lemma sheafCohomology_subsingleton_of_empty_dim (X : TopCat.{u}) [NoetherianSpace X]
    (hbot : topologicalKrullDim X = ⊥)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) :
    Subsingleton (Sheaf.H F n) := by
  -- topologicalKrullDim X = ⊥ means IsEmpty (IrreducibleCloseds X)
  have h_empty_irr : IsEmpty (IrreducibleCloseds X) := by
    rwa [topologicalKrullDim, krullDim_eq_bot_iff] at hbot
  -- Every nonempty Noetherian space has irreducible components,
  -- so no irreducible closed subsets implies X is empty.
  have h_empty : IsEmpty X := by
    rw [isEmpty_iff]
    intro x
    exact h_empty_irr.false ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  -- On an empty space, the constant sheaf is zero, so Ext vanishes
  have hZ : IsZero ((constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))) :=
    TopCat.Sheaf.isZero_of_isEmpty X _
  exact Abelian.Ext.subsingleton_of_isZero hZ F n

set_option synthInstance.maxHeartbeats 160000 in
/-- **Grothendieck's vanishing theorem** (Hartshorne III, Theorem 2.7).

For a Noetherian topological space X of topological Krull dimension d, and any sheaf F
of abelian groups on X, the sheaf cohomology H^n(X, F) = 0 for all n > d.

The proof reduces to two cases based on `topologicalKrullDim X`:
- **Empty case** (`dim X = ⊥`): Uses `sheafCohomology_subsingleton_of_empty_dim`. ✓
- **Finite dimension** (`dim X = ↑↑d`): Uses `grothendieck_vanishing_nat`. ⚠ Requires j_!. -/
theorem FlasqueVanishing (X : TopCat.{u}) [NoetherianSpace X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) (hn : n > topologicalKrullDim X) :
    Subsingleton (Sheaf.H F n) := by
  obtain hbot | ⟨d, hd, hdn⟩ := WithBot.ENat.lt_nat_cases _ n hn
  · exact sheafCohomology_subsingleton_of_empty_dim X hbot F n
  · exact grothendieck_vanishing_nat X d (le_of_eq hd) F n hdn

