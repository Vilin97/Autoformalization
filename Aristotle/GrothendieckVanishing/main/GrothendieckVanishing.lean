/-
  GrothendieckVanishing.lean — Main theorem

  Grothendieck's vanishing theorem (Hartshorne III.2.7):
  For a Noetherian topological space X of dimension n, and any sheaf F
  of abelian groups on X, H^i(X, F) = 0 for all i > n.

  The proof assembles (all proved, modulo IrreduciblePosVanishing sorry in Setup.lean):
  - DimZeroVanishing: irreducible dim 0 case (PROVED via projectivity)
  - IrreducibleStep: irreducible dim ≥ 1 case (uses IrreduciblePosVanishing)
  - ClosedOpenDecomposition: reduction to irreducible (PROVED)
-/
import Aristotle.GrothendieckVanishing.main.DimZeroVanishing
import Aristotle.GrothendieckVanishing.main.ClosedOpenDecomposition
import Aristotle.GrothendieckVanishing.main.IrreducibleStep

universe u

open CategoryTheory TopologicalSpace Order Limits

/-! ## Main induction -/

/-- The core induction step: vanishing at dimension d, given vanishing at all d' < d. -/
private theorem grothendieck_vanishing_aux (d : WithBot ℕ∞)
    (ih : ∀ d' < d, ∀ (X : TopCat.{u}) [NoetherianSpace X]
      (n : ℕ) (F : TopCat.Sheaf AddCommGrpCat.{u} X),
      topologicalKrullDim X = d' → n > d' → Subsingleton (Sheaf.H F n))
    (X : TopCat.{u}) [NoetherianSpace X]
    (n : ℕ) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hd : topologicalKrullDim X = d) (hn : n > d) :
    Subsingleton (Sheaf.H F n) := by
  -- Step 1: Reduce to irreducible X
  apply grothendieck_vanishing_of_irreducible X n (hd ▸ hn) F
  intro Y _ _ G hle hY
  by_cases hdim : topologicalKrullDim Y ≤ 0
  · -- dim Y ≤ 0: use DimZeroVanishing
    have hn0 : n ≠ 0 := by
      intro heq; subst heq
      exact not_lt.mpr (topologicalKrullDim_nonneg_of_irreducible (X := Y)) (by exact_mod_cast hY)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    exact grothendieck_vanishing_dim_zero Y hdim G m
  · -- dim Y > 0: use IrreducibleStep
    push_neg at hdim
    exact grothendieck_vanishing_irreducible_pos Y n hY hdim G
      (fun Z _ G' hlt hG' =>
        ih (topologicalKrullDim Z) (lt_of_lt_of_le hlt (hd ▸ hle)) Z n G' rfl hG')

/-- **Grothendieck's vanishing theorem** (Hartshorne III, Theorem 2.7). -/
theorem GrothendieckVanishing (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [NoetherianSpace X] (n : ℕ) (h : n > topologicalKrullDim X) :
    Subsingleton (Sheaf.H F n) := by
  have hwf : WellFounded (fun (a b : WithBot ℕ∞) => a < b) := IsWellFounded.wf
  exact hwf.induction (C := fun d =>
    ∀ (X : TopCat.{u}) [NoetherianSpace X]
      (n : ℕ) (F : TopCat.Sheaf AddCommGrpCat.{u} X),
      topologicalKrullDim X = d → n > d → Subsingleton (Sheaf.H F n))
    (topologicalKrullDim X) grothendieck_vanishing_aux X n F rfl h
