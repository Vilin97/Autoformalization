/-
  GrothendieckVanishing.lean — Main theorem

  Grothendieck's vanishing theorem (Hartshorne III.2.7):
  For a Noetherian topological space X of dimension n, and any sheaf F
  of abelian groups on X, H^i(X, F) = 0 for all i > n.

  The proof assembles (1 sorry in FiniteGeneratorReduction.lean: isSheaf_presheaf_filtered_colimit):
  - DimZeroVanishing: irreducible dim 0 case
  - IrreducibleStep + FiniteGeneratorReduction: irreducible dim >= 1 case
  - ClosedOpenDecomposition: reduction to irreducible
-/
import Aristotle.GrothendieckVanishing.main.DimZeroVanishing
import Aristotle.GrothendieckVanishing.main.ClosedOpenDecomposition
import Aristotle.GrothendieckVanishing.main.IrreducibleStep

universe u

open CategoryTheory TopologicalSpace Order Limits

/-! ## Degree cascade: vanishing at one degree implies vanishing at all higher degrees

Once we establish `H^m₀(F) = 0` for ALL sheaves `F` on `X` at a single degree `m₀`,
we get `H^n(F) = 0` for all `n ≥ m₀` by injective presentation + dimension shifting:
embed `F ↪ I` (injective), form `0 → F → I → Q → 0`, then `H^n(Q) = 0` by the inductive
hypothesis and `H^{n+1}(I) = 0` since `I` is injective. -/

/-- Vanishing cascades upward: `H^m = 0` for all sheaves implies `H^{m+1} = 0` for all
    sheaves, via injective presentation + dimension shifting. -/
theorem sheafH_vanishing_succ (X : TopCat.{u})
    (m : ℕ)
    (hall : ∀ (F : TopCat.Sheaf AddCommGrpCat.{u} X), Subsingleton (Sheaf.H F m))
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Subsingleton (Sheaf.H F (m + 1)) := by
  obtain ⟨ip⟩ := EnoughInjectives.presentation F
  have hInj : Subsingleton (Sheaf.H ip.shortComplex.X₂ (m + 1)) :=
    ⟨fun a b => (Abelian.Ext.eq_zero_of_injective a).trans
      (Abelian.Ext.eq_zero_of_injective b).symm⟩
  exact sheafH_dimension_shift_ses ip.shortExact_shortComplex m
    (hall ip.shortComplex.X₃) hInj

/-- Once vanishing holds at degree `m₀` for all sheaves, it holds at all degrees `≥ m₀`.
    This means the colimit step (`ext_vanishing_of_colimit_pieces`) is only needed at `dim(X)+1`;
    all higher degrees follow for free. -/
theorem sheafH_vanishing_cascade (X : TopCat.{u})
    (m₀ : ℕ)
    (hbase : ∀ (F : TopCat.Sheaf AddCommGrpCat.{u} X), Subsingleton (Sheaf.H F m₀))
    (n : ℕ) (hn : n ≥ m₀) :
    ∀ (F : TopCat.Sheaf AddCommGrpCat.{u} X), Subsingleton (Sheaf.H F n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m₀ + k := ⟨n - m₀, (Nat.add_sub_cancel' hn).symm⟩
  induction k with
  | zero => exact hbase
  | succ k ih => exact sheafH_vanishing_succ X (m₀ + k) (ih (Nat.le_add_right m₀ k))

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
  intro Y _ _ m G hle hY
  by_cases hdim : topologicalKrullDim Y ≤ 0
  · -- dim Y ≤ 0: use DimZeroVanishing
    have hm0 : m ≠ 0 := by
      intro heq; subst heq
      exact not_lt.mpr (topologicalKrullDim_nonneg_of_irreducible (X := Y)) (by exact_mod_cast hY)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    exact grothendieck_vanishing_dim_zero Y hdim G k
  · -- dim Y > 0: use IrreducibleStep
    push_neg at hdim
    exact IrreduciblePosVanishing Y m hY hdim G
      (fun Z _ m' G' hlt hG' =>
        ih (topologicalKrullDim Z) (lt_of_lt_of_le hlt (hd ▸ hle)) Z m' G' rfl hG')

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
