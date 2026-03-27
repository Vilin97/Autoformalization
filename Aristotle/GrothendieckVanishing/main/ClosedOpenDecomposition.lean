/-
  ClosedOpenDecomposition.lean — Reduction from general to irreducible spaces

  Hartshorne III.2.7, Step 1: If X is a Noetherian space and vanishing
  holds for all irreducible Noetherian spaces (of appropriate dimension),
  then vanishing holds for X.

  The proof (to be filled in) uses:
  - Extension by zero: for Y ⊆ X closed and U = X \ Y open,
    there is a short exact sequence 0 → F̄_U → F → F̄_Y → 0
  - Lemma 2.10: H^i(X, F̄_Y) ≅ H^i(Y, F|_Y)
  - Induction on the number of irreducible components

  SORRY — requires extension-by-zero infrastructure not yet in Mathlib.
-/
import Aristotle.GrothendieckVanishing.main.Setup

universe u

open CategoryTheory TopologicalSpace

/-- Reduction from general Noetherian spaces to irreducible ones.

    If vanishing holds for all irreducible Noetherian spaces Y with
    dim Y ≤ dim X and n > dim Y, then it holds for X.

    Hartshorne Step 1: decompose X by irreducible components, use the closed/open
    exact sequence and Lemma 2.10 to reduce to each component.
    The irreducible spaces Y that appear all have dim Y ≤ dim X. -/
theorem grothendieck_vanishing_of_irreducible
    (X : TopCat.{u}) [TopologicalSpace.NoetherianSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (ih_irred : ∀ (Y : TopCat.{u}) [TopologicalSpace.NoetherianSpace Y]
      [IrreducibleSpace Y] (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y ≤ topologicalKrullDim X →
      n > topologicalKrullDim Y → Subsingleton (Sheaf.H G n)) :
    Subsingleton (Sheaf.H F n) := by
  admit
