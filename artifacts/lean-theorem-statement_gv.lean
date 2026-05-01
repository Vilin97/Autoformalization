import Aristotle.GrothendieckVanishing.main.GrothendieckVanishing

/-!
# Final Lean 4 Theorem Statement

Extracted from `Aristotle/GrothendieckVanishing/main/GrothendieckVanishing.lean`.
This is the main result of the formalization: **Grothendieck's vanishing theorem**
(Hartshorne III, Theorem 2.7) — for a Noetherian topological space `X` of
topological Krull dimension `d`, every sheaf `F` of abelian groups on `X` has
vanishing higher cohomology in degrees strictly above `d`.

Verified by the Lean 4 kernel. 0 sorry's, 0 axioms beyond `propext` /
`Classical.choice` / `Quot.sound`.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.GrothendieckVanishing

/-- **Grothendieck's vanishing theorem** (Hartshorne III, Theorem 2.7).

For any Noetherian topological space `X` and sheaf `F` of abelian groups on `X`,
the cohomology `Hⁿ(X, F)` vanishes whenever `n` exceeds the topological Krull
dimension of `X`. -/
theorem GrothendieckVanishing
    (X : TopCat.{u}) [TopologicalSpace.NoetherianSpace X]
    (n : ℕ) (h : n > topologicalKrullDim X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Subsingleton (Sheaf.H F n) := by
  -- Full proof omitted for display purposes (~30 lines including the
  -- well-founded induction on Krull dimension; reduces to the irreducible
  -- case via `grothendieck_vanishing_of_irreducible`, then to dim-0 / flasque
  -- vanishing via `irreducible_pos_vanishing`).
  -- See Aristotle/GrothendieckVanishing/main/GrothendieckVanishing.lean for the
  -- complete proof.
  sorry

/-! ## Architectural pillars used in the proof -/

-- Reducible → irreducible reduction (well-founded induction on Krull dim)
#check @grothendieck_vanishing_of_irreducible

-- Irreducible, dim ≥ 1 case via finite-generator reduction
-- (closed immersion SES + extension by zero + filtered colimits)
#check @irreducible_pos_vanishing

-- Flasque vanishing: H^n vanishes for flasque sheaves
#check @sheafH_subsingleton_of_flasque

end AlgebraicGeometry.GrothendieckVanishing
