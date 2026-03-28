/-
  Grothendieck's Vanishing Theorem (Hartshorne III, Theorem 2.7)

  For a Noetherian topological space X of dimension n, and any sheaf F
  of abelian groups on X, H^i(X, F) = 0 for all i > n.

  File structure:
  - Setup.lean: category instances + FlasqueVanishing axiom
  - Auxiliary.lean: topology/dimension helpers (irreducible dim 0 characterization)
  - DimZeroVanishing.lean: PROVED — irreducible dim 0 case
  - ClosedOpenDecomposition.lean: axiom — reduction to irreducible (needs j_!)
  - IrreducibleStep.lean: axiom — irreducible dim ≥ 1 (needs j_!)
  - GrothendieckVanishing.lean: assembled (modulo axioms in Setup.lean) — main theorem by induction
-/
import Aristotle.GrothendieckVanishing.main.GrothendieckVanishing

-- Re-export the main theorem
#check GrothendieckVanishing
-- DO NOT PROVE FlasqueVanishing, JUST USE IT AS NEEDED
#check FlasqueVanishing
