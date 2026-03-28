/-
  Grothendieck's Vanishing Theorem (Hartshorne III, Theorem 2.7)

  For a Noetherian topological space X of dimension n, and any sheaf F
  of abelian groups on X, H^i(X, F) = 0 for all i > n.

  Single remaining gap: FlasqueVanishing (= Grothendieck vanishing itself)
  All other theorems are fully proved.

  File structure:
  - Setup.lean: category instances + FlasqueVanishing (single remaining gap)
  - Auxiliary.lean: topology/dimension helpers
  - ConstantSheafFlasque.lean: PROVED — constant sheaf on irreducible space is flasque
  - CohomologyIso.lean: PROVED — H'(⊤, F) ≅ H(F)
  - DimZeroVanishing.lean: PROVED — irreducible dim 0 case (via projectivity)
  - ClosedOpenDecomposition.lean: reduction to irreducible
  - IrreducibleStep.lean: irreducible dim ≥ 1 case
  - GrothendieckVanishing.lean: main theorem by well-founded induction
-/
import Aristotle.GrothendieckVanishing.main.GrothendieckVanishing

#check GrothendieckVanishing
#check FlasqueVanishing
