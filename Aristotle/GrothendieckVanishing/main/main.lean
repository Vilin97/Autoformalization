/-
  Grothendieck's Vanishing Theorem (Hartshorne III, Theorem 2.7)

  For a Noetherian topological space X of dimension n, and any sheaf F
  of abelian groups on X, H^i(X, F) = 0 for all i > n.

  Sorry's:
  1. FlasqueVanishing — flasque sheaves have vanishing higher cohomology
  2. ReducibleVanishing — reduction from reducible to irreducible (needs j_!)
  3. IrreduciblePosVanishing — irreducible dim ≥ 1 case (needs j_!)

  File structure:
  - Setup.lean: category instances + 3 sorry'd theorems
  - Auxiliary.lean: topology/dimension helpers + counterexample (flasque ≠ injective)
  - ConstantSheafFlasque.lean: PROVED — constant sheaf on irreducible space is flasque
  - CohomologyIso.lean: PROVED — H'(⊤, F) ≅ H(F)
  - DimZeroVanishing.lean: PROVED — irreducible dim 0 case
  - ClosedOpenDecomposition.lean: PROVED — reduction to irreducible (modulo ReducibleVanishing)
  - IrreducibleStep.lean: PROVED — irreducible step (modulo IrreduciblePosVanishing)
  - GrothendieckVanishing.lean: PROVED — main theorem by well-founded induction
-/
import Aristotle.GrothendieckVanishing.main.GrothendieckVanishing

#check GrothendieckVanishing
#check FlasqueVanishing
