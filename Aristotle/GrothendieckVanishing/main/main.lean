/-
  Grothendieck's Vanishing Theorem (Hartshorne III, Theorem 2.7)

  For a Noetherian topological space X of dimension n, and any sheaf F
  of abelian groups on X, H^i(X, F) = 0 for all i > n.

  Sorry's (2 remaining, both Mathlib API gaps):
  - ext_comm_filtered_colimit_mono (IrreducibleStep.lean) — Ext^n commutes with
    filtered colimits of mono diagrams in Grothendieck abelian categories
  - cohomology_vanishing_of_finitelyGenerated_vanishing (IrreducibleStep.lean) — Step 3A:
    applies the above to the sheaf case (Hartshorne 2.9)

  File structure:
  - SetupCore.lean: category instances, FlasqueVanishing (PROVED),
    PushforwardHVanishing (PROVED), ClosedImmersionSES (PROVED)
  - Setup.lean: ReducibleVanishing (PROVED), IrreduciblePosVanishing (2 sorry's inside)
  - Auxiliary.lean: topology/dimension helpers
  - ClosedImmersion.lean: PROVED — closed immersion counit/stalk infrastructure
  - ZeroOutside.lean: PROVED — zero-outside / extension-by-zero infrastructure
  - ConstantSheafFlasque.lean: PROVED — constant sheaf on irreducible space is flasque
  - CohomologyIso.lean: PROVED — H'(⊤, F) ≅ H(F)
  - DimZeroVanishing.lean: PROVED — irreducible dim 0 case
  - ReducibleVanishing.lean: PROVED — reducible case via Finset.induction
  - ClosedOpenDecomposition.lean: PROVED — reduction to irreducible
  - IrreducibleStep.lean: PROVED — irreducible step (modulo IrreduciblePosVanishing)
  - GrothendieckVanishing.lean: PROVED — main theorem by well-founded induction
-/
import Aristotle.GrothendieckVanishing.main.ClosedImmersion
import Aristotle.GrothendieckVanishing.main.ZeroOutside
import Aristotle.GrothendieckVanishing.main.GrothendieckVanishing

#check GrothendieckVanishing
#check FlasqueVanishing
