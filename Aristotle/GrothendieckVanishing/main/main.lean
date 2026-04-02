/-
  Grothendieck's Vanishing Theorem (Hartshorne III, Theorem 2.7)

  For a Noetherian topological space X of dimension n, and any sheaf F
  of abelian groups on X, H^i(X, F) = 0 for all i > n.

  Sorry's (1 remaining, Mathlib API gap):
  - ext_comm_filtered_colimit_mono n≥1 case (FiniteGeneratorReduction.lean) —
    Ext^{n+1}(Z,-) preserves filtered colimits of mono diagrams.
    The n=0 case (Hom) is PROVED via constantSheafAdj + direct section argument.
    The n≥1 case requires Čech cohomology / universal δ-functors / Godement resolution.

  File structure:
  - SetupCore.lean: category instances, FlasqueVanishing, PushforwardHVanishing, ClosedImmersionSES
  - Setup.lean: ReducibleVanishing, IrreduciblePosVanishing wrapper
  - Auxiliary.lean: topology/dimension helpers
  - ClosedImmersion.lean: closed immersion counit/stalk infrastructure
  - ZeroOutside.lean: extension-by-zero sheaf machinery
  - ConstantSheafFlasque.lean: constant sheaf on irreducible space is flasque
  - CohomologyIso.lean: H'(⊤, F) ≅ H(F) isomorphisms
  - DimZeroVanishing.lean: irreducible dim 0 case
  - ReducibleVanishing.lean: reducible case via Finset.induction
  - ClosedOpenDecomposition.lean: reduction to irreducible
  - FiniteGeneratorReduction.lean: colimit step, filtered diagram, f.g. vanishing (1 sorry)
  - IrreducibleStep.lean: irreducible step assembly
  - GrothendieckVanishing.lean: main theorem + cascade theorems
-/
import Aristotle.GrothendieckVanishing.main.ClosedImmersion
import Aristotle.GrothendieckVanishing.main.ZeroOutside
import Aristotle.GrothendieckVanishing.main.GrothendieckVanishing

#check GrothendieckVanishing
#check FlasqueVanishing
