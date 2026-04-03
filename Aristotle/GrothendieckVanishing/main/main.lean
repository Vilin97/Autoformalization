/-
  Grothendieck's Vanishing Theorem (Hartshorne III, Theorem 2.7)

  For a Noetherian topological space X of dimension n, and any sheaf F
  of abelian groups on X, H^i(X, F) = 0 for all i > n.

  Sorry's (2 remaining):
  - isSheaf_filtered_colimit_of_sheaves (SheafHom.lean:63) — filtered presheaf colimits of
    sheaves are sheaves on Noetherian spaces (AB5: filtered colimits commute with finite
    limits in the sheaf condition).
  - hQprov (FiniteGeneratorReduction.lean:198) — recursive quotient vanishing for IH call.

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
  - SheafHom.lean: Hom(Z_X,-) preserves filtered colimit vanishing (1 sorry: AB5)
  - FiniteGeneratorReduction.lean: colimit step, filtered diagram, f.g. vanishing (1 sorry: hQprov)
  - IrreducibleStep.lean: irreducible step assembly
  - GrothendieckVanishing.lean: main theorem + cascade theorems
-/
import Aristotle.GrothendieckVanishing.main.ClosedImmersion
import Aristotle.GrothendieckVanishing.main.ZeroOutside
import Aristotle.GrothendieckVanishing.main.ZeroOutsideFinset
import Aristotle.GrothendieckVanishing.main.GrothendieckVanishing

#check GrothendieckVanishing
#check FlasqueVanishing
