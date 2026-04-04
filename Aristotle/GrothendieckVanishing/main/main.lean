/-
  Grothendieck's Vanishing Theorem (Hartshorne III, Theorem 2.7)

  For a Noetherian topological space X of dimension n, and any sheaf F
  of abelian groups on X, H^i(X, F) = 0 for all i > n.

  Sorry's (2 remaining, both in sheafH_filtered_colimit_aux in FiniteGeneratorReduction.lean):
  - h_van_Q n=0: H^0(Q_j) = 0 for quotient diagram (needs direct H^1 surjectivity argument)
  - h_van_Q n≥1: Mono condition on c'.ι.app j ≫ ι' (provable with mono coprojections)
  Both arise from proving sheaf cohomology H^n commutes with filtered colimits.

  File structure:
  - FlasqueVanishing.lean + FlasqueCohomology.lean: IsFlasqueSheaf, FlasqueVanishing, dim shift
  - SetupCore.lean: PushforwardHVanishing, ClosedImmersionSES, dimension shift lemmas
  - Setup.lean: ReducibleVanishing, IrreduciblePosVanishing wrappers
  - Auxiliary.lean: topology/dimension helpers
  - ClosedImmersion.lean: closed immersion counit/stalk infrastructure
  - ZeroOutside.lean + ZeroOutsideFinset.lean: extension-by-zero sheaf machinery
  - ConstantSheafFlasque.lean: constant sheaf on irreducible space is flasque
  - CohomologyIso.lean: H'(⊤, F) ≅ H(F) isomorphisms
  - DimZeroVanishing.lean: irreducible dim 0 case
  - ReducibleVanishing.lean: reducible case via Finset.induction
  - ClosedOpenDecomposition.lean: reduction to irreducible
  - FiniteGeneratorReduction.lean: colimit step, filtered diagram, f.g. vanishing (2 sorry's)
  - SheafStalkAlgebra.lean + StalkGeneratorAlgebra.lean: stalk algebra, generator section
  - IrreducibleStep.lean: irreducible step assembly
  - GrothendieckVanishing.lean: main theorem + cascade theorems
-/
import Aristotle.GrothendieckVanishing.main.ClosedImmersion
import Aristotle.GrothendieckVanishing.main.ZeroOutside
import Aristotle.GrothendieckVanishing.main.ZeroOutsideFinset
import Aristotle.GrothendieckVanishing.main.GrothendieckVanishing

#check GrothendieckVanishing
#check FlasqueVanishing
