/-
  Grothendieck's Vanishing Theorem (Hartshorne III, Theorem 2.7)

  For a Noetherian topological space X of dimension n, and any sheaf F
  of abelian groups on X, H^i(X, F) = 0 for all i > n.

  FULLY PROVED — 0 sorry's, 0 axioms, 0 admits.
  The last sorry (Gabriel's theorem) was eliminated by replacing "filtered colimits of
  injectives are injective" with "filtered colimits of flasque sheaves are flasque"
  (isFlasque_filtered_colimit) + FlasqueVanishing, since injective ⟹ flasque.

  File structure:
  - FlasqueVanishing.lean + FlasqueCohomology.lean: IsFlasqueSheaf, FlasqueVanishing, dim shift
  - SetupCore.lean: PushforwardHVanishing, closedImmersionSES, dimension shift, epi lemmas
  - TopologicalKrullDim.lean: topological Krull dimension API
  - ClosedImmersion.lean: closed immersion counit/stalk infrastructure
  - ZeroOutside.lean + ZeroOutsideFinset.lean: extension-by-zero sheaf machinery
  - ConstantSheafFlasque.lean: constant sheaf on irreducible space is flasque
  - DimZeroVanishing.lean: irreducible dim 0 case
  - ReducibleVanishing.lean: reducible case via Finset.induction
  - ClosedOpenDecomposition.lean: reduction to irreducible
  - PresheafFilteredColimit.lean: presheaf colimit is sheaf on Noetherian spaces (PROVED)
  - FiniteGeneratorReduction.lean: colimit step, f.g. vanishing (FULLY PROVED)
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
