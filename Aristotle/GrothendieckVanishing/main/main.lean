/-
  Grothendieck's Vanishing Theorem (Hartshorne III, Theorem 2.7)

  For a Noetherian topological space X of dimension n, and any sheaf F
  of abelian groups on X, H^i(X, F) = 0 for all i > n.

  Sorry's (1 remaining — gabriel_injective_of_filtered_colimit in FiniteGeneratorReduction.lean):
  - Gabriel's theorem: filtered colimits of injective sheaves are injective on Noetherian
    spaces. TRUE standard mathematical fact (Gabriel's thesis; Hartshorne, Residues and
    Duality, Ch. II, Thm. 7.8). Proof requires Baer's criterion + locally Noetherian
    subobjects are finitely presentable. All other sorry's have been eliminated.

  File structure:
  - FlasqueVanishing.lean + FlasqueCohomology.lean: IsFlasqueSheaf, FlasqueVanishing, dim shift
  - SetupCore.lean: PushforwardHVanishing, ClosedImmersionSES, dimension shift, epi lemmas
  - Setup.lean: ReducibleVanishing, IrreduciblePosVanishing wrappers
  - Auxiliary.lean: topology/dimension helpers
  - ClosedImmersion.lean: closed immersion counit/stalk infrastructure
  - ZeroOutside.lean + ZeroOutsideFinset.lean: extension-by-zero sheaf machinery
  - ConstantSheafFlasque.lean: constant sheaf on irreducible space is flasque
  - CohomologyIso.lean: H'(⊤, F) ≅ H(F) isomorphisms
  - DimZeroVanishing.lean: irreducible dim 0 case
  - ReducibleVanishing.lean: reducible case via Finset.induction
  - ClosedOpenDecomposition.lean: reduction to irreducible
  - PresheafFilteredColimit.lean: presheaf colimit is sheaf on Noetherian spaces (PROVED)
  - FiniteGeneratorReduction.lean: colimit step, f.g. vanishing (1 sorry: Gabriel's theorem)
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
