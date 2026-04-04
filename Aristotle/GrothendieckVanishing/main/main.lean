/-
  Grothendieck's Vanishing Theorem (Hartshorne III, Theorem 2.7)

  For a Noetherian topological space X of dimension n, and any sheaf F
  of abelian groups on X, H^i(X, F) = 0 for all i > n.

  Sorry's (1 remaining in sheafH_filtered_colimit_aux in FiniteGeneratorReduction.lean):
  - hmono_ι: ∀ j, Mono (c'.ι.app j) — mono coprojections for filtered diagram.
    True at call site (finsetGenFunctor has mono transitions → mono_ι_app_of_isFiltered),
    but the recursive IH call on the quotient diagram Q reintroduces this sorry
    (Q has epi, not mono, coprojections). Requires Čech cohomology to close.

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
  - FiniteGeneratorReduction.lean: colimit step, f.g. vanishing (1 sorry: hmono_ι)
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
