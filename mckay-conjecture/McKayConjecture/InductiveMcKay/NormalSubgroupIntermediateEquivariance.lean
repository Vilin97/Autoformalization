/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AutomorphismInvariantSubgroupOperations
import McKayConjecture.InductiveMcKay.NormalSubgroupJoinCenterReduction

/-!
# Automorphism invariance of Rossi's normal-subgroup intermediate

If `N` is invariant under `Aut(G)_P`, then so are `N Z(G)` and
`N Z(G) N_G(P)`.  This is the subgroup-theoretic part of packaging
Proposition 4.2 as an equivariant local correspondence.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupJoinCenterReduction

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (P : Sylow p G) (N : Subgroup G) [N.Normal]

/-- Adjoining the center preserves invariance under `Aut(G)_P`. -/
theorem joinCenter_invariant
    (hN :
      AutomorphismInvariant (SylowAutStabilizer P) N) :
    AutomorphismInvariant
      (SylowAutStabilizer P) (joinCenter N) :=
  hN.sup AutomorphismInvariant.center

/-- Rossi's intermediate `N Z(G) N_G(P)` is invariant under
`Aut(G)_P`. -/
theorem normalizerIntermediate_invariant
    (hN :
      AutomorphismInvariant (SylowAutStabilizer P) N) :
    AutomorphismInvariant
      (SylowAutStabilizer P)
      (normalizerIntermediate P N) :=
  (joinCenter_invariant P N hN).sup
    (SylowAutStabilizer.normalizer_invariant P)

end NormalSubgroupJoinCenterReduction
end InductiveMcKay
end McKayConjecture
