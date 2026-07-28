/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionDirectProductActivation

/-!
# Local activation for the central-intersection reduction

This module exposes the fixed-point activation theorem under the name used
by the Glauberman/Okuyama--Wajima assembly.  The construction itself lives
in `NormalSubgroupCentralIntersectionDirectProductActivation`: it extends a
fixed-point character by the trivial Sylow character in direct-product
coordinates and transports activity back to the actual normalizer.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace ComplementReduction

open CliffordPartition
open CentralIntersectionKernelAssembly

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- Every prime-to-`q` fixed-point character is active in the local
Clifford partition. -/
theorem productFixedPointCharacter_isActive
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (φ :
      PPrimeIrreducibleCharacter
        (productPPrimeKernelFixedPoints
          S C hcentral) q) :
    IsActivePPrimeCharacter
      (internalKernelNormalizer
        (productPPrimeKernel S C hcentral)
        (productSylow S C :
          Subgroup (product S C)))
      (IrreducibleCharacter.pPrimeComapEquiv q
        (localKernelAmbientFixedPointsEquiv
          S C hcentral) φ) :=
  productPPrimeKernel_fixedPointCharacter_active
    S C hcentral φ

end ComplementReduction
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
