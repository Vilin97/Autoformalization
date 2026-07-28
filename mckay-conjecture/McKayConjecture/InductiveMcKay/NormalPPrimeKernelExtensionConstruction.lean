/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.NormalHallPPrimeExtension
import McKayConjecture.InductiveMcKay.NormalPPrimeKernelGlauberman

/-!
# Constructing invariant extensions over a normal prime-to-p kernel

The Schur--Zassenhaus splitting of the finite projective factor set supplies
the invariant extensions required in the normal `p'`-kernel branch of the
central-intersection reduction.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalPPrimeKernelGlauberman

open CentralIntersectionKernelAssembly

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (K P : Subgroup G) [K.Normal]

/-- Construct all prime-to-`p` invariant extensions for a normal
prime-to-`p` kernel and `p`-group quotient. -/
def invariantPPrimeExtensionDataOfPPrimeKernel
    (s : CentralIntersectionSetup (p := p) K P)
    (hK : GroupTheory.IsPPrimeGroup p K) :
    InvariantPPrimeExtensionData K P s where
  extension theta :=
    Classical.choose
      (CharacterTriple.exists_pPrime_extension_of_normalHall_inertiaTop
        K theta.1.1
        (GlaubermanCorrespondence.inertia_eq_top_of_generate
          s.generate theta)
        hK s.quotientPGroup theta.1.2)
  isExtension theta :=
    Classical.choose_spec
      (CharacterTriple.exists_pPrime_extension_of_normalHall_inertiaTop
        K theta.1.1
        (GlaubermanCorrespondence.inertia_eq_top_of_generate
          s.generate theta)
        hK s.quotientPGroup theta.1.2)

end NormalPPrimeKernelGlauberman
end InductiveMcKay
end McKayConjecture
