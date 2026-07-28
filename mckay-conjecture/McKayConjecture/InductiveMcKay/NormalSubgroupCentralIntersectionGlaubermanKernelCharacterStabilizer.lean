/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanProjectiveMultiplicity
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionNormalizerAssemblyNaturality

/-!
# The canonical ambient character's Glauberman kernel representative

The active Clifford orbit of a prime-to-`q` character of `CS` selects a
canonical `P`-invariant character of the normal `q'`-kernel.  This file
proves that every ambient-normalizer element fixing the ambient character
also fixes that canonical kernel representative.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace ComplementReduction

open CliffordPartition

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

noncomputable local instance productGlaubermanKernelCharacterStabilizerFintype :
    Fintype (product S C) :=
  Fintype.ofFinite (product S C)

/-- The canonical invariant kernel character selected by the active
Clifford orbit of an ambient prime-to-`q` character. -/
abbrev productAmbientGlaubermanSourceKernelCharacter
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q) :
    PInvariantPPrimeIrreducibleCharacter
      (productPPrimeKernel S C hcentral)
      (productSylow S C : Subgroup (product S C)) q :=
  GlaubermanCorrespondence.invariantCharacterOfActiveOrbit
    (K := productPPrimeKernel S C hcentral)
    (P := (productSylow S C : Subgroup (product S C)))
    (productPPrimeKernelCentralIntersectionSetup
      S C hcentral).quotientPGroup
    (activeOrbitIndex
      (productPPrimeKernel S C hcentral) theta)

/-- Fixing the ambient character fixes the canonical representative of
its active kernel orbit. -/
theorem productAmbientGlaubermanSourceKernelCharacter_fixed_of_fixed
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    (h : ambientNormalizer S)
    (hfix : h • theta = theta) :
    h •
        (productAmbientGlaubermanSourceKernelCharacter
          S C hcentral theta).1 =
      (productAmbientGlaubermanSourceKernelCharacter
        S C hcentral theta).1 := by
  let K := productPPrimeKernel S C hcentral
  let r := activeOrbitIndex K theta
  let d :=
    productSourceActivePPrimeOrbitwiseConjugation
      S C hcentral h
  have horbit :
      productSourceActiveOrbitConjugation
          S C hcentral h r =
        r := by
    have hindex := d.activeOrbitIndex_assemble theta
    rw [productSourceActivePPrimeOrbitwiseConjugation_assemble,
      productSourceActivePPrimeOrbitwiseConjugation_activeOrbitEquiv]
      at hindex
    change
      activeOrbitIndex K (h • theta) =
        productSourceActiveOrbitConjugation
          S C hcentral h r at hindex
    rw [hfix] at hindex
    exact hindex.symm
  change h • r.pPrimeOut K = r.pPrimeOut K
  have hrepresentative :=
    productSourceActiveOrbitConjugation_pPrimeOut
      S C hcentral h r
  rw [horbit] at hrepresentative
  exact hrepresentative.symm

end ComplementReduction
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
