/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralIntersectionKernelScalar
import McKayConjecture.InductiveMcKay.CentralScalarLocalCorrespondence
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionReduction

/-!
# Kernel DGN input for Rossi's `CP` central-intersection subgroup

This file specializes `CentralIntersectionKernelAssembly` to the subgroup

`L = C P`

already used by `NormalSubgroupCentralIntersectionReduction`.  It converts
the literal hypothesis `C ∩ P ≤ Z(X)` into the exact internal
central-intersection setup and assembles the Theorem 4.4 character
equivalence from kernel-level DGN data.

Thus the former direct hypothesis

`Irr_{p'}(CP) ≃ Irr_{p'}(N_{CP}(P))`

can be replaced, for the character-equivalence part of the theorem, by
the exact active-orbit DGN correspondence on the smaller groups `C` and
`C ∩ N_{CP}(P)`, with central inertia-triple witnesses.  A stronger
all-kernel-character interface is retained separately for convenience.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction

namespace KernelAssembly

open CharacterTriple
open CentralIntersectionKernelAssembly

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The exact active-orbit DGN datum for the internal extension
`C ◁ CP` and its chosen Sylow subgroup. -/
abbrev ProductActiveKernelDGNData :=
  ActiveKernelDGNData
    (p := q)
    (internalKernel S C)
    (productSylow S C :
      Subgroup (product S C))

/-- The stronger all-kernel-character DGN datum for the same internal
extension.  This is not the preferred faithful interface. -/
abbrev ProductStrongKernelDGNData :=
  StrongKernelDGNData
    (p := q)
    (internalKernel S C)
    (productSylow S C :
      Subgroup (product S C))

omit [Finite X] [Fact q.Prime] in
/-- The exact central-intersection setup internal to `CP`. -/
theorem productCentralIntersectionSetup
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :
    CentralIntersectionSetup
      (p := q)
      (internalKernel S C)
      (productSylow S C :
        Subgroup (product S C)) where
  pSubgroup := (productSylow S C).isPGroup'
  generate := internalKernel_sup_productSylow S C
  quotientPGroup := quotientInternalKernel_isPGroup S C
  intersection_le_center :=
    internalKernel_inf_productSylow_le_center
      S C hcentral

/-- The exact numerical Corollary 5.14 output for `CP`: active-orbit
matching, inertia-fibre equivalences, and their central cross identity. -/
abbrev ProductActiveKernelCentralFibreData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X) :=
  ActiveKernelCentralFibreData
    (p := q)
    (internalKernel S C)
    (productSylow S C :
      Subgroup (product S C))
    (productCentralIntersectionSetup
      S C hcentral)

/-- Assemble the ordinary-character equivalence in Rossi's Theorem 4.4
for `CP` from the exact active-orbit DGN data.

No argument to this definition is an equivalence between the displayed
source and target. -/
def theorem44CharacterEquivOfActiveKernelDGNData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (d : ProductActiveKernelDGNData S C) :
    PPrimeIrreducibleCharacter (product S C) q ≃
      PPrimeIrreducibleCharacter
        (Subgroup.normalizer
          (productSylow S C :
            Set (product S C))) q :=
  pPrimeEquivOfCentralIntersectionActiveKernelDGNData
    (K := internalKernel S C)
    (P := (productSylow S C :
      Subgroup (product S C)))
    (productCentralIntersectionSetup
      S C hcentral)
    d

/-- Assemble the Theorem 4.4 ordinary-character equivalence from the
narrow numerical Corollary 5.14 fibre output. -/
def theorem44CharacterEquivOfCentralFibreData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (d :
      ProductActiveKernelCentralFibreData
        S C hcentral) :
    PPrimeIrreducibleCharacter (product S C) q ≃
      PPrimeIrreducibleCharacter
        (Subgroup.normalizer
          (productSylow S C :
            Set (product S C))) q :=
  ActiveKernelCentralFibreData.assembledPPrimeEquiv
    (internalKernel S C)
    (productSylow S C :
      Subgroup (product S C))
    d

/-- The narrow numerical Corollary 5.14 fibre output is already sufficient
to construct the desired central-scalar local correspondence. -/
def theorem44CentralScalarLocalCorrespondenceOfCentralFibreData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (d :
      ProductActiveKernelCentralFibreData
        S C hcentral) :
    CentralScalarLocalCorrespondence (productSylow S C) where
  toLocalCorrespondence :=
    { intermediate :=
        Subgroup.normalizer
          (productSylow S C :
            Set (product S C))
      normalizer_le := le_rfl
      proper_of_normalizer_ne_top := fun hne =>
        lt_top_iff_ne_top.mpr hne
      correspondence :=
        theorem44CharacterEquivOfCentralFibreData
          S C hcentral d }
  correspondence_central_cross := by
    intro χ z hzcentral hzintermediate
    have h :=
      ActiveKernelCentralFibreData.assembledPPrimeEquiv_central_cross
        (K := internalKernel S C)
        (P := (productSylow S C :
          Subgroup (product S C)))
        d χ z hzcentral
    have hzEq :
        (⟨z,
          Subgroup.center_le_normalizer
            (productSylow S C : Set (product S C))
            hzcentral⟩ :
          Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) =
        ⟨z, hzintermediate⟩ :=
      Subtype.ext rfl
    rw [hzEq] at h
    convert h using 1 <;>
      rfl

/-- Package the active-kernel construction as the exact numerical local
datum: the intermediate group is the Sylow normalizer itself, and the
assembled correspondence preserves normalized values on the center. -/
def theorem44CentralScalarLocalCorrespondenceOfActiveKernelDGNData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (d : ProductActiveKernelDGNData S C) :
    CentralScalarLocalCorrespondence (productSylow S C) where
  toLocalCorrespondence :=
    { intermediate :=
        Subgroup.normalizer
          (productSylow S C :
            Set (product S C))
      normalizer_le := le_rfl
      proper_of_normalizer_ne_top := fun hne =>
        lt_top_iff_ne_top.mpr hne
      correspondence :=
        theorem44CharacterEquivOfActiveKernelDGNData
          S C hcentral d }
  correspondence_central_cross := by
    intro χ z hzcentral hzintermediate
    have h :=
      pPrimeEquivOfCentralIntersectionActiveKernelDGNData_central_cross
        (K := internalKernel S C)
        (P := (productSylow S C :
          Subgroup (product S C)))
        (productCentralIntersectionSetup
          S C hcentral)
        d χ z hzcentral
    have hzEq :
        (⟨z,
          Subgroup.center_le_normalizer
            (productSylow S C : Set (product S C))
            hzcentral⟩ :
          Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) =
        ⟨z, hzintermediate⟩ :=
      Subtype.ext rfl
    rw [hzEq] at h
    convert h using 1 <;>
      rfl

/-- Assemble the same equivalence from the stronger
all-kernel-character interface. -/
def theorem44CharacterEquivOfStrongKernelDGNData
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (d : ProductStrongKernelDGNData S C) :
    PPrimeIrreducibleCharacter (product S C) q ≃
      PPrimeIrreducibleCharacter
        (Subgroup.normalizer
          (productSylow S C :
            Set (product S C))) q :=
  pPrimeEquivOfStrongKernelDGNData
    (K := internalKernel S C)
    (P := (productSylow S C :
      Subgroup (product S C)))
    (productCentralIntersectionSetup
      S C hcentral)
    d

end KernelAssembly

end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
