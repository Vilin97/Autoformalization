/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Inertia
import McKayConjecture.Character.Transport

/-!
# Transporting a normal subgroup into an intermediate subgroup

If `N ◁ G` and `N ≤ H ≤ G`, the subgroup `N.subgroupOf H` is the
canonical internal copy of `N` in `H`.  The identity-on-elements group
equivalence transports prime-to-`p` irreducible characters to this copy.
The transport is equivariant for `H`, and its inertia group is exactly the
pullback to `H` of the original inertia group.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace IrreducibleCharacter

variable {G : Type u} [Group G]
variable (N H : Subgroup G) [N.Normal]
variable (hNH : N ≤ H)

/-- The canonical copy of `N` inside `H`. -/
abbrev internalNormal :
    Subgroup H :=
  N.subgroupOf H

/-- The identity-on-elements equivalence from the internal copy back to
`N`. -/
abbrev internalNormalEquiv :
    internalNormal N H ≃* N :=
  Subgroup.subgroupOfEquivOfLe hNH

/-- Transport prime-to-`p` characters from `N` to its copy in `H`. -/
def internalNormalPPrimeEquiv
    (p : ℕ) :
    PPrimeIrreducibleCharacter N p ≃
      PPrimeIrreducibleCharacter (internalNormal N H) p :=
  pPrimeComapEquiv p (internalNormalEquiv N H hNH)

@[simp]
theorem internalNormalPPrimeEquiv_apply_coe
    (p : ℕ) (θ : PPrimeIrreducibleCharacter N p) :
    (internalNormalPPrimeEquiv N H hNH p θ).1 =
      θ.1.comap (internalNormalEquiv N H hNH) :=
  rfl

/-- The canonical character transport is equivariant under the restricted
action of `H`. -/
theorem internalNormalPPrimeEquiv_smul
    (p : ℕ) (h : H)
    (θ : PPrimeIrreducibleCharacter N p) :
    internalNormalPPrimeEquiv N H hNH p
        (((h : H) : G) • θ) =
      h • internalNormalPPrimeEquiv N H hNH p θ := by
  apply Subtype.ext
  apply IrreducibleCharacter.ext
  funext x
  rfl

/-- The target inertia group is the pullback to `H` of the source inertia
group. -/
theorem inertia_internalNormalPPrimeEquiv_eq_comap
    (p : ℕ) (θ : PPrimeIrreducibleCharacter N p) :
    IrreducibleCharacter.inertia
        (internalNormal N H)
        (internalNormalPPrimeEquiv N H hNH p θ).1 =
      (IrreducibleCharacter.inertia N θ.1).comap H.subtype := by
  ext h
  rw [Subgroup.mem_comap,
    IrreducibleCharacter.mem_inertia_iff,
    IrreducibleCharacter.mem_inertia_iff]
  constructor
  · intro hfix
    have hfix' :
        h • internalNormalPPrimeEquiv N H hNH p θ =
          internalNormalPPrimeEquiv N H hNH p θ := by
      apply Subtype.ext
      exact hfix
    have htransport :
        internalNormalPPrimeEquiv N H hNH p
            (((h : H) : G) • θ) =
          internalNormalPPrimeEquiv N H hNH p θ := by
      rw [internalNormalPPrimeEquiv_smul]
      exact hfix'
    exact
      congrArg Subtype.val
        ((internalNormalPPrimeEquiv N H hNH p).injective
          htransport)
  · intro hfix
    have hfix' :
        (((h : H) : G) • θ) = θ := by
      apply Subtype.ext
      exact hfix
    have htransport :=
      congrArg
        (internalNormalPPrimeEquiv N H hNH p)
        hfix'
    rw [internalNormalPPrimeEquiv_smul] at htransport
    exact congrArg Subtype.val htransport

end IrreducibleCharacter
end McKayConjecture
