/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.AutomorphismInertia
import McKayConjecture.Character.CliffordPPrimeCorrespondence
import McKayConjecture.Character.OverAlongTransport

/-!
# Automorphism transport of prime-to-prime inertia fibres

An automorphism of an ambient group preserving a normal subgroup sends the
inertia group of a normal character isomorphically to the inertia group of
the transported character.  Simultaneous pullback along these two
isomorphisms therefore transports the full prime-to-`p` character fibre
lying over that character.

This file records the resulting equivalence and its underlying-character
formula.  It is the fibre-level vertical map used in naturality squares for
Clifford assembly.
-/

noncomputable section

namespace McKayConjecture
namespace IrreducibleCharacter

open CliffordCorrespondence

variable {G : Type} [Group G] [Finite G]
variable (N : Subgroup G) [N.Normal]

/-- The inverse inertia equivalence and inverse restricted automorphism
form a commuting square with the two inertia inclusions. -/
theorem inertiaEquiv_symm_inclusion_commutes
    (a : NormalSubgroupAutStabilizer N)
    (θ : IrreducibleCharacter N) :
    (inertiaEquiv N a θ).symm.toMonoidHom.comp
        (inertiaInclusion N (a • θ)) =
      (inertiaInclusion N θ).comp
        (NormalSubgroupAutStabilizer.restrict a).symm.toMonoidHom := by
  ext n
  exact inertiaEquiv_symm_apply_coe N a θ
    (inertiaInclusion N (a • θ) n)

/-- Pullback along an ambient automorphism preserving `N` transports the
prime-to-`p` inertia fibre over `θ` to the fibre over `a • θ`. -/
def pPrimeInertiaFibreTransportEquiv
    (p : ℕ)
    (a : NormalSubgroupAutStabilizer N)
    (θ : IrreducibleCharacter N) :
    PPrimeIrreducibleCharactersOverInertia N θ p ≃
      PPrimeIrreducibleCharactersOverInertia N (a • θ) p :=
  pPrimeIrreducibleCharactersOverAlongComapEquiv
    (inertiaEquiv N a θ).symm
    (NormalSubgroupAutStabilizer.restrict a).symm
    (inertiaInclusion N θ)
    (inertiaInclusion N (a • θ))
    (inertiaEquiv_symm_inclusion_commutes N a θ)
    θ p

@[simp]
theorem pPrimeInertiaFibreTransportEquiv_apply_character
    (p : ℕ)
    (a : NormalSubgroupAutStabilizer N)
    (θ : IrreducibleCharacter N)
    (χ : PPrimeIrreducibleCharactersOverInertia N θ p) :
    (pPrimeInertiaFibreTransportEquiv N p a θ χ).1.1 =
      χ.1.1.comap (inertiaEquiv N a θ).symm :=
  rfl

@[simp]
theorem pPrimeInertiaFibreTransportEquiv_apply_degree
    (p : ℕ)
    (a : NormalSubgroupAutStabilizer N)
    (θ : IrreducibleCharacter N)
    (χ : PPrimeIrreducibleCharactersOverInertia N θ p) :
    (pPrimeInertiaFibreTransportEquiv N p a θ χ).1.1.degree =
      χ.1.1.degree :=
  rfl

@[simp]
theorem pPrimeInertiaFibreTransportEquiv_symm_apply_character
    (p : ℕ)
    (a : NormalSubgroupAutStabilizer N)
    (θ : IrreducibleCharacter N)
    (χ :
      PPrimeIrreducibleCharactersOverInertia N (a • θ) p) :
    ((pPrimeInertiaFibreTransportEquiv N p a θ).symm χ).1.1 =
      χ.1.1.comap (inertiaEquiv N a θ) :=
  rfl

@[simp]
theorem pPrimeInertiaFibreTransportEquiv_symm_apply_degree
    (p : ℕ)
    (a : NormalSubgroupAutStabilizer N)
    (θ : IrreducibleCharacter N)
    (χ :
      PPrimeIrreducibleCharactersOverInertia N (a • θ) p) :
    ((pPrimeInertiaFibreTransportEquiv
      N p a θ).symm χ).1.1.degree =
        χ.1.1.degree :=
  rfl

end IrreducibleCharacter
end McKayConjecture
