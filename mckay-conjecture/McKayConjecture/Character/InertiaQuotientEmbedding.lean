/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InertiaQuotientIndex
import McKayConjecture.GroupTheory.PPrimeCore
import Mathlib.Data.Nat.Squarefree

/-!
# Embedding an inertia quotient in the ambient quotient

For `N ◁ G` and `θ ∈ Irr(N)`, inclusion of the inertia group in `G`
induces the canonical injection

`I_G(θ) / N ↪ G / N`.

Besides recording this map explicitly, this file transfers cyclicity and
the `p′`-group property from the ambient quotient to the inertia quotient.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace CliffordEquivalence

open GroupTheory

variable {G : Type u} [Group G] [Finite G]
variable (N : Subgroup G) [N.Normal]
variable (theta : IrreducibleCharacter N)

noncomputable local instance : Fintype G :=
  Fintype.ofFinite G

/-- The canonical inclusion of an inertia quotient in the ambient
quotient. -/
def inertiaQuotientEmbedding :
    (IrreducibleCharacter.inertia N theta ⧸
        N.subgroupOf
          (IrreducibleCharacter.inertia N theta)) →*
      G ⧸ N :=
  QuotientGroup.map
    (N.subgroupOf
      (IrreducibleCharacter.inertia N theta)) N
    (IrreducibleCharacter.inertia N theta).subtype
    (by
      intro x hx
      exact hx)

@[simp]
theorem inertiaQuotientEmbedding_mk
    (x : IrreducibleCharacter.inertia N theta) :
    inertiaQuotientEmbedding N theta
        (QuotientGroup.mk'
          (N.subgroupOf
            (IrreducibleCharacter.inertia N theta)) x) =
      QuotientGroup.mk' N (x : G) :=
  rfl

/-- The canonical map from an inertia quotient to the ambient quotient is
injective. -/
theorem inertiaQuotientEmbedding_injective :
    Function.Injective
      (inertiaQuotientEmbedding N theta) := by
  apply
    (QuotientGroup.injective_lift_iff
      (N.subgroupOf
        (IrreducibleCharacter.inertia N theta))
      ((QuotientGroup.mk' N).comp
        (IrreducibleCharacter.inertia N theta).subtype)
      (by
        intro x hx
        apply MonoidHom.mem_ker.mpr
        exact
          (QuotientGroup.eq_one_iff (N := N) (x : G)).mpr hx)).2
  ext x
  change
    x ∈ N.subgroupOf
        (IrreducibleCharacter.inertia N theta) ↔
      QuotientGroup.mk' N (x : G) = 1
  exact
    (QuotientGroup.eq_one_iff (N := N) (x : G)).symm

/-- The order of an inertia quotient divides the order of the ambient
quotient. -/
theorem card_inertiaQuotient_dvd_card_ambientQuotient :
    Nat.card
        (IrreducibleCharacter.inertia N theta ⧸
          N.subgroupOf
            (IrreducibleCharacter.inertia N theta)) ∣
      Nat.card (G ⧸ N) := by
  let f := inertiaQuotientEmbedding N theta
  calc
    Nat.card
          (IrreducibleCharacter.inertia N theta ⧸
            N.subgroupOf
              (IrreducibleCharacter.inertia N theta)) =
        Nat.card (MonoidHom.range f) :=
      Nat.card_congr
        (MonoidHom.ofInjective
          (inertiaQuotientEmbedding_injective N theta)).toEquiv
    _ ∣ Nat.card (G ⧸ N) :=
      Subgroup.card_subgroup_dvd_card
        (MonoidHom.range f)

/-- If the ambient quotient is cyclic, every inertia quotient is cyclic. -/
theorem inertiaQuotient_isCyclic
    (hcyclic : IsCyclic (G ⧸ N)) :
    IsCyclic
      (IrreducibleCharacter.inertia N theta ⧸
        N.subgroupOf
          (IrreducibleCharacter.inertia N theta)) := by
  letI : IsCyclic (G ⧸ N) := hcyclic
  exact
    isCyclic_of_injective
      (inertiaQuotientEmbedding N theta)
      (inertiaQuotientEmbedding_injective N theta)

/-- If the ambient quotient has order prime to `p`, every inertia quotient
has order prime to `p`. -/
theorem inertiaQuotient_isPPrimeGroup
    {p : ℕ}
    (hPPrime : IsPPrimeGroup p (G ⧸ N)) :
    IsPPrimeGroup p
      (IrreducibleCharacter.inertia N theta ⧸
        N.subgroupOf
          (IrreducibleCharacter.inertia N theta)) := by
  let f := inertiaQuotientEmbedding N theta
  have hrange :
      IsPPrimeGroup p (MonoidHom.range f) :=
    hPPrime.to_subgroup (MonoidHom.range f)
  exact
    hrange.of_equiv
      (MonoidHom.ofInjective
        (inertiaQuotientEmbedding_injective N theta)).symm

/-- Squarefreeness of the ambient quotient order passes to every inertia
quotient. -/
theorem inertiaQuotient_card_squarefree
    (hsquarefree :
      Squarefree (Nat.card (G ⧸ N))) :
    Squarefree
      (Nat.card
        (IrreducibleCharacter.inertia N theta ⧸
          N.subgroupOf
            (IrreducibleCharacter.inertia N theta))) :=
  hsquarefree.squarefree_of_dvd
    (card_inertiaQuotient_dvd_card_ambientQuotient
      N theta)

end CliffordEquivalence
end McKayConjecture
