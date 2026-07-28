/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AutomorphismStabilizer

/-!
# Closure properties of automorphism-invariant subgroups

Elementary lattice operations preserve invariance under a subgroup of the
automorphism group.  These facts are used repeatedly when constructing the
intermediate subgroups in the equivariant Rossi reduction.
-/

namespace McKayConjecture.InductiveMcKay

universe u

variable {G : Type u} [Group G]
variable {A : Subgroup (MulAut G)}
variable {H K : Subgroup G}

namespace AutomorphismInvariant

/-- A characteristic subgroup is invariant under every prescribed
automorphism subgroup. -/
theorem of_characteristic
    (H : Subgroup G) [H.Characteristic] :
    AutomorphismInvariant A H := by
  intro a
  exact
    Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : H.Characteristic) a.1

/-- The join of two invariant subgroups is invariant. -/
theorem sup
    (hH : AutomorphismInvariant A H)
    (hK : AutomorphismInvariant A K) :
    AutomorphismInvariant A (H ⊔ K) := by
  intro a
  rw [Subgroup.map_sup, hH a, hK a]

/-- The meet of two invariant subgroups is invariant. -/
theorem inf
    (hH : AutomorphismInvariant A H)
    (hK : AutomorphismInvariant A K) :
    AutomorphismInvariant A (H ⊓ K) := by
  intro a
  rw [Subgroup.map_inf _ _ _ a.1.injective, hH a, hK a]

/-- The center is invariant. -/
theorem center :
    AutomorphismInvariant A (Subgroup.center G) :=
  of_characteristic (Subgroup.center G)

end AutomorphismInvariant
end McKayConjecture.InductiveMcKay
