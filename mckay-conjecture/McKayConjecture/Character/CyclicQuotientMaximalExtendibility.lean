/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CyclicMaximalExtendibility

/-!
# Maximal extendibility from a cyclic ambient quotient

If `N ◁ G` and `G/N` is cyclic, then every inertia quotient
`I_G(χ)/N` embeds as a subgroup of `G/N` and is therefore cyclic.
Combining this elementary first-isomorphism argument with the cyclic
extension construction gives maximal extendibility of `N` in `G`.

This is a useful entry point for applying the cyclic-extension and
Gallagher layers in reductions with a cyclic factor.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace IrreducibleCharacter

variable {G : Type u} [Group G] [Finite G]
variable (N : Subgroup G) [N.Normal]

omit [Finite G] in
/-- If `G/N` is cyclic, all character inertia quotients over `N` are
cyclic. -/
theorem hasCyclicInertiaQuotients_of_cyclicQuotient
    [IsCyclic (G ⧸ N)] :
    HasCyclicInertiaQuotients N := by
  intro χ
  let I : Subgroup G := inertia N χ
  let f : I →* G ⧸ N :=
    (QuotientGroup.mk' N).comp I.subtype
  have hker :
      N.subgroupOf I = f.ker := by
    ext x
    change (x : G) ∈ N ↔
      QuotientGroup.mk' N (x : G) = 1
    exact (QuotientGroup.eq_one_iff (x : G)).symm
  let e :
      inertiaQuotient N χ ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivRange f)
  letI : IsCyclic f.range := inferInstance
  exact isCyclic_of_surjective e.symm e.symm.surjective

/-- A normal subgroup with cyclic ambient quotient is maximally
extendible. -/
theorem maximallyExtendible_of_cyclicQuotient
    [IsCyclic (G ⧸ N)] :
    IsMaximallyExtendible N :=
  maximallyExtendible_of_cyclicInertiaQuotients N
    (hasCyclicInertiaQuotients_of_cyclicQuotient N)

/-- The corresponding chosen extension map. -/
def extensionMapOfCyclicQuotient
    [IsCyclic (G ⧸ N)] :
    ExtensionMap N :=
  ExtensionMap.ofMaximallyExtendible
    (maximallyExtendible_of_cyclicQuotient N)

end IrreducibleCharacter
end McKayConjecture
