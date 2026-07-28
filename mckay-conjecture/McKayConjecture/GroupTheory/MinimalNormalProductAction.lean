/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.MinimalNormalFactorAction
import McKayConjecture.GroupTheory.NormalConjugation

/-!
# Conjugation on a product decomposition of a minimal normal subgroup

Transporting ambient conjugation through the internal direct-product
equivalence gives an action on the product of the simple factors.  Its
kernel remains the ambient centralizer, so the quotient by that centralizer
is identified with the induced automorphism group of the factor product.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory
namespace MinimalNormalFactors

variable {G : Type u} [Group G]
variable {N : Subgroup G} [N.Normal]

namespace NonabelianMinimalNormalDecomposition

/-- Ambient conjugation, transported to the external product of the simple
factors in a nonabelian minimal-normal decomposition. -/
def productConjugation
    (D : NonabelianMinimalNormalDecomposition N) :
    G →* MulAut (∀ i, D.factor i) :=
  (MulAut.congr D.productEquiv.symm).toMonoidHom.comp
    (MulAut.conjNormal (H := N))

/-- Transport to the factor product does not change the kernel of ambient
conjugation. -/
theorem ker_productConjugation
    (D : NonabelianMinimalNormalDecomposition N) :
    D.productConjugation.ker =
      Subgroup.centralizer (N : Set G) := by
  rw [productConjugation,
    MonoidHom.ker_comp_of_injective
      (MulAut.conjNormal (H := N))
      (MulAut.congr D.productEquiv.symm).toMonoidHom
      (MulAut.congr D.productEquiv.symm).injective,
    ker_conjNormal]

/-- The automorphisms of the factor product induced by the ambient group. -/
abbrev ProductConjugationImage
    (D : NonabelianMinimalNormalDecomposition N) :=
  D.productConjugation.range

/-- The first isomorphism theorem for the transported action on the product
of simple factors. -/
def quotientCentralizerEquivProductConjugationImage
    (D : NonabelianMinimalNormalDecomposition N) :
    G ⧸ Subgroup.centralizer (N : Set G) ≃*
      D.ProductConjugationImage :=
  (QuotientGroup.quotientMulEquivOfEq
      D.ker_productConjugation.symm).trans
    (QuotientGroup.quotientKerEquivRange
      D.productConjugation)

end NonabelianMinimalNormalDecomposition

end MinimalNormalFactors
end GroupTheory
end McKayConjecture
