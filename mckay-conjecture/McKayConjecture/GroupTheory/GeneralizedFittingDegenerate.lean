/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.GeneralizedFittingCentralizer

/-!
# The degenerate generalized-Fitting case

Bender's self-centralizing theorem immediately rules out
`F*(G) = Z(G)` in a nonabelian finite group.  This is the short structural
step which turns `F(G) = Z(G)` into the strict containment
`F(G) < F*(G)` in the McKay reduction.
-/

noncomputable section

universe u

namespace McKayConjecture.GroupTheory

variable {G : Type u} [Group G] [Finite G]

/-- If the generalized Fitting subgroup of a finite group is its center,
then the whole group is commutative. -/
theorem isMulCommutative_of_generalizedFittingSubgroup_eq_center
    (hFstar :
      generalizedFittingSubgroup G = Subgroup.center G) :
    IsMulCommutative G := by
  rw [← Subgroup.center_eq_top_iff]
  apply top_unique
  calc
    (⊤ : Subgroup G) =
        generalizedFittingCentralizer G := by
      change (⊤ : Subgroup G) =
        Subgroup.centralizer
          (generalizedFittingSubgroup G : Set G)
      rw [hFstar, Subgroup.centralizer_center]
    _ ≤ generalizedFittingSubgroup G :=
      centralizer_generalizedFittingSubgroup_le_self
    _ = Subgroup.center G := hFstar

/-- If `F(G) = Z(G)` in a noncommutative finite group, then `F(G)` is
properly contained in `F*(G)`. -/
theorem fittingSubgroup_lt_generalizedFittingSubgroup_of_eq_center
    (hnoncomm : ¬IsMulCommutative G)
    (hF : fittingSubgroup G = Subgroup.center G) :
    fittingSubgroup G < generalizedFittingSubgroup G := by
  refine lt_of_le_of_ne
    fittingSubgroup_le_generalizedFitting ?_
  intro heq
  apply hnoncomm
  apply
    isMulCommutative_of_generalizedFittingSubgroup_eq_center
  exact heq.symm.trans hF

/-- Under the same hypotheses, the layer cannot be contained in the
ambient center. -/
theorem not_layer_le_center_of_fittingSubgroup_eq_center
    (hnoncomm : ¬IsMulCommutative G)
    (hF : fittingSubgroup G = Subgroup.center G) :
    ¬layer G ≤ Subgroup.center G := by
  intro hE
  have hFstarLe :
      generalizedFittingSubgroup G ≤
        Subgroup.center G :=
    generalizedFittingSubgroup_le hF.le hE
  have hEq :
      generalizedFittingSubgroup G =
        Subgroup.center G :=
    le_antisymm hFstarLe
      (hF ▸ fittingSubgroup_le_generalizedFitting)
  exact hnoncomm
    (isMulCommutative_of_generalizedFittingSubgroup_eq_center hEq)

end McKayConjecture.GroupTheory
