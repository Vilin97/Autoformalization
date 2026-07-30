/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CharacterCenterDegreeDivisibility
import McKayConjecture.Character.NavarroRelativeDegree
import McKayConjecture.CharacterTriple.AssociatedFiniteFactorMultiplicityCharacter
import McKayConjecture.CharacterTriple.Inertia

/-!
# Relative-degree divisibility above an inertia character

For `N ◁ G`, `θ ∈ Irr(N)`, and `ψ ∈ Irr(I_G(θ) | θ)`, the relative
degree `ψ(1) / θ(1)` divides `|I_G(θ) / N|`.

The proof realizes the relative degree as the degree of the irreducible
multiplicity character on the finite factor-set extension of
`I_G(θ) / N`.  Character-center degree divisibility applies because the
central kernel of that extension lies in the character center.
-/

noncomputable section

namespace McKayConjecture
namespace CliffordCorrespondence

variable {G : Type} [Group G] [Finite G]

/-- The relative degree of every irreducible character above an inertia
character divides the order of the inertia quotient. -/
theorem inertiaRelativeDegreeDivisibility
    (N : Subgroup G) [N.Normal]
    (θ : IrreducibleCharacter N) :
    InertiaRelativeDegreeDivisibility N θ := by
  intro ψ
  let T := CharacterTriple.ofInertia N θ
  let R := CharacterTriple.AssociatedGeneralExistence.associated T
  let ψT :=
    CharacterTriple.irreducibleCharactersOverInertiaEquivTriple N θ ψ
  let ξ :=
    R.associatedFiniteMultiplicityExtensionCharacter ψT.1 ψT.2
  refine ⟨ξ.degree, ?_, ?_⟩
  · let projection :=
      CharacterTriple.FactorSet.CentralExtensionGroup.projection
        R.associatedFiniteQuotientFactorSet
        R.associatedFiniteQuotientFactorSet_isNormalized
    have hkernel :
        projection.ker ≤ ξ.characterCenter := by
      exact
        (CharacterTriple.FactorSet.CentralExtensionGroup.projection_ker_le_center
          R.associatedFiniteQuotientFactorSet
          R.associatedFiniteQuotientFactorSet_isNormalized).trans
            ξ.center_le_characterCenter
    have hcenterIndex :
        ξ.characterCenter.index ∣ projection.ker.index :=
      Subgroup.index_dvd_of_le hkernel
    have hdegree :
        ξ.degree ∣ projection.ker.index :=
      ξ.degree_dvd_characterCenter_index.trans hcenterIndex
    have hkernelIndex :
        projection.ker.index =
          Nat.card
            ((IrreducibleCharacter.inertia N θ) ⧸
              (CharacterTriple.ofInertia N θ).normalSubgroup) := by
      rw [Subgroup.index_ker]
      exact
        Nat.card_congr
          ((MulEquiv.subgroupCongr
            (projection.range_eq_top.mpr
              (CharacterTriple.FactorSet.CentralExtensionGroup.projection_surjective
                R.associatedFiniteQuotientFactorSet
                R.associatedFiniteQuotientFactorSet_isNormalized))).trans
            Subgroup.topEquiv)
    rw [hkernelIndex] at hdegree
    simpa [IrreducibleCharacter.inertiaQuotient, T] using hdegree
  · have hdegree :=
      R.associatedFiniteMultiplicityExtensionCharacter_degree_mul
        ψT.1 ψT.2
    have hθdegree :
        T.character.degree = θ.degree := by
      simp [T, CharacterTriple.ofInertia,
        CliffordEquivalence.inertiaCopyCharacter]
    change ξ.degree * θ.degree = ψT.1.degree
    rw [← hθdegree]
    exact hdegree

end CliffordCorrespondence
end McKayConjecture
