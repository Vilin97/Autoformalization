/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Group.Action.End
import McKayConjecture.GroupTheory.GeneralizedFittingCentralizer
import McKayConjecture.GroupTheory.NormalConjugation

/-!
# The generalized-Fitting action

Conjugation gives an action of a group `G` on its generalized Fitting
subgroup `F*(G)`.  For finite `G`, the generalized-Fitting centralizer
theorem identifies the kernel of this action with the ambient image of
`Z(F*(G))`.  Consequently both

`G / C_G(F*(G))` and `G / Z(F*(G))`

embed faithfully in `Aut(F*(G))`.

The same ambient conjugation action permutes the components of `G`.
-/

noncomputable section

universe u

namespace McKayConjecture.GroupTheory

variable (G : Type u) [Group G]

/-- Conjugation of `G` on its generalized Fitting subgroup. -/
abbrev generalizedFittingConjugation :
    G →* MulAut (generalizedFittingSubgroup G) :=
  MulAut.conjNormal

/-- The kernel of conjugation on `F*(G)` is its ambient centralizer. -/
theorem ker_generalizedFittingConjugation :
    (generalizedFittingConjugation G).ker =
      generalizedFittingCentralizer G :=
  ker_conjNormal

/-- The subgroup of `Aut(F*(G))` induced by conjugation by `G`. -/
abbrev GeneralizedFittingConjugationImage :=
  ConjugationImage (generalizedFittingSubgroup G)

/-- The first isomorphism theorem for conjugation on `F*(G)`. -/
abbrev quotientGeneralizedFittingCentralizerEquivConjugationImage :
    G ⧸ generalizedFittingCentralizer G ≃*
      GeneralizedFittingConjugationImage G :=
  quotientCentralizerEquivConjugationImage

/-- The faithful homomorphism
`G / C_G(F*(G)) → Aut(F*(G))` induced by conjugation. -/
def quotientGeneralizedFittingCentralizerToAut :
    G ⧸ generalizedFittingCentralizer G →*
      MulAut (generalizedFittingSubgroup G) :=
  (GeneralizedFittingConjugationImage G).subtype.comp
    (quotientGeneralizedFittingCentralizerEquivConjugationImage G).toMonoidHom

/-- Conjugation embeds `G / C_G(F*(G))` in `Aut(F*(G))`. -/
theorem quotientGeneralizedFittingCentralizerToAut_injective :
    Function.Injective
      (quotientGeneralizedFittingCentralizerToAut G) :=
  (GeneralizedFittingConjugationImage G).subtype_injective.comp
    (quotientGeneralizedFittingCentralizerEquivConjugationImage G).injective

/-- The ambient copy of the center of `F*(G)`. -/
abbrev generalizedFittingCenterImage : Subgroup G :=
  (Subgroup.center (generalizedFittingSubgroup G)).map
    (generalizedFittingSubgroup G).subtype

/-- For finite `G`, the kernel of conjugation on `F*(G)` is the ambient
copy of `Z(F*(G))`. -/
theorem ker_generalizedFittingConjugation_eq_centerImage
    [Finite G] :
    (generalizedFittingConjugation G).ker =
      generalizedFittingCenterImage G := by
  rw [ker_generalizedFittingConjugation]
  exact centralizer_generalizedFittingSubgroup_eq_map_center

/-- For finite `G`, quotienting by the ambient copy of `Z(F*(G))`
gives exactly the conjugation image in `Aut(F*(G))`. -/
def quotientGeneralizedFittingCenterEquivConjugationImage
    [Finite G] :
    G ⧸ generalizedFittingCenterImage G ≃*
      GeneralizedFittingConjugationImage G :=
  (QuotientGroup.quotientMulEquivOfEq
      (centralizer_generalizedFittingSubgroup_eq_map_center
        (G := G)).symm).trans
    (quotientGeneralizedFittingCentralizerEquivConjugationImage G)

/-- The faithful homomorphism
`G / Z(F*(G)) → Aut(F*(G))`, where the center is viewed in `G`. -/
def quotientGeneralizedFittingCenterToAut
    [Finite G] :
    G ⧸ generalizedFittingCenterImage G →*
      MulAut (generalizedFittingSubgroup G) :=
  (GeneralizedFittingConjugationImage G).subtype.comp
    (quotientGeneralizedFittingCenterEquivConjugationImage G).toMonoidHom

/-- For finite `G`, conjugation embeds `G / Z(F*(G))` in
`Aut(F*(G))`, with `Z(F*(G))` understood as its ambient image. -/
theorem quotientGeneralizedFittingCenterToAut_injective
    [Finite G] :
    Function.Injective
      (quotientGeneralizedFittingCenterToAut G) :=
  (GeneralizedFittingConjugationImage G).subtype_injective.comp
    (quotientGeneralizedFittingCenterEquivConjugationImage G).injective

/-- Conjugation by an ambient element sends a component to a component. -/
theorem IsComponent.map_conj {K : Subgroup G}
    (hK : IsComponent K) (g : G) :
    IsComponent (K.map (MulAut.conj g).toMonoidHom) :=
  hK.map_mulEquiv (MulAut.conj g)

/-- The set of components, regarded as the type on which `G` acts. -/
abbrev ComponentIndex :=
  components G

/-- Ambient conjugation acts on the components of `G`. -/
instance componentConjugationMulAction :
    MulAction G (ComponentIndex G) where
  smul g K :=
    ⟨K.1.map (MulAut.conj g).toMonoidHom,
      IsComponent.map_conj G
        (show IsComponent K.1 from K.2) g⟩
  one_smul K := by
    apply Subtype.ext
    change K.1.map (MulAut.conj (1 : G)).toMonoidHom = K.1
    rw [map_one, MulAut.one_def]
    change K.1.map (MonoidHom.id G) = K.1
    exact K.1.map_id
  mul_smul g h K := by
    apply Subtype.ext
    change K.1.map (MulAut.conj (g * h)).toMonoidHom =
      (K.1.map (MulAut.conj h).toMonoidHom).map
        (MulAut.conj g).toMonoidHom
    rw [map_mul, MulAut.mul_def, Subgroup.map_map]
    rfl

/-- The permutation representation of `G` on its components. -/
def componentConjugationPermutation :
    G →* Equiv.Perm (ComponentIndex G) :=
  MulAction.toPermHom G (ComponentIndex G)

/-- The underlying subgroup of a conjugated component is its image under
the corresponding inner automorphism. -/
@[simp]
theorem componentConjugationPermutation_apply_coe
    (g : G) (K : ComponentIndex G) :
    ((componentConjugationPermutation G g K :
        ComponentIndex G) : Subgroup G) =
      K.1.map (MulAut.conj g).toMonoidHom :=
  by
    change ((g • K : ComponentIndex G) : Subgroup G) =
      K.1.map (MulAut.conj g).toMonoidHom
    rfl

end McKayConjecture.GroupTheory
