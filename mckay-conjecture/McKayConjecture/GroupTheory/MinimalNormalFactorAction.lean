/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.MinimalNormalFactors

/-!
# The ambient action on the simple factors of a minimal normal subgroup

The simple factors constructed in `MinimalNormalFactors` are the distinct
ambient conjugates of one chosen factor.  Consequently the ambient group
acts transitively on their index type.  This file records that action and
the induced isomorphism between a factor and each of its translates.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory
namespace MinimalNormalFactors

variable {G : Type u} [Group G]

/-- Ambient conjugation acts on the distinct conjugates of `L`. -/
@[instance_reducible]
def conjugateFactorIndexMulAction
    (N : Subgroup G) [N.Normal] (L : Subgroup N) :
    MulAction G (ConjugateFactorIndex N L) where
  smul g i :=
    ⟨i.1.map (MulAut.conjNormal g).toMonoidHom, by
      obtain ⟨h, hh⟩ := i.2
      refine ⟨g * h, ?_⟩
      change
        L.map (MulAut.conjNormal (g * h)).toMonoidHom =
          i.1.map (MulAut.conjNormal g).toMonoidHom
      rw [← hh]
      simp only [conjugateFactor, Subgroup.map_map,
        map_mul]
      rfl⟩
  one_smul i := by
    apply Subtype.ext
    change
      i.1.map (MulAut.conjNormal 1).toMonoidHom = i.1
    have h :
        (MulAut.conjNormal (H := N) 1).toMonoidHom =
          MonoidHom.id N := by
      ext x
      simp
    rw [h]
    exact i.1.map_id
  mul_smul g h i := by
    apply Subtype.ext
    change
      i.1.map (MulAut.conjNormal (g * h)).toMonoidHom =
        (i.1.map (MulAut.conjNormal h).toMonoidHom).map
          (MulAut.conjNormal g).toMonoidHom
    simp only [Subgroup.map_map, map_mul]
    rfl

namespace ConjugateFactorIndex

variable (N : Subgroup G) [N.Normal] (L : Subgroup N)

local instance : MulAction G (ConjugateFactorIndex N L) :=
  conjugateFactorIndexMulAction N L

@[simp]
theorem smul_factor (g : G) (i : ConjugateFactorIndex N L) :
    conjugateFactorFamily N L (g • i) =
      (conjugateFactorFamily N L i).map
        (MulAut.conjNormal g).toMonoidHom :=
  rfl

/-- Conjugation by `g` identifies a factor with the factor indexed by its
translate under `g`. -/
def factorMulEquiv (g : G) (i : ConjugateFactorIndex N L) :
    conjugateFactorFamily N L i ≃*
      conjugateFactorFamily N L (g • i) :=
  (conjugateFactorFamily N L i).equivMapOfInjective
    (MulAut.conjNormal g).toMonoidHom
    (MulAut.conjNormal g).injective

@[simp]
theorem factorMulEquiv_apply_coe
    (g : G) (i : ConjugateFactorIndex N L)
    (x : conjugateFactorFamily N L i) :
    ((factorMulEquiv N L g i x :
        conjugateFactorFamily N L (g • i)) : N) =
      MulAut.conjNormal g x :=
  rfl

/-- The ambient action on the set of factors is transitive. -/
theorem exists_smul_eq
    (i j : ConjugateFactorIndex N L) :
    ∃ g : G, g • i = j := by
  obtain ⟨g, hg⟩ :=
    conjugateFactorFamily_pairwise_conjugate N L i j
  refine ⟨g, ?_⟩
  apply Subtype.ext
  exact hg.symm

/-- The factor index is a transitive `G`-set. -/
instance instIsPretransitive :
    MulAction.IsPretransitive G
      (ConjugateFactorIndex N L) where
  exists_smul_eq := exists_smul_eq N L

end ConjugateFactorIndex

/-- A nonabelian minimal-normal decomposition together with the coherent
ambient action on its factors.  Keeping the action as data makes subsequent
wreath-product and equivariance constructions independent of the particular
choice used to build the factors. -/
structure EquivariantNonabelianMinimalNormalDecomposition
    (N : Subgroup G) [N.Normal] where
  toDecomposition :
    NonabelianMinimalNormalDecomposition N
  action :
    MulAction G toDecomposition.ι
  transitive :
    letI := action
    MulAction.IsPretransitive G
      toDecomposition.ι
  factor_smul :
    letI := action
    ∀ (g : G) (i : toDecomposition.ι),
      toDecomposition.factor (g • i) =
        (toDecomposition.factor i).map
          (MulAut.conjNormal g).toMonoidHom

namespace EquivariantNonabelianMinimalNormalDecomposition

variable {N : Subgroup G} [N.Normal]

instance :
    Coe (EquivariantNonabelianMinimalNormalDecomposition N)
      (NonabelianMinimalNormalDecomposition N) :=
  ⟨fun D ↦ D.toDecomposition⟩

@[instance_reducible]
def instMulAction
    (D : EquivariantNonabelianMinimalNormalDecomposition N) :
    MulAction G D.toDecomposition.ι :=
  D.action

instance instIsPretransitive
    (D : EquivariantNonabelianMinimalNormalDecomposition N) :
    letI := D.instMulAction
    MulAction.IsPretransitive G D.toDecomposition.ι :=
  D.transitive

/-- Conjugation by `g` identifies a factor of an equivariant decomposition
with its translated factor. -/
def factorMulEquiv
    (D : EquivariantNonabelianMinimalNormalDecomposition N)
    (g : G) (i : D.toDecomposition.ι) :
    D.toDecomposition.factor i ≃*
      D.toDecomposition.factor
        (letI := D.instMulAction
         g • i) :=
  ((D.toDecomposition.factor i).equivMapOfInjective
      (MulAut.conjNormal g).toMonoidHom
      (MulAut.conjNormal g).injective).trans
    (MulEquiv.subgroupCongr (by
      letI := D.instMulAction
      exact (D.factor_smul g i).symm))

@[simp]
theorem factorMulEquiv_apply_coe
    (D : EquivariantNonabelianMinimalNormalDecomposition N)
    (g : G) (i : D.toDecomposition.ι)
    (x : D.toDecomposition.factor i) :
    ((D.factorMulEquiv g i x :
        D.toDecomposition.factor
          (letI := D.instMulAction
           g • i)) : N) =
      MulAut.conjNormal g x :=
  rfl

end EquivariantNonabelianMinimalNormalDecomposition

/-- The canonical simple-factor decomposition carries its ambient
conjugation action and that action is transitive. -/
def equivariantNonabelianMinimalNormalDecomposition
    [Finite G] {N : Subgroup G} [N.Normal]
    (hN : IsMinimalNormal N)
    (hnoncomm : ¬ IsMulCommutative N) :
    EquivariantNonabelianMinimalNormalDecomposition N := by
  letI : Nontrivial N :=
    N.nontrivial_iff_ne_bot.mpr hN.ne_bot
  let L : Subgroup N :=
    chosenMinimalNormalSubgroup N
  let hL : IsMinimalNormal L :=
    chosenMinimalNormalSubgroup_isMinimalNormal N
  let D : NonabelianMinimalNormalDecomposition N :=
    { ι := ConjugateFactorIndex N L
      fintype := Fintype.ofFinite _
      nonempty := ⟨identityConjugateFactorIndex N L⟩
      factor := conjugateFactorFamily N L
      factor_minimalNormal :=
        conjugateFactorFamily_isMinimalNormal N hL
      factor_simple :=
        conjugateFactorFamily_isSimpleGroup hN hL
      factor_nonabelian :=
        conjugateFactorFamily_not_isMulCommutative
          hN hnoncomm hL
      pairwise_conjugate :=
        conjugateFactorFamily_pairwise_conjugate N L
      pairwise_commute :=
        conjugateFactorFamily_pairwise_commute N hL
      independent :=
        conjugateFactorFamily_iSupIndep
          hN hnoncomm hL
      iSup_eq_top :=
        conjugateFactorFamily_iSup_eq_top hN hL
      productEquiv :=
        conjugateFactorProductEquiv
          hN hnoncomm hL }
  exact
    { toDecomposition := D
      action := conjugateFactorIndexMulAction N L
      transitive := by
        letI : MulAction G (ConjugateFactorIndex N L) :=
          conjugateFactorIndexMulAction N L
        exact
          { exists_smul_eq :=
              ConjugateFactorIndex.exists_smul_eq N L }
      factor_smul := by
        letI : MulAction G (ConjugateFactorIndex N L) :=
          conjugateFactorIndexMulAction N L
        intro g i
        rfl }

end MinimalNormalFactors
end GroupTheory
end McKayConjecture
