/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.EndomorphismBrauerComparison
import McKayConjecture.Character.EndomorphismPermutationBasis
import McKayConjecture.Character.PermutationModuleBrauerQuotientBasis

/-!
# Endomorphism Brauer comparison for permutation modules

Let a finite `p`-group permute a basis of a module over a field of
characteristic `p`.  The natural Brauer homomorphism

`End(V)(P) → End(V(P))`

is an isomorphism.  The proof is the matrix-unit form of the standard
permutation-module Brauer quotient theorem: the surviving matrix units
are precisely those whose two indices are globally fixed.
-/

noncomputable section

namespace Representation
namespace PermutationModuleBasis

variable {p : ℕ} [Fact p.Prime]
variable {k P V ι : Type}
variable [Field k] [CharP k p]
variable [Group P] [Finite P]
variable [AddCommGroup V] [Module k V]
variable [DistribMulAction P V] [SMulCommClass P k V]
variable [MulAction P ι] [Finite ι]

variable (B : PermutationModuleBasis
  (k := k) (P := P) (V := V) (ι := ι))

local notation "Fix" =>
  MulAction.fixedPoints P ι

noncomputable local instance endomorphismComparisonGroupFintype :
    Fintype P :=
  Fintype.ofFinite P

noncomputable local instance endomorphismComparisonIndexFintype :
    Fintype ι :=
  Fintype.ofFinite ι

noncomputable local instance endomorphismComparisonIndexDecidableEq :
    DecidableEq ι :=
  Classical.decEq ι

noncomputable local instance endomorphismComparisonFixedIndexFintype :
    Fintype Fix :=
  Fintype.ofFinite Fix

noncomputable local instance endomorphismComparisonFixedIndexDecidableEq :
    DecidableEq Fix :=
  Classical.decEq Fix

local instance endomorphismComparisonConjugationAction :
    MulSemiringAction P (Module.End k V) :=
  endomorphismConjugationMulSemiringAction
    (representationLinearAction
      (Representation.ofDistribMulAction k P V))

local instance endomorphismComparisonConjugationScalarComm :
    SMulCommClass P k (Module.End k V) :=
  endomorphismConjugation_smulCommClass
    (representationLinearAction
      (Representation.ofDistribMulAction k P V))

/-- A pair of globally fixed indices, regarded as a globally fixed
index for the diagonal action on pairs. -/
def fixedPair
    (ij : Fix × Fix) :
    MulAction.fixedPoints P (ι × ι) :=
  ⟨((ij.1 : ι), (ij.2 : ι)), fun g ↦ by
    apply Prod.ext
    · exact ij.1.property g
    · exact ij.2.property g⟩

omit [Finite P] [Finite ι] in
@[simp]
theorem fixedPair_val
    (ij : Fix × Fix) :
    (fixedPair (P := P) ij : ι × ι) =
      ((ij.1 : ι), (ij.2 : ι)) :=
  rfl

/-- A diagonally fixed pair has two globally fixed coordinates. -/
def fixedPairCoordinates
    (ij : MulAction.fixedPoints P (ι × ι)) :
    Fix × Fix :=
  (⟨ij.1.1, fun g ↦ by
      simpa using congrArg Prod.fst (ij.property g)⟩,
    ⟨ij.1.2, fun g ↦ by
      simpa using congrArg Prod.snd (ij.property g)⟩)

/-- Diagonally fixed pairs are canonically pairs of globally fixed
indices. -/
def fixedPairEquiv :
    MulAction.fixedPoints P (ι × ι) ≃ Fix × Fix where
  toFun := fixedPairCoordinates (P := P)
  invFun := fixedPair (P := P)
  left_inv ij := by
    apply Subtype.ext
    rfl
  right_inv ij := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl

/-- The matrix unit attached to two fixed basis indices, as an
element of the conjugation-fixed endomorphism algebra. -/
def fixedMatrixUnit
    (ij : Fix × Fix) :
    fixedSubalgebra
      (k := k) (P := P) (A := Module.End k V) :=
  ⟨B.basis.end (ij.1, ij.2), fun g ↦ by
    rw [B.smul_end_basis]
    congr 2
    apply Prod.ext
    · exact ij.1.property g
    · exact ij.2.property g⟩

omit [Finite P] in
@[simp]
theorem fixedMatrixUnit_coe
    (ij : Fix × Fix) :
    (B.fixedMatrixUnit ij : Module.End k V) =
      B.basis.end (ij.1, ij.2) :=
  rfl

/-- On a surviving matrix unit, the canonical endomorphism Brauer map
is the corresponding matrix unit for the fixed-point basis of
`V(P)`. -/
theorem endomorphismBrauerAlgHom_brauerAlgebraProjection_fixedMatrixUnit
    (hP : IsPGroup p P)
    (ij : Fix × Fix) :
    endomorphismBrauerAlgHom B.representation
        (brauerAlgebraProjection
          (k := k) (P := P) (A := Module.End k V)
          (B.fixedMatrixUnit ij)) =
      (B.brauerQuotientFixedBasis hP).end ij := by
  apply (B.brauerQuotientFixedBasis hP).ext
  intro t
  rw [(B.brauerQuotientFixedBasis hP).end_apply_apply]
  rw [B.brauerQuotientFixedBasis_apply]
  rw [endomorphismBrauerAlgHom_brauerAlgebraProjection]
  rw [fixedEndomorphismBrauerAlgHom_brauerProjection]
  by_cases ht : ij.2 = t
  · subst t
    rw [if_pos rfl]
    apply
      (B.brauerQuotientEquivFixedCoordinates hP).injective
    rw [B.brauerQuotientEquivFixedCoordinates_brauerProjection]
    funext u
    simp only [fixedCoordinates_apply,
      selfIntertwinerOnInvariants_coe,
      B.fixedBasisVector_coe,
      fixedEndomorphismIntertwinerAlgEquiv,
      AlgEquiv.coe_mk, Equiv.coe_fn_mk,
      fixedMatrixUnit_coe]
    change
      B.basis.coord (u : ι)
          (B.basis.end ((ij.1 : ι), (ij.2 : ι))
            (B.basis (ij.2 : ι))) =
        B.brauerQuotientEquivFixedCoordinates hP
          (B.brauerQuotientFixedBasis hP ij.1) u
    rw [B.basis.end_apply_apply, if_pos rfl]
    rw [B.brauerQuotientFixedBasis_apply,
      B.brauerQuotientEquivFixedCoordinates_brauerProjection]
    by_cases hu : ij.1 = u
    · subst u
      simp
    · have hval : (ij.1 : ι) ≠ (u : ι) := by
        intro h
        apply hu
        exact Subtype.ext h
      simp [hval]
  · rw [if_neg ht]
    apply
      (B.brauerQuotientEquivFixedCoordinates hP).injective
    rw [B.brauerQuotientEquivFixedCoordinates_brauerProjection]
    funext u
    simp only [fixedCoordinates_apply,
      selfIntertwinerOnInvariants_coe,
      B.fixedBasisVector_coe,
      fixedEndomorphismIntertwinerAlgEquiv,
      AlgEquiv.coe_mk, Equiv.coe_fn_mk,
      fixedMatrixUnit_coe]
    change
      B.basis.coord (u : ι)
          (B.basis.end ((ij.1 : ι), (ij.2 : ι))
            (B.basis (t : ι))) =
        B.brauerQuotientEquivFixedCoordinates hP 0 u
    have hval : (ij.2 : ι) ≠ (t : ι) := by
      intro h
      apply ht
      exact Subtype.ext h
    rw [B.basis.end_apply_apply, if_neg hval]
    simp

/-- For a permutation module, every endomorphism of the module Brauer
quotient is the image of a linear combination of surviving matrix
units. -/
theorem endomorphismBrauerAlgHom_surjective_of_permutationBasis
    (hP : IsPGroup p P) :
    Function.Surjective
      (endomorphismBrauerAlgHom B.representation) := by
  intro f
  let bP :=
    B.brauerQuotientFixedBasis hP
  rw [← bP.end.sum_repr f]
  refine
    ⟨∑ ij : Fix × Fix,
        (bP.end.repr f) ij •
          brauerAlgebraProjection
            (k := k) (P := P) (A := Module.End k V)
            (B.fixedMatrixUnit ij), ?_⟩
  rw [map_sum]
  apply Fintype.sum_congr
  intro ij
  rw [map_smul]
  rw [B.endomorphismBrauerAlgHom_brauerAlgebraProjection_fixedMatrixUnit
    hP ij]

/-- Identity-on-endomorphisms linear equivalence between the invariant
submodule of the matrix-unit representation and the conjugation-fixed
subalgebra. -/
def endomorphismInvariantsEquivFixedSubalgebra :
    invariants B.endomorphism.representation ≃ₗ[k]
      fixedSubalgebra
        (k := k) (P := P) (A := Module.End k V) where
  toFun x := ⟨x, x.property⟩
  invFun c := ⟨c, c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A conjugation-fixed endomorphism, regarded as an invariant vector
for the permutation representation on matrix units. -/
def fixedEndomorphismInvariant
    (c :
      fixedSubalgebra
        (k := k) (P := P) (A := Module.End k V)) :
    invariants B.endomorphism.representation :=
  ⟨c, c.property⟩

omit [Finite P] in
@[simp]
theorem fixedEndomorphismInvariant_coe
    (c :
      fixedSubalgebra
        (k := k) (P := P) (A := Module.End k V)) :
    (B.fixedEndomorphismInvariant c : Module.End k V) = c :=
  rfl

/-- A subgroup-invariant endomorphism, regarded as an element of the
corresponding fixed subalgebra. -/
def subgroupInvariantFixedEndomorphism
    (Q : Subgroup P)
    (x :
      invariants
        (B.endomorphism.representation.comp Q.subtype)) :
    fixedSubalgebra
      (k := k) (P := Q) (A := Module.End k V) :=
  ⟨x, x.property⟩

/-- The linear relative trace for the matrix-unit representation and
the algebra relative trace have the same underlying endomorphism. -/
theorem invariantsEquivFixedSubalgebra_relativeTrace_endomorphism
    (Q : Subgroup P)
    (x :
      invariants
        (B.endomorphism.representation.comp Q.subtype)) :
    B.endomorphismInvariantsEquivFixedSubalgebra
        (relativeTrace B.endomorphism.representation Q x) =
      fixedRelativeTrace
        (k := k) (P := P) (A := Module.End k V) Q
        (B.subgroupInvariantFixedEndomorphism Q x) := by
  apply Subtype.ext
  rfl

/-- Membership in the linear Brauer trace submodule for the
matrix-unit representation implies membership in the multiplicative
Brauer trace ideal. -/
theorem mem_brauerTraceIdeal_of_fixedEndomorphismInvariant_mem
    (c :
      fixedSubalgebra
        (k := k) (P := P) (A := Module.End k V))
    (hc :
      B.fixedEndomorphismInvariant c ∈
        brauerTraceSubmodule B.endomorphism.representation) :
    c ∈
      brauerTraceIdeal
        (k := k) (P := P) (A := Module.End k V) := by
  let T :=
    brauerTraceIdeal
      (k := k) (P := P) (A := Module.End k V)
  let e :=
    B.endomorphismInvariantsEquivFixedSubalgebra
  have he :
      e (B.fixedEndomorphismInvariant c) ∈ T := by
    change
      B.fixedEndomorphismInvariant c ∈
        ⨆ (Q : Subgroup P) (_hQ : Q < ⊤),
          relativeTraceRange B.endomorphism.representation Q at hc
    refine Submodule.iSup_induction
      (fun Q : Subgroup P ↦
        ⨆ _hQ : Q < ⊤,
          relativeTraceRange B.endomorphism.representation Q)
      (motive := fun y ↦ e y ∈ T)
      hc ?_ ?_ ?_
    · intro Q y hy
      refine Submodule.iSup_induction
        (fun _hQ : Q < ⊤ ↦
          relativeTraceRange B.endomorphism.representation Q)
        (motive := fun z ↦ e z ∈ T)
        hy ?_ ?_ ?_
      · intro hQ z hz
        obtain ⟨x, rfl⟩ := hz
        rw [B.invariantsEquivFixedSubalgebra_relativeTrace_endomorphism
          Q x]
        exact
          fixedRelativeTrace_mem_brauerTraceIdeal
            (k := k) (P := P) (A := Module.End k V)
            Q hQ
            (B.subgroupInvariantFixedEndomorphism Q x)
      · exact T.zero_mem
      · intro u v hu hv
        rw [map_add]
        exact T.add_mem hu hv
    · exact T.zero_mem
    · intro u v hu hv
      rw [map_add]
      exact T.add_mem hu hv
  exact he

/-- If a fixed endomorphism acts trivially on `V(P)`, then all of its
matrix coefficients at diagonally fixed pairs vanish. -/
theorem endomorphism_fixedCoordinates_eq_zero_of_brauerAction_eq_zero
    (hP : IsPGroup p P)
    (c :
      fixedSubalgebra
        (k := k) (P := P) (A := Module.End k V))
    (hc :
      fixedEndomorphismBrauerAlgHom B.representation c = 0) :
    B.endomorphism.fixedCoordinates
        (B.fixedEndomorphismInvariant c) =
      0 := by
  funext z
  rw [Pi.zero_apply]
  let ij : Fix × Fix :=
    fixedPairCoordinates (P := P) z
  have hact :=
    congrArg
      (fun f : Module.End k (BrauerQuotient B.representation) ↦
        f (B.brauerQuotientFixedBasis hP ij.2))
      hc
  rw [B.brauerQuotientFixedBasis_apply] at hact
  rw [fixedEndomorphismBrauerAlgHom_brauerProjection] at hact
  have hquot :
      brauerProjection B.representation
          (selfIntertwinerOnInvariants B.representation
            (fixedEndomorphismIntertwinerAlgEquiv
              B.representation c)
            (B.fixedBasisVector ij.2)) =
        0 := by
    simpa using hact
  have hcoord :=
    congrArg
      (fun q : BrauerQuotient B.representation ↦
        B.brauerQuotientEquivFixedCoordinates hP q ij.1)
      hquot
  rw [B.brauerQuotientEquivFixedCoordinates_brauerProjection]
      at hcoord
  simp only [map_zero, Pi.zero_apply] at hcoord
  change
    B.basis.coord (ij.1 : ι)
        ((c : Module.End k V) (B.basis (ij.2 : ι))) =
      0 at hcoord
  change
    B.basis.end.coord (z : ι × ι) (c : Module.End k V) =
      0
  have hz :
      (z : ι × ι) =
        ((ij.1 : ι), (ij.2 : ι)) :=
    rfl
  rw [hz]
  simpa [Module.Basis.coord_apply, Matrix.stdBasis,
    LinearMap.toMatrix_apply] using hcoord

/-- A fixed endomorphism which acts trivially on `V(P)` belongs to the
Brauer trace ideal of the endomorphism algebra. -/
theorem fixedEndomorphism_mem_brauerTraceIdeal_of_brauerAction_eq_zero
    (hP : IsPGroup p P)
    (c :
      fixedSubalgebra
        (k := k) (P := P) (A := Module.End k V))
    (hc :
      fixedEndomorphismBrauerAlgHom B.representation c = 0) :
    c ∈
      brauerTraceIdeal
        (k := k) (P := P) (A := Module.End k V) := by
  apply B.mem_brauerTraceIdeal_of_fixedEndomorphismInvariant_mem
  rw [← B.endomorphism.ker_fixedCoordinates hP]
  exact
    LinearMap.mem_ker.mpr
      (B.endomorphism_fixedCoordinates_eq_zero_of_brauerAction_eq_zero
        hP c hc)

/-- The canonical endomorphism Brauer homomorphism is injective for a
permutation module. -/
theorem endomorphismBrauerAlgHom_injective_of_permutationBasis
    (hP : IsPGroup p P) :
    Function.Injective
      (endomorphismBrauerAlgHom B.representation) := by
  intro x y hxy
  apply sub_eq_zero.mp
  have hmap :
      endomorphismBrauerAlgHom B.representation (x - y) =
        0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨c, hc⟩ :=
    brauerAlgebraProjection_surjective
      (k := k) (P := P) (A := Module.End k V)
      (x - y)
  rw [← hc]
  rw [brauerAlgebraProjection,
    Ideal.Quotient.eq_zero_iff_mem]
  apply
    B.fixedEndomorphism_mem_brauerTraceIdeal_of_brauerAction_eq_zero
      hP c
  rw [← endomorphismBrauerAlgHom_brauerAlgebraProjection]
  simpa only [hc] using hmap

/-- **Endomorphism Brauer comparison for permutation modules.**
For a finite `p`-group acting through a permutation basis, the natural
map `End(V)(P) → End(V(P))` is an isomorphism. -/
theorem endomorphismBrauerComparisonIsomorphism_of_permutationBasis
    (hP : IsPGroup p P) :
    EndomorphismBrauerComparisonIsomorphism
      B.representation :=
  ⟨B.endomorphismBrauerAlgHom_injective_of_permutationBasis hP,
    B.endomorphismBrauerAlgHom_surjective_of_permutationBasis hP⟩

end PermutationModuleBasis
end Representation
