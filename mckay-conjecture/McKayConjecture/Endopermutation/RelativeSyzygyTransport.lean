/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Endopermutation.RelativeSyzygyBasic
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.RepresentationTheory.Intertwining

/-!
# Transport of relative syzygies along group equivalences

A multiplicative equivalence `e : P ≃* P'` carrying `Q ≤ P` onto
`Q' ≤ P'` induces an equivalence of left coset spaces.  Relabelling
the corresponding permutation bases preserves augmentation and
restricts to an equivalence of relative syzygy modules.

The main result packages this linear equivalence as an equivalence
between the `P`-representation on `Ω_{P/Q}(k)` and the restriction
along `e` of the `P'`-representation on `Ω_{P'/Q'}(k)`.
-/

noncomputable section

namespace Representation

section Cosets

variable {P P' P'' : Type*}
variable [Group P] [Group P'] [Group P'']
variable {Q : Subgroup P} {Q' : Subgroup P'}
variable {Q'' : Subgroup P''}

/-- A group equivalence carrying `Q` onto `Q'` induces an equivalence
between their left coset spaces. -/
def cosetEquivOfMapEq
    (e : P ≃* P')
    (hQ : Q.map e.toMonoidHom = Q') :
    (P ⧸ Q) ≃ (P' ⧸ Q') where
  toFun :=
    Quotient.map' e fun x y hxy => by
      rw [QuotientGroup.leftRel_apply] at hxy ⊢
      rw [← hQ, Subgroup.mem_map_equiv]
      simpa using hxy
  invFun :=
    Quotient.map' e.symm fun x y hxy => by
      rw [QuotientGroup.leftRel_apply] at hxy ⊢
      rw [← hQ, Subgroup.mem_map_equiv] at hxy
      simpa using hxy
  left_inv q := by
    induction q using Quotient.inductionOn' with
    | _ x => simp
  right_inv q := by
    induction q using Quotient.inductionOn' with
    | _ x => simp

@[simp]
theorem cosetEquivOfMapEq_mk
    (e : P ≃* P')
    (hQ : Q.map e.toMonoidHom = Q')
    (x : P) :
    cosetEquivOfMapEq e hQ (QuotientGroup.mk x) =
      QuotientGroup.mk (e x) :=
  rfl

@[simp]
theorem cosetEquivOfMapEq_symm_mk
    (e : P ≃* P')
    (hQ : Q.map e.toMonoidHom = Q')
    (x : P') :
    (cosetEquivOfMapEq e hQ).symm
        (QuotientGroup.mk x) =
      QuotientGroup.mk (e.symm x) :=
  rfl

/-- The coset equivalence is equivariant for the group equivalence. -/
@[simp]
theorem cosetEquivOfMapEq_smul
    (e : P ≃* P')
    (hQ : Q.map e.toMonoidHom = Q')
    (g : P)
    (x : P ⧸ Q) :
    cosetEquivOfMapEq e hQ (g • x) =
      e g • cosetEquivOfMapEq e hQ x := by
  induction x using Quotient.inductionOn' with
  | _ x =>
      simp only [MulAction.Quotient.smul_mk,
        cosetEquivOfMapEq_mk]
      exact congrArg QuotientGroup.mk (e.map_mul g x)

/-- The inverse equivalence carries `Q'` back onto `Q`. -/
theorem map_symm_eq_of_map_eq
    (e : P ≃* P')
    (hQ : Q.map e.toMonoidHom = Q') :
    Q'.map e.symm.toMonoidHom = Q :=
  (Subgroup.map_symm_eq_iff_map_eq (K := Q)).mpr hQ

@[simp]
theorem cosetEquivOfMapEq_symm
    (e : P ≃* P')
    (hQ : Q.map e.toMonoidHom = Q') :
    (cosetEquivOfMapEq e hQ).symm =
      cosetEquivOfMapEq e.symm
        (map_symm_eq_of_map_eq e hQ) := by
  apply _root_.Equiv.ext
  intro q
  induction q using Quotient.inductionOn' with
  | _ x => rfl

/-- The image condition for a composite group equivalence. -/
theorem map_trans_eq_of_map_eq
    (e : P ≃* P')
    (f : P' ≃* P'')
    (hQ : Q.map e.toMonoidHom = Q')
    (hQ' : Q'.map f.toMonoidHom = Q'') :
    Q.map (e.trans f).toMonoidHom = Q'' := by
  change
    Q.map (f.toMonoidHom.comp e.toMonoidHom) = Q''
  rw [← Subgroup.map_map, hQ, hQ']

@[simp]
theorem cosetEquivOfMapEq_trans
    (e : P ≃* P')
    (f : P' ≃* P'')
    (hQ : Q.map e.toMonoidHom = Q')
    (hQ' : Q'.map f.toMonoidHom = Q'') :
    (cosetEquivOfMapEq e hQ).trans
        (cosetEquivOfMapEq f hQ') =
      cosetEquivOfMapEq (e.trans f)
        (map_trans_eq_of_map_eq e f hQ hQ') := by
  apply _root_.Equiv.ext
  intro q
  induction q using Quotient.inductionOn' with
  | _ x => rfl

end Cosets

section PermutationModules

variable (k : Type*) [CommSemiring k]
variable {P P' : Type*} [Group P] [Group P']
variable {Q : Subgroup P} {Q' : Subgroup P'}

/-- Relabelling cosets along a group equivalence intertwines the two
permutation representations. -/
theorem cosetPermutationLinearEquiv_intertwines
    (e : P ≃* P')
    (hQ : Q.map e.toMonoidHom = Q')
    (g : P) :
    (MonoidAlgebra.mapDomainLinearEquiv k k
        (cosetEquivOfMapEq e hQ)).toLinearMap ∘ₗ
        cosetPermutationRepresentation k P Q g =
      cosetPermutationRepresentation k P' Q' (e g) ∘ₗ
        (MonoidAlgebra.mapDomainLinearEquiv k k
          (cosetEquivOfMapEq e hQ)).toLinearMap := by
  apply MonoidAlgebra.lhom_ext'
  intro x
  apply LinearMap.ext
  intro a
  simp [cosetPermutationRepresentation]

theorem cosetPermutationLinearEquiv_apply_action
    (e : P ≃* P')
    (hQ : Q.map e.toMonoidHom = Q')
    (g : P)
    (v : CosetPermutationModule k P Q) :
    MonoidAlgebra.mapDomainLinearEquiv k k
        (cosetEquivOfMapEq e hQ)
        (cosetPermutationRepresentation k P Q g v) =
      cosetPermutationRepresentation k P' Q' (e g)
        (MonoidAlgebra.mapDomainLinearEquiv k k
          (cosetEquivOfMapEq e hQ) v) :=
  LinearMap.congr_fun
    (cosetPermutationLinearEquiv_intertwines
      k e hQ g) v

end PermutationModules

section RelativeSyzygies

variable (k : Type*) [CommSemiring k]
variable {P P' : Type*} [Group P] [Group P']
variable {Q : Subgroup P} {Q' : Subgroup P'}

/-- The linear equivalence of relative syzygies induced by a group
equivalence carrying one subgroup onto the other. -/
def relativeSyzygyEquivOfGroupEquiv
    (e : P ≃* P')
    (hQ : Q.map e.toMonoidHom = Q') :
    relativeSyzygy k P Q ≃ₗ[k]
      relativeSyzygy k P' Q' :=
  relativeSyzygyEquivOfCosetEquiv
    k P P' Q Q' (cosetEquivOfMapEq e hQ)

@[simp]
theorem relativeSyzygyEquivOfGroupEquiv_apply_coe
    (e : P ≃* P')
    (hQ : Q.map e.toMonoidHom = Q')
    (v : relativeSyzygy k P Q) :
    ((relativeSyzygyEquivOfGroupEquiv
          k e hQ v :
        relativeSyzygy k P' Q') :
      CosetPermutationModule k P' Q') =
      MonoidAlgebra.mapDomainLinearEquiv k k
        (cosetEquivOfMapEq e hQ)
        (v : CosetPermutationModule k P Q) :=
  rfl

@[simp]
theorem relativeSyzygyEquivOfGroupEquiv_symm
    (e : P ≃* P')
    (hQ : Q.map e.toMonoidHom = Q') :
    (relativeSyzygyEquivOfGroupEquiv k e hQ).symm =
      relativeSyzygyEquivOfGroupEquiv k e.symm
        (map_symm_eq_of_map_eq e hQ) := by
  apply LinearEquiv.ext
  intro v
  apply Subtype.ext
  change
    MonoidAlgebra.mapDomainLinearEquiv k k
        (cosetEquivOfMapEq e hQ).symm v =
      MonoidAlgebra.mapDomainLinearEquiv k k
        (cosetEquivOfMapEq e.symm
          (map_symm_eq_of_map_eq e hQ)) v
  rw [cosetEquivOfMapEq_symm]

@[simp]
theorem relativeSyzygyEquivOfGroupEquiv_trans
    {P'' : Type*} [Group P'']
    {Q'' : Subgroup P''}
    (e : P ≃* P')
    (f : P' ≃* P'')
    (hQ : Q.map e.toMonoidHom = Q')
    (hQ' : Q'.map f.toMonoidHom = Q'') :
    (relativeSyzygyEquivOfGroupEquiv k e hQ).trans
        (relativeSyzygyEquivOfGroupEquiv k f hQ') =
      relativeSyzygyEquivOfGroupEquiv k (e.trans f)
        (map_trans_eq_of_map_eq e f hQ hQ') := by
  apply LinearEquiv.ext
  intro v
  apply Subtype.ext
  change
    ((MonoidAlgebra.mapDomainLinearEquiv k k
          (cosetEquivOfMapEq e hQ)).trans
        (MonoidAlgebra.mapDomainLinearEquiv k k
          (cosetEquivOfMapEq f hQ'))) v =
      MonoidAlgebra.mapDomainLinearEquiv k k
        (cosetEquivOfMapEq (e.trans f)
          (map_trans_eq_of_map_eq e f hQ hQ')) v
  rw [← MonoidAlgebra.mapDomainLinearEquiv_trans,
    cosetEquivOfMapEq_trans]

/-- The relative-syzygy equivalence intertwines the natural actions. -/
theorem relativeSyzygyEquivOfGroupEquiv_apply_action
    (e : P ≃* P')
    (hQ : Q.map e.toMonoidHom = Q')
    (g : P)
    (v : relativeSyzygy k P Q) :
    relativeSyzygyEquivOfGroupEquiv k e hQ
        (relativeSyzygyRepresentation k P Q g v) =
      relativeSyzygyRepresentation k P' Q' (e g)
        (relativeSyzygyEquivOfGroupEquiv k e hQ v) := by
  apply Subtype.ext
  exact
    cosetPermutationLinearEquiv_apply_action
      k e hQ g (v : CosetPermutationModule k P Q)

/-- Equivariant form of relative-syzygy transport.  The target
representation is restricted from `P'` to `P` along `e`. -/
def relativeSyzygyRepresentationEquivOfGroupEquiv
    (e : P ≃* P')
    (hQ : Q.map e.toMonoidHom = Q') :
    (relativeSyzygyRepresentation k P Q).Equiv
      ((relativeSyzygyRepresentation k P' Q').comp
        e.toMonoidHom) :=
  Representation.Equiv.mk
    (relativeSyzygyEquivOfGroupEquiv k e hQ)
    (by
      intro g
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      exact
        cosetPermutationLinearEquiv_apply_action
          k e hQ g
            (v : CosetPermutationModule k P Q))

@[simp]
theorem relativeSyzygyRepresentationEquivOfGroupEquiv_apply
    (e : P ≃* P')
    (hQ : Q.map e.toMonoidHom = Q')
    (v : relativeSyzygy k P Q) :
    relativeSyzygyRepresentationEquivOfGroupEquiv
        k e hQ v =
      relativeSyzygyEquivOfGroupEquiv k e hQ v :=
  rfl

end RelativeSyzygies

end Representation
