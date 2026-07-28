/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.PermutationModuleBrauerQuotientBasis
import McKayConjecture.Character.PermutationModuleTensorProduct

/-!
# Brauer quotients of tensor products of permutation modules

For permutation modules over a field of characteristic `p`, the
Brauer quotient is freely spanned by the globally fixed basis
vectors.  Global fixed points of a product action are exactly pairs
of global fixed points.  Comparing the corresponding bases therefore
gives a canonical linear equivalence

`V(P) ⊗ W(P) ≃ (V ⊗ W)(P)`.
-/

noncomputable section

open scoped TensorProduct

namespace Representation
namespace PermutationModuleBasis

variable {p : ℕ} [Fact p.Prime]
variable {k P V W ι κ : Type}
variable [Field k] [CharP k p]
variable [Group P] [Finite P]
variable [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]
variable [DistribMulAction P V] [SMulCommClass P k V]
variable [DistribMulAction P W] [SMulCommClass P k W]
variable [MulAction P ι] [MulAction P κ]
variable [Finite ι] [Finite κ]

variable
  (B : PermutationModuleBasis
    (k := k) (P := P) (V := V) (ι := ι))
  (C : PermutationModuleBasis
    (k := k) (P := P) (V := W) (ι := κ))

noncomputable local instance tensorBrauerProductGroupFintype :
    Fintype P :=
  Fintype.ofFinite P

local notation "FixB" => MulAction.fixedPoints P ι
local notation "FixC" => MulAction.fixedPoints P κ
local notation "FixBC" => MulAction.fixedPoints P (ι × κ)

/-- A pair is globally fixed under the diagonal action precisely when
both of its coordinates are globally fixed. -/
def fixedPointsTensorProductEquiv :
    FixBC ≃ FixB × FixC where
  toFun x :=
    (⟨x.1.1, fun g =>
        congrArg Prod.fst (x.property g)⟩,
      ⟨x.1.2, fun g =>
        congrArg Prod.snd (x.property g)⟩)
  invFun x :=
    ⟨(x.1.1, x.2.1), fun g =>
      Prod.ext (x.1.property g) (x.2.property g)⟩
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl rfl
  right_inv x := by
    apply Prod.ext
    · exact Subtype.ext rfl
    · exact Subtype.ext rfl

/-- The globally fixed product index determined by two globally fixed
indices. -/
def fixedTensorIndex (i : FixB) (j : FixC) : FixBC :=
  (fixedPointsTensorProductEquiv
    (P := P) (ι := ι) (κ := κ)).symm (i, j)

omit [Finite P] [Finite ι] [Finite κ] in
@[simp]
theorem fixedTensorIndex_fst
    (i : FixB) (j : FixC) :
    (fixedTensorIndex (P := P) i j : ι × κ).1 = i :=
  rfl

omit [Finite P] [Finite ι] [Finite κ] in
@[simp]
theorem fixedTensorIndex_snd
    (i : FixB) (j : FixC) :
    (fixedTensorIndex (P := P) i j : ι × κ).2 = j :=
  rfl

/-- Basis comparison between the tensor product of the two Brauer
quotients and the Brauer quotient attached to the tensor-product
permutation basis. -/
def brauerQuotientTensorBasisEquiv
    (hP : IsPGroup p P) :
    letI : DistribMulAction P (V ⊗[k] W) :=
      B.tensorProductDistribMulAction C
    letI : SMulCommClass P k (V ⊗[k] W) :=
      B.tensorProductSMulCommClass C
    (BrauerQuotient B.representation ⊗[k]
        BrauerQuotient C.representation) ≃ₗ[k]
      BrauerQuotient (B.tensorProduct C).representation := by
  letI : DistribMulAction P (V ⊗[k] W) :=
    B.tensorProductDistribMulAction C
  letI : SMulCommClass P k (V ⊗[k] W) :=
    B.tensorProductSMulCommClass C
  exact
    ((B.brauerQuotientFixedBasis hP).tensorProduct
        (C.brauerQuotientFixedBasis hP)).equiv
      ((B.tensorProduct C).brauerQuotientFixedBasis hP)
      (fixedPointsTensorProductEquiv
        (P := P) (ι := ι) (κ := κ)).symm

/-- The basis comparison sends a tensor of fixed-index basis vectors
to the basis vector indexed by the corresponding fixed pair. -/
@[simp]
theorem brauerQuotientTensorBasisEquiv_basis_tmul
    (hP : IsPGroup p P)
    (i : FixB) (j : FixC) :
    letI : DistribMulAction P (V ⊗[k] W) :=
      B.tensorProductDistribMulAction C
    letI : SMulCommClass P k (V ⊗[k] W) :=
      B.tensorProductSMulCommClass C
    B.brauerQuotientTensorBasisEquiv C hP
        (B.brauerQuotientFixedBasis hP i ⊗ₜ[k]
          C.brauerQuotientFixedBasis hP j) =
      (B.tensorProduct C).brauerQuotientFixedBasis hP
        (fixedTensorIndex (P := P) i j) := by
  letI : DistribMulAction P (V ⊗[k] W) :=
    B.tensorProductDistribMulAction C
  letI : SMulCommClass P k (V ⊗[k] W) :=
    B.tensorProductSMulCommClass C
  simpa only [brauerQuotientTensorBasisEquiv,
      Module.Basis.tensorProduct_apply,
      fixedTensorIndex] using
    (Module.Basis.equiv_apply
      ((B.brauerQuotientFixedBasis hP).tensorProduct
        (C.brauerQuotientFixedBasis hP))
      (i, j)
      ((B.tensorProduct C).brauerQuotientFixedBasis hP)
      (fixedPointsTensorProductEquiv
        (P := P) (ι := ι) (κ := κ)).symm)

/-- On the distinguished fixed vectors, the basis comparison is
induced by tensoring the two Brauer projections. -/
theorem brauerQuotientTensorBasisEquiv_projection
    (hP : IsPGroup p P)
    (i : FixB) (j : FixC) :
    letI : DistribMulAction P (V ⊗[k] W) :=
      B.tensorProductDistribMulAction C
    letI : SMulCommClass P k (V ⊗[k] W) :=
      B.tensorProductSMulCommClass C
    B.brauerQuotientTensorBasisEquiv C hP
        (brauerProjection B.representation
            (B.fixedBasisVector i) ⊗ₜ[k]
          brauerProjection C.representation
            (C.fixedBasisVector j)) =
      brauerProjection (B.tensorProduct C).representation
        ((B.tensorProduct C).fixedBasisVector
          (fixedTensorIndex (P := P) i j)) := by
  letI : DistribMulAction P (V ⊗[k] W) :=
    B.tensorProductDistribMulAction C
  letI : SMulCommClass P k (V ⊗[k] W) :=
    B.tensorProductSMulCommClass C
  rw [← B.brauerQuotientFixedBasis_apply hP i]
  rw [← C.brauerQuotientFixedBasis_apply hP j]
  rw [B.brauerQuotientTensorBasisEquiv_basis_tmul C hP i j]
  rw [(B.tensorProduct C).brauerQuotientFixedBasis_apply]

/-- Transport a Brauer quotient along equality of the underlying
representation packages. -/
def brauerQuotientTransport
    {X : Type} [AddCommGroup X] [Module k X]
    {rho sigma : Representation k P X}
    (h : rho = sigma) :
    BrauerQuotient rho ≃ₗ[k] BrauerQuotient sigma := by
  subst sigma
  exact LinearEquiv.refl k _

/-- Tensor-product comparison with codomain expressed using the
ordinary tensor-product representation. -/
def brauerQuotientTensorEquiv
    (hP : IsPGroup p P) :
    (BrauerQuotient B.representation ⊗[k]
        BrauerQuotient C.representation) ≃ₗ[k]
      BrauerQuotient
        (B.representation.tprod C.representation) := by
  letI : DistribMulAction P (V ⊗[k] W) :=
    B.tensorProductDistribMulAction C
  letI : SMulCommClass P k (V ⊗[k] W) :=
    B.tensorProductSMulCommClass C
  exact
    (B.brauerQuotientTensorBasisEquiv C hP).trans
      (brauerQuotientTransport
        (B.tensorProduct_representation_eq_tprod C))

/-- The Brauer quotient dimension of a tensor product of permutation
modules is the product of the two Brauer quotient dimensions. -/
theorem finrank_brauerQuotient_tprod
    (hP : IsPGroup p P) :
    Module.finrank k
        (BrauerQuotient
          (B.representation.tprod C.representation)) =
      Module.finrank k (BrauerQuotient B.representation) *
        Module.finrank k (BrauerQuotient C.representation) := by
  calc
    Module.finrank k
        (BrauerQuotient
          (B.representation.tprod C.representation)) =
        Module.finrank k
          (BrauerQuotient B.representation ⊗[k]
            BrauerQuotient C.representation) :=
      (B.brauerQuotientTensorEquiv C hP).finrank_eq.symm
    _ =
        Module.finrank k (BrauerQuotient B.representation) *
          Module.finrank k (BrauerQuotient C.representation) :=
      Module.finrank_tensorProduct

end PermutationModuleBasis
end Representation
