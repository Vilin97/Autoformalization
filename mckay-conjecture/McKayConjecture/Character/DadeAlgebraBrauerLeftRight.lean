/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerQuotientAlgEquiv
import McKayConjecture.Character.DadeAlgebraBrauerTensorProduct
import McKayConjecture.Character.DadeAlgebraOpposite
import McKayConjecture.Character.EndomorphismFixedIntertwiner
import McKayConjecture.Character.EndomorphismTensorProductEquivariance
import McKayConjecture.Character.FiniteFieldCentralSimpleAzumaya
import McKayConjecture.Character.PermutationModuleEndomorphismBrauerComparison

/-!
# The left-right Brauer quotient of a split Dade algebra

For a Dade algebra over a finite field, finite-field splitting makes
the left-right multiplication map

`A ⊗[k] Aᵐᵒᵖ → Endₖ(A)`

an algebra equivalence.  Its equivariance identifies the Brauer
quotient of the tensor-product algebra with the Brauer quotient of
the conjugation endomorphism algebra.

This is the upper square in the standard elementary proof that the
Brauer quotient of a split Dade algebra is again split central
simple.
-/

noncomputable section

open scoped TensorProduct

namespace Representation
namespace DadeAlgebra

variable {p : ℕ} [Fact p.Prime]
variable {k P A : Type}
variable [Field k] [Finite k] [CharP k p]
variable [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

/-- The left-right multiplication equivalence supplied by
finite-field splitting of a Dade algebra. -/
def leftRightAlgEquiv
    (S : DadeAlgebra p k P A) :
    A ⊗[k] Aᵐᵒᵖ ≃ₐ[k] Module.End k A := by
  letI : Algebra.IsCentral k A := S.isCentral
  letI : IsSimpleRing A := S.isSimple
  letI : FiniteDimensional k A := S.finiteDimensional
  letI : IsAzumaya k A :=
    isAzumaya_of_finiteField k A
  exact
    AlgEquiv.ofBijective
      (AlgHom.mulLeftRight k A)
      (IsAzumaya.AlgHom.mulLeftRight_bij k A)

omit [Fact p.Prime] [CharP k p] [Fintype P] in
/-- The left-right multiplication equivalence intertwines the
diagonal action on `A ⊗ Aᵐᵒᵖ` with conjugation on `Endₖ(A)`. -/
theorem leftRightAlgEquiv_smul
    (S : DadeAlgebra p k P A)
    (g : P) (z : A ⊗[k] Aᵐᵒᵖ) :
    letI : MulSemiringAction P (A ⊗[k] Aᵐᵒᵖ) :=
      S.permutationBasis.tensorProductMulSemiringAction
        S.permutationBasis.opposite
    let rho :=
      representationLinearAction
        (algebraActionRepresentation
          (k := k) (P := P) (A := A))
    letI : MulSemiringAction P (Module.End k A) :=
      endomorphismConjugationMulSemiringAction rho
    S.leftRightAlgEquiv (g • z) =
      g • S.leftRightAlgEquiv z := by
  letI : MulSemiringAction P (A ⊗[k] Aᵐᵒᵖ) :=
    S.permutationBasis.tensorProductMulSemiringAction
      S.permutationBasis.opposite
  let rho :=
    representationLinearAction
      (algebraActionRepresentation
        (k := k) (P := P) (A := A))
  letI : MulSemiringAction P (Module.End k A) :=
    endomorphismConjugationMulSemiringAction rho
  induction z using TensorProduct.induction_on with
  | zero =>
      simp
  | add x y hx hy =>
      simp only [smul_add, map_add, hx, hy]
  | tmul a b =>
      apply LinearMap.ext
      intro x
      simp only [
        S.permutationBasis.tensorProduct_smul_tmul,
        leftRightAlgEquiv, AlgEquiv.ofBijective_apply,
        AlgHom.mulLeftRight_apply,
        endomorphismConjugation_smul_apply]
      change
        (g • a) * x * (g • MulOpposite.unop b) =
          g • (a * (g⁻¹ • x) * MulOpposite.unop b)
      rw [MulSemiringAction.smul_mul,
        MulSemiringAction.smul_mul, smul_inv_smul]

/-- The equivariant left-right equivalence descends to the algebra
Brauer quotients. -/
def brauerLeftRightAlgEquiv
    (S : DadeAlgebra p k P A) :
    letI : MulSemiringAction P (A ⊗[k] Aᵐᵒᵖ) :=
      S.permutationBasis.tensorProductMulSemiringAction
        S.permutationBasis.opposite
    letI : SMulCommClass P k (A ⊗[k] Aᵐᵒᵖ) :=
      S.permutationBasis.tensorProductSMulCommClass
        S.permutationBasis.opposite
    let rho :=
      representationLinearAction
        (algebraActionRepresentation
          (k := k) (P := P) (A := A))
    letI : MulSemiringAction P (Module.End k A) :=
      endomorphismConjugationMulSemiringAction rho
    letI : SMulCommClass P k (Module.End k A) :=
      endomorphismConjugation_smulCommClass rho
    BrauerQuotientAlgebra
        (k := k) (P := P) (A := A ⊗[k] Aᵐᵒᵖ) ≃ₐ[k]
      BrauerQuotientAlgebra
        (k := k) (P := P) (A := Module.End k A) := by
  letI : MulSemiringAction P (A ⊗[k] Aᵐᵒᵖ) :=
    S.permutationBasis.tensorProductMulSemiringAction
      S.permutationBasis.opposite
  letI : SMulCommClass P k (A ⊗[k] Aᵐᵒᵖ) :=
    S.permutationBasis.tensorProductSMulCommClass
      S.permutationBasis.opposite
  let rho :=
    representationLinearAction
      (algebraActionRepresentation
        (k := k) (P := P) (A := A))
  letI : MulSemiringAction P (Module.End k A) :=
    endomorphismConjugationMulSemiringAction rho
  letI : SMulCommClass P k (Module.End k A) :=
    endomorphismConjugation_smulCommClass rho
  exact
    brauerQuotientAlgEquiv
      S.leftRightAlgEquiv
      (S.leftRightAlgEquiv_smul)

omit [Finite k] in
/-- The conjugation endomorphism Brauer comparison for the underlying
permutation module of a Dade algebra. -/
theorem algebraActionEndomorphismBrauerComparisonIsomorphism
    (S : DadeAlgebra p k P A) :
    EndomorphismBrauerComparisonIsomorphism
      (algebraActionRepresentation
        (k := k) (P := P) (A := A)) := by
  letI : FiniteDimensional k A :=
    S.finiteDimensional
  letI : Finite S.permutationBasis.index :=
    Module.Finite.finite_basis S.permutationBasis.basis
  letI : MulAction P S.permutationBasis.index :=
    PointedPermutationAlgebraBasis.indexMulAction
      (B := S.permutationBasis)
  have h :=
    S.permutationBasis.toPermutationModuleBasis
      |>.endomorphismBrauerComparisonIsomorphism_of_permutationBasis
        S.isPGroup
  rw [S.permutationBasis.toPermutationModuleBasis_representation] at h
  exact h

/-- The tensor product of the Brauer quotient with the Brauer
quotient of the opposite algebra is a full endomorphism algebra.

This statement is the elementary split form before identifying
`Aᵐᵒᵖ(P)` with `A(P)ᵐᵒᵖ`. -/
def brauerTensorOppositeEquivEndomorphism
    (S : DadeAlgebra p k P A) :
    let BQ :=
      BrauerQuotientAlgebra (k := k) (P := P) (A := A)
    let BQop :=
      BrauerQuotientAlgebra (k := k) (P := P) (A := Aᵐᵒᵖ)
    BQ ⊗[k] BQop ≃ₐ[k] Module.End k BQ := by
  letI : FiniteDimensional k A :=
    S.finiteDimensional
  letI : Finite S.permutationBasis.index :=
    Module.Finite.finite_basis S.permutationBasis.basis
  let rho :=
    algebraActionRepresentation
      (k := k) (P := P) (A := A)
  let rhoLinear :=
    representationLinearAction rho
  letI : MulSemiringAction P (Module.End k A) :=
    endomorphismConjugationMulSemiringAction rhoLinear
  letI : SMulCommClass P k (Module.End k A) :=
    endomorphismConjugation_smulCommClass rhoLinear
  let BQ :=
    BrauerQuotientAlgebra (k := k) (P := P) (A := A)
  let BQop :=
    BrauerQuotientAlgebra (k := k) (P := P) (A := Aᵐᵒᵖ)
  let q :=
    PointedPermutationAlgebraBasis.brauerQuotientAlgebraEquivBrauerQuotient
      (k := k) (P := P) (A := A)
  exact
    (S.brauerQuotientTensorEquiv S.opposite).trans
      (S.brauerLeftRightAlgEquiv |>.trans
        ((endomorphismBrauerAlgEquiv rho
            S.algebraActionEndomorphismBrauerComparisonIsomorphism).trans
          (q.symm.conjAlgEquiv k)))

end DadeAlgebra
end Representation
