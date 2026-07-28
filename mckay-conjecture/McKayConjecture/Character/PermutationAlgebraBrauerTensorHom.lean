/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.PermutationAlgebraTensorProduct

/-!
# The Brauer homomorphism for tensor products of permutation algebras

The inclusions of the two tensor factors carry their Brauer trace
ideals into the trace ideal of the diagonal tensor product.  They
therefore descend to the two algebra Brauer quotients.  Their images
commute, giving a natural algebra homomorphism

`A(P) ⊗ B(P) → (A ⊗ B)(P)`.
-/

noncomputable section

open scoped BigOperators TensorProduct

namespace Representation
namespace PointedPermutationAlgebraBasis

variable {p : ℕ} [Fact p.Prime]
variable {k P A D : Type}
variable [Field k] [CharP k p]
variable [Group P] [Finite P]
variable [Ring A] [Algebra k A]
variable [Ring D] [Algebra k D]
variable [MulSemiringAction P A] [SMulCommClass P k A]
variable [MulSemiringAction P D] [SMulCommClass P k D]

variable
  (B : PointedPermutationAlgebraBasis
    (k := k) (P := P) (A := A))
  (C : PointedPermutationAlgebraBasis
    (k := k) (P := P) (A := D))

noncomputable local instance tensorBrauerAlgebraGroupFintype :
    Fintype P :=
  Fintype.ofFinite P

/-- The tensor of two globally fixed elements is globally fixed under
the diagonal action. -/
def fixedTensorProduct
    (x : fixedSubalgebra (k := k) (P := P) (A := A))
    (y : fixedSubalgebra (k := k) (P := P) (A := D)) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    fixedSubalgebra (k := k) (P := P) (A := A ⊗[k] D) := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  exact
    ⟨(x : A) ⊗ₜ[k] (y : D), fun g => by
      rw [B.tensorProduct_smul_tmul C]
      rw [x.property g, y.property g]⟩

omit [Finite P] in
@[simp]
theorem fixedTensorProduct_coe
    (x : fixedSubalgebra (k := k) (P := P) (A := A))
    (y : fixedSubalgebra (k := k) (P := P) (A := D)) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    ((B.fixedTensorProduct C x y :
        fixedSubalgebra
          (k := k) (P := P) (A := A ⊗[k] D)) :
      A ⊗[k] D) =
        (x : A) ⊗ₜ[k] (y : D) :=
  rfl

/-- Inclusion of the left fixed algebra into the fixed algebra of the
diagonal tensor product. -/
def fixedTensorIncludeLeft :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    fixedSubalgebra (k := k) (P := P) (A := A) →ₐ[k]
      fixedSubalgebra (k := k) (P := P) (A := A ⊗[k] D) := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  exact
    { toFun := fun x => B.fixedTensorProduct C x 1
      map_zero' := by
        apply Subtype.ext
        simp
      map_add' := fun x y => by
        apply Subtype.ext
        change
          ((x : A) + (y : A)) ⊗ₜ[k] (1 : D) =
            (x : A) ⊗ₜ[k] (1 : D) +
              (y : A) ⊗ₜ[k] (1 : D)
        rw [TensorProduct.add_tmul]
      map_one' := by
        apply Subtype.ext
        exact Algebra.TensorProduct.one_def.symm
      map_mul' := fun x y => by
        apply Subtype.ext
        change
          ((x : A) * (y : A)) ⊗ₜ[k] (1 : D) =
            ((x : A) ⊗ₜ[k] (1 : D)) *
              ((y : A) ⊗ₜ[k] (1 : D))
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      commutes' := fun a => by
        apply Subtype.ext
        change
          (algebraMap k A a) ⊗ₜ[k] (1 : D) =
            algebraMap k (A ⊗[k] D) a
        rw [Algebra.TensorProduct.algebraMap_apply] }

/-- Inclusion of the right fixed algebra into the fixed algebra of the
diagonal tensor product. -/
def fixedTensorIncludeRight :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    fixedSubalgebra (k := k) (P := P) (A := D) →ₐ[k]
      fixedSubalgebra (k := k) (P := P) (A := A ⊗[k] D) := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  exact
    { toFun := fun y => B.fixedTensorProduct C 1 y
      map_zero' := by
        apply Subtype.ext
        simp
      map_add' := fun x y => by
        apply Subtype.ext
        change
          (1 : A) ⊗ₜ[k] ((x : D) + (y : D)) =
            (1 : A) ⊗ₜ[k] (x : D) +
              (1 : A) ⊗ₜ[k] (y : D)
        rw [TensorProduct.tmul_add]
      map_one' := by
        apply Subtype.ext
        exact Algebra.TensorProduct.one_def.symm
      map_mul' := fun x y => by
        apply Subtype.ext
        change
          (1 : A) ⊗ₜ[k] ((x : D) * (y : D)) =
            ((1 : A) ⊗ₜ[k] (x : D)) *
              ((1 : A) ⊗ₜ[k] (y : D))
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      commutes' := fun a => by
        apply Subtype.ext
        change
          (1 : A) ⊗ₜ[k] (algebraMap k D a) =
            algebraMap k (A ⊗[k] D) a
        rw [Algebra.TensorProduct.algebraMap_apply'] }

/-- The left inclusion commutes with relative traces. -/
theorem fixedTensorIncludeLeft_fixedRelativeTrace
    (Q : Subgroup P)
    (x : fixedSubalgebra (k := k) (P := Q) (A := A)) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    B.fixedTensorIncludeLeft C
        (fixedRelativeTrace (k := k) (P := P) (A := A) Q x) =
      fixedRelativeTrace (k := k) (P := P) (A := A ⊗[k] D) Q
        ⟨(x : A) ⊗ₜ[k] (1 : D), fun q => by
          change
            (q : P) • ((x : A) ⊗ₜ[k] (1 : D)) =
              (x : A) ⊗ₜ[k] (1 : D)
          rw [B.tensorProduct_smul_tmul C]
          have hx := x.property q
          change (q : P) • (x : A) = x at hx
          rw [hx, smul_one]⟩ := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  apply Subtype.ext
  change
    (∑ c : P ⧸ Q, c.out • (x : A)) ⊗ₜ[k] (1 : D) =
      ∑ c : P ⧸ Q,
        c.out • ((x : A) ⊗ₜ[k] (1 : D))
  rw [TensorProduct.sum_tmul]
  apply Fintype.sum_congr
  intro c
  rw [B.tensorProduct_smul_tmul C, smul_one]

/-- The right inclusion commutes with relative traces. -/
theorem fixedTensorIncludeRight_fixedRelativeTrace
    (Q : Subgroup P)
    (y : fixedSubalgebra (k := k) (P := Q) (A := D)) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    B.fixedTensorIncludeRight C
        (fixedRelativeTrace (k := k) (P := P) (A := D) Q y) =
      fixedRelativeTrace (k := k) (P := P) (A := A ⊗[k] D) Q
        ⟨(1 : A) ⊗ₜ[k] (y : D), fun q => by
          change
            (q : P) • ((1 : A) ⊗ₜ[k] (y : D)) =
              (1 : A) ⊗ₜ[k] (y : D)
          rw [B.tensorProduct_smul_tmul C]
          have hy := y.property q
          change (q : P) • (y : D) = y at hy
          rw [smul_one, hy]⟩ := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  apply Subtype.ext
  change
    (1 : A) ⊗ₜ[k] (∑ c : P ⧸ Q, c.out • (y : D)) =
      ∑ c : P ⧸ Q,
        c.out • ((1 : A) ⊗ₜ[k] (y : D))
  rw [TensorProduct.tmul_sum]
  apply Fintype.sum_congr
  intro c
  rw [B.tensorProduct_smul_tmul C, smul_one]

/-- The composite of the left fixed-algebra inclusion with the target
Brauer projection. -/
def leftFixedToTensorBrauer :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    fixedSubalgebra (k := k) (P := P) (A := A) →ₐ[k]
      BrauerQuotientAlgebra
        (k := k) (P := P) (A := A ⊗[k] D) := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  exact
    (Ideal.Quotient.mkₐ k
      (brauerTraceIdeal
        (k := k) (P := P) (A := A ⊗[k] D))).comp
      (B.fixedTensorIncludeLeft C)

/-- The corresponding composite for the right fixed algebra. -/
def rightFixedToTensorBrauer :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    fixedSubalgebra (k := k) (P := P) (A := D) →ₐ[k]
      BrauerQuotientAlgebra
        (k := k) (P := P) (A := A ⊗[k] D) := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  exact
    (Ideal.Quotient.mkₐ k
      (brauerTraceIdeal
        (k := k) (P := P) (A := A ⊗[k] D))).comp
      (B.fixedTensorIncludeRight C)

/-- The left trace ideal is killed after inclusion and target Brauer
projection. -/
theorem leftFixedToTensorBrauer_eq_zero_of_mem
    (z : fixedSubalgebra (k := k) (P := P) (A := A))
    (hz : z ∈ brauerTraceIdeal (k := k) (P := P) (A := A)) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    B.leftFixedToTensorBrauer C z = 0 := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  change
    z ∈
      ⨆ (Q : Subgroup P) (_hQ : Q < ⊤),
        fixedRelativeTraceIdeal
          (k := k) (P := P) (A := A) Q at hz
  refine Submodule.iSup_induction
    (fun Q : Subgroup P ↦
      ⨆ _hQ : Q < ⊤,
        fixedRelativeTraceIdeal
          (k := k) (P := P) (A := A) Q)
    (motive := fun w ↦ B.leftFixedToTensorBrauer C w = 0)
    hz ?_ ?_ ?_
  · intro Q w hw
    refine Submodule.iSup_induction
      (fun _hQ : Q < ⊤ ↦
        fixedRelativeTraceIdeal
          (k := k) (P := P) (A := A) Q)
      (motive := fun v ↦ B.leftFixedToTensorBrauer C v = 0)
      hw ?_ ?_ ?_
    · intro hQ v hv
      rcases hv with ⟨x, rfl⟩
      rw [leftFixedToTensorBrauer, AlgHom.comp_apply]
      rw [B.fixedTensorIncludeLeft_fixedRelativeTrace C Q x]
      exact
        brauerAlgebraProjection_fixedRelativeTrace
          (k := k) (P := P) (A := A ⊗[k] D) Q hQ _
    · exact map_zero _
    · intro x y hx hy
      rw [map_add, hx, hy, add_zero]
  · exact map_zero _
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]

/-- The right trace ideal is killed after inclusion and target Brauer
projection. -/
theorem rightFixedToTensorBrauer_eq_zero_of_mem
    (z : fixedSubalgebra (k := k) (P := P) (A := D))
    (hz : z ∈ brauerTraceIdeal (k := k) (P := P) (A := D)) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    B.rightFixedToTensorBrauer C z = 0 := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  change
    z ∈
      ⨆ (Q : Subgroup P) (_hQ : Q < ⊤),
        fixedRelativeTraceIdeal
          (k := k) (P := P) (A := D) Q at hz
  refine Submodule.iSup_induction
    (fun Q : Subgroup P ↦
      ⨆ _hQ : Q < ⊤,
        fixedRelativeTraceIdeal
          (k := k) (P := P) (A := D) Q)
    (motive := fun w ↦ B.rightFixedToTensorBrauer C w = 0)
    hz ?_ ?_ ?_
  · intro Q w hw
    refine Submodule.iSup_induction
      (fun _hQ : Q < ⊤ ↦
        fixedRelativeTraceIdeal
          (k := k) (P := P) (A := D) Q)
      (motive := fun v ↦ B.rightFixedToTensorBrauer C v = 0)
      hw ?_ ?_ ?_
    · intro hQ v hv
      rcases hv with ⟨y, rfl⟩
      rw [rightFixedToTensorBrauer, AlgHom.comp_apply]
      rw [B.fixedTensorIncludeRight_fixedRelativeTrace C Q y]
      exact
        brauerAlgebraProjection_fixedRelativeTrace
          (k := k) (P := P) (A := A ⊗[k] D) Q hQ _
    · exact map_zero _
    · intro x y hx hy
      rw [map_add, hx, hy, add_zero]
  · exact map_zero _
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]

/-- The left inclusion descended to the left Brauer quotient. -/
def leftBrauerToTensorBrauer :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    BrauerQuotientAlgebra (k := k) (P := P) (A := A) →ₐ[k]
      BrauerQuotientAlgebra
        (k := k) (P := P) (A := A ⊗[k] D) := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  exact
    Ideal.Quotient.liftₐ
      (brauerTraceIdeal (k := k) (P := P) (A := A))
      (B.leftFixedToTensorBrauer C)
      (B.leftFixedToTensorBrauer_eq_zero_of_mem C)

/-- The right inclusion descended to the right Brauer quotient. -/
def rightBrauerToTensorBrauer :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    BrauerQuotientAlgebra (k := k) (P := P) (A := D) →ₐ[k]
      BrauerQuotientAlgebra
        (k := k) (P := P) (A := A ⊗[k] D) := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  exact
    Ideal.Quotient.liftₐ
      (brauerTraceIdeal (k := k) (P := P) (A := D))
      (B.rightFixedToTensorBrauer C)
      (B.rightFixedToTensorBrauer_eq_zero_of_mem C)

@[simp]
theorem leftBrauerToTensorBrauer_projection
    (x : fixedSubalgebra (k := k) (P := P) (A := A)) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    B.leftBrauerToTensorBrauer C
        (brauerAlgebraProjection
          (k := k) (P := P) (A := A) x) =
      brauerAlgebraProjection
        (k := k) (P := P) (A := A ⊗[k] D)
        (B.fixedTensorProduct C x 1) := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  simp only [leftBrauerToTensorBrauer,
    brauerAlgebraProjection,
    Ideal.Quotient.liftₐ_apply,
    leftFixedToTensorBrauer]
  rfl

@[simp]
theorem rightBrauerToTensorBrauer_projection
    (y : fixedSubalgebra (k := k) (P := P) (A := D)) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    B.rightBrauerToTensorBrauer C
        (brauerAlgebraProjection
          (k := k) (P := P) (A := D) y) =
      brauerAlgebraProjection
        (k := k) (P := P) (A := A ⊗[k] D)
        (B.fixedTensorProduct C 1 y) := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  simp only [rightBrauerToTensorBrauer,
    brauerAlgebraProjection,
    Ideal.Quotient.liftₐ_apply,
    rightFixedToTensorBrauer]
  rfl

/-- The descended left and right inclusions have commuting images. -/
theorem leftBrauer_commutes_rightBrauer
    (x : BrauerQuotientAlgebra (k := k) (P := P) (A := A))
    (y : BrauerQuotientAlgebra (k := k) (P := P) (A := D)) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    Commute
      (B.leftBrauerToTensorBrauer C x)
      (B.rightBrauerToTensorBrauer C y) := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  refine Quotient.inductionOn' x ?_
  intro a
  refine Quotient.inductionOn' y ?_
  intro d
  change
    Commute
      (B.leftBrauerToTensorBrauer C
        (brauerAlgebraProjection
          (k := k) (P := P) (A := A) a))
      (B.rightBrauerToTensorBrauer C
        (brauerAlgebraProjection
          (k := k) (P := P) (A := D) d))
  rw [B.leftBrauerToTensorBrauer_projection C]
  rw [B.rightBrauerToTensorBrauer_projection C]
  apply Commute.map
  apply Subtype.ext
  change
    ((a : A) ⊗ₜ[k] (1 : D)) *
        ((1 : A) ⊗ₜ[k] (d : D)) =
      ((1 : A) ⊗ₜ[k] (d : D)) *
        ((a : A) ⊗ₜ[k] (1 : D))
  rw [Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]
  rw [one_mul, mul_one]

/-- The natural algebra homomorphism from the tensor product of the
two Brauer quotients to the Brauer quotient of the diagonal tensor
product. -/
def brauerQuotientAlgebraTensorHom :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    (BrauerQuotientAlgebra (k := k) (P := P) (A := A) ⊗[k]
      BrauerQuotientAlgebra (k := k) (P := P) (A := D)) →ₐ[k]
        BrauerQuotientAlgebra
          (k := k) (P := P) (A := A ⊗[k] D) := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  exact
    Algebra.TensorProduct.lift
      (B.leftBrauerToTensorBrauer C)
      (B.rightBrauerToTensorBrauer C)
      (B.leftBrauer_commutes_rightBrauer C)

/-- The natural tensor Brauer homomorphism agrees with tensoring
representatives and applying the target Brauer projection. -/
@[simp]
theorem brauerQuotientAlgebraTensorHom_projection_tmul
    (x : fixedSubalgebra (k := k) (P := P) (A := A))
    (y : fixedSubalgebra (k := k) (P := P) (A := D)) :
    letI : MulSemiringAction P (A ⊗[k] D) :=
      B.tensorProductMulSemiringAction C
    letI : SMulCommClass P k (A ⊗[k] D) :=
      B.tensorProductSMulCommClass C
    B.brauerQuotientAlgebraTensorHom C
        (brauerAlgebraProjection
            (k := k) (P := P) (A := A) x ⊗ₜ[k]
          brauerAlgebraProjection
            (k := k) (P := P) (A := D) y) =
      brauerAlgebraProjection
        (k := k) (P := P) (A := A ⊗[k] D)
        (B.fixedTensorProduct C x y) := by
  letI : MulSemiringAction P (A ⊗[k] D) :=
    B.tensorProductMulSemiringAction C
  letI : SMulCommClass P k (A ⊗[k] D) :=
    B.tensorProductSMulCommClass C
  rw [brauerQuotientAlgebraTensorHom]
  rw [Algebra.TensorProduct.lift_tmul]
  rw [B.leftBrauerToTensorBrauer_projection C]
  rw [B.rightBrauerToTensorBrauer_projection C]
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  change
    ((x : A) ⊗ₜ[k] (1 : D)) *
        ((1 : A) ⊗ₜ[k] (y : D)) =
      (x : A) ⊗ₜ[k] (y : D)
  rw [Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]

end PointedPermutationAlgebraBasis
end Representation
