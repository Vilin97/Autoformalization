/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedTensorIrreducible
import McKayConjecture.CharacterTriple.MultiplicityProjective
import McKayConjecture.CharacterTriple.ProjectiveIntertwiner

/-!
# Recovering a projective tensor factor as a multiplicity action

Suppose an associated projective representation `P` is tensored with an
inverse-factor projective representation `Q`.  If an ordinary representation
`D` is equivalent to that cancelled tensor, then

`z ↦ (v ↦ e (v ⊗ z))`

is an exact intertwiner from `Q` to the projective multiplicity action of
`D`.  For irreducible source and target projective actions this is a linear
equivalence.  The construction records operator equality, not merely
equality of factor-set cohomology classes.
-/

noncomputable section

open scoped TensorProduct

universe u

namespace McKayConjecture
namespace CharacterTriple
namespace MultiplicityProjective

variable {A : Type u} [Finite A] [Group A]
variable {T : CharacterTriple A}
variable {V : Type} [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable {Z : Type} [AddCommGroup Z] [Module ℂ Z]
variable {Y : Type} [AddCommGroup Y] [Module ℂ Y]
variable {P : ProjectiveRepresentation ℂ A V}

/-- A tensor-factor vector, regarded as an intertwiner from the associated
normal representation into `D`. -/
def tensorFactorMultiplicityValue
    (R : AssociatedProjectiveRepresentation T V P)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : P.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal T)
    (D : Representation ℂ A Y)
    (e : Representation.Equiv
      (P.cancelTensorRepresentation Q hQ) D)
    (z : Z) :
    Space R D where
  toLinearMap :=
    e.toLinearEquiv.toLinearMap.comp
      ((TensorProduct.mk ℂ V Z).flip z)
  isIntertwining' x := by
    apply LinearMap.ext
    intro v
    change
      e (R.restriction x v ⊗ₜ[ℂ] z) =
        D (x : A) (e (v ⊗ₜ[ℂ] z))
    have he :=
      LinearMap.congr_fun
        (e.toIntertwiningMap.isIntertwining' (x : A))
        (v ⊗ₜ[ℂ] z)
    rw [R.cancelTensorRepresentation_normal
      Q hQ htriv x] at he
    change
      e (TensorProduct.map
          (R.restriction x) LinearMap.id
          (v ⊗ₜ[ℂ] z)) =
        D (x : A) (e (v ⊗ₜ[ℂ] z)) at he
    rw [TensorProduct.map_tmul] at he
    simpa using he

@[simp]
theorem tensorFactorMultiplicityValue_apply
    (R : AssociatedProjectiveRepresentation T V P)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : P.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal T)
    (D : Representation ℂ A Y)
    (e : Representation.Equiv
      (P.cancelTensorRepresentation Q hQ) D)
    (z : Z) (v : V) :
    tensorFactorMultiplicityValue R Q hQ htriv D e z v =
      e (v ⊗ₜ[ℂ] z) :=
  rfl

/-- The tensor-factor-to-multiplicity assignment is linear. -/
def tensorFactorMultiplicityLinearMap
    (R : AssociatedProjectiveRepresentation T V P)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : P.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal T)
    (D : Representation ℂ A Y)
    (e : Representation.Equiv
      (P.cancelTensorRepresentation Q hQ) D) :
    Z →ₗ[ℂ] Space R D where
  toFun := tensorFactorMultiplicityValue
    R Q hQ htriv D e
  map_add' z z' := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    change
      e (v ⊗ₜ[ℂ] (z + z')) =
        e (v ⊗ₜ[ℂ] z) + e (v ⊗ₜ[ℂ] z')
    rw [TensorProduct.tmul_add, map_add]
  map_smul' c z := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    change
      e (v ⊗ₜ[ℂ] (c • z)) =
        c • e (v ⊗ₜ[ℂ] z)
    rw [TensorProduct.tmul_smul, map_smul]

@[simp]
theorem tensorFactorMultiplicityLinearMap_apply
    (R : AssociatedProjectiveRepresentation T V P)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : P.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal T)
    (D : Representation ℂ A Y)
    (e : Representation.Equiv
      (P.cancelTensorRepresentation Q hQ) D)
    (z : Z) :
    tensorFactorMultiplicityLinearMap R Q hQ htriv D e z =
      tensorFactorMultiplicityValue R Q hQ htriv D e z :=
  rfl

/-- Pointwise operator compatibility of the tensor-factor multiplicity
map. -/
theorem tensorFactorMultiplicityLinearMap_intertwines_apply
    (R : AssociatedProjectiveRepresentation T V P)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : P.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal T)
    (D : Representation ℂ A Y)
    (e : Representation.Equiv
      (P.cancelTensorRepresentation Q hQ) D)
    (g : A) (z : Z) (v : V) :
    tensorFactorMultiplicityLinearMap R Q hQ htriv D e
        (Q.operator g z) v =
      (projective R D).operator g
        (tensorFactorMultiplicityLinearMap
          R Q hQ htriv D e z) v := by
  change
    e (v ⊗ₜ[ℂ] Q.operator g z) =
      D g
        (e ((P.operator g).symm v ⊗ₜ[ℂ] z))
  have he :=
    Representation.IntertwiningMap.isIntertwining
      (P.cancelTensorRepresentation Q hQ) D
      e.toIntertwiningMap g
      ((P.operator g).symm v ⊗ₜ[ℂ] z)
  rw [ProjectiveRepresentation.cancelTensorRepresentation_apply,
    TensorProduct.map_tmul] at he
  simpa using he

/-- The tensor-factor map commutes with the exact chosen projective
operators. -/
def tensorFactorMultiplicityIntertwiningMap
    (R : AssociatedProjectiveRepresentation T V P)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : P.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal T)
    (D : Representation ℂ A Y)
    (e : Representation.Equiv
      (P.cancelTensorRepresentation Q hQ) D) :
    Q.IntertwiningMap (projective R D) where
  toLinearMap :=
    tensorFactorMultiplicityLinearMap R Q hQ htriv D e
  intertwines g := by
    apply LinearMap.ext
    intro z
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    exact
      tensorFactorMultiplicityLinearMap_intertwines_apply
        R Q hQ htriv D e g z v

/-- On nonzero tensor factors, the recovery intertwiner is nonzero. -/
theorem tensorFactorMultiplicityIntertwiningMap_ne_zero
    [Nontrivial Z]
    (R : AssociatedProjectiveRepresentation T V P)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : P.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal T)
    (D : Representation ℂ A Y)
    (e : Representation.Equiv
      (P.cancelTensorRepresentation Q hQ) D) :
    (tensorFactorMultiplicityIntertwiningMap
      R Q hQ htriv D e).toLinearMap ≠ 0 := by
  obtain ⟨z : Z, hz⟩ := exists_ne (0 : Z)
  obtain ⟨v : V, hv⟩ := exists_ne (0 : V)
  obtain ⟨φ, hφ⟩ :=
    Module.Projective.exists_dual_eq_one ℂ hz
  intro hzero
  have hzmap := LinearMap.congr_fun hzero z
  have hvmap :=
    congrArg
      (fun f : Space R D ↦ f v)
      hzmap
  change e (v ⊗ₜ[ℂ] z) = 0 at hvmap
  have htensor : v ⊗ₜ[ℂ] z = 0 := by
    apply e.toLinearEquiv.injective
    simpa using hvmap
  have hsliced :=
    congrArg
      (fun t : V ⊗[ℂ] Z ↦
        TensorProduct.rid ℂ V (φ.lTensor V t))
      htensor
  simp only [map_zero, LinearMap.lTensor_tmul,
    TensorProduct.rid_tmul, hφ, one_smul] at hsliced
  exact hv hsliced

/-- For irreducible projective actions, tensor-factor recovery is a linear
equivalence. -/
def tensorFactorMultiplicityLinearEquiv
    [Nontrivial Z]
    (R : AssociatedProjectiveRepresentation T V P)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : P.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal T)
    (D : Representation ℂ A Y)
    (e : Representation.Equiv
      (P.cancelTensorRepresentation Q hQ) D)
    (hQirr : Q.IsIrreducible)
    (hMirr : (projective R D).IsIrreducible) :
    Z ≃ₗ[ℂ] Space R D :=
  (tensorFactorMultiplicityIntertwiningMap
    R Q hQ htriv D e).linearEquivOfNeZero
      hQirr hMirr
      (tensorFactorMultiplicityIntertwiningMap_ne_zero
        R Q hQ htriv D e)

@[simp]
theorem tensorFactorMultiplicityLinearEquiv_intertwines
    [Nontrivial Z]
    (R : AssociatedProjectiveRepresentation T V P)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : P.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal T)
    (D : Representation ℂ A Y)
    (e : Representation.Equiv
      (P.cancelTensorRepresentation Q hQ) D)
    (hQirr : Q.IsIrreducible)
    (hMirr : (projective R D).IsIrreducible)
    (g : A) (z : Z) :
    tensorFactorMultiplicityLinearEquiv
        R Q hQ htriv D e hQirr hMirr
        (Q.operator g z) =
      (projective R D).operator g
        (tensorFactorMultiplicityLinearEquiv
          R Q hQ htriv D e hQirr hMirr z) :=
  (tensorFactorMultiplicityIntertwiningMap
    R Q hQ htriv D e).intertwines_apply g z

end MultiplicityProjective
end CharacterTriple
end McKayConjecture
