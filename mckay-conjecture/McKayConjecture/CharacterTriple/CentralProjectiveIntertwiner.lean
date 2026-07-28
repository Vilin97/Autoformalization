/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedTensorIrreducible
import McKayConjecture.CharacterTriple.CentralProjectiveLift
import McKayConjecture.CharacterTriple.ProjectiveIntertwiner

/-!
# Extending projective intertwiners across a central isomorphism

For inverse-factor projective representations that are identity on the left
normal subgroup, every chosen operator on `A` is already an operator on the
embedded copy of `B`.  Thus an exact projective intertwiner after comapping
along the embedding extends unchanged to `A`.

The file also packages tensoring such a projective equivalence with a common
first factor as an equivalence of the cancelled ordinary representations.
-/

noncomputable section

open scoped TensorProduct

universe u v

namespace McKayConjecture
namespace CharacterTriple

namespace ProjectiveRepresentation

variable {G : Type u} [Group G]
variable {V Z Y : Type}
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup Z] [Module ℂ Z]
variable [AddCommGroup Y] [Module ℂ Y]

/-- Pull an exact projective intertwiner back along a group homomorphism. -/
def IntertwiningMap.comap
    {H : Type*} [Group H]
    {Q : ProjectiveRepresentation ℂ G Z}
    {R : ProjectiveRepresentation ℂ G Y}
    (f : Q.IntertwiningMap R) (φ : H →* G) :
    (Q.comap φ).IntertwiningMap (R.comap φ) where
  toLinearMap := f.toLinearMap
  intertwines h := f.intertwines (φ h)

@[simp]
theorem IntertwiningMap.comap_toLinearMap
    {H : Type*} [Group H]
    {Q : ProjectiveRepresentation ℂ G Z}
    {R : ProjectiveRepresentation ℂ G Y}
    (f : Q.IntertwiningMap R) (φ : H →* G) :
    (f.comap φ).toLinearMap = f.toLinearMap :=
  rfl

/-- Transport a projective intertwiner across equalities of its source and
target projective representations. -/
def IntertwiningMap.transport
    {P P' : ProjectiveRepresentation ℂ G Z}
    {Q Q' : ProjectiveRepresentation ℂ G Y}
    (hP : P = P') (hQ : Q = Q')
    (f : P.IntertwiningMap Q) :
    P'.IntertwiningMap Q' := by
  subst P'
  subst Q'
  exact f

@[simp]
theorem IntertwiningMap.transport_toLinearMap
    {P P' : ProjectiveRepresentation ℂ G Z}
    {Q Q' : ProjectiveRepresentation ℂ G Y}
    (hP : P = P') (hQ : Q = Q')
    (f : P.IntertwiningMap Q) :
    (f.transport hP hQ).toLinearMap = f.toLinearMap := by
  subst P'
  subst Q'
  rfl

/-- Tensor a projective operator equivalence with a common first factor. -/
def cancelTensorRepresentationEquiv
    (P : ProjectiveRepresentation ℂ G V)
    (Q : ProjectiveRepresentation ℂ G Z)
    (R : ProjectiveRepresentation ℂ G Y)
    (hQ : P.HasInverseFactorSet Q)
    (hR : P.HasInverseFactorSet R)
    (e : Z ≃ₗ[ℂ] Y)
    (he : ∀ (g : G) (z : Z),
      e (Q.operator g z) = R.operator g (e z)) :
    Representation.Equiv
      (P.cancelTensorRepresentation Q hQ)
      (P.cancelTensorRepresentation R hR) := by
  let tensorEquiv :
      V ⊗[ℂ] Z ≃ₗ[ℂ] V ⊗[ℂ] Y :=
    TensorProduct.congr (LinearEquiv.refl ℂ V) e
  apply Representation.Equiv.mk tensorEquiv
  intro g
  apply LinearMap.ext
  intro t
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · simp
  · intro v z
    change
      tensorEquiv
          (TensorProduct.map
            (P.operator g : V →ₗ[ℂ] V)
            (Q.operator g : Z →ₗ[ℂ] Z)
            (v ⊗ₜ[ℂ] z)) =
        TensorProduct.map
          (P.operator g : V →ₗ[ℂ] V)
          (R.operator g : Y →ₗ[ℂ] Y)
          (tensorEquiv (v ⊗ₜ[ℂ] z))
    change
      P.operator g v ⊗ₜ[ℂ] e (Q.operator g z) =
        P.operator g v ⊗ₜ[ℂ] R.operator g (e z)
    rw [he]
  · intro x y hx hy
    simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- A nonzero intertwiner between irreducible projective factors gives an
equivalence of the corresponding cancelled tensor representations. -/
def cancelTensorRepresentationEquivOfIntertwiningMap
    (P : ProjectiveRepresentation ℂ G V)
    (Q : ProjectiveRepresentation ℂ G Z)
    (R : ProjectiveRepresentation ℂ G Y)
    (hQ : P.HasInverseFactorSet Q)
    (hR : P.HasInverseFactorSet R)
    (f : Q.IntertwiningMap R)
    (hQirr : Q.IsIrreducible)
    (hRirr : R.IsIrreducible)
    (hf : f.toLinearMap ≠ 0) :
    Representation.Equiv
      (P.cancelTensorRepresentation Q hQ)
      (P.cancelTensorRepresentation R hR) :=
  let e := f.linearEquivOfNeZero hQirr hRirr hf
  cancelTensorRepresentationEquiv P Q R hQ hR e
    (fun g z ↦ f.intertwines_apply g z)

end ProjectiveRepresentation

namespace FactorMatchedIsomorphismWitness

local notation "CentralIsomorphismWitness" =>
  FactorMatchedIsomorphismWitness

variable {A : Type u} {B : Type v}
variable [Finite A] [Finite B] [Group A] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {V W Z Y : Type}
variable [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W]
  [Module.Finite ℂ W] [Nontrivial W]
variable [AddCommGroup Z] [Module ℂ Z]
variable [AddCommGroup Y] [Module ℂ Y]

/-- A specified normal-times-embedded decomposition computes the chosen
operator of any inverse-factor, normal-trivial projective representation. -/
theorem multiplicity_operator_eq_embedding_of_decomposition
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (hQ : C.leftProjective.HasInverseFactorSet Q)
    (htriv : Q.IsTrivialOnNormal T)
    (a : A) (x : T.normalSubgroup) (b : B)
    (hxb : (x : A) * C.embedding b = a) :
    Q.operator a = Q.operator (C.embedding b) := by
  have hfactor :
      Q.factor (x : A) (C.embedding b) = 1 := by
    rw [hQ, C.leftAssociated.factor_normal_left x, inv_one]
  have hmul := Q.map_mul (x : A) (C.embedding b)
  rw [htriv x, one_mul, hfactor, map_one,
    one_mul, hxb] at hmul
  exact hmul.symm

/-- Extend an exact projective intertwiner from the embedded right group to
the left ambient group. -/
def extendProjectiveIntertwiningMap
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (R : ProjectiveRepresentation ℂ A Y)
    (hQ : C.leftProjective.HasInverseFactorSet Q)
    (hR : C.leftProjective.HasInverseFactorSet R)
    (hQtriv : Q.IsTrivialOnNormal T)
    (hRtriv : R.IsTrivialOnNormal T)
    (f : (Q.comap C.embedding).IntertwiningMap
      (R.comap C.embedding)) :
    Q.IntertwiningMap R where
  toLinearMap := f.toLinearMap
  intertwines a := by
    obtain ⟨x, b, hxb⟩ := C.ambient_eq_product a
    have hQop :=
      C.multiplicity_operator_eq_embedding_of_decomposition
        Q hQ hQtriv a x b hxb
    have hRop :=
      C.multiplicity_operator_eq_embedding_of_decomposition
        R hR hRtriv a x b hxb
    rw [hQop, hRop]
    exact f.intertwines b

@[simp]
theorem extendProjectiveIntertwiningMap_toLinearMap
    (C : CentralIsomorphismWitness T U V W)
    (Q : ProjectiveRepresentation ℂ A Z)
    (R : ProjectiveRepresentation ℂ A Y)
    (hQ : C.leftProjective.HasInverseFactorSet Q)
    (hR : C.leftProjective.HasInverseFactorSet R)
    (hQtriv : Q.IsTrivialOnNormal T)
    (hRtriv : R.IsTrivialOnNormal T)
    (f : (Q.comap C.embedding).IntertwiningMap
      (R.comap C.embedding)) :
    (C.extendProjectiveIntertwiningMap
      Q R hQ hR hQtriv hRtriv f).toLinearMap =
      f.toLinearMap :=
  rfl

end FactorMatchedIsomorphismWitness

namespace CentralIsomorphismWitness

export FactorMatchedIsomorphismWitness
  (multiplicity_operator_eq_embedding_of_decomposition
    extendProjectiveIntertwiningMap
    extendProjectiveIntertwiningMap_toLinearMap)

end CentralIsomorphismWitness
end CharacterTriple
end McKayConjecture
