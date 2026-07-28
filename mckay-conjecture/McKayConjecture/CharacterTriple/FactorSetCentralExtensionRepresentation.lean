/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.RepresentationTheory.Basic
import McKayConjecture.CharacterTriple.FactorSetCentralExtension
import McKayConjecture.CharacterTriple.FiniteFactorNormalization

/-!
# Linear representations of factor-set central extensions

If the factor of a projective representation `P` is obtained from a
normalized factor set `α : FactorSet G A` through a coefficient homomorphism
`A →* Kˣ`, then the twisted central extension associated to `α` acts
linearly.  On the element `(g, a)`, the action is

`scalar(a) * P(g)`.

The final section applies this construction to the finite root-of-unity
factor set supplied by `ProjectiveRepresentation.finiteFactorSet`.
-/

noncomputable section

universe u v w z

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

variable {K : Type u} {V : Type v} {G : Type w} {A : Type z}
variable [Field K] [AddCommGroup V] [Module K V]
variable [Group G] [CommGroup A]

/-- The honest action of the factor-set central extension associated to a
projective representation.

The hypothesis says that applying `ι : A →* Kˣ` to the chosen factor set
recovers the factors of `P`.
-/
def centralExtensionLinearAction
    (P : ProjectiveRepresentation K G V)
    (α : FactorSet G A) (hα : α.IsNormalized)
    (ι : A →* Kˣ)
    (hfactor : ∀ g h : G, ι (α g h) = P.factor g h) :
    FactorSet.CentralExtensionGroup α hα →* (V ≃ₗ[K] V) where
  toFun x :=
    scalarLinearEquiv K V
        (ι (FactorSet.CentralExtensionGroup.coefficient α hα x)) *
      P.operator (FactorSet.CentralExtensionGroup.base α hα x)
  map_one' := by
    simp only [FactorSet.CentralExtensionGroup.coefficient_one,
      FactorSet.CentralExtensionGroup.base_one, map_one,
      one_mul]
    rw [P.operator_one_eq_scalar_left 1, ← hfactor 1 1,
      hα.1 1, map_one, scalarLinearEquiv_one]
  map_mul' x y := by
    simp only [FactorSet.CentralExtensionGroup.coefficient_mul,
      FactorSet.CentralExtensionGroup.base_mul]
    calc
      scalarLinearEquiv K V
            (ι
              (α (FactorSet.CentralExtensionGroup.base α hα x)
                  (FactorSet.CentralExtensionGroup.base α hα y) *
                FactorSet.CentralExtensionGroup.coefficient α hα x *
                FactorSet.CentralExtensionGroup.coefficient α hα y)) *
          P.operator
            (FactorSet.CentralExtensionGroup.base α hα x *
              FactorSet.CentralExtensionGroup.base α hα y) =
          scalarLinearEquiv K V
              (ι (FactorSet.CentralExtensionGroup.coefficient α hα x) *
                ι (FactorSet.CentralExtensionGroup.coefficient α hα y) *
                P.factor
                  (FactorSet.CentralExtensionGroup.base α hα x)
                  (FactorSet.CentralExtensionGroup.base α hα y)) *
            P.operator
              (FactorSet.CentralExtensionGroup.base α hα x *
                FactorSet.CentralExtensionGroup.base α hα y) := by
                  congr 1
                  congr 1
                  rw [ι.map_mul, ι.map_mul, hfactor]
                  ac_rfl
      _ =
          (scalarLinearEquiv K V
              (ι (FactorSet.CentralExtensionGroup.coefficient α hα x)) *
            scalarLinearEquiv K V
              (ι (FactorSet.CentralExtensionGroup.coefficient α hα y))) *
            (scalarLinearEquiv K V
                (P.factor
                  (FactorSet.CentralExtensionGroup.base α hα x)
                  (FactorSet.CentralExtensionGroup.base α hα y)) *
              P.operator
                (FactorSet.CentralExtensionGroup.base α hα x *
                  FactorSet.CentralExtensionGroup.base α hα y)) := by
                    rw [scalarLinearEquiv_mul, scalarLinearEquiv_mul]
                    simp only [mul_assoc]
      _ =
          (scalarLinearEquiv K V
              (ι (FactorSet.CentralExtensionGroup.coefficient α hα x)) *
            scalarLinearEquiv K V
              (ι (FactorSet.CentralExtensionGroup.coefficient α hα y))) *
            (P.operator (FactorSet.CentralExtensionGroup.base α hα x) *
              P.operator
                (FactorSet.CentralExtensionGroup.base α hα y)) := by
                  rw [P.map_mul]
      _ =
          scalarLinearEquiv K V
                (ι (FactorSet.CentralExtensionGroup.coefficient α hα x)) *
              (scalarLinearEquiv K V
                  (ι (FactorSet.CentralExtensionGroup.coefficient α hα y)) *
                P.operator
                  (FactorSet.CentralExtensionGroup.base α hα x)) *
            P.operator
              (FactorSet.CentralExtensionGroup.base α hα y) := by
                simp only [mul_assoc]
      _ =
          scalarLinearEquiv K V
                (ι (FactorSet.CentralExtensionGroup.coefficient α hα x)) *
              (P.operator (FactorSet.CentralExtensionGroup.base α hα x) *
                scalarLinearEquiv K V
                  (ι (FactorSet.CentralExtensionGroup.coefficient α hα y))) *
            P.operator
              (FactorSet.CentralExtensionGroup.base α hα y) := by
                rw [scalarLinearEquiv_comm K V
                  (ι (FactorSet.CentralExtensionGroup.coefficient α hα y))
                  (P.operator (FactorSet.CentralExtensionGroup.base α hα x))]
      _ =
          (scalarLinearEquiv K V
                (ι (FactorSet.CentralExtensionGroup.coefficient α hα x)) *
              P.operator (FactorSet.CentralExtensionGroup.base α hα x)) *
            (scalarLinearEquiv K V
                (ι (FactorSet.CentralExtensionGroup.coefficient α hα y)) *
              P.operator
                (FactorSet.CentralExtensionGroup.base α hα y)) := by
                  simp only [mul_assoc]

@[simp]
theorem centralExtensionLinearAction_apply
    (P : ProjectiveRepresentation K G V)
    (α : FactorSet G A) (hα : α.IsNormalized)
    (ι : A →* Kˣ)
    (hfactor : ∀ g h : G, ι (α g h) = P.factor g h)
    (x : FactorSet.CentralExtensionGroup α hα) :
    P.centralExtensionLinearAction α hα ι hfactor x =
      scalarLinearEquiv K V
          (ι (FactorSet.CentralExtensionGroup.coefficient α hα x)) *
        P.operator (FactorSet.CentralExtensionGroup.base α hα x) :=
  rfl

@[simp]
theorem centralExtensionLinearAction_apply_mk
    (P : ProjectiveRepresentation K G V)
    (α : FactorSet G A) (hα : α.IsNormalized)
    (ι : A →* Kˣ)
    (hfactor : ∀ g h : G, ι (α g h) = P.factor g h)
    (g : G) (a : A) :
    P.centralExtensionLinearAction α hα ι hfactor
        (FactorSet.CentralExtensionGroup.mk α hα g a) =
      scalarLinearEquiv K V (ι a) * P.operator g :=
  rfl

@[simp]
theorem centralExtensionLinearAction_apply_coefficientEmbedding
    (P : ProjectiveRepresentation K G V)
    (α : FactorSet G A) (hα : α.IsNormalized)
    (ι : A →* Kˣ)
    (hfactor : ∀ g h : G, ι (α g h) = P.factor g h)
    (a : A) :
    P.centralExtensionLinearAction α hα ι hfactor
        (FactorSet.CentralExtensionGroup.coefficientEmbedding α hα a) =
      scalarLinearEquiv K V (ι a) := by
  rw [FactorSet.CentralExtensionGroup.coefficientEmbedding_apply,
    centralExtensionLinearAction_apply_mk,
    P.operator_one_eq_scalar_left 1, ← hfactor 1 1,
    hα.1 1, map_one, scalarLinearEquiv_one, mul_one]

@[simp]
theorem centralExtensionLinearAction_apply_baseLift
    (P : ProjectiveRepresentation K G V)
    (α : FactorSet G A) (hα : α.IsNormalized)
    (ι : A →* Kˣ)
    (hfactor : ∀ g h : G, ι (α g h) = P.factor g h)
    (g : G) :
    P.centralExtensionLinearAction α hα ι hfactor
        (FactorSet.CentralExtensionGroup.mk α hα g 1) =
      P.operator g := by
  simp

/-- Restricting the extension action to its coefficient copy gives the
scalar action induced by `ι`. -/
theorem centralExtensionLinearAction_comp_coefficientEmbedding
    (P : ProjectiveRepresentation K G V)
    (α : FactorSet G A) (hα : α.IsNormalized)
    (ι : A →* Kˣ)
    (hfactor : ∀ g h : G, ι (α g h) = P.factor g h) :
    (P.centralExtensionLinearAction α hα ι hfactor).comp
        (FactorSet.CentralExtensionGroup.coefficientEmbedding α hα) =
      (scalarLinearEquiv K V).comp ι := by
  apply MonoidHom.ext
  intro a
  exact P.centralExtensionLinearAction_apply_coefficientEmbedding
    α hα ι hfactor a

/-- The mathlib `Representation` underlying the honest automorphism action of
the factor-set extension. -/
def centralExtensionRepresentation
    (P : ProjectiveRepresentation K G V)
    (α : FactorSet G A) (hα : α.IsNormalized)
    (ι : A →* Kˣ)
    (hfactor : ∀ g h : G, ι (α g h) = P.factor g h) :
    Representation K (FactorSet.CentralExtensionGroup α hα) V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (P.centralExtensionLinearAction α hα ι hfactor)

@[simp]
theorem centralExtensionRepresentation_apply
    (P : ProjectiveRepresentation K G V)
    (α : FactorSet G A) (hα : α.IsNormalized)
    (ι : A →* Kˣ)
    (hfactor : ∀ g h : G, ι (α g h) = P.factor g h)
    (x : FactorSet.CentralExtensionGroup α hα) :
    P.centralExtensionRepresentation α hα ι hfactor x =
      (scalarLinearEquiv K V
          (ι (FactorSet.CentralExtensionGroup.coefficient α hα x)) *
        P.operator (FactorSet.CentralExtensionGroup.base α hα x) :
          V →ₗ[K] V) :=
  rfl

@[simp]
theorem centralExtensionRepresentation_apply_vector
    (P : ProjectiveRepresentation K G V)
    (α : FactorSet G A) (hα : α.IsNormalized)
    (ι : A →* Kˣ)
    (hfactor : ∀ g h : G, ι (α g h) = P.factor g h)
    (x : FactorSet.CentralExtensionGroup α hα) (v : V) :
    P.centralExtensionRepresentation α hα ι hfactor x v =
      ((ι (FactorSet.CentralExtensionGroup.coefficient α hα x) : K) •
        P.operator (FactorSet.CentralExtensionGroup.base α hα x) v) :=
  rfl

@[simp]
theorem centralExtensionRepresentation_apply_coefficientEmbedding
    (P : ProjectiveRepresentation K G V)
    (α : FactorSet G A) (hα : α.IsNormalized)
    (ι : A →* Kˣ)
    (hfactor : ∀ g h : G, ι (α g h) = P.factor g h)
    (a : A) :
    P.centralExtensionRepresentation α hα ι hfactor
        (FactorSet.CentralExtensionGroup.coefficientEmbedding α hα a) =
      (scalarLinearEquiv K V (ι a) : V →ₗ[K] V) := by
  exact congrArg LinearEquiv.toLinearMap
    (P.centralExtensionLinearAction_apply_coefficientEmbedding
      α hα ι hfactor a)

section FiniteFactor

variable [IsAlgClosed K] [Module.Finite K V] [Nontrivial V]

/-- The root-of-unity central extension group attached to the
determinant-normalized factor set of `P`.

Its coefficient group is finite, so the `Finite` instance from
`FactorSet.CentralExtensionGroup` makes this group finite whenever `G` is
finite.
-/
abbrev FiniteFactorCentralExtensionGroup
    (P : ProjectiveRepresentation K G V) :=
  FactorSet.CentralExtensionGroup
    P.finiteFactorSet P.finiteFactorSet_isNormalized

/-- The central extension packaged from the finite root-of-unity factor set
of `P`. -/
def finiteFactorCentralExtension
    (P : ProjectiveRepresentation K G V) :
    GroupTheory.CentralExtension
      P.FiniteFactorCentralExtensionGroup G :=
  FactorSet.CentralExtensionGroup.centralExtension
    P.finiteFactorSet P.finiteFactorSet_isNormalized

/-- The honest automorphism action of the finite factor-set extension. -/
def finiteFactorCentralExtensionLinearAction
    (P : ProjectiveRepresentation K G V) :
    P.FiniteFactorCentralExtensionGroup →* (V ≃ₗ[K] V) :=
  P.finiteFactorNormalize.centralExtensionLinearAction
    P.finiteFactorSet P.finiteFactorSet_isNormalized
    (rootsOfUnity (Module.finrank K V) K).subtype
    P.finiteFactorSet_coe

/-- The honest linear representation of the finite factor-set extension. -/
def finiteFactorCentralExtensionRepresentation
    (P : ProjectiveRepresentation K G V) :
    Representation K P.FiniteFactorCentralExtensionGroup V :=
  P.finiteFactorNormalize.centralExtensionRepresentation
    P.finiteFactorSet P.finiteFactorSet_isNormalized
    (rootsOfUnity (Module.finrank K V) K).subtype
    P.finiteFactorSet_coe

@[simp]
theorem finiteFactorCentralExtensionLinearAction_apply
    (P : ProjectiveRepresentation K G V)
    (x : P.FiniteFactorCentralExtensionGroup) :
    P.finiteFactorCentralExtensionLinearAction x =
      scalarLinearEquiv K V
          ((FactorSet.CentralExtensionGroup.coefficient
            P.finiteFactorSet P.finiteFactorSet_isNormalized x :
              rootsOfUnity (Module.finrank K V) K) : Kˣ) *
        P.finiteFactorNormalize.operator
          (FactorSet.CentralExtensionGroup.base
            P.finiteFactorSet P.finiteFactorSet_isNormalized x) :=
  rfl

@[simp]
theorem finiteFactorCentralExtensionRepresentation_apply_vector
    (P : ProjectiveRepresentation K G V)
    (x : P.FiniteFactorCentralExtensionGroup) (v : V) :
    P.finiteFactorCentralExtensionRepresentation x v =
      ((((FactorSet.CentralExtensionGroup.coefficient
          P.finiteFactorSet P.finiteFactorSet_isNormalized x :
            rootsOfUnity (Module.finrank K V) K) : Kˣ) : K) •
        P.finiteFactorNormalize.operator
          (FactorSet.CentralExtensionGroup.base
            P.finiteFactorSet P.finiteFactorSet_isNormalized x) v) :=
  rfl

@[simp]
theorem finiteFactorCentralExtensionLinearAction_apply_baseLift
    (P : ProjectiveRepresentation K G V) (g : G) :
    P.finiteFactorCentralExtensionLinearAction
        (FactorSet.CentralExtensionGroup.mk
          P.finiteFactorSet P.finiteFactorSet_isNormalized g 1) =
      P.finiteFactorNormalize.operator g := by
  exact P.finiteFactorNormalize.centralExtensionLinearAction_apply_baseLift
    P.finiteFactorSet P.finiteFactorSet_isNormalized
    (rootsOfUnity (Module.finrank K V) K).subtype
    P.finiteFactorSet_coe g

@[simp]
theorem finiteFactorCentralExtensionLinearAction_apply_coefficientEmbedding
    (P : ProjectiveRepresentation K G V)
    (a : rootsOfUnity (Module.finrank K V) K) :
    P.finiteFactorCentralExtensionLinearAction
        (FactorSet.CentralExtensionGroup.coefficientEmbedding
          P.finiteFactorSet P.finiteFactorSet_isNormalized a) =
      scalarLinearEquiv K V (a : Kˣ) := by
  exact
    P.finiteFactorNormalize.centralExtensionLinearAction_apply_coefficientEmbedding
      P.finiteFactorSet P.finiteFactorSet_isNormalized
      (rootsOfUnity (Module.finrank K V) K).subtype
      P.finiteFactorSet_coe a

end FiniteFactor

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
