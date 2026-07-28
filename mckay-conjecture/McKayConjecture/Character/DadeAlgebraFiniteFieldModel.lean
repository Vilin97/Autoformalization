/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeAlgebra
import McKayConjecture.Character.EndomorphismInteriorAction
import McKayConjecture.Character.FiniteFieldCentralSimpleSplitting
import McKayConjecture.CharacterTriple.FiniteFieldEndomorphismActionLift

/-!
# Finite-field endomorphism models of Dade algebras

A central simple algebra over a finite field is a full endomorphism
algebra.  This file chooses such a model, transports the algebra action
to it, and applies the finite-field lifting theorem to obtain an honest
linear action inducing the transported action on endomorphisms.
-/

noncomputable section

namespace Representation

variable {p : ℕ} [Fact p.Prime]
variable {k P A : Type}
variable [Field k] [Finite k] [CharP k p]
variable [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

namespace DadeAlgebra

/-- A chosen realization of an algebra as the full endomorphism algebra
of a nonzero finite-dimensional vector space. -/
structure FiniteFieldModel (k A : Type)
    [Field k] [Ring A] [Algebra k A] where
  /-- Dimension of the splitting module. -/
  dimension : ℕ
  /-- Central simplicity excludes the zero-dimensional matrix algebra. -/
  dimension_neZero : NeZero dimension
  /-- The chosen splitting isomorphism. -/
  algEquiv :
    A ≃ₐ[k] Module.End k (Fin dimension → k)

namespace FiniteFieldModel

variable {k A : Type}
variable [Field k] [Ring A] [Algebra k A]

/-- The splitting module attached to a finite-field model. -/
abbrev ModuleSpace (M : FiniteFieldModel k A) :=
  Fin M.dimension → k

instance (M : FiniteFieldModel k A) :
    Nontrivial M.ModuleSpace := by
  letI : NeZero M.dimension := M.dimension_neZero
  infer_instance

instance (M : FiniteFieldModel k A) :
    FiniteDimensional k M.ModuleSpace :=
  inferInstance

end FiniteFieldModel

omit [Fact p.Prime] [CharP k p] [Fintype P]
    [SMulCommClass P k A] in
/-- A Dade algebra over a finite field admits a full-endomorphism-algebra
model. -/
theorem finiteFieldModel_nonempty
    (S : DadeAlgebra p k P A) :
    Nonempty (FiniteFieldModel k A) := by
  letI : Algebra.IsCentral k A := S.isCentral
  letI : IsSimpleRing A := S.isSimple
  letI : FiniteDimensional k A := S.finiteDimensional
  obtain ⟨n, hn, ⟨e⟩⟩ :=
    exists_algEquiv_endomorphism_of_finiteField k A
  exact ⟨
    { dimension := n
      dimension_neZero := hn
      algEquiv := e }⟩

/-- Choose a full-endomorphism-algebra model for a Dade algebra over a
finite field. -/
def finiteFieldModel
    (S : DadeAlgebra p k P A) :
    FiniteFieldModel k A :=
  Classical.choice (finiteFieldModel_nonempty S)

namespace FiniteFieldModel

variable
  (M : FiniteFieldModel k A)

/-- Transport the original algebra action through a finite-field
endomorphism model. -/
def transportedAlgebraAction :
    P →*
      (Module.End k M.ModuleSpace ≃ₐ[k]
        Module.End k M.ModuleSpace) where
  toFun g :=
    M.algEquiv.symm.trans
      ((MulSemiringAction.toAlgEquiv k A g).trans M.algEquiv)
  map_one' := by
    ext f
    simp
  map_mul' g h := by
    ext f
    simp [mul_smul]

omit [Finite k] [Fintype P] in
@[simp]
theorem transportedAlgebraAction_algEquiv
    (g : P) (a : A) :
    M.transportedAlgebraAction g (M.algEquiv a) =
      M.algEquiv (g • a) := by
  simp [transportedAlgebraAction]

/-- The honest linear action supplied by projective lifting and
finite-field coprime linearization. -/
def liftedLinearAction
    (hP : IsPGroup p P) :
    P →* (M.ModuleSpace ≃ₗ[k] M.ModuleSpace) :=
  McKayConjecture.CharacterTriple.EndomorphismAction.linearActionLift
    M.transportedAlgebraAction hP

/-- Conjugation by the lifted linear action is exactly the transported
action on the full endomorphism algebra. -/
theorem transportedAlgebraAction_eq_conjAlgEquiv
    (hP : IsPGroup p P)
    (g : P) :
    M.transportedAlgebraAction g =
      (M.liftedLinearAction hP g).conjAlgEquiv k :=
  McKayConjecture.CharacterTriple.EndomorphismAction.linearActionLift_conjAlgEquiv
    M.transportedAlgebraAction hP g

/-- The splitting isomorphism is equivariant for the original action
and conjugation by the lifted linear action. -/
theorem algEquiv_smul
    (hP : IsPGroup p P)
    (g : P) (a : A) :
    letI :=
      endomorphismConjugationMulSemiringAction
        (M.liftedLinearAction hP)
    g • M.algEquiv a = M.algEquiv (g • a) := by
  let rho := M.liftedLinearAction hP
  letI :=
    endomorphismConjugationMulSemiringAction rho
  change
    (rho g).conjAlgEquiv k (M.algEquiv a) =
      M.algEquiv (g • a)
  rw [← M.transportedAlgebraAction_eq_conjAlgEquiv hP g]
  exact M.transportedAlgebraAction_algEquiv g a

end FiniteFieldModel
end DadeAlgebra
end Representation
