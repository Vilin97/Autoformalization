/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.EndomorphismActionProjectiveLift
import McKayConjecture.CharacterTriple.FiniteFieldProjectiveLinearization

/-!
# Linear lifts of endomorphism-algebra actions over finite fields

An action of a finite `p`-group on a full endomorphism algebra first
lifts projectively by Skolem--Noether.  Over a finite field of
characteristic `p`, the projective factor can be removed by scalar
rescaling.  Scalar rescaling does not change conjugation, so the
resulting honest linear action induces the original algebra action.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace EndomorphismAction

universe u v w

variable {p : ℕ} [Fact p.Prime]
variable {K : Type u} {P : Type v} {V : Type w}
variable [Field K] [Finite K] [CharP K p]
variable [Group P] [Finite P]
variable [AddCommGroup V] [Module K V] [Nontrivial V]

omit [Finite K] [Finite P] [Nontrivial V] in
/-- Multiplying a linear automorphism by a nonzero scalar does not
change its conjugation action on the endomorphism algebra. -/
theorem scalarLinearEquiv_mul_conjAlgEquiv
    (a : Kˣ) (f : V ≃ₗ[K] V) :
    (scalarLinearEquiv K V a * f).conjAlgEquiv K =
      f.conjAlgEquiv K := by
  apply
    (LinearEquiv.conjAlgEquiv_ext_iff'
      (scalarLinearEquiv K V a * f) f).2
  refine ⟨a, ?_⟩
  ext v
  rfl

/-- Every action of a finite `p`-group on a full endomorphism algebra
over a finite field of characteristic `p` is induced by an honest
linear action. -/
theorem exists_linearAction_lift
    (alpha : P →* AlgAut (K := K) (V := V))
    (hP : IsPGroup p P) :
    ∃ rho : P →* (V ≃ₗ[K] V),
      ∀ g : P,
        alpha g = (rho g).conjAlgEquiv K := by
  obtain ⟨d, rho, hrho⟩ :=
    (projectiveLift alpha).exists_linearAction_rescaling hP
  refine ⟨rho, ?_⟩
  intro g
  rw [hrho]
  rw [scalarLinearEquiv_mul_conjAlgEquiv]
  exact projectiveLift_operator_conjAlgEquiv alpha g

/-- A chosen honest linear lift of an endomorphism-algebra action. -/
def linearActionLift
    (alpha : P →* AlgAut (K := K) (V := V))
    (hP : IsPGroup p P) :
    P →* (V ≃ₗ[K] V) :=
  Classical.choose (exists_linearAction_lift alpha hP)

@[simp]
theorem linearActionLift_conjAlgEquiv
    (alpha : P →* AlgAut (K := K) (V := V))
    (hP : IsPGroup p P)
    (g : P) :
    alpha g =
      (linearActionLift alpha hP g).conjAlgEquiv K :=
  Classical.choose_spec
    (exists_linearAction_lift alpha hP) g

end EndomorphismAction
end CharacterTriple
end McKayConjecture
