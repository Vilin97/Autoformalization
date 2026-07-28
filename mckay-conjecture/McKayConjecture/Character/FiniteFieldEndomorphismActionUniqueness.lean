/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.EndomorphismConjugationImplementer
import McKayConjecture.Character.EndomorphismInteriorAction
import McKayConjecture.CharacterTriple.FiniteFieldEndomorphismActionLift

/-!
# Uniqueness of finite-field lifts of `p`-group actions

Two linear actions inducing the same conjugation action on a full
endomorphism algebra differ by a linear character into the coefficient
field's unit group.  Over a finite field of characteristic `p`, every
such character of a finite `p`-group is trivial.  Consequently the
linear lift of an endomorphism-algebra action is unique.

This is the uniqueness assertion in the elementary finite-field
implementer lemma used for Dade algebras.
-/

noncomputable section

namespace Representation

open McKayConjecture.CharacterTriple

variable {p : ℕ} [Fact p.Prime]
variable {k P V : Type}
variable [Field k] [Finite k] [CharP k p]
variable [Group P] [Finite P]
variable [AddCommGroup V] [Module k V]
variable [Nontrivial V]

/-- A multiplicative character from a finite `p`-group to the units of
a finite field of characteristic `p` is trivial. -/
theorem finiteFieldUnitsCharacter_eq_one
    (hP : IsPGroup p P)
    (χ : P →* kˣ) :
    χ = 1 := by
  apply MonoidHom.ext
  intro g
  exact orderOf_eq_one_iff.mp <|
    Nat.eq_one_of_dvd_coprimes
      (finiteField_units_card_coprime_pGroup
        (K := k) hP)
      (orderOf_dvd_natCard (χ g))
      ((orderOf_map_dvd χ g).trans
        (orderOf_dvd_natCard g))

/-- Unit-valued lifts of the same conjugation action are equal over a
finite field when the acting group is a `p`-group. -/
theorem unitAction_eq_of_conjugation_eq
    (hP : IsPGroup p P)
    (σ τ : P →* (Module.End k V)ˣ)
    (hconj :
      ∀ (g : P) (f : Module.End k V),
        (σ g : Module.End k V) * f *
              (↑((σ g)⁻¹) : Module.End k V) =
          (τ g : Module.End k V) * f *
              (↑((τ g)⁻¹) : Module.End k V)) :
    σ = τ := by
  obtain ⟨χ, hχ, _⟩ :=
    exists_unique_scalarCharacter_of_conjugation_eq
      σ τ hconj
  have hχ_one :
      χ = 1 :=
    finiteFieldUnitsCharacter_eq_one hP χ
  apply MonoidHom.ext
  intro g
  have hχg : χ g = 1 := by
    rw [hχ_one]
    rfl
  calc
    σ g =
        τ g *
          endomorphismScalarUnit (V := V) (χ g) :=
      hχ g
    _ = τ g := by
      rw [hχg, map_one, mul_one]

/-- Linear actions of a finite `p`-group over a finite field are equal
when they induce the same conjugation action on the full endomorphism
algebra. -/
theorem linearAction_eq_of_conjAlgEquiv_eq
    (hP : IsPGroup p P)
    (σ τ : P →* (V ≃ₗ[k] V))
    (hconj :
      ∀ g : P,
        (σ g).conjAlgEquiv k =
          (τ g).conjAlgEquiv k) :
    σ = τ := by
  apply MonoidHom.ext
  intro g
  have hunit :
      linearActionUnit σ =
        linearActionUnit τ := by
    apply unitAction_eq_of_conjugation_eq hP
    intro x f
    have hx :=
      DFunLike.congr_fun (hconj x) f
    ext v
    have hxv :=
      DFunLike.congr_fun hx v
    change
      σ x (f ((σ x).symm v)) =
        τ x (f ((τ x).symm v))
    simpa using hxv
  have hg :=
    congrArg
      (fun ρ : P →* (Module.End k V)ˣ =>
        LinearMap.GeneralLinearGroup.generalLinearEquiv k V (ρ g))
      hunit
  simpa only [generalLinearEquiv_linearActionUnit] using hg

end Representation

namespace McKayConjecture
namespace CharacterTriple
namespace EndomorphismAction

variable {p : ℕ} [Fact p.Prime]
variable {K P V : Type}
variable [Field K] [Finite K] [CharP K p]
variable [Group P] [Finite P]
variable [AddCommGroup V] [Module K V] [Nontrivial V]

/-- An action of a finite `p`-group on a full endomorphism algebra over
a finite field has a unique honest linear lift. -/
theorem existsUnique_linearAction_lift
    (alpha : P →* AlgAut (K := K) (V := V))
    (hP : IsPGroup p P) :
    ∃! rho : P →* (V ≃ₗ[K] V),
      ∀ g : P,
        alpha g = (rho g).conjAlgEquiv K := by
  refine ⟨linearActionLift alpha hP,
    linearActionLift_conjAlgEquiv alpha hP, ?_⟩
  intro rho hrho
  apply Representation.linearAction_eq_of_conjAlgEquiv_eq hP
  intro g
  exact
    (hrho g).symm.trans
      (linearActionLift_conjAlgEquiv alpha hP g)

end EndomorphismAction
end CharacterTriple
end McKayConjecture
