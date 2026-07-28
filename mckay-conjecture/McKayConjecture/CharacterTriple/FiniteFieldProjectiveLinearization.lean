/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FactorSetCoprimeSplitting
import McKayConjecture.CharacterTriple.FiniteFieldPGroupCoprime
import McKayConjecture.CharacterTriple.ProjectiveRepresentation

/-!
# Linearizing projective representations of p-groups over finite fields

Over a finite field `K` of characteristic `p`, the scalar group
`Kˣ` has order prime to every finite `p`-group.  Schur--Zassenhaus
therefore trivializes every normalized factor set.  After first
normalizing and then applying the resulting gauge, a projective
representation becomes an honest linear action.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

universe u v w

variable {p : ℕ} [Fact p.Prime]
variable {K : Type u} {P : Type v} {V : Type w}
variable [Field K] [Finite K] [CharP K p]
variable [Group P] [Finite P]
variable [AddCommGroup V] [Module K V] [Nontrivial V]

omit [Finite K] [Finite P] [Nontrivial V] in
/-- The operators of a factor-one projective representation form an
honest linear action. -/
def factorOneLinearAction
    (Q : ProjectiveRepresentation K P V)
    (hfactor : ∀ g h, Q.factor g h = 1) :
    P →* (V ≃ₗ[K] V) where
  toFun := Q.operator
  map_one' := by
    have h := Q.map_mul 1 1
    simp only [hfactor, map_one, one_mul] at h
    apply mul_left_cancel (a := Q.operator 1)
    simpa using h
  map_mul' g h := by
    have hmul := Q.map_mul g h
    simpa only [hfactor, map_one, one_mul] using hmul.symm

omit [Finite K] [Finite P] [Nontrivial V] in
@[simp]
theorem factorOneLinearAction_apply
    (Q : ProjectiveRepresentation K P V)
    (hfactor : ∀ g h, Q.factor g h = 1)
    (g : P) :
    Q.factorOneLinearAction hfactor g = Q.operator g :=
  rfl

/-- After normalization, a projective representation of a finite
`p`-group over a finite field of characteristic `p` admits a
normalized rescaling whose factor is identically one. -/
theorem exists_normalized_rescale_factor_one
    (Q : ProjectiveRepresentation K P V)
    (hP : IsPGroup p P) :
    ∃ c : P → Kˣ,
      c 1 = 1 ∧
        ∀ g h : P, (Q.normalize.rescale c).factor g h = 1 := by
  have hnormalized :
      Q.normalize.factorSet.IsNormalized :=
    Q.normalize.factorSet_isNormalized
      Q.normalize_isNormalized
  obtain ⟨c, hc_one, hc_gauge⟩ :=
    FactorSet.exists_normalized_gauge_eq_one_of_coprime
      Q.normalize.factorSet
      hnormalized
      (finiteField_units_card_coprime_pGroup
        (K := K) hP)
  refine ⟨c, hc_one, ?_⟩
  intro g h
  have happ :=
    congrArg
      (fun alpha : FactorSet P Kˣ ↦ alpha g h)
      hc_gauge
  simpa only [FactorSet.gauge_apply, FactorSet.one_apply,
    factorSet_apply, rescale_factor] using happ

/-- Honest action obtained by rescaling the normalized projective
representation. -/
theorem exists_linearAction_rescaling_normalize
    (Q : ProjectiveRepresentation K P V)
    (hP : IsPGroup p P) :
    ∃ c : P → Kˣ,
      c 1 = 1 ∧
        ∃ rho : P →* (V ≃ₗ[K] V),
          ∀ g : P,
            rho g =
              scalarLinearEquiv K V (c g) *
                Q.normalize.operator g := by
  obtain ⟨c, hc_one, hfactor⟩ :=
    Q.exists_normalized_rescale_factor_one hP
  let R := Q.normalize.rescale c
  let rho := R.factorOneLinearAction hfactor
  refine ⟨c, hc_one, rho, ?_⟩
  intro g
  rfl

/-- Every projective representation of a finite `p`-group over a
finite field of characteristic `p` can be rescaled directly to an
honest linear action. -/
theorem exists_linearAction_rescaling
    (Q : ProjectiveRepresentation K P V)
    (hP : IsPGroup p P) :
    ∃ d : P → Kˣ,
      ∃ rho : P →* (V ≃ₗ[K] V),
        ∀ g : P,
          rho g =
            scalarLinearEquiv K V (d g) *
              Q.operator g := by
  obtain ⟨c, _hc_one, rho, hrho⟩ :=
    Q.exists_linearAction_rescaling_normalize hP
  refine
    ⟨fun g ↦ c g * (Q.factor 1 1)⁻¹,
      rho, ?_⟩
  intro g
  rw [hrho]
  change
    scalarLinearEquiv K V (c g) *
        (scalarLinearEquiv K V (Q.factor 1 1)⁻¹ *
          Q.operator g) =
      scalarLinearEquiv K V
          (c g * (Q.factor 1 1)⁻¹) *
        Q.operator g
  rw [← mul_assoc, ← scalarLinearEquiv_mul]

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
