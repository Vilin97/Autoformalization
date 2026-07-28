/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FiniteFieldProjectiveLinearization
import McKayConjecture.CharacterTriple.ProjectivePointwiseNormalizer
import McKayConjecture.CharacterTriple.ProjectiveRestriction

/-!
# Self-normalization of a linearized projective action

A linear action obtained by scalar-rescaling the operators of a projective
representation is normalized by those original operators.  Indeed, each
original operator differs from the corresponding honest operator by a
central scalar, so both induce the same conjugation.

For a finite `p`-group over a finite field of characteristic `p`, the
existing projective-linearization theorem therefore supplies not only an
honest action but also exactly the pointwise-normalization witness needed by
an interior-normalizer construction.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

variable {K G V : Type}
variable [Field K] [Group G]
variable [AddCommGroup V] [Module K V]

/-- The scalar introduced by conjugating one chosen projective operator by
another.  For a normalized projective representation it satisfies

`Q(g) Q(x) Q(g)⁻¹ = scalar(operatorConjugationFactor Q g x) Q(g x g⁻¹)`.
-/
def operatorConjugationFactor
    (Q : ProjectiveRepresentation K G V)
    (g x : G) : Kˣ :=
  Q.factor g x * Q.factor (g * x) g⁻¹ *
    (Q.factor g g⁻¹)⁻¹

/-- Conjugation of chosen operators in a normalized projective
representation, with the scalar discrepancy made explicit. -/
theorem operator_mul_operator_mul_inv
    (Q : ProjectiveRepresentation K G V)
    (hQ : Q.IsNormalized)
    (g x : G) :
    Q.operator g * Q.operator x * (Q.operator g)⁻¹ =
      scalarLinearEquiv K V
          (Q.operatorConjugationFactor g x) *
        Q.operator (g * x * g⁻¹) := by
  have hmul_inv :
      Q.operator g * Q.operator g⁻¹ =
        scalarLinearEquiv K V (Q.factor g g⁻¹) := by
    change Q.operator 1 = 1 at hQ
    rw [Q.map_mul g g⁻¹, mul_inv_cancel, hQ, mul_one]
  have hoperator_inv :
      (Q.operator g)⁻¹ =
        Q.operator g⁻¹ *
          (scalarLinearEquiv K V
            (Q.factor g g⁻¹))⁻¹ := by
    rw [← hmul_inv]
    group
  rw [Q.map_mul g x, hoperator_inv]
  calc
    (scalarLinearEquiv K V (Q.factor g x) *
          Q.operator (g * x)) *
          (Q.operator g⁻¹ *
            (scalarLinearEquiv K V
              (Q.factor g g⁻¹))⁻¹) =
        scalarLinearEquiv K V (Q.factor g x) *
          (Q.operator (g * x) * Q.operator g⁻¹) *
          (scalarLinearEquiv K V
            (Q.factor g g⁻¹))⁻¹ := by
              group
    _ =
        scalarLinearEquiv K V (Q.factor g x) *
          (scalarLinearEquiv K V
              (Q.factor (g * x) g⁻¹) *
            Q.operator (g * x * g⁻¹)) *
          (scalarLinearEquiv K V
            (Q.factor g g⁻¹))⁻¹ := by
              rw [Q.map_mul (g * x) g⁻¹]
    _ =
        scalarLinearEquiv K V
            (Q.operatorConjugationFactor g x) *
          Q.operator (g * x * g⁻¹) := by
      rw [← map_inv]
      calc
        scalarLinearEquiv K V (Q.factor g x) *
              (scalarLinearEquiv K V
                  (Q.factor (g * x) g⁻¹) *
                Q.operator (g * x * g⁻¹)) *
              scalarLinearEquiv K V
                (Q.factor g g⁻¹)⁻¹ =
            scalarLinearEquiv K V (Q.factor g x) *
              scalarLinearEquiv K V
                (Q.factor (g * x) g⁻¹) *
              (Q.operator (g * x * g⁻¹) *
                scalarLinearEquiv K V
                  (Q.factor g g⁻¹)⁻¹) := by
                    group
        _ =
            scalarLinearEquiv K V (Q.factor g x) *
              scalarLinearEquiv K V
                (Q.factor (g * x) g⁻¹) *
              (scalarLinearEquiv K V
                  (Q.factor g g⁻¹)⁻¹ *
                Q.operator (g * x * g⁻¹)) := by
                  rw [scalarLinearEquiv_comm K V
                    (Q.factor g g⁻¹)⁻¹
                    (Q.operator (g * x * g⁻¹))]
        _ =
            (scalarLinearEquiv K V (Q.factor g x) *
              scalarLinearEquiv K V
                (Q.factor (g * x) g⁻¹) *
              scalarLinearEquiv K V
                (Q.factor g g⁻¹)⁻¹) *
              Q.operator (g * x * g⁻¹) := by
                  group
        _ =
            scalarLinearEquiv K V
                (Q.operatorConjugationFactor g x) *
              Q.operator (g * x * g⁻¹) := by
                  rw [← scalarLinearEquiv_mul,
                    ← scalarLinearEquiv_mul]
                  rfl

/-- Conjugation by a projective operator agrees with conjugation by any
honest action obtained from it by pointwise scalar rescaling. -/
theorem conjugate_rescaledLinearAction
    (Q : ProjectiveRepresentation K G V)
    (d : G → Kˣ)
    (rho : G →* (V ≃ₗ[K] V))
    (hrho :
      ∀ g : G,
        rho g =
          scalarLinearEquiv K V (d g) * Q.operator g)
    (g x : G) :
    Q.operator g * rho x * (Q.operator g)⁻¹ =
      rho (g * x * g⁻¹) := by
  have hoperator :
      Q.operator g =
        scalarLinearEquiv K V (d g)⁻¹ * rho g := by
    rw [hrho g]
    rw [← mul_assoc, ← scalarLinearEquiv_mul]
    simp
  rw [hoperator]
  calc
    (scalarLinearEquiv K V (d g)⁻¹ * rho g) *
          rho x *
          (scalarLinearEquiv K V (d g)⁻¹ * rho g)⁻¹ =
        scalarLinearEquiv K V (d g)⁻¹ *
          (rho g * rho x * (rho g)⁻¹) *
          (scalarLinearEquiv K V (d g)⁻¹)⁻¹ := by
            group
    _ = rho g * rho x * (rho g)⁻¹ := by
      rw [scalarLinearEquiv_comm K V (d g)⁻¹
        (rho g * rho x * (rho g)⁻¹)]
      simp
    _ = rho (g * x * g⁻¹) := by simp

/-- Any scalar rescaling of a project's operators that is an honest action
is pointwise normalized by the original projective representation. -/
theorem pointwiseNormalizes_rescaledLinearAction
    (Q : ProjectiveRepresentation K G V)
    (d : G → Kˣ)
    (rho : G →* (V ≃ₗ[K] V))
    (hrho :
      ∀ g : G,
        rho g =
          scalarLinearEquiv K V (d g) * Q.operator g) :
    Q.PointwiseNormalizesLinearAction rho := by
  intro g x
  exact ⟨g * x * g⁻¹,
    Q.conjugate_rescaledLinearAction d rho hrho g x⟩

section RestrictedAction

variable {R : Type} [Group R] [Finite R]

/-- The exact equivariance condition on a scalar correction for a projective
action restricted along `i : R → G`.

The first equality says that the image of `R` is closed under conjugation by
`G`.  The second says that the chosen scalar correction absorbs precisely
the projective conjugation factor. -/
def ScalarCorrectionIsConjugationStable
    (Q : ProjectiveRepresentation K G V)
    (i : R →* G)
    (d : R → Kˣ) : Prop :=
  ∀ g r, ∃ r',
    i r' = g * i r * g⁻¹ ∧
      d r' =
        d r * Q.operatorConjugationFactor g (i r)

omit [Finite R] in
/-- A conjugation-stable scalar correction turns a linearization of a
restricted projective action into an honest action normalized by every
ambient projective operator. -/
theorem pointwiseNormalizes_rescaledComapLinearAction
    (Q : ProjectiveRepresentation K G V)
    (hQ : Q.IsNormalized)
    (i : R →* G)
    (d : R → Kˣ)
    (rho : R →* (V ≃ₗ[K] V))
    (hrho :
      ∀ r : R,
        rho r =
          scalarLinearEquiv K V (d r) *
            Q.operator (i r))
    (hstable :
      ScalarCorrectionIsConjugationStable Q i d) :
    Q.PointwiseNormalizesLinearAction rho := by
  intro g r
  obtain ⟨r', hi, hd⟩ := hstable g r
  refine ⟨r', ?_⟩
  rw [hrho r, hrho r']
  calc
    Q.operator g *
          (scalarLinearEquiv K V (d r) *
            Q.operator (i r)) *
          (Q.operator g)⁻¹ =
        scalarLinearEquiv K V (d r) *
          (Q.operator g * Q.operator (i r) *
            (Q.operator g)⁻¹) := by
              calc
                Q.operator g *
                      (scalarLinearEquiv K V (d r) *
                        Q.operator (i r)) *
                      (Q.operator g)⁻¹ =
                    (Q.operator g *
                      scalarLinearEquiv K V (d r)) *
                      Q.operator (i r) *
                      (Q.operator g)⁻¹ := by
                        group
                _ =
                    (scalarLinearEquiv K V (d r) *
                      Q.operator g) *
                      Q.operator (i r) *
                      (Q.operator g)⁻¹ := by
                        rw [← scalarLinearEquiv_comm K V (d r)
                          (Q.operator g)]
                _ =
                    scalarLinearEquiv K V (d r) *
                      (Q.operator g * Q.operator (i r) *
                        (Q.operator g)⁻¹) := by
                          group
    _ =
        scalarLinearEquiv K V (d r) *
          (scalarLinearEquiv K V
              (Q.operatorConjugationFactor g (i r)) *
            Q.operator (g * i r * g⁻¹)) := by
              rw [Q.operator_mul_operator_mul_inv hQ]
    _ =
        scalarLinearEquiv K V
            (d r *
              Q.operatorConjugationFactor g (i r)) *
          Q.operator (g * i r * g⁻¹) := by
            rw [scalarLinearEquiv_mul]
            exact (mul_assoc _ _ _).symm
    _ =
        scalarLinearEquiv K V (d r') *
          Q.operator (i r') := by
            rw [hd, hi]

end RestrictedAction

variable {p : ℕ} [Fact p.Prime]
variable [Finite K] [CharP K p]
variable [Finite G]

/-- A projective representation of a finite `p`-group over a finite field of
characteristic `p` admits an honest scalar-rescaling which is pointwise
normalized by the original projective operators.

No nontriviality assumption on the representation space is needed: on the
zero space the unique action works, while on a nonzero space finite-field
projective linearization applies. -/
theorem exists_linearAction_rescaling_pointwiseNormalizer
    (Q : ProjectiveRepresentation K G V)
    (hG : IsPGroup p G) :
    ∃ d : G → Kˣ,
      ∃ rho : G →* (V ≃ₗ[K] V),
        (∀ g : G,
          rho g =
            scalarLinearEquiv K V (d g) * Q.operator g) ∧
          Q.PointwiseNormalizesLinearAction rho := by
  cases subsingleton_or_nontrivial V with
  | inl hV =>
      letI : Subsingleton V := hV
      let rho : G →* (V ≃ₗ[K] V) := 1
      refine ⟨fun _ ↦ 1, rho, ?_, ?_⟩
      · intro g
        exact Subsingleton.elim _ _
      · intro g x
        exact ⟨x, Subsingleton.elim _ _⟩
  | inr hV =>
      letI : Nontrivial V := hV
      obtain ⟨d, rho, hrho⟩ :=
        Q.exists_linearAction_rescaling hG
      exact
        ⟨d, rho, hrho,
          Q.pointwiseNormalizes_rescaledLinearAction d rho hrho⟩

section RestrictedPGroup

variable {R : Type} [Group R] [Finite R]

omit [Finite G] in
/-- Restricting a finite-field projective representation to a finite
`p`-group always produces an honest scalar-rescaled action.  Extending its
normalization from the restricted projective action to all ambient operators
is exactly the `ScalarCorrectionIsConjugationStable` obligation above. -/
theorem exists_comap_linearAction_rescaling
    (Q : ProjectiveRepresentation K G V)
    (i : R →* G)
    (hR : IsPGroup p R) :
    ∃ d : R → Kˣ,
      ∃ rho : R →* (V ≃ₗ[K] V),
        ∀ r : R,
          rho r =
            scalarLinearEquiv K V (d r) *
              Q.operator (i r) := by
  obtain ⟨d, rho, hrho, _hnorm⟩ :=
    (Q.comap i).exists_linearAction_rescaling_pointwiseNormalizer hR
  exact ⟨d, rho, hrho⟩

end RestrictedPGroup

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
