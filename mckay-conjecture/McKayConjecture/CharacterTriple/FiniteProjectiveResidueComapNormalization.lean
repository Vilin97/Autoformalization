/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FiniteProjectiveResidueLinearAction
import McKayConjecture.CharacterTriple.FiniteProjectiveResidueNormalizerLift

/-!
# Normalizing a projective residue action along a trivial homomorphism

If a group homomorphism into the indexing group of a projective residue
representation is trivial, the restricted projective action has a canonical
constant-one honest linearization.  Its constant-one scalar correction is
conjugation-stable, hence every ambient projective operator normalizes the
honest action.

The resulting action is faithful exactly when its acting group is trivial.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

variable {K G V R : Type}
variable [Field K] [Group G] [Group R]
variable [AddCommGroup V] [Module K V]

/-- A trivial restricted homomorphism has a conjugation-stable constant-one
scalar correction as soon as the ambient factor is one on the right at the
identity. -/
theorem scalarCorrectionIsConjugationStable_constOne_of_hom_eq_one
    (Q : ProjectiveRepresentation K G V)
    (hfactor_right : ∀ g : G, Q.factor g 1 = 1)
    (i : R →* G)
    (hi : i = 1) :
    Q.ScalarCorrectionIsConjugationStable i (fun _ ↦ 1) := by
  intro g r
  refine ⟨r, ?_, ?_⟩
  · rw [hi]
    simp
  · rw [hi]
    simp only [MonoidHom.one_apply]
    simp [operatorConjugationFactor, hfactor_right]

variable {G₀ V₀ ι R₀ : Type}
variable [Group G₀] [Finite G₀] [Group R₀] [Finite R₀]
variable [AddCommGroup V₀] [Module ℂ V₀]
variable [Module.Finite ℂ V₀] [Nontrivial V₀] [Finite ι]

private instance residueComapNormalizationFinrankNeZero :
    NeZero (Module.finrank ℂ V₀) :=
  ⟨Module.finrank_pos.ne'⟩

/-- The finite residue factor is one on the right at the identity, directly
from normalization of the finite-root factor.  This remains true even if the
quotient module itself is zero. -/
theorem residueFieldProjectiveRepresentation_factor_right_one
    (P : ProjectiveRepresentation ℂ G₀ V₀)
    (b : Module.Basis ι ℂ V₀)
    (q₀ : ℕ) [Fact q₀.Prime]
    (g : G₀) :
    (P.residueFieldProjectiveRepresentation b q₀
      ).factor g 1 = 1 := by
  rw [P.residueFieldProjectiveRepresentation_factor b q₀]
  rw [P.finiteFactorSet_isNormalized.2 g]
  exact map_one _

/-- An honest action on a projective residue lattice together with the exact
rescaling and ambient-normalization witnesses needed by the interior
normalizer construction. -/
structure ResidueFieldComapLinearActionNormalization
    (P : ProjectiveRepresentation ℂ G₀ V₀)
    (b : Module.Basis ι ℂ V₀)
    (q₀ : ℕ) [Fact q₀.Prime]
    (i : R₀ →* G₀) where
  /-- Scalar correction applied to the restricted projective operators. -/
  correction :
    R₀ →
      (FiniteRootCoefficientRing.ResidueFieldAbovePrime
        q₀ (Module.finrank ℂ V₀))ˣ
  /-- The resulting honest linear action. -/
  action :
    R₀ →*
      (P.residueFieldLattice b q₀ ≃ₗ[
        FiniteRootCoefficientRing.ResidueFieldAbovePrime
          q₀ (Module.finrank ℂ V₀)]
        P.residueFieldLattice b q₀)
  /-- The honest action is the stated scalar rescaling. -/
  action_eq :
    ∀ r : R₀,
      action r =
        scalarLinearEquiv
            (FiniteRootCoefficientRing.ResidueFieldAbovePrime
              q₀ (Module.finrank ℂ V₀))
            (P.residueFieldLattice b q₀)
            (correction r) *
          (P.residueFieldProjectiveRepresentation b q₀
            ).operator (i r)
  /-- The correction is equivariant under ambient projective conjugation. -/
  conjugationStable :
    (P.residueFieldProjectiveRepresentation b q₀
      ).ScalarCorrectionIsConjugationStable i correction
  /-- Every ambient projective operator normalizes the honest action. -/
  pointwiseNormalizes :
    (P.residueFieldProjectiveRepresentation b q₀
      ).PointwiseNormalizesLinearAction action

omit [Finite R₀] in
/-- Along a trivial homomorphism, the residue projective action has the
canonical constant-one honest action, and its scalar correction is stable
under all ambient projective operators. -/
def residueFieldConstOneLinearActionNormalization
    (P : ProjectiveRepresentation ℂ G₀ V₀)
    (b : Module.Basis ι ℂ V₀)
    (q₀ : ℕ) [Fact q₀.Prime]
    (i : R₀ →* G₀)
    (hi : i = 1) :
    ResidueFieldComapLinearActionNormalization P b q₀ i := by
  let d :
      R₀ →
        (FiniteRootCoefficientRing.ResidueFieldAbovePrime
          q₀ (Module.finrank ℂ V₀))ˣ :=
    fun _ ↦ 1
  let rho :
      R₀ →*
        (P.residueFieldLattice b q₀ ≃ₗ[
          FiniteRootCoefficientRing.ResidueFieldAbovePrime
            q₀ (Module.finrank ℂ V₀)]
          P.residueFieldLattice b q₀) :=
    1
  have hstable :
      (P.residueFieldProjectiveRepresentation b q₀
        ).ScalarCorrectionIsConjugationStable i d := by
    exact
      scalarCorrectionIsConjugationStable_constOne_of_hom_eq_one
        (P.residueFieldProjectiveRepresentation b q₀)
        (P.residueFieldProjectiveRepresentation_factor_right_one
          b q₀)
        i hi
  refine
    { correction := d
      action := rho
      action_eq := ?_
      conjugationStable := hstable
      pointwiseNormalizes := ?_ }
  · intro r
    dsimp only [d, rho]
    rw [hi]
    simp only [MonoidHom.one_apply, scalarLinearEquiv_one, one_mul]
    exact
      (P.residueFieldProjectiveRepresentation_isNormalized
        b q₀).symm
  · exact
      (P.residueFieldProjectiveRepresentation b q₀
        ).pointwiseNormalizes_rescaledComapLinearAction
          (P.residueFieldProjectiveRepresentation_isNormalized b q₀)
          i d rho
          (by
            intro r
            dsimp only [d, rho]
            rw [hi]
            simp only [MonoidHom.one_apply, scalarLinearEquiv_one,
              one_mul]
            exact
              (P.residueFieldProjectiveRepresentation_isNormalized
                b q₀).symm)
          hstable

omit [Finite R₀] in
/-- The constant-one normalization is faithful exactly when its acting group
is trivial.  This is the precise obstruction to using it as the faithful
interior action of a nontrivial Dade algebra. -/
theorem residueFieldConstOneLinearActionNormalization_action_injective_iff
    (P : ProjectiveRepresentation ℂ G₀ V₀)
    (b : Module.Basis ι ℂ V₀)
    (q₀ : ℕ) [Fact q₀.Prime]
    (i : R₀ →* G₀)
    (hi : i = 1) :
    Function.Injective
        (P.residueFieldConstOneLinearActionNormalization
          b q₀ i hi).action ↔
      Subsingleton R₀ := by
  constructor
  · intro hinjective
    constructor
    intro r s
    apply hinjective
    rfl
  · intro hsubsingleton r s _hrs
    exact hsubsingleton.elim r s

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
