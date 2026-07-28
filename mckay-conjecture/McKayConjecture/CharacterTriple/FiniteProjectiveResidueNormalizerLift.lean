/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FiniteProjectiveResidueFieldRepresentation
import McKayConjecture.CharacterTriple.ProjectivePointwiseNormalizer

/-!
# Residue-field projective operators in an interior normalizer

The integral-lattice quotient gives a normalized projective representation
over the chosen finite residue field.  Given any honest linear action of a
finite group on that quotient module, pointwise normalization of its image by
the quotient projective operators packages those operators as a
`ProjectiveNormalizerLift`.

The bundled lift retains exactly the integral residue factor.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

open Representation

variable {G V ι S : Type}
variable [Group G] [Finite G]
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable [Finite ι]
variable [Group S] [Fintype S]

private instance residueNormalizerFinrankNeZero :
    NeZero (Module.finrank ℂ V) :=
  ⟨Module.finrank_pos.ne'⟩

variable
  (P : ProjectiveRepresentation ℂ G V)
  (b : Module.Basis ι ℂ V)
  (q : ℕ) [Fact q.Prime]

/-- Reduction of a normalized integral-lattice operator remains normalized
on every quotient lattice. -/
@[simp]
theorem residueLatticeAutomorphism_one
    (I :
      Ideal
        (FiniteRootCoefficientRing
          (Module.finrank ℂ V))) :
    P.residueLatticeAutomorphism b I 1 = 1 := by
  ext x
  obtain ⟨x, rfl⟩ :=
    Submodule.mkQ_surjective
      (I •
        (⊤ :
          Submodule
            (FiniteRootCoefficientRing
              (Module.finrank ℂ V))
            (P.integralLattice b)))
      x
  change
    P.residueLatticeAutomorphism b I 1
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x
  rw [P.residueLatticeAutomorphism_mk b I]
  change
    Submodule.Quotient.mk
        (P.integralLatticeEndomorphism b 1 x) =
      Submodule.Quotient.mk x
  rw [P.integralLatticeEndomorphism_one b]
  rfl

/-- The residue-field projective representation has identity operator at
the identity element. -/
@[simp]
theorem residueFieldProjectiveRepresentation_isNormalized :
    (P.residueFieldProjectiveRepresentation b q).IsNormalized :=
  P.residueLatticeAutomorphism_one b
    (FiniteRootCoefficientRing.maximalIdealAbovePrime
      q (Module.finrank ℂ V))

/-- Package the integral-lattice quotient operators as a projective lift in
the normalizer of an honest finite-group action on the residue module.

The only operator-level premise says pointwise that conjugation sends each
implementing operator back into the implementing image. -/
def residueFieldProjectiveNormalizerLift
    (ρ :
      S →*
        (P.residueFieldLattice b q ≃ₗ[FiniteRootCoefficientRing.ResidueFieldAbovePrime
            q (Module.finrank ℂ V)]
          P.residueFieldLattice b q))
    (hnorm :
      PointwiseNormalizesLinearAction
        (P.residueFieldProjectiveRepresentation b q) ρ) :=
  toProjectiveNormalizerLiftOfPointwise
    (P.residueFieldProjectiveRepresentation b q)
    ρ hnorm
    (P.residueFieldProjectiveRepresentation_isNormalized b q)

/-- Pointwise commuting quotient operators give the same residue normalizer
lift without separately supplying a normalization witness. -/
def residueFieldProjectiveNormalizerLiftOfCommutes
    (ρ :
      S →*
        (P.residueFieldLattice b q ≃ₗ[FiniteRootCoefficientRing.ResidueFieldAbovePrime
            q (Module.finrank ℂ V)]
          P.residueFieldLattice b q))
    (hcomm :
      ∀ g s,
        (P.residueFieldProjectiveRepresentation b q).operator g * ρ s =
          ρ s *
            (P.residueFieldProjectiveRepresentation b q).operator g) :=
  toProjectiveNormalizerLiftOfCommutes
    (P.residueFieldProjectiveRepresentation b q)
    ρ hcomm
    (P.residueFieldProjectiveRepresentation_isNormalized b q)

/-- The residue normalizer lift retains exactly the finite-root residue
factor. -/
@[simp]
theorem residueFieldProjectiveNormalizerLift_factor
    (ρ :
      S →*
        (P.residueFieldLattice b q ≃ₗ[FiniteRootCoefficientRing.ResidueFieldAbovePrime
            q (Module.finrank ℂ V)]
          P.residueFieldLattice b q))
    (hnorm :
      PointwiseNormalizesLinearAction
        (P.residueFieldProjectiveRepresentation b q) ρ)
    (g h : G) :
    letI :
        MulAction
          (FiniteRootCoefficientRing.ResidueFieldAbovePrime
            q (Module.finrank ℂ V))
          (P.residueFieldLattice b q) :=
      (inferInstance :
        Module
          (FiniteRootCoefficientRing.ResidueFieldAbovePrime
            q (Module.finrank ℂ V))
          (P.residueFieldLattice b q)).toDistribMulAction.toMulAction
    letI :=
      endomorphismConjugationMulSemiringAction ρ
    letI :=
      endomorphismConjugation_smulCommClass ρ
    (P.residueFieldProjectiveNormalizerLift b q ρ hnorm).factor g h =
      P.finiteFactorResidueReduction
        (FiniteRootCoefficientRing.maximalIdealAbovePrime
          q (Module.finrank ℂ V)) g h := by
  exact
    toProjectiveNormalizerLiftOfPointwise_factor
      (P.residueFieldProjectiveRepresentation b q)
      ρ hnorm
      (P.residueFieldProjectiveRepresentation_isNormalized b q)
      g h

/-- The commuting form of the residue normalizer lift has the same finite-root
residue factor. -/
@[simp]
theorem residueFieldProjectiveNormalizerLiftOfCommutes_factor
    (ρ :
      S →*
        (P.residueFieldLattice b q ≃ₗ[FiniteRootCoefficientRing.ResidueFieldAbovePrime
            q (Module.finrank ℂ V)]
          P.residueFieldLattice b q))
    (hcomm :
      ∀ g s,
        (P.residueFieldProjectiveRepresentation b q).operator g * ρ s =
          ρ s *
            (P.residueFieldProjectiveRepresentation b q).operator g)
    (g h : G) :
    letI :
        MulAction
          (FiniteRootCoefficientRing.ResidueFieldAbovePrime
            q (Module.finrank ℂ V))
          (P.residueFieldLattice b q) :=
      (inferInstance :
        Module
          (FiniteRootCoefficientRing.ResidueFieldAbovePrime
            q (Module.finrank ℂ V))
          (P.residueFieldLattice b q)).toDistribMulAction.toMulAction
    letI :=
      endomorphismConjugationMulSemiringAction ρ
    letI :=
      endomorphismConjugation_smulCommClass ρ
    (P.residueFieldProjectiveNormalizerLiftOfCommutes
        b q ρ hcomm).factor g h =
      P.finiteFactorResidueReduction
        (FiniteRootCoefficientRing.maximalIdealAbovePrime
          q (Module.finrank ℂ V)) g h := by
  exact
    toProjectiveNormalizerLiftOfCommutes_factor
      (P.residueFieldProjectiveRepresentation b q)
      ρ hcomm
      (P.residueFieldProjectiveRepresentation_isNormalized b q)
      g h

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
