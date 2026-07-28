/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FiniteProjectiveResidueReduction

/-!
# A projective representation over a finite residue field

Reducing the integral projective lattice at the chosen maximal ideal
above `q` produces an actual projective representation over a finite
field of characteristic `q`.
-/

noncomputable section

universe u v w

namespace McKayConjecture
namespace CharacterTriple

open Representation

namespace ProjectiveRepresentation

variable {G : Type u} {V : Type v} {ι : Type w}
variable [Group G] [Finite G]
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable [Finite ι]

private instance projectiveFinrankNeZero :
    NeZero (Module.finrank ℂ V) :=
  ⟨Module.finrank_pos.ne'⟩

variable
  (P : ProjectiveRepresentation ℂ G V)
  (b : Module.Basis ι ℂ V)

theorem unitScalarLinearEquiv_eq_scalarLinearEquiv
    {K M : Type*}
    [Field K] [AddCommGroup M] [Module K M]
    (a : Kˣ) :
    unitScalarLinearEquiv a =
      scalarLinearEquiv K M a := by
  ext x
  rfl

/-- The quotient of the integral lattice at the chosen maximal ideal
above `q`. -/
abbrev residueFieldLattice
    (q : ℕ) [Fact q.Prime] :=
  P.residueLattice b
    (FiniteRootCoefficientRing.maximalIdealAbovePrime
      q (Module.finrank ℂ V))

/-- The determinant-normalized complex projective representation,
reduced on its integral lattice at the chosen maximal ideal above
`q`. -/
def residueFieldProjectiveRepresentation
    (q : ℕ) [Fact q.Prime] :
    ProjectiveRepresentation
      (FiniteRootCoefficientRing.ResidueFieldAbovePrime
        q (Module.finrank ℂ V))
      G
      (P.residueFieldLattice b q) where
  operator g :=
    P.residueLatticeAutomorphism b
      (FiniteRootCoefficientRing.maximalIdealAbovePrime
        q (Module.finrank ℂ V)) g
  factor g h :=
    P.finiteFactorResidueReduction
      (FiniteRootCoefficientRing.maximalIdealAbovePrime
        q (Module.finrank ℂ V)) g h
  map_mul g h := by
    rw [P.residueLatticeAutomorphism_mul b
      (FiniteRootCoefficientRing.maximalIdealAbovePrime
        q (Module.finrank ℂ V)) g h]
    rw [unitScalarLinearEquiv_eq_scalarLinearEquiv]

@[simp]
theorem residueFieldProjectiveRepresentation_operator
    (q : ℕ) [Fact q.Prime] (g : G) :
    (P.residueFieldProjectiveRepresentation b q).operator g =
      P.residueLatticeAutomorphism b
        (FiniteRootCoefficientRing.maximalIdealAbovePrime
          q (Module.finrank ℂ V)) g :=
  rfl

@[simp]
theorem residueFieldProjectiveRepresentation_factor
    (q : ℕ) [Fact q.Prime] (g h : G) :
    (P.residueFieldProjectiveRepresentation b q).factor g h =
      FiniteRootCoefficientRing.rootToResidueField
        q (Module.finrank ℂ V)
        (P.finiteFactorSet g h) :=
  rfl

end ProjectiveRepresentation

end CharacterTriple
end McKayConjecture
