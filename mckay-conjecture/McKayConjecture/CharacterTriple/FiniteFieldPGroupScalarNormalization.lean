/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.FiniteFieldEndomorphismActionUniqueness
import McKayConjecture.CharacterTriple.FiniteProjectiveResidueComapNormalization

/-!
# Scalar normalizations of finite-field `p`-group actions

Let a projective complex representation be reduced on its canonical
cyclotomic lattice at a prime `p`.  If its reduced operators are the
identity along a finite `p`-group, then every honest action obtained by
scalar correction along that restriction is trivial.

The correction function is not assumed to be a homomorphism.  Honesty of
the resulting action and injectivity of scalar automorphisms on a nonzero
module force it to be a character into the finite residue-field unit group.
Such a character of a finite `p`-group is trivial.  If the residue module is
zero, the conclusion is immediate.

This gives a reusable no-go criterion: a faithful Dade interior action
cannot be extracted by scalar-normalizing a projective restriction whose
reduced operators are already trivial.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

open Representation

variable {G V ι R : Type}
variable [Group G] [Finite G]
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable [Finite ι]
variable [Group R] [Finite R]
variable {p : ℕ} [Fact p.Prime]

private instance finiteFieldPGroupScalarNormalizationFinrankNeZero :
    NeZero (Module.finrank ℂ V) :=
  ⟨Module.finrank_pos.ne'⟩

variable
  (P : ProjectiveRepresentation ℂ G V)
  (b : Module.Basis ι ℂ V)
  (i : R →* G)

omit [Finite G] in
/-- If a chosen complex operator agrees with the identity operator, its
determinant-normalized finite-factor operator is the identity as well.

The point is that determinant normalization applies the same scalar to
equal operators, while the final global normalization makes the operator
at `1` exactly one. -/
theorem finiteFactorNormalize_operator_eq_one_of_operator_eq_one
    (hP : P.IsNormalized)
    {g : G}
    (hg : P.operator g = 1) :
    P.finiteFactorNormalize.operator g = 1 := by
  have hg_one : P.operator g = P.operator 1 := by
    rw [hg, hP]
  have hrescale :
      P.determinantRescaling g =
        P.determinantRescaling 1 := by
    simp only [determinantRescaling, hg_one]
  have hop :
      P.finiteFactorNormalize.operator g =
        P.finiteFactorNormalize.operator 1 := by
    simp only [
      finiteFactorNormalize, determinantNormalize, normalize,
      rescale_operator, hrescale, hg_one]
  exact hop.trans P.finiteFactorNormalize_isNormalized

/-- Identity of a complex chosen operator descends to identity on the
canonical residue lattice. -/
theorem residueFieldProjectiveRepresentation_operator_eq_one_of_operator_eq_one
    (hP : P.IsNormalized)
    {g : G}
    (hg : P.operator g = 1) :
    (P.residueFieldProjectiveRepresentation b p).operator g = 1 := by
  have hfinite :
      P.finiteFactorNormalize.operator g = 1 :=
    P.finiteFactorNormalize_operator_eq_one_of_operator_eq_one hP hg
  have hintegral :
      P.integralLatticeEndomorphism b g = 1 := by
    ext x
    change P.finiteFactorNormalize.operator g (x : V) = x
    rw [hfinite]
    rfl
  apply LinearEquiv.ext
  intro z
  obtain ⟨x, rfl⟩ :=
    Submodule.mkQ_surjective
      ((FiniteRootCoefficientRing.maximalIdealAbovePrime
          p (Module.finrank ℂ V)) •
        (⊤ :
          Submodule
            (FiniteRootCoefficientRing (Module.finrank ℂ V))
            (P.integralLattice b)))
      z
  change
    P.residueLatticeAutomorphism b
        (FiniteRootCoefficientRing.maximalIdealAbovePrime
          p (Module.finrank ℂ V)) g
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x
  rw [P.residueLatticeAutomorphism_mk]
  rw [hintegral]
  rfl

omit [Finite R] in
/-- If the complex operators are identity along a restriction, so are all
operators of the canonical residue representation. -/
theorem residueFieldProjectiveRepresentation_comap_operator_eq_one
    (hP : P.IsNormalized)
    (hoperator : ∀ r : R, P.operator (i r) = 1)
    (r : R) :
    (P.residueFieldProjectiveRepresentation b p).operator (i r) = 1 :=
  P.residueFieldProjectiveRepresentation_operator_eq_one_of_operator_eq_one
    b (p := p) hP (hoperator r)

/-- Every honest scalar normalization of an operator-trivial residue
restriction of a finite `p`-group is the trivial linear action.

No homomorphism law is required of `d.correction`; it follows from the
homomorphism law for `d.action` whenever the residue module is nonzero. -/
theorem ResidueFieldComapLinearActionNormalization.action_eq_one_of_isPGroup
    (hR : IsPGroup p R)
    (d : ResidueFieldComapLinearActionNormalization P b p i)
    (hoperator :
      ∀ r : R,
        (P.residueFieldProjectiveRepresentation b p).operator
            (i r) =
          1) :
    d.action = 1 := by
  let k :=
    FiniteRootCoefficientRing.ResidueFieldAbovePrime
      p (Module.finrank ℂ V)
  let M := P.residueFieldLattice b p
  have hactionScalar :
      ∀ r : R,
        d.action r =
          scalarLinearEquiv k M (d.correction r) := by
    intro r
    rw [d.action_eq r, hoperator r, mul_one]
  cases subsingleton_or_nontrivial M with
  | inl hM =>
      apply MonoidHom.ext
      intro r
      apply LinearEquiv.ext
      intro x
      exact hM.elim _ _
  | inr hM =>
      letI : Nontrivial M := hM
      let correctionCharacter : R →* kˣ :=
        { toFun := d.correction
          map_one' := by
            apply scalarLinearEquiv_injective k M
            calc
              scalarLinearEquiv k M (d.correction 1) =
                  d.action 1 :=
                (hactionScalar 1).symm
              _ = 1 := map_one d.action
              _ = scalarLinearEquiv k M 1 :=
                (map_one (scalarLinearEquiv k M)).symm
          map_mul' := by
            intro r s
            apply scalarLinearEquiv_injective k M
            calc
              scalarLinearEquiv k M (d.correction (r * s)) =
                  d.action (r * s) :=
                (hactionScalar (r * s)).symm
              _ = d.action r * d.action s :=
                d.action.map_mul r s
              _ =
                  scalarLinearEquiv k M (d.correction r) *
                    scalarLinearEquiv k M (d.correction s) := by
                rw [hactionScalar r, hactionScalar s]
              _ =
                  scalarLinearEquiv k M
                    (d.correction r * d.correction s) :=
                (scalarLinearEquiv_mul
                  (K := k) (V := M)
                  (d.correction r) (d.correction s)).symm }
      have hcharacter :
          correctionCharacter = 1 :=
        finiteFieldUnitsCharacter_eq_one hR correctionCharacter
      apply MonoidHom.ext
      intro r
      have hr : d.correction r = 1 := by
        exact DFunLike.congr_fun hcharacter r
      calc
        d.action r =
            scalarLinearEquiv k M (d.correction r) :=
          hactionScalar r
        _ = scalarLinearEquiv k M 1 := by rw [hr]
        _ = 1 := map_one (scalarLinearEquiv k M)
        _ = (1 : R →* (M ≃ₗ[k] M)) r := rfl

/-- Under the same operator-triviality hypothesis, a scalar-normalized
action is faithful exactly when the acting `p`-group is trivial. -/
theorem
    ResidueFieldComapLinearActionNormalization.action_injective_iff_subsingleton
    (hR : IsPGroup p R)
    (d : ResidueFieldComapLinearActionNormalization P b p i)
    (hoperator :
      ∀ r : R,
        (P.residueFieldProjectiveRepresentation b p).operator
            (i r) =
          1) :
    Function.Injective d.action ↔ Subsingleton R := by
  have haction :
      d.action = 1 :=
    ResidueFieldComapLinearActionNormalization.action_eq_one_of_isPGroup
      (P := P) (b := b) (i := i) hR d hoperator
  constructor
  · intro hinjective
    constructor
    intro r s
    apply hinjective
    rw [haction]
    rfl
  · intro hRsub r s _hrs
    exact hRsub.elim r s

/-- Complex operator-triviality is a sufficient input for the general
finite-field scalar-normalization no-go theorem. -/
theorem
    ResidueFieldComapLinearActionNormalization.action_eq_one_of_complex_operator_eq_one
    (hP : P.IsNormalized)
    (hR : IsPGroup p R)
    (d : ResidueFieldComapLinearActionNormalization P b p i)
    (hoperator : ∀ r : R, P.operator (i r) = 1) :
    d.action = 1 := by
  exact
    ResidueFieldComapLinearActionNormalization.action_eq_one_of_isPGroup
      (P := P) (b := b) (i := i) hR d
      (P.residueFieldProjectiveRepresentation_comap_operator_eq_one
        b (p := p) i hP hoperator)

/-- Faithfulness form of the complex operator-triviality criterion. -/
theorem
    ResidueFieldComapLinearActionNormalization.action_injective_iff_subsingleton_of_complex
    (hP : P.IsNormalized)
    (hR : IsPGroup p R)
    (d : ResidueFieldComapLinearActionNormalization P b p i)
    (hoperator : ∀ r : R, P.operator (i r) = 1) :
    Function.Injective d.action ↔ Subsingleton R := by
  exact
    ResidueFieldComapLinearActionNormalization.action_injective_iff_subsingleton
      (P := P) (b := b) (i := i) hR d
      (P.residueFieldProjectiveRepresentation_comap_operator_eq_one
        b (p := p) i hP hoperator)

/-- A compact reusable formulation of the no-go boundary: every faithful
scalar normalization forces the acting group to be trivial. -/
def OnlyTrivialGroupHasFaithfulResidueScalarNormalization : Prop :=
  ∀ d : ResidueFieldComapLinearActionNormalization P b p i,
    Function.Injective d.action →
      Subsingleton R

/-- A normalized projective restriction with identity complex operators
satisfies the compact no-go predicate after residue reduction. -/
theorem
    onlyTrivialGroupHasFaithfulResidueScalarNormalization_of_operator_eq_one
    (hP : P.IsNormalized)
    (hR : IsPGroup p R)
    (hoperator : ∀ r : R, P.operator (i r) = 1) :
    OnlyTrivialGroupHasFaithfulResidueScalarNormalization
      (p := p) P b i := by
  intro d hd
  exact
    (ResidueFieldComapLinearActionNormalization.action_injective_iff_subsingleton_of_complex
      (P := P) (b := b) (i := i)
      hP hR d hoperator).1 hd

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
