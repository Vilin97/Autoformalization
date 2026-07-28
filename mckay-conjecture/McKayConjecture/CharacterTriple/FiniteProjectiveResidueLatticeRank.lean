/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.Algebra.Module.Torsion.Free
import McKayConjecture.CharacterTriple.FiniteProjectiveResidueFieldRepresentation

/-!
# Rank of an integral lattice after residue-field reduction

This file separates the commutative-algebra rank calculation from the
specific integral lattice attached to a finite complex projective
representation.

For an `R`-module `M`, reduction modulo an ideal `I` is canonically the
base change `(R ⧸ I) ⊗[R] M`.  Consequently:

* a finite free module has the same finite rank after reduction modulo
  every proper ideal;
* a finite projective module over a domain has the same generic rank
  after reduction modulo every maximal ideal.

The final section applies this API to `ProjectiveRepresentation.integralLattice`.
The lattice is already known to be finite and full.  Its projectivity
and its expected generic rank are deliberately retained as explicit
hypotheses: neither follows merely from fullness of a finitely generated
submodule of a complex vector space.
-/

noncomputable section

universe u v w

namespace McKayConjecture
namespace CharacterTriple

namespace ResidueModule

variable {R : Type u} {M : Type v}
variable [CommRing R] [AddCommGroup M] [Module R M]

/-- Reduction of an `R`-module modulo an ideal. -/
abbrev Reduction (I : Ideal R) :=
  M ⧸ I • (⊤ : Submodule R M)

/-- Reduction modulo an ideal is extension of scalars to the quotient
ring.  This is the quotient-linear form of
`TensorProduct.quotTensorEquivQuotSMul`. -/
noncomputable def reductionEquivBaseChange
    (I : Ideal R) :
    Reduction (M := M) I ≃ₗ[(R ⧸ I)]
      TensorProduct R (R ⧸ I) M :=
  ((TensorProduct.quotTensorEquivQuotSMul M I).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective).symm

/-- Finite free rank is preserved by reduction modulo a proper ideal.
No domain hypothesis on the coefficient ring is needed. -/
theorem finrank_reduction_eq_of_free
    (I : Ideal R) [Nontrivial R] [Nontrivial (R ⧸ I)]
    [Module.Free R M] [Module.Finite R M] :
    Module.finrank (R ⧸ I) (Reduction (M := M) I) =
      Module.finrank R M := by
  rw [(reductionEquivBaseChange (M := M) I).finrank_eq]
  exact
    Module.finrank_baseChange
      (R := R ⧸ I) (S := R) (M' := M)

section Maximal

variable (I : Ideal R) [I.IsMaximal]

/-- For a maximal ideal, the quotient field is canonically equivalent
to the residue field of the corresponding local ring. -/
noncomputable def quotientEquivResidueField :
    (R ⧸ I) ≃ₐ[R ⧸ I] I.ResidueField :=
  AlgEquiv.ofBijective
    (Algebra.ofId (R ⧸ I) I.ResidueField)
    I.bijective_algebraMap_quotient_residueField

/-- Changing the coefficient factor from `R ⧸ I` to the local residue
field identifies quotient-ring base change with the fiber at `I`.

The target is viewed as an `R ⧸ I`-module through the canonical
isomorphism. -/
noncomputable def baseChangeEquivFiber :
    TensorProduct R (R ⧸ I) M ≃ₗ[(R ⧸ I)] I.Fiber M :=
  TensorProduct.AlgebraTensorModule.congr
    (quotientEquivResidueField I).toLinearEquiv
    (LinearEquiv.refl R M)

theorem finrank_quotient_residueField :
    Module.finrank (R ⧸ I) I.ResidueField = 1 := by
  simpa using
    (quotientEquivResidueField I).toLinearEquiv.finrank_eq.symm

/-- Since `R ⧸ I → I.ResidueField` is an isomorphism for maximal `I`,
restricting scalars along it does not change finite rank. -/
theorem finrank_fiber_restrictScalars :
    Module.finrank (R ⧸ I) (I.Fiber M) =
      Module.finrank I.ResidueField (I.Fiber M) := by
  apply congrArg Cardinal.toNat
  apply rank_eq_of_equiv_equiv
    (quotientEquivResidueField I).toRingEquiv
    (AddEquiv.refl (I.Fiber M))
    (quotientEquivResidueField I).bijective
  intro r x
  rfl

/-- Finite flat modules over a domain preserve their generic rank after
reduction at a maximal ideal.  This is the local-fiber rank formula,
transported from `I.ResidueField` back to the literal quotient `R ⧸ I`. -/
theorem finrank_reduction_eq_of_finite_flat
    [IsDomain R]
    [Module.Flat R M] [Module.Finite R M] :
    Module.finrank (R ⧸ I) (Reduction (M := M) I) =
      Module.finrank R M := by
  calc
    Module.finrank (R ⧸ I) (Reduction (M := M) I) =
        Module.finrank (R ⧸ I) (TensorProduct R (R ⧸ I) M) :=
      (reductionEquivBaseChange (M := M) I).finrank_eq
    _ = Module.finrank (R ⧸ I) (I.Fiber M) :=
      (baseChangeEquivFiber (M := M) I).finrank_eq
    _ = Module.finrank I.ResidueField (I.Fiber M) := by
      exact finrank_fiber_restrictScalars (M := M) I
    _ = Module.finrank R M :=
      I.finrank_fiber_eq_finrank

/-- In particular, a finite projective module over a domain preserves
its generic rank after reduction at a maximal ideal. -/
theorem finrank_reduction_eq_of_projective
    [IsDomain R]
    [Module.Projective R M] [Module.Finite R M] :
    Module.finrank (R ⧸ I) (Reduction (M := M) I) =
      Module.finrank R M :=
  finrank_reduction_eq_of_finite_flat (M := M) I

end Maximal

end ResidueModule

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

/-- The chosen complex basis, regarded as a family inside the canonical
integral lattice. -/
def integralBasisVector (i : ι) :
    P.integralLattice b :=
  ⟨b i, P.basis_mem_integralLattice b i⟩

@[simp]
theorem integralBasisVector_coe (i : ι) :
    (P.integralBasisVector b i : V) = b i :=
  rfl

/-- The complex basis remains linearly independent over the cyclotomic
coefficient ring when regarded as a family in the integral lattice. -/
theorem integralBasisVector_linearIndependent :
    LinearIndependent
      (FiniteRootCoefficientRing (Module.finrank ℂ V))
      (P.integralBasisVector b) := by
  apply LinearIndependent.of_comp
    (P.integralLattice b).subtype
  simpa [integralBasisVector, Function.comp_def] using
    b.linearIndependent.restrict_scalars'
      (FiniteRootCoefficientRing (Module.finrank ℂ V))

omit [Finite G] [Finite ι] in
/-- The canonical integral lattice is torsion-free over its coefficient
ring.  Thus projectivity, not torsion-freeness, is the unresolved module
property in the projective reduction theorem below. -/
theorem integralLattice_isTorsionFree :
    Module.IsTorsionFree
      (FiniteRootCoefficientRing (Module.finrank ℂ V))
      (P.integralLattice b) := by
  letI :
      Module.IsTorsionFree
        (FiniteRootCoefficientRing (Module.finrank ℂ V)) V :=
    Module.IsTorsionFree.trans_faithfulSMul
      (FiniteRootCoefficientRing (Module.finrank ℂ V)) ℂ V
  infer_instance

/-- Fullness supplies the lower bound on generic rank: the integral
lattice contains a copy of the chosen complex basis.  It does not
supply the opposite inequality. -/
theorem complex_finrank_le_integralLattice_finrank :
    Module.finrank ℂ V ≤
      Module.finrank
        (FiniteRootCoefficientRing (Module.finrank ℂ V))
        (P.integralLattice b) := by
  letI : Fintype ι := Fintype.ofFinite ι
  letI :
      Module.Finite
        (FiniteRootCoefficientRing (Module.finrank ℂ V))
        (P.integralLattice b) :=
    P.integralLattice_moduleFinite b
  calc
    Module.finrank ℂ V = Fintype.card ι :=
      Module.finrank_eq_card_basis b
    _ ≤
        Module.finrank
          (FiniteRootCoefficientRing (Module.finrank ℂ V))
          (P.integralLattice b) :=
      (P.integralBasisVector_linearIndependent b).fintype_card_le_finrank

variable (q : ℕ) [Fact q.Prime]

/-- Projectivity of the canonical integral lattice is sufficient for
residue reduction to preserve its generic rank. -/
theorem residueFieldLattice_finrank_eq_integralLattice
    (hprojective :
      Module.Projective
        (FiniteRootCoefficientRing (Module.finrank ℂ V))
        (P.integralLattice b)) :
    Module.finrank
        (FiniteRootCoefficientRing.ResidueFieldAbovePrime
          q (Module.finrank ℂ V))
        (P.residueFieldLattice b q) =
      Module.finrank
        (FiniteRootCoefficientRing (Module.finrank ℂ V))
        (P.integralLattice b) := by
  letI :
      Module.Finite
        (FiniteRootCoefficientRing (Module.finrank ℂ V))
        (P.integralLattice b) :=
    P.integralLattice_moduleFinite b
  letI :
      Module.Projective
        (FiniteRootCoefficientRing (Module.finrank ℂ V))
        (P.integralLattice b) :=
    hprojective
  exact
    ResidueModule.finrank_reduction_eq_of_projective
      (M := P.integralLattice b)
      (FiniteRootCoefficientRing.maximalIdealAbovePrime
        q (Module.finrank ℂ V))

/-- The exact two algebraic conditions which identify the dimension of
the residue lattice with the original complex representation degree:
the canonical lattice must be projective and have the expected generic
rank. -/
theorem residueFieldLattice_finrank_eq
    (hprojective :
      Module.Projective
        (FiniteRootCoefficientRing (Module.finrank ℂ V))
        (P.integralLattice b))
    (hrank :
      Module.finrank
          (FiniteRootCoefficientRing (Module.finrank ℂ V))
          (P.integralLattice b) =
        Module.finrank ℂ V) :
    Module.finrank
        (FiniteRootCoefficientRing.ResidueFieldAbovePrime
          q (Module.finrank ℂ V))
        (P.residueFieldLattice b q) =
      Module.finrank ℂ V :=
  (P.residueFieldLattice_finrank_eq_integralLattice b q hprojective).trans
    hrank

/-- It is enough to prove the missing upper bound on the generic rank:
the reverse inequality already follows from the complex basis lying in
the lattice. -/
theorem residueFieldLattice_finrank_eq_of_projective_of_le
    (hprojective :
      Module.Projective
        (FiniteRootCoefficientRing (Module.finrank ℂ V))
        (P.integralLattice b))
    (hupper :
      Module.finrank
          (FiniteRootCoefficientRing (Module.finrank ℂ V))
          (P.integralLattice b) ≤
        Module.finrank ℂ V) :
    Module.finrank
        (FiniteRootCoefficientRing.ResidueFieldAbovePrime
          q (Module.finrank ℂ V))
        (P.residueFieldLattice b q) =
      Module.finrank ℂ V := by
  apply P.residueFieldLattice_finrank_eq b q hprojective
  exact le_antisymm hupper
    (P.complex_finrank_le_integralLattice_finrank b)

/-- A concrete sufficient integral-model hypothesis: if the canonical
lattice has an `R`-basis indexed by the same finite type as the chosen
complex basis, then reduction has exactly the complex dimension. -/
theorem residueFieldLattice_finrank_eq_of_basis
    (bIntegral :
      Module.Basis ι
        (FiniteRootCoefficientRing (Module.finrank ℂ V))
        (P.integralLattice b)) :
    Module.finrank
        (FiniteRootCoefficientRing.ResidueFieldAbovePrime
          q (Module.finrank ℂ V))
        (P.residueFieldLattice b q) =
      Module.finrank ℂ V := by
  letI : Fintype ι := Fintype.ofFinite ι
  letI :
      Module.Finite
        (FiniteRootCoefficientRing (Module.finrank ℂ V))
        (P.integralLattice b) :=
    P.integralLattice_moduleFinite b
  letI :
      Module.Free
        (FiniteRootCoefficientRing (Module.finrank ℂ V))
        (P.integralLattice b) :=
    Module.Free.of_basis bIntegral
  calc
    Module.finrank
        (FiniteRootCoefficientRing.ResidueFieldAbovePrime
          q (Module.finrank ℂ V))
        (P.residueFieldLattice b q) =
        Module.finrank
          (FiniteRootCoefficientRing (Module.finrank ℂ V))
          (P.integralLattice b) := by
      exact
        ResidueModule.finrank_reduction_eq_of_free
          (M := P.integralLattice b)
          (FiniteRootCoefficientRing.maximalIdealAbovePrime
            q (Module.finrank ℂ V))
    _ = Fintype.card ι := Module.finrank_eq_card_basis bIntegral
    _ = Module.finrank ℂ V :=
      (Module.finrank_eq_card_basis b).symm

end ProjectiveRepresentation

end CharacterTriple
end McKayConjecture
