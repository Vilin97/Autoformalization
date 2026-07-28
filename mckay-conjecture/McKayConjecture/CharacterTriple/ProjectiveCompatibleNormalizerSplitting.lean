/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeAlgebraBrauerDimensionCriterion
import McKayConjecture.CharacterTriple.CrossCharacteristicNormalizerFactor
import McKayConjecture.CharacterTriple.ProjectiveCompatibleReductionSplitting
import McKayConjecture.CharacterTriple.ProjectivePointwiseNormalizer

/-!
# Normalizer splitting through a compatible complex character

A modular normalizer lift need not be transported into a separately chosen
finite coefficient field.  A multiplicative character from its scalar units
to complex units suffices, provided that character lifts the prime-to-`q`
part of every determinant-normalized complex root.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

open Representation

variable {G V k S A : Type}
variable [Group G]
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable [Field k]
variable [Group S] [Fintype S]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction S A] [SMulCommClass S k A]

private instance compatibleNormalizerFinrankNeZero :
    NeZero (Module.finrank ℂ V) :=
  ⟨Module.finrank_pos.ne'⟩

/-- A Brauer-normalizer factor over an arbitrary field splits the original
complex obstruction if a complex character maps it pointwise to the
prime-to-`q` part of the determinant-normalized factor. -/
theorem factorSet_h2Class_eq_zero_of_retainedNormalizerFactor
    (P : ProjectiveRepresentation ℂ G V)
    (q : ℕ) [Fact q.Prime]
    (hdegree : ¬q ∣ Module.finrank ℂ V)
    {I : InteriorAction (P := S) (A := A)}
    (T : ProjectiveNormalizerLift (k := k) (H := G) I)
    (E : BrauerNormalizerExtension (k := k) I)
    (Z : BrauerScalarIdentification (k := k) (P := S) (A := A))
    (κ : kˣ →* ℂˣ)
    (hfactor :
      ∀ g h,
        κ (T.factor g h) =
          ((primeToRootsProjection q (Module.finrank ℂ V)
              (P.finiteFactorSet g h) :
            rootsOfUnity (Module.finrank ℂ V) ℂ) : ℂˣ)) :
    letI := trivialMulDistribMulAction G ℂˣ
    P.factorSet.h2Class = 0 := by
  apply
    P.factorSet_h2Class_eq_zero_of_retainedFactor
      q hdegree
      (P.finiteFactorSet.map
        ((rootsOfUnity (Module.finrank ℂ V) ℂ).subtype.comp
          (primeToRootsProjection q (Module.finrank ℂ V))))
      (fun _ _ ↦ rfl)
  let b : G → ℂˣ :=
    fun g ↦ κ (T.brauerScalar E Z g)
  apply FactorSet.h2Class_eq_zero_of_scalar_split _ b
  intro g h
  have hmul :=
    congrArg κ (T.brauerScalar_mul E Z g h)
  change
    κ (T.brauerScalar E Z g) *
        κ (T.brauerScalar E Z h) =
      ((primeToRootsProjection q (Module.finrank ℂ V)
          (P.finiteFactorSet g h) :
        rootsOfUnity (Module.finrank ℂ V) ℂ) : ℂˣ) *
        κ (T.brauerScalar E Z (g * h))
  rw [← hfactor g h]
  calc
    κ (T.brauerScalar E Z g) *
        κ (T.brauerScalar E Z h) =
      κ
        (T.brauerScalar E Z g *
          T.brauerScalar E Z h) :=
      (κ.map_mul _ _).symm
    _ =
      κ
        (T.factor g h *
          T.brauerScalar E Z (g * h)) :=
      hmul
    _ =
      κ (T.factor g h) *
        κ (T.brauerScalar E Z (g * h)) :=
      κ.map_mul _ _

/-- A Brauer-normalizer factor over an arbitrary field splits the original
complex obstruction if a complex character identifies its coefficient
reduction with the prime-to-`q` projection. -/
theorem factorSet_h2Class_eq_zero_of_compatibleNormalizerFactor
    (P : ProjectiveRepresentation ℂ G V)
    (q : ℕ) [Fact q.Prime]
    (hdegree : ¬q ∣ Module.finrank ℂ V)
    {I : InteriorAction (P := S) (A := A)}
    (T : ProjectiveNormalizerLift (k := k) (H := G) I)
    (E : BrauerNormalizerExtension (k := k) I)
    (Z : BrauerScalarIdentification (k := k) (P := S) (A := A))
    (r :
      rootsOfUnity (Module.finrank ℂ V) ℂ →* kˣ)
    (κ : kˣ →* ℂˣ)
    (hcompat :
      ∀ z : rootsOfUnity (Module.finrank ℂ V) ℂ,
        κ (r z) =
          ((primeToRootsProjection q (Module.finrank ℂ V) z :
            rootsOfUnity (Module.finrank ℂ V) ℂ) : ℂˣ))
    (hfactor :
      ∀ g h,
        T.factor g h =
          r (P.finiteFactorSet g h)) :
    letI := trivialMulDistribMulAction G ℂˣ
    P.factorSet.h2Class = 0 := by
  apply
    P.factorSet_h2Class_eq_zero_of_retainedNormalizerFactor
      q hdegree T E Z κ
  intro g h
  rw [hfactor g h]
  exact hcompat (P.finiteFactorSet g h)

/-- Brauer primitivity supplies the scalar identification in the compatible
complex-character formulation. -/
theorem factorSet_h2Class_eq_zero_of_retainedDadeFactor
    (P : ProjectiveRepresentation ℂ G V)
    (q : ℕ) [Fact q.Prime] [CharP k q]
    (hdegree : ¬q ∣ Module.finrank ℂ V)
    (D : DadeAlgebra q k S A)
    (hprimitive : D.IsBrauerPrimitive)
    (I : InteriorAction (P := S) (A := A))
    (T : ProjectiveNormalizerLift (k := k) (H := G) I)
    (E : BrauerNormalizerExtension (k := k) I)
    (κ : kˣ →* ℂˣ)
    (hfactor :
      ∀ g h,
        κ (T.factor g h) =
          ((primeToRootsProjection q (Module.finrank ℂ V)
              (P.finiteFactorSet g h) :
            rootsOfUnity (Module.finrank ℂ V) ℂ) : ℂˣ)) :
    letI := trivialMulDistribMulAction G ℂˣ
    P.factorSet.h2Class = 0 :=
  P.factorSet_h2Class_eq_zero_of_retainedNormalizerFactor
    q hdegree T E
    (brauerScalarIdentificationOfFinrankOne
      ((D.finrank_brauerQuotientAlgebra_eq_one_iff_isBrauerPrimitive).2
        hprimitive))
    κ hfactor

/-- Brauer primitivity supplies the scalar identification in the compatible
coefficient-reduction formulation. -/
theorem factorSet_h2Class_eq_zero_of_compatibleDadeFactor
    (P : ProjectiveRepresentation ℂ G V)
    (q : ℕ) [Fact q.Prime] [CharP k q]
    (hdegree : ¬q ∣ Module.finrank ℂ V)
    (D : DadeAlgebra q k S A)
    (hprimitive : D.IsBrauerPrimitive)
    (I : InteriorAction (P := S) (A := A))
    (T : ProjectiveNormalizerLift (k := k) (H := G) I)
    (E : BrauerNormalizerExtension (k := k) I)
    (r :
      rootsOfUnity (Module.finrank ℂ V) ℂ →* kˣ)
    (κ : kˣ →* ℂˣ)
    (hcompat :
      ∀ z : rootsOfUnity (Module.finrank ℂ V) ℂ,
        κ (r z) =
          ((primeToRootsProjection q (Module.finrank ℂ V) z :
            rootsOfUnity (Module.finrank ℂ V) ℂ) : ℂˣ))
    (hfactor :
      ∀ g h,
        T.factor g h =
          r (P.finiteFactorSet g h)) :
    letI := trivialMulDistribMulAction G ℂˣ
    P.factorSet.h2Class = 0 :=
  P.factorSet_h2Class_eq_zero_of_retainedDadeFactor
    q hdegree D hprimitive I T E κ
    (fun g h ↦ by
      rw [hfactor g h]
      exact hcompat (P.finiteFactorSet g h))

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
