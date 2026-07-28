/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.GroupAction.Quotient
import McKayConjecture.Character.Determination
import McKayConjecture.Character.KernelQuotient

/-!
# Actions on faithful character quotients

An action preserving an irreducible character also preserves its
representation kernel.  Consequently it descends to the faithful quotient,
where the descended character remains invariant.  The faithful-invariant
center theorem then shows that the quotient center is fixed pointwise and,
under the coprime hypotheses, supplies the fixed-point-product centralizer
containment.

The induced quotient action is an explicit definition rather than a global
instance: its construction depends on the supplied proof of character
invariance.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace IrreducibleCharacter

universe u v

variable {P : Type u} {A : Type v}
variable [Group P] [Group A] [Finite A]
variable [MulDistribMulAction P A]

/-- The chosen realization twisted by one element of the acting group. -/
abbrev actionTwistRepresentation
    (χ : IrreducibleCharacter A) (g : P) :
    FDRep ℂ A :=
  FDRep.of
    (χ.realization.ρ.comp
      (GroupTheory.actionHom P A g).toMonoidHom)

instance actionTwistRepresentationSimple
    (χ : IrreducibleCharacter A) (g : P) :
    Simple (actionTwistRepresentation χ g) := by
  let E : FDRep ℂ A ≌ FDRep ℂ A :=
    Action.resEquiv (FGModuleCat ℂ)
      (GroupTheory.actionHom P A g)
  show Simple (E.functor.obj χ.realization)
  exact CategoryTheory.simple_obj E.functor χ.realization

@[simp]
theorem actionTwistRepresentation_ρ
    (χ : IrreducibleCharacter A) (g : P) (a : A) :
    (actionTwistRepresentation χ g).ρ a =
      χ.realization.ρ (g • a) :=
  rfl

/-- Invariance identifies the character of every action twist with the
original character. -/
theorem actionTwistRepresentation_character_eq
    (χ : IrreducibleCharacter A)
    (hinvariant : IsInvariantUnderAction (P := P) χ)
    (g : P) :
    (actionTwistRepresentation χ g).character =
      χ.values := by
  funext a
  change χ.realization.character (g • a) =
    χ.values a
  rw [χ.realization_character]
  exact hinvariant g a

/-- The kernel of an action-invariant irreducible character is stable under
the acting group. -/
theorem smul_mem_kernel_of_isInvariantUnderAction
    (χ : IrreducibleCharacter A)
    (hinvariant : IsInvariantUnderAction (P := P) χ)
    (g : P) {a : A} (ha : a ∈ χ.kernel) :
    g • a ∈ χ.kernel := by
  have htrivialTwist :
      FDRep.IsTrivialOn
        (actionTwistRepresentation χ g) χ.kernel :=
    (χ.trivialOn_iff_of_character_eq
      χ.kernel (actionTwistRepresentation χ g)
      (χ.actionTwistRepresentation_character_eq
        hinvariant g)).mp χ.trivialOn_kernel
  exact (χ.mem_kernel_iff (g • a)).mpr
    (htrivialTwist ⟨a, ha⟩)

/-- Stability of the character kernel supplies mathlib's quotient-action
condition. -/
def kernelQuotientAction
    (χ : IrreducibleCharacter A)
    (hinvariant : IsInvariantUnderAction (P := P) χ) :
    MulAction.QuotientAction P χ.kernel where
  inv_mul_mem g a a' haa' := by
    have hstable :=
      χ.smul_mem_kernel_of_isInvariantUnderAction
        hinvariant g haa'
    change
      ((GroupTheory.actionHom P A g) a)⁻¹ *
          (GroupTheory.actionHom P A g) a' ∈
        χ.kernel
    rw [← map_inv, ← map_mul]
    exact hstable

/-- The induced multiplicative action of `P` on the faithful quotient
`A / ker(χ)`. -/
def kernelQuotientMulDistribMulAction
    (χ : IrreducibleCharacter A)
    (hinvariant : IsInvariantUnderAction (P := P) χ) :
    MulDistribMulAction P (A ⧸ χ.kernel) := by
  letI : MulAction.QuotientAction P χ.kernel :=
    χ.kernelQuotientAction hinvariant
  letI : MulAction P (A ⧸ χ.kernel) :=
    MulAction.quotient P χ.kernel
  exact MulDistribMulAction.mk
    (fun g ↦ by
      change
        g • (↑(1 : A) : A ⧸ χ.kernel) =
          (↑(1 : A) : A ⧸ χ.kernel)
      rw [MulAction.Quotient.smul_mk, smul_one])
    (fun g q r ↦
      Quotient.inductionOn₂' q r fun a b ↦ by
        change
          g • (↑(a * b) : A ⧸ χ.kernel) =
            (↑(g • a) : A ⧸ χ.kernel) *
              (↑(g • b) : A ⧸ χ.kernel)
        rw [MulAction.Quotient.smul_mk, smul_mul']
        exact map_mul (QuotientGroup.mk' χ.kernel)
          (g • a) (g • b))

/-- The quotient action has the expected value on a quotient class. -/
theorem kernelQuotient_smul_mk
    (χ : IrreducibleCharacter A)
    (hinvariant : IsInvariantUnderAction (P := P) χ)
    (g : P) (a : A) :
    letI := χ.kernelQuotientMulDistribMulAction hinvariant
    g • QuotientGroup.mk' χ.kernel a =
      QuotientGroup.mk' χ.kernel (g • a) := by
  letI : MulAction.QuotientAction P χ.kernel :=
    χ.kernelQuotientAction hinvariant
  letI : MulDistribMulAction P (A ⧸ χ.kernel) :=
    χ.kernelQuotientMulDistribMulAction hinvariant
  rfl

/-- The faithful quotient character remains invariant under the induced
quotient action. -/
theorem faithfulQuotientCharacter_isInvariantUnderAction
    (χ : IrreducibleCharacter A)
    (hinvariant : IsInvariantUnderAction (P := P) χ) :
    letI := χ.kernelQuotientMulDistribMulAction hinvariant
    IsInvariantUnderAction (P := P)
      χ.faithfulQuotientCharacter := by
  letI : MulDistribMulAction P (A ⧸ χ.kernel) :=
    χ.kernelQuotientMulDistribMulAction hinvariant
  intro g q
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective χ.kernel q
  rw [χ.kernelQuotient_smul_mk hinvariant,
    faithfulQuotientCharacter_values_mk,
    faithfulQuotientCharacter_values_mk]
  exact hinvariant g a

/-- The center of the faithful quotient is fixed pointwise by the induced
action. -/
theorem faithfulQuotient_center_le_fixedPoints
    (χ : IrreducibleCharacter A)
    (hinvariant : IsInvariantUnderAction (P := P) χ) :
    letI := χ.kernelQuotientMulDistribMulAction hinvariant
    Subgroup.center (A ⧸ χ.kernel) ≤
      FixedPoints.subgroup P (A ⧸ χ.kernel) := by
  letI : MulDistribMulAction P (A ⧸ χ.kernel) :=
    χ.kernelQuotientMulDistribMulAction hinvariant
  exact
    χ.faithfulQuotientCharacter
      |>.center_le_fixedPoints_of_isFaithful_isInvariantUnderAction
        χ.faithfulQuotientCharacter_isFaithful
        (χ.faithfulQuotientCharacter_isInvariantUnderAction
          hinvariant)

/-- On the faithful quotient, an invariant character supplies the
centralizer containment required by the coprime fixed-point-product seam. -/
theorem faithfulQuotient_centralizer_actionKernel_le_range
    {p : ℕ}
    (hP : IsPGroup p P)
    (hA : GroupTheory.IsPPrimeGroup p A)
    (χ : IrreducibleCharacter A)
    (hinvariant : IsInvariantUnderAction (P := P) χ) :
    letI := χ.kernelQuotientMulDistribMulAction hinvariant
    Subgroup.centralizer
          (GroupTheory.actionKernel P (A ⧸ χ.kernel) :
            Set (GroupTheory.actionSemidirectProduct
              P (A ⧸ χ.kernel))) ≤
        MonoidHom.range
          (GroupTheory.actionFixedPointProductEmbedding
            P (A ⧸ χ.kernel)) := by
  letI : MulDistribMulAction P (A ⧸ χ.kernel) :=
    χ.kernelQuotientMulDistribMulAction hinvariant
  exact
    χ.faithfulQuotientCharacter
      |>.centralizer_actionKernel_le_fixedPointProduct_range_of_faithful_invariant
        hP (hA.to_quotient χ.kernel)
        χ.faithfulQuotientCharacter_isFaithful
        (χ.faithfulQuotientCharacter_isInvariantUnderAction
          hinvariant)

end IrreducibleCharacter
end McKayConjecture
