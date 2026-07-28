/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.QuotientDescent
import McKayConjecture.GroupTheory.PerfectCentralExtensionCenter
import McKayConjecture.InductiveMcKay.CentralExtensionIntermediateProjection
import McKayConjecture.InductiveMcKay.CentralQuotientTriviality
import McKayConjecture.InductiveMcKay.CentralScalarLocalCorrespondence

/-!
# Numerical local descent through a central extension

Let `E : A → Q` be a finite-source central extension, let `S` be a Sylow
subgroup of `Q`, and suppose that the lifted Sylow subgroup of `A` satisfies
the full local inductive McKay condition.  The character-triple witness in
that condition forces the stored correspondence to preserve triviality on
the central kernel.  Restricting to those characters and applying ordinary
quotient descent therefore gives a genuine numerical local correspondence
for `S`.

This construction does not claim that the full inductive datum descends.
Equivariance under every automorphism of `Q` requires coherent lifts of
those automorphisms to `A`.  At the triple level one must restrict the
upstairs witness to the lifted stabilizer and quotient its subgroup geometry
through the corresponding semidirect-product kernels.  Once character
triviality on those kernels is known, exact descent of the chosen projective
operators and factors is automatic; see
`AssociatedProjectiveRepresentation.isQuotientCompatible_of_trivialOn`.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace GroupTheory
namespace CentralExtension

variable {A : Type u} {Q : Type v}
variable [Group A] [Group Q] [Finite A]

/-- Inflation across a central extension, expressed as an equivalence onto
the irreducible `p'`-degree characters trivial on its kernel.  Centrality is
not needed for this character-theoretic equivalence, but packaging it here
makes the two sides of local central-extension descent explicit. -/
def pPrimeInflationEquiv
    (E : CentralExtension A Q) (p : ℕ) :
    PPrimeIrreducibleCharacter Q p ≃
      IrreducibleCharacter.PPrimeTrivialOnCharacters
        E.projection.ker p :=
  (IrreducibleCharacter.pPrimeComapEquiv p
      (QuotientGroup.quotientKerEquivOfSurjective
        E.projection E.surjective)).trans
    (IrreducibleCharacter.pPrimeQuotientDescentEquiv
      E.projection.ker p)

@[simp]
theorem pPrimeInflationEquiv_apply_values
    (E : CentralExtension A Q) (p : ℕ)
    (χ : PPrimeIrreducibleCharacter Q p) (a : A) :
    (E.pPrimeInflationEquiv p χ).1.1.values a =
      χ.1.values (E.projection a) := by
  change
    (IrreducibleCharacter.inflate E.projection.ker
      ((χ.1.comap
        (QuotientGroup.quotientKerEquivOfSurjective
          E.projection E.surjective)))).values a =
      χ.1.values (E.projection a)
  rw [IrreducibleCharacter.inflate_values,
    IrreducibleCharacter.comap_values]
  rfl

@[simp]
theorem pPrimeInflationEquiv_apply_degree
    (E : CentralExtension A Q) (p : ℕ)
    (χ : PPrimeIrreducibleCharacter Q p) :
    (E.pPrimeInflationEquiv p χ).1.1.degree =
      χ.1.degree := by
  change
    (IrreducibleCharacter.inflate E.projection.ker
      ((χ.1.comap
        (QuotientGroup.quotientKerEquivOfSurjective
          E.projection E.surjective)))).degree =
      χ.1.degree
  rw [IrreducibleCharacter.inflate_degree,
    IrreducibleCharacter.comap_degree]

end CentralExtension
end GroupTheory

namespace InductiveMcKay
namespace LocalInductiveMcKayData

open GroupTheory

variable {A : Type u} {Q : Type v}
variable [Group A] [Group Q] [Finite A]
variable {p : ℕ} [Fact p.Prime]
variable (E : CentralExtension A Q) (S : Sylow p Q)
variable (d : LocalInductiveMcKayData (E.sylowLift S))

/-- The copy of an extension kernel in the upstairs intermediate is normal.
This named instance keeps quotient notation independent of reducibility of
`subgroupInIntermediate`. -/
instance subgroupInIntermediateKerNormal :
    (d.subgroupInIntermediate E.projection.ker).Normal :=
  (inferInstance : E.projection.ker.Normal).comap
    d.intermediate.subtype

/-- The quotient of the upstairs intermediate by the extension kernel is
canonically the projected intermediate downstairs. -/
def projectedIntermediateQuotientEquiv :
    (d.intermediate ⧸
        d.subgroupInIntermediate E.projection.ker) ≃*
      d.projectedIntermediate E.projection :=
  (QuotientGroup.quotientMulEquivOfEq (by
      rw [d.intermediateProjection_ker E.projection]
      ext x
      rfl)).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (d.intermediateProjection E.projection)
      (d.intermediateProjection_surjective E.projection))

@[simp]
theorem projectedIntermediateQuotientEquiv_mk
    (a : d.intermediate) :
    d.projectedIntermediateQuotientEquiv E S
        (QuotientGroup.mk a) =
      d.intermediateProjection E.projection a := by
  rw [projectedIntermediateQuotientEquiv,
    MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  change
    QuotientGroup.kerLift
        (d.intermediateProjection E.projection)
        (QuotientGroup.mk a) =
      d.intermediateProjection E.projection a
  exact QuotientGroup.kerLift_mk _ _

/-- Inflation from the projected intermediate identifies its `p'`-degree
characters with the upstairs intermediate characters trivial on the copy
of the extension kernel. -/
def projectedIntermediatePPrimeInflationEquiv :
    PPrimeIrreducibleCharacter
        (d.projectedIntermediate E.projection) p ≃
      IrreducibleCharacter.PPrimeTrivialOnCharacters
        (d.subgroupInIntermediate E.projection.ker) p :=
  (IrreducibleCharacter.pPrimeComapEquiv p
      (d.projectedIntermediateQuotientEquiv E S)).trans
    (IrreducibleCharacter.pPrimeQuotientDescentEquiv
      (d.subgroupInIntermediate E.projection.ker) p)

@[simp]
theorem projectedIntermediatePPrimeInflationEquiv_apply_values
    (ψ : PPrimeIrreducibleCharacter
      (d.projectedIntermediate E.projection) p)
    (a : d.intermediate) :
    (d.projectedIntermediatePPrimeInflationEquiv E S ψ).1.1.values a =
      ψ.1.values
        (d.intermediateProjection E.projection a) := by
  change
    (IrreducibleCharacter.inflate
      (d.subgroupInIntermediate E.projection.ker)
      (ψ.1.comap
        (d.projectedIntermediateQuotientEquiv E S))).values a =
      ψ.1.values
        (d.intermediateProjection E.projection a)
  rw [IrreducibleCharacter.inflate_values,
    IrreducibleCharacter.comap_values]
  exact congrArg ψ.1.values
    (d.projectedIntermediateQuotientEquiv_mk E S a)

@[simp]
theorem projectedIntermediatePPrimeInflationEquiv_apply_degree
    (ψ : PPrimeIrreducibleCharacter
      (d.projectedIntermediate E.projection) p) :
    (d.projectedIntermediatePPrimeInflationEquiv E S ψ).1.1.degree =
      ψ.1.degree := by
  change
    (IrreducibleCharacter.inflate
      (d.subgroupInIntermediate E.projection.ker)
      (ψ.1.comap
        (d.projectedIntermediateQuotientEquiv E S))).degree =
      ψ.1.degree
  rw [IrreducibleCharacter.inflate_degree,
    IrreducibleCharacter.comap_degree]

@[simp]
theorem projectedIntermediatePPrimeInflationEquiv_symm_values
    (ψ : IrreducibleCharacter.PPrimeTrivialOnCharacters
      (d.subgroupInIntermediate E.projection.ker) p)
    (a : d.intermediate) :
    ((d.projectedIntermediatePPrimeInflationEquiv E S).symm ψ).1.values
        (d.intermediateProjection E.projection a) =
      ψ.1.1.values a := by
  change
    (IrreducibleCharacter.descend
      (d.subgroupInIntermediate E.projection.ker)
      ⟨ψ.1.1, ψ.2⟩).values
        ((d.projectedIntermediateQuotientEquiv E S).symm
          (d.intermediateProjection E.projection a)) =
      ψ.1.1.values a
  have harg :
      (d.projectedIntermediateQuotientEquiv E S).symm
          (d.intermediateProjection E.projection a) =
        QuotientGroup.mk'
          (d.subgroupInIntermediate E.projection.ker) a := by
    apply (d.projectedIntermediateQuotientEquiv E S).injective
    rw [MulEquiv.apply_symm_apply]
    exact d.projectedIntermediateQuotientEquiv_mk E S a
  rw [harg]
  exact
    IrreducibleCharacter.descend_values_mk
      (d.subgroupInIntermediate E.projection.ker)
      ⟨ψ.1.1, ψ.2⟩ a

@[simp]
theorem projectedIntermediatePPrimeInflationEquiv_symm_degree
    (ψ : IrreducibleCharacter.PPrimeTrivialOnCharacters
      (d.subgroupInIntermediate E.projection.ker) p) :
    ((d.projectedIntermediatePPrimeInflationEquiv E S).symm ψ).1.degree =
      ψ.1.1.degree := by
  change
    ((IrreducibleCharacter.descend
      (d.subgroupInIntermediate E.projection.ker)
      ⟨ψ.1.1, ψ.2⟩).comap
        (d.projectedIntermediateQuotientEquiv E S).symm).degree =
      ψ.1.1.degree
  rw [IrreducibleCharacter.comap_degree,
    IrreducibleCharacter.descend_degree]

/-- The local character correspondence descended to the quotient.

The middle equivalence is not an extra hypothesis: it is forced by the
central character-triple witness stored in `d`. -/
def projectedCorrespondence :
    PPrimeIrreducibleCharacter Q p ≃
      PPrimeIrreducibleCharacter
        (d.projectedIntermediate E.projection) p :=
  (E.pPrimeInflationEquiv p).trans <|
    (d.correspondenceTrivialOnEquiv
      E.projection.ker E.ker_le_center
      (d.ker_le_intermediate E S)).trans <|
        (d.projectedIntermediatePPrimeInflationEquiv E S).symm

@[simp]
theorem projectedIntermediatePPrimeInflationEquiv_projectedCorrespondence
    (χ : PPrimeIrreducibleCharacter Q p) :
    d.projectedIntermediatePPrimeInflationEquiv E S
        (d.projectedCorrespondence E S χ) =
      d.correspondenceTrivialOnEquiv
        E.projection.ker E.ker_le_center
        (d.ker_le_intermediate E S)
        (E.pPrimeInflationEquiv p χ) := by
  exact
    (d.projectedIntermediatePPrimeInflationEquiv E S).apply_symm_apply _

@[simp]
theorem projectedCorrespondence_values_projection
    (χ : PPrimeIrreducibleCharacter Q p)
    (a : d.intermediate) :
    (d.projectedCorrespondence E S χ).1.values
        (d.intermediateProjection E.projection a) =
      (d.correspondence
        (E.pPrimeInflationEquiv p χ).1).1.values a := by
  exact
    d.projectedIntermediatePPrimeInflationEquiv_symm_values
      E S
      (d.correspondenceTrivialOnEquiv
        E.projection.ker E.ker_le_center
        (d.ker_le_intermediate E S)
        (E.pPrimeInflationEquiv p χ))
      a

@[simp]
theorem projectedCorrespondence_degree
    (χ : PPrimeIrreducibleCharacter Q p) :
    (d.projectedCorrespondence E S χ).1.degree =
      (d.correspondence
        (E.pPrimeInflationEquiv p χ).1).1.degree :=
  d.projectedIntermediatePPrimeInflationEquiv_symm_degree
    E S
    (d.correspondenceTrivialOnEquiv
      E.projection.ker E.ker_le_center
      (d.ker_le_intermediate E S)
      (E.pPrimeInflationEquiv p χ))

/-- A full upstairs inductive-McKay datum descends unconditionally to a
numerical local correspondence through a central extension. -/
def quotientLocalCorrespondence :
    LocalCorrespondence S where
  intermediate := d.projectedIntermediate E.projection
  normalizer_le := d.normalizer_le_projectedIntermediate E S
  proper_of_normalizer_ne_top htarget :=
    d.projectedIntermediate_lt_top_of_normalizer_ne_top E S (by
      intro hsource
      apply htarget
      apply (Subgroup.eq_top_iff'
        (Subgroup.normalizer (S : Set Q))).mpr
      intro q
      obtain ⟨a, ha⟩ := E.surjective q
      have haNormalizer :
          a ∈ Subgroup.normalizer
            (E.sylowLift S : Set A) := by
        rw [hsource]
        exact Subgroup.mem_top a
      simpa [ha] using
        E.projection_mem_sylowNormalizer S
          ⟨a, haNormalizer⟩)
  correspondence := d.projectedCorrespondence E S

/-- If the source of the central extension is perfect, the descended
correspondence also preserves the exact normalized values on the whole
target center.

Perfectness is used only to rule out new central elements downstairs:
`map (center A) = center Q`.  No automorphism-lifting hypothesis is needed
for this central-scalar numerical layer. -/
def quotientCentralScalarLocalCorrespondence
    [Finite Q]
    (hperfect : Group.IsPerfect A) :
    CentralScalarLocalCorrespondence S where
  toLocalCorrespondence := d.quotientLocalCorrespondence E S
  correspondence_central_cross := by
    intro χ z hzcentral hzintermediate
    obtain ⟨a, ha⟩ := E.surjective z
    have haTargetCenter :
        E.projection a ∈ Subgroup.center Q := by
      simpa [ha] using hzcentral
    have haCenter :
        a ∈ Subgroup.center A :=
      E.mem_center_of_projection_mem_center
        hperfect haTargetCenter
    have haNormalizer :
        a ∈ Subgroup.normalizer
          (E.sylowLift S : Set A) :=
      Subgroup.center_le_normalizer
        (E.sylowLift S : Set A) haCenter
    have haIntermediate : a ∈ d.intermediate :=
      d.normalizer_le haNormalizer
    let aI : d.intermediate := ⟨a, haIntermediate⟩
    have hprojection :
        d.intermediateProjection E.projection aI =
          ⟨z, hzintermediate⟩ := by
      apply Subtype.ext
      exact ha
    have hcross :=
      d.correspondence_central_cross
        (E.pPrimeInflationEquiv p χ).1
        a haCenter haIntermediate
    change
      χ.1.values z *
          ((d.projectedCorrespondence E S χ).1.degree : ℂ) =
        (d.projectedCorrespondence E S χ).1.values
            ⟨z, hzintermediate⟩ *
          (χ.1.degree : ℂ)
    rw [← hprojection,
      d.projectedCorrespondence_values_projection E S,
      d.projectedCorrespondence_degree E S]
    simpa [ha] using hcross

end LocalInductiveMcKayData
end InductiveMcKay
end McKayConjecture
