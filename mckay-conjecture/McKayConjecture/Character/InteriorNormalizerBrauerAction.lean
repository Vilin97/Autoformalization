/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerRelativeTraceEquivariance
import McKayConjecture.Character.InteriorNormalizerCovariance
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Interior normalizer action on the Brauer quotient

For a faithful interior action, conjugation by a unit normalizing the
interior group permutes the relative traces from proper subgroups.
Consequently it preserves the Brauer trace ideal and descends to an
algebra automorphism of the Brauer quotient.
-/

noncomputable section

namespace Representation

variable {k P A : Type}
variable [CommRing k] [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

namespace InteriorAction

variable (I : InteriorAction (P := P) (A := A))

/-- Conjugation by an interior normalizer unit carries every element of
the Brauer trace ideal back into that ideal. -/
theorem normalizerConjFixedAlgEquiv_mem_brauerTraceIdeal
    (hI : Function.Injective I.unit)
    (s : I.unitNormalizer)
    (c : fixedSubalgebra (k := k) (P := P) (A := A))
    (hc :
      c ∈ brauerTraceIdeal (k := k) (P := P) (A := A)) :
    I.normalizerConjFixedAlgEquiv (k := k) s c ∈
      brauerTraceIdeal (k := k) (P := P) (A := A) := by
  let B :=
    brauerTraceIdeal (k := k) (P := P) (A := A)
  change _ ∈ B
  refine Submodule.iSup_induction
    (fun Q : Subgroup P ↦
      ⨆ _hQ : Q < ⊤,
        fixedRelativeTraceIdeal
          (k := k) (P := P) (A := A) Q)
    (motive := fun x ↦
      I.normalizerConjFixedAlgEquiv (k := k) s x ∈ B)
    hc ?_ ?_ ?_
  · intro Q x hxQ
    refine Submodule.iSup_induction
      (fun _hQ : Q < ⊤ ↦
        fixedRelativeTraceIdeal
          (k := k) (P := P) (A := A) Q)
      (motive := fun y ↦
        I.normalizerConjFixedAlgEquiv (k := k) s y ∈ B)
      hxQ ?_ ?_ ?_
    · intro hQ y hy
      obtain ⟨x, rfl⟩ := hy
      let eP : P ≃* P :=
        I.normalizerMulAut hI s⁻¹
      let eA : A ≃ₐ[k] A :=
        unitConjugationAlgEquiv (k := k) (s : Aˣ)
      have hcompat :
          ∀ (g : P) (a : A),
            eA (g • a) = eP g • eA a := by
        intro g a
        exact I.unitConjugationAlgEquiv_map_smul hI s g a
      let x' :=
        transportFixedSubalgebra eP eA hcompat Q x
      have htrace :
          I.normalizerConjFixedAlgEquiv (k := k) s
              (fixedRelativeTrace
                (k := k) (P := P) (A := A) Q x) =
            fixedRelativeTrace
              (k := k) (P := P) (A := A)
              (Q.map eP.toMonoidHom) x' := by
        apply Subtype.ext
        exact fixedRelativeTrace_equivariant
          eP eA hcompat Q x
      rw [htrace]
      apply fixedRelativeTrace_mem_brauerTraceIdeal
      rw [← Subgroup.map_top_of_surjective
        eP.toMonoidHom eP.surjective]
      exact
        (Subgroup.map_lt_map_iff_of_injective
          eP.injective).mpr hQ
    · simp
    · intro x y hx hy
      simpa using B.add_mem hx hy
  · simp
  · intro x y hx hy
    simpa using B.add_mem hx hy

/-- The Brauer trace ideal is invariant under conjugation by an
interior normalizer unit. -/
theorem map_brauerTraceIdeal_normalizerConjFixedAlgEquiv
    (hI : Function.Injective I.unit)
    (s : I.unitNormalizer) :
    (brauerTraceIdeal (k := k) (P := P) (A := A)).map
        (I.normalizerConjFixedAlgEquiv
          (k := k) s).toRingEquiv.toRingHom =
      brauerTraceIdeal (k := k) (P := P) (A := A) := by
  let B :=
    brauerTraceIdeal (k := k) (P := P) (A := A)
  let e :=
    I.normalizerConjFixedAlgEquiv (k := k) s
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro c hc
    exact
      I.normalizerConjFixedAlgEquiv_mem_brauerTraceIdeal
        hI s c hc
  · intro c hc
    have hc' :
        I.normalizerConjFixedAlgEquiv (k := k) s⁻¹ c ∈ B :=
      I.normalizerConjFixedAlgEquiv_mem_brauerTraceIdeal
        hI s⁻¹ c hc
    have hmapped :=
      Ideal.mem_map_of_mem
        e.toRingEquiv.toRingHom hc'
    simpa [e, normalizerConjFixedAlgEquiv,
      unitConjugationAlgEquiv, ConjAct.units_smul_def,
      mul_assoc] using hmapped

/-- Algebra automorphism of the Brauer quotient induced by an interior
normalizer unit. -/
def normalizerConjBrauerAlgEquiv
    (hI : Function.Injective I.unit)
    (s : I.unitNormalizer) :
    BrauerQuotientAlgebra (k := k) (P := P) (A := A) ≃ₐ[k]
      BrauerQuotientAlgebra (k := k) (P := P) (A := A) :=
  Ideal.quotientEquivAlg
    (brauerTraceIdeal (k := k) (P := P) (A := A))
    (brauerTraceIdeal (k := k) (P := P) (A := A))
    (I.normalizerConjFixedAlgEquiv (k := k) s)
    (I.map_brauerTraceIdeal_normalizerConjFixedAlgEquiv
      hI s).symm

@[simp]
theorem normalizerConjBrauerAlgEquiv_brauerAlgebraProjection
    (hI : Function.Injective I.unit)
    (s : I.unitNormalizer)
    (c : fixedSubalgebra (k := k) (P := P) (A := A)) :
    I.normalizerConjBrauerAlgEquiv (k := k) hI s
        (brauerAlgebraProjection (k := k) (P := P) (A := A) c) =
      brauerAlgebraProjection (k := k) (P := P) (A := A)
        (I.normalizerConjFixedAlgEquiv (k := k) s c) :=
  rfl

end InteriorAction
end Representation
