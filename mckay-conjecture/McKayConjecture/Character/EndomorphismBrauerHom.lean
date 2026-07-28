/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.EndomorphismRelativeTraceEvaluation

/-!
# The endomorphism Brauer homomorphism

The conjugation-fixed endomorphism algebra acts naturally on the module
Brauer quotient.  Relative traces from proper subgroups act trivially,
so this action factors through a canonical algebra homomorphism

`End(V)(P) → End(V(P))`.

For the endopermutation modules used in Dade theory, the deeper next
step is to prove that this homomorphism is an equivalence.
-/

noncomputable section

namespace Representation

variable {k P V : Type}
variable [Field k] [Group P] [Fintype P]
variable [AddCommGroup V] [Module k V]

/-- The conjugation-fixed endomorphism algebra acts on the module
Brauer quotient. -/
def fixedEndomorphismBrauerAlgHom
    (ρ : Representation k P V) :
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction ρ)
    letI :=
      endomorphismConjugation_smulCommClass
        (representationLinearAction ρ)
    fixedSubalgebra
        (k := k) (P := P) (A := Module.End k V) →ₐ[k]
      Module.End k (BrauerQuotient ρ) := by
  letI :=
    endomorphismConjugationMulSemiringAction
      (representationLinearAction ρ)
  letI :=
    endomorphismConjugation_smulCommClass
      (representationLinearAction ρ)
  exact
    (selfIntertwinerBrauerAlgHom ρ).comp
      (fixedEndomorphismIntertwinerAlgEquiv ρ).toAlgHom

@[simp]
theorem fixedEndomorphismBrauerAlgHom_brauerProjection
    (ρ : Representation k P V)
    (c :
      letI :=
        endomorphismConjugationMulSemiringAction
          (representationLinearAction ρ)
      letI :=
        endomorphismConjugation_smulCommClass
          (representationLinearAction ρ)
      fixedSubalgebra
        (k := k) (P := P) (A := Module.End k V))
    (x : invariants ρ) :
    fixedEndomorphismBrauerAlgHom ρ c
        (brauerProjection ρ x) =
      brauerProjection ρ
        (selfIntertwinerOnInvariants ρ
          (fixedEndomorphismIntertwinerAlgEquiv ρ c) x) :=
  rfl

/-- A relative trace from a proper subgroup acts trivially on the
module Brauer quotient. -/
theorem fixedEndomorphismBrauerAlgHom_fixedRelativeTrace
    (ρ : Representation k P V)
    (Q : Subgroup P)
    (hQ : Q < ⊤)
    (f :
      letI :=
        endomorphismConjugationMulSemiringAction
          (representationLinearAction ρ)
      letI :=
        endomorphismConjugation_smulCommClass
          (representationLinearAction ρ)
      fixedSubalgebra
        (k := k) (P := Q) (A := Module.End k V)) :
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction ρ)
    letI :=
      endomorphismConjugation_smulCommClass
        (representationLinearAction ρ)
    fixedEndomorphismBrauerAlgHom ρ
        (fixedRelativeTrace
          (k := k) (P := P) (A := Module.End k V) Q f) =
      0 := by
  letI :=
    endomorphismConjugationMulSemiringAction
      (representationLinearAction ρ)
  letI :=
    endomorphismConjugation_smulCommClass
      (representationLinearAction ρ)
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := brauerProjection_surjective ρ z
  rw [fixedEndomorphismBrauerAlgHom_brauerProjection]
  have heval :
      selfIntertwinerOnInvariants ρ
          (fixedEndomorphismIntertwinerAlgEquiv ρ
            (fixedRelativeTrace
              (k := k) (P := P) (A := Module.End k V)
              Q f))
          x =
        relativeTrace ρ Q
          (subgroupFixedEndomorphismOnInvariant
            ρ Q f x) := by
    apply Subtype.ext
    exact fixedRelativeTrace_apply_invariant ρ Q f x
  rw [heval]
  exact brauerProjection_relativeTrace
    ρ Q hQ
    (subgroupFixedEndomorphismOnInvariant ρ Q f x)

/-- The endomorphism-algebra Brauer trace ideal lies in the kernel of
the action on the module Brauer quotient. -/
theorem brauerTraceIdeal_le_ker_fixedEndomorphismBrauerAlgHom
    (ρ : Representation k P V) :
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction ρ)
    letI :=
      endomorphismConjugation_smulCommClass
        (representationLinearAction ρ)
    brauerTraceIdeal
        (k := k) (P := P) (A := Module.End k V) ≤
      RingHom.ker
        (fixedEndomorphismBrauerAlgHom ρ).toRingHom := by
  letI :=
    endomorphismConjugationMulSemiringAction
      (representationLinearAction ρ)
  letI :=
    endomorphismConjugation_smulCommClass
      (representationLinearAction ρ)
  intro c hc
  change fixedEndomorphismBrauerAlgHom ρ c = 0
  let B :=
    brauerTraceIdeal
      (k := k) (P := P) (A := Module.End k V)
  refine Submodule.iSup_induction
    (fun Q : Subgroup P ↦
      ⨆ _hQ : Q < ⊤,
        fixedRelativeTraceIdeal
          (k := k) (P := P) (A := Module.End k V) Q)
    (motive := fun y ↦
      fixedEndomorphismBrauerAlgHom ρ y = 0)
    hc ?_ ?_ ?_
  · intro Q y hyQ
    refine Submodule.iSup_induction
      (fun _hQ : Q < ⊤ ↦
        fixedRelativeTraceIdeal
          (k := k) (P := P) (A := Module.End k V) Q)
      (motive := fun z ↦
        fixedEndomorphismBrauerAlgHom ρ z = 0)
      hyQ ?_ ?_ ?_
    · intro hQ z hz
      obtain ⟨f, rfl⟩ := hz
      exact
        fixedEndomorphismBrauerAlgHom_fixedRelativeTrace
          ρ Q hQ f
    · exact map_zero _
    · intro u v hu hv
      rw [map_add, hu, hv, add_zero]
  · exact map_zero _
  · intro u v hu hv
    rw [map_add, hu, hv, add_zero]

/-- Canonical algebra homomorphism from the Brauer quotient of an
endomorphism algebra to the endomorphism algebra of the module Brauer
quotient. -/
def endomorphismBrauerAlgHom
    (ρ : Representation k P V) :
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction ρ)
    letI :=
      endomorphismConjugation_smulCommClass
        (representationLinearAction ρ)
    BrauerQuotientAlgebra
        (k := k) (P := P) (A := Module.End k V) →ₐ[k]
      Module.End k (BrauerQuotient ρ) := by
  letI :=
    endomorphismConjugationMulSemiringAction
      (representationLinearAction ρ)
  letI :=
    endomorphismConjugation_smulCommClass
      (representationLinearAction ρ)
  exact Ideal.Quotient.liftₐ
    (brauerTraceIdeal
      (k := k) (P := P) (A := Module.End k V))
    (fixedEndomorphismBrauerAlgHom ρ)
    (brauerTraceIdeal_le_ker_fixedEndomorphismBrauerAlgHom ρ)

@[simp]
theorem endomorphismBrauerAlgHom_brauerAlgebraProjection
    (ρ : Representation k P V) :
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction ρ)
    letI :=
      endomorphismConjugation_smulCommClass
        (representationLinearAction ρ)
    ∀ c :
        fixedSubalgebra
          (k := k) (P := P) (A := Module.End k V),
      endomorphismBrauerAlgHom ρ
          (brauerAlgebraProjection
            (k := k) (P := P) (A := Module.End k V) c) =
        fixedEndomorphismBrauerAlgHom ρ c := by
  letI :=
    endomorphismConjugationMulSemiringAction
      (representationLinearAction ρ)
  letI :=
    endomorphismConjugation_smulCommClass
      (representationLinearAction ρ)
  intro c
  rfl

end Representation
