/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.EndomorphismFixedIntertwiner

/-!
# Evaluating relative traces of endomorphisms

When an endomorphism fixed by a subgroup acts on a globally invariant
vector, its relative trace as an endomorphism evaluates to the relative
trace of the resulting vector.  This observation makes the
endomorphism-algebra Brauer trace ideal vanish on the module Brauer
quotient.
-/

noncomputable section

namespace Representation

open scoped BigOperators

variable {k P V : Type}
variable [Field k] [Group P] [Fintype P]
variable [AddCommGroup V] [Module k V]

noncomputable local instance endomorphismTraceEvaluationCosetFintype
    (Q : Subgroup P) :
    Fintype (P ⧸ Q) :=
  Fintype.ofFinite (P ⧸ Q)

/-- Applying a subgroup-fixed endomorphism to a globally invariant
vector produces a subgroup-invariant vector. -/
def subgroupFixedEndomorphismOnInvariant
    (ρ : Representation k P V)
    (Q : Subgroup P) :
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction ρ)
    letI :=
      endomorphismConjugation_smulCommClass
        (representationLinearAction ρ)
    fixedSubalgebra
        (k := k) (P := Q) (A := Module.End k V) →
      invariants ρ →
        invariants (ρ.comp Q.subtype) := by
  letI :=
    endomorphismConjugationMulSemiringAction
      (representationLinearAction ρ)
  letI :=
    endomorphismConjugation_smulCommClass
      (representationLinearAction ρ)
  intro f x
  refine ⟨(f : Module.End k V) x, ?_⟩
  intro q
  have hf := f.property q
  change
    (q : P) • (f : Module.End k V) =
      (f : Module.End k V) at hf
  rw [endomorphismConjugation_smul] at hf
  have hm := congrArg
    (fun c : Module.End k V ↦
      c *
        (linearActionUnit
          (representationLinearAction ρ) (q : P) :
            Module.End k V))
    hf
  have hcomm :
      (linearActionUnit
          (representationLinearAction ρ) (q : P) :
        Module.End k V) * (f : Module.End k V) =
        (f : Module.End k V) *
          (linearActionUnit
            (representationLinearAction ρ) (q : P) :
              Module.End k V) := by
    simpa only [mul_assoc, Units.inv_mul, mul_one] using hm
  change
    ρ (q : P) ((f : Module.End k V) (x : V)) =
      (f : Module.End k V) (x : V)
  calc
    ρ (q : P) ((f : Module.End k V) (x : V)) =
        (f : Module.End k V) (ρ (q : P) (x : V)) :=
      LinearMap.congr_fun hcomm (x : V)
    _ = (f : Module.End k V) (x : V) := by
      rw [x.property (q : P)]

omit [Fintype P] in
@[simp]
theorem subgroupFixedEndomorphismOnInvariant_coe
    (ρ : Representation k P V)
    (Q : Subgroup P)
    (f :
      letI :=
        endomorphismConjugationMulSemiringAction
          (representationLinearAction ρ)
      letI :=
        endomorphismConjugation_smulCommClass
          (representationLinearAction ρ)
      fixedSubalgebra
        (k := k) (P := Q) (A := Module.End k V))
    (x : invariants ρ) :
    (subgroupFixedEndomorphismOnInvariant ρ Q f x : V) =
      (f : Module.End k V) (x : V) :=
  rfl

/-- A relative trace in the endomorphism algebra evaluates on a
globally invariant vector as the corresponding vector relative trace. -/
theorem fixedRelativeTrace_apply_invariant
    (ρ : Representation k P V)
    (Q : Subgroup P) :
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction ρ)
    letI :=
      endomorphismConjugation_smulCommClass
        (representationLinearAction ρ)
    ∀
      (f :
        fixedSubalgebra
          (k := k) (P := Q) (A := Module.End k V))
      (x : invariants ρ),
      ((fixedRelativeTrace
          (k := k) (P := P) (A := Module.End k V) Q f :
        fixedSubalgebra
          (k := k) (P := P) (A := Module.End k V)) :
          Module.End k V) (x : V) =
        ((relativeTrace ρ Q
          (subgroupFixedEndomorphismOnInvariant ρ Q f x) :
            invariants ρ) : V) := by
  letI :=
    endomorphismConjugationMulSemiringAction
      (representationLinearAction ρ)
  letI :=
    endomorphismConjugation_smulCommClass
      (representationLinearAction ρ)
  intro f x
  change
    (∑ c : P ⧸ Q, c.out • (f : Module.End k V)) (x : V) =
      ∑ c : P ⧸ Q,
        ρ c.out ((f : Module.End k V) (x : V))
  rw [LinearMap.sum_apply]
  apply Fintype.sum_congr
  intro c
  rw [endomorphismConjugation_smul]
  simp only [Module.End.mul_apply,
    linearActionUnit_representationLinearAction]
  rw [show
    ((↑((linearActionUnit
        (representationLinearAction ρ) c.out)⁻¹) :
          Module.End k V) (x : V)) =
      ρ c.out⁻¹ (x : V) by
        rw [← map_inv]
        exact congrArg
          (fun u : (Module.End k V)ˣ ↦
            (u : Module.End k V) (x : V))
          rfl]
  rw [x.property c.out⁻¹]

end Representation
