/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.TwistedInteriorTraceMultiplication
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Multiplication of twisted Brauer components

The trace-product identities imply that multiplication of twisted
fixed elements descends through the Brauer trace submodules in both
variables.  Thus the twisted Brauer components carry bilinear products

`A(φ) × A(ψ) → A(φψ)`.

This file constructs the product componentwise.  Assembling all
components into a single graded algebra is a separate packaging step.
-/

noncomputable section

namespace Representation
namespace InteriorAction

variable {k P A : Type}
variable [CommRing k] [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A]

variable (I : InteriorAction (P := P) (A := A))

/-- Multiplication of invariant representatives followed by projection
to the product twisted Brauer component. -/
def twistedBrauerRepresentativeMul
    (φ ψ : MulAut P) :
    invariants
        (I.twistedInteriorRepresentation (k := k) φ) →ₗ[k]
      invariants
          (I.twistedInteriorRepresentation (k := k) ψ) →ₗ[k]
        I.TwistedBrauerComponent (k := k) (φ * ψ) :=
  LinearMap.mk₂ k
    (fun a b =>
      I.twistedBrauerProjection (k := k) (φ * ψ)
        (I.twistedFixedMulLinear (k := k) φ ψ
          (I.twistedInvariantsEquiv (k := k) φ a)
          (I.twistedInvariantsEquiv (k := k) ψ b)))
    (fun a b c => by
      simp only [map_add, LinearMap.add_apply])
    (fun r a b => by
      simp only [map_smul, LinearMap.smul_apply])
    (fun a b c => by
      simp only [map_add])
    (fun r a b => by
      simp only [map_smul])

@[simp]
theorem twistedBrauerRepresentativeMul_apply
    (φ ψ : MulAut P)
    (a :
      invariants
        (I.twistedInteriorRepresentation (k := k) φ))
    (b :
      invariants
        (I.twistedInteriorRepresentation (k := k) ψ)) :
    I.twistedBrauerRepresentativeMul (k := k) φ ψ a b =
      I.twistedBrauerProjection (k := k) (φ * ψ)
        (I.twistedFixedMul (k := k)
          (I.twistedInvariantsEquiv (k := k) φ a)
          (I.twistedInvariantsEquiv (k := k) ψ b)) :=
  rfl

/-- The representative product vanishes when its left argument lies
in the Brauer trace submodule. -/
theorem twistedBrauerRepresentativeMul_eq_zero_of_left_mem
    (φ ψ : MulAut P)
    (a :
      invariants
        (I.twistedInteriorRepresentation (k := k) φ))
    (ha :
      a ∈ brauerTraceSubmodule
        (I.twistedInteriorRepresentation (k := k) φ))
    (b :
      invariants
        (I.twistedInteriorRepresentation (k := k) ψ)) :
    I.twistedBrauerRepresentativeMul (k := k) φ ψ a b =
      0 := by
  let F :=
    I.twistedBrauerRepresentativeMul (k := k) φ ψ
  refine
    Submodule.iSup_induction
      (fun Q : Subgroup P =>
        ⨆ _hQ : Q < ⊤,
          relativeTraceRange
            (I.twistedInteriorRepresentation (k := k) φ) Q)
      (motive := fun y => F y b = 0) ha ?_ ?_ ?_
  · intro Q y hy
    refine
      Submodule.iSup_induction
        (fun _hQ : Q < ⊤ =>
          relativeTraceRange
            (I.twistedInteriorRepresentation (k := k) φ) Q)
        (motive := fun z => F z b = 0) hy ?_ ?_ ?_
    · intro hQ z hz
      rcases hz with ⟨x, rfl⟩
      exact
        I.twistedBrauerProjection_twistedRelativeTrace_twistedFixedMul
          (k := k) Q hQ x
          (I.twistedInvariantsEquiv (k := k) ψ b)
    · rw [map_zero, LinearMap.zero_apply]
    · intro x y hx hy
      rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
  · rw [map_zero, LinearMap.zero_apply]
  · intro x y hx hy
    rw [map_add, LinearMap.add_apply, hx, hy, add_zero]

/-- The representative product vanishes when its right argument lies
in the Brauer trace submodule. -/
theorem twistedBrauerRepresentativeMul_eq_zero_of_right_mem
    (φ ψ : MulAut P)
    (a :
      invariants
        (I.twistedInteriorRepresentation (k := k) φ))
    (b :
      invariants
        (I.twistedInteriorRepresentation (k := k) ψ))
    (hb :
      b ∈ brauerTraceSubmodule
        (I.twistedInteriorRepresentation (k := k) ψ)) :
    I.twistedBrauerRepresentativeMul (k := k) φ ψ a b =
      0 := by
  let F :=
    I.twistedBrauerRepresentativeMul (k := k) φ ψ
  refine
    Submodule.iSup_induction
      (fun Q : Subgroup P =>
        ⨆ _hQ : Q < ⊤,
          relativeTraceRange
            (I.twistedInteriorRepresentation (k := k) ψ) Q)
      (motive := fun y => F a y = 0) hb ?_ ?_ ?_
  · intro Q y hy
    refine
      Submodule.iSup_induction
        (fun _hQ : Q < ⊤ =>
          relativeTraceRange
            (I.twistedInteriorRepresentation (k := k) ψ) Q)
        (motive := fun z => F a z = 0) hy ?_ ?_ ?_
    · intro hQ z hz
      rcases hz with ⟨x, rfl⟩
      exact
        I.twistedBrauerProjection_twistedFixedMul_twistedRelativeTrace
          (k := k)
          (I.twistedInvariantsEquiv (k := k) φ a)
          Q hQ x
    · exact map_zero (F a)
    · intro x y hx hy
      rw [map_add, hx, hy, add_zero]
  · exact map_zero (F a)
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]

/-- The left Brauer trace submodule lies in the kernel of
representative multiplication. -/
theorem brauerTraceSubmodule_le_twistedBrauerRepresentativeMul_ker
    (φ ψ : MulAut P) :
    brauerTraceSubmodule
        (I.twistedInteriorRepresentation (k := k) φ) ≤
      (I.twistedBrauerRepresentativeMul (k := k) φ ψ).ker := by
  intro a ha
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro b
  exact
    I.twistedBrauerRepresentativeMul_eq_zero_of_left_mem
      (k := k) φ ψ a ha b

/-- The right Brauer trace submodule lies in the kernel of flipped
representative multiplication. -/
theorem brauerTraceSubmodule_le_twistedBrauerRepresentativeMul_flip_ker
    (φ ψ : MulAut P) :
    brauerTraceSubmodule
        (I.twistedInteriorRepresentation (k := k) ψ) ≤
      (I.twistedBrauerRepresentativeMul
        (k := k) φ ψ).flip.ker := by
  intro b hb
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro a
  exact
    I.twistedBrauerRepresentativeMul_eq_zero_of_right_mem
      (k := k) φ ψ a b hb

/-- Bilinear multiplication on twisted Brauer components. -/
def twistedBrauerMul
    (φ ψ : MulAut P) :
    I.TwistedBrauerComponent (k := k) φ →ₗ[k]
      I.TwistedBrauerComponent (k := k) ψ →ₗ[k]
        I.TwistedBrauerComponent (k := k) (φ * ψ) :=
  (I.twistedBrauerRepresentativeMul (k := k) φ ψ).liftQ₂
    (brauerTraceSubmodule
      (I.twistedInteriorRepresentation (k := k) φ))
    (brauerTraceSubmodule
      (I.twistedInteriorRepresentation (k := k) ψ))
    (I.brauerTraceSubmodule_le_twistedBrauerRepresentativeMul_ker
      (k := k) φ ψ)
    (I.brauerTraceSubmodule_le_twistedBrauerRepresentativeMul_flip_ker
      (k := k) φ ψ)

/-- The component product is represented by ordinary multiplication
of twisted fixed representatives. -/
@[simp]
theorem twistedBrauerMul_projection
    (φ ψ : MulAut P)
    (a : I.twistedFixedSubmodule (k := k) φ)
    (b : I.twistedFixedSubmodule (k := k) ψ) :
    I.twistedBrauerMul (k := k) φ ψ
        (I.twistedBrauerProjection (k := k) φ a)
        (I.twistedBrauerProjection (k := k) ψ b) =
      I.twistedBrauerProjection (k := k) (φ * ψ)
        (I.twistedFixedMul (k := k) a b) := by
  rfl

end InteriorAction
end Representation
