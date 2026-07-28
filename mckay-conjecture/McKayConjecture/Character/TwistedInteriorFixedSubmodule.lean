/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InteriorFaithfulNormalizerAction

/-!
# Twisted fixed submodules for an interior action

Let `P` act on a `k`-algebra `A` through an interior action `I`.
For an automorphism `φ` of `P`, the `φ`-twisted fixed submodule consists
of the elements `a` satisfying

`a I(g) = I(φ(g)) a`

for every `g`.  These submodules multiply according to composition of
automorphisms.  Moreover, when the interior action is faithful, every
unit normalizing `I(P)` belongs to the component indexed by its induced
automorphism of `P`.

This is the elementary graded-algebra layer underlying the extended
Brauer quotient used in Puig's local extension theorem.  No quotient by
relative traces is taken in this file.
-/

noncomputable section

namespace Representation
namespace InteriorAction

variable {k P A : Type}
variable [CommRing k] [Group P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A]

variable (I : InteriorAction (P := P) (A := A))

/-- The elements of an interior algebra intertwining the implementing
action with its twist by `φ`. -/
def twistedFixedSubmodule (φ : MulAut P) : Submodule k A where
  carrier :=
    {a | ∀ g : P,
      a * (I.unit g : A) =
        (I.unit (φ g) : A) * a}
  zero_mem' g := by simp
  add_mem' ha hb g := by
    rw [add_mul, mul_add, ha g, hb g]
  smul_mem' r a ha g := by
    simp only [Algebra.smul_def]
    calc
      (algebraMap k A r * a) * (I.unit g : A) =
          algebraMap k A r * (a * (I.unit g : A)) := by
            rw [mul_assoc]
      _ = algebraMap k A r *
          ((I.unit (φ g) : A) * a) := by rw [ha g]
      _ = (I.unit (φ g) : A) *
          (algebraMap k A r * a) := by
            rw [← mul_assoc,
              Algebra.commutes r (I.unit (φ g) : A),
              mul_assoc]

@[simp]
theorem mem_twistedFixedSubmodule
    (φ : MulAut P)
    (a : A) :
    a ∈ I.twistedFixedSubmodule (k := k) φ ↔
      ∀ g : P,
        a * (I.unit g : A) =
          (I.unit (φ g) : A) * a :=
  Iff.rfl

/-- The identity component consists precisely of the elements
centralizing all implementing units. -/
theorem mem_twistedFixedSubmodule_one_iff
    (a : A) :
    a ∈ I.twistedFixedSubmodule (k := k) 1 ↔
      ∀ g : P, Commute a (I.unit g : A) := by
  simp only [mem_twistedFixedSubmodule (k := k),
    MulAut.one_apply, commute_iff_eq]

/-- Multiplication sends the `φ`- and `ψ`-components into the
`φ * ψ`-component. -/
theorem mul_mem_twistedFixedSubmodule
    {φ ψ : MulAut P}
    {a b : A}
    (ha : a ∈ I.twistedFixedSubmodule (k := k) φ)
    (hb : b ∈ I.twistedFixedSubmodule (k := k) ψ) :
    a * b ∈ I.twistedFixedSubmodule (k := k) (φ * ψ) := by
  rw [mem_twistedFixedSubmodule (k := k)] at ha hb ⊢
  intro g
  calc
    (a * b) * (I.unit g : A) =
        a * (b * (I.unit g : A)) := by rw [mul_assoc]
    _ = a * ((I.unit (ψ g) : A) * b) := by rw [hb g]
    _ = (a * (I.unit (ψ g) : A)) * b := by rw [mul_assoc]
    _ = ((I.unit (φ (ψ g)) : A) * a) * b := by
      rw [ha (ψ g)]
    _ = (I.unit ((φ * ψ) g) : A) * (a * b) := by
      simp [mul_assoc]

/-- Multiplication as a map of underlying sets between twisted
components.  Bilinearity is recorded separately when needed. -/
def twistedFixedMul
    {φ ψ : MulAut P}
    (a : I.twistedFixedSubmodule (k := k) φ)
    (b : I.twistedFixedSubmodule (k := k) ψ) :
    I.twistedFixedSubmodule (k := k) (φ * ψ) :=
  ⟨(a : A) * (b : A),
    I.mul_mem_twistedFixedSubmodule a.property b.property⟩

@[simp]
theorem coe_twistedFixedMul
    {φ ψ : MulAut P}
    (a : I.twistedFixedSubmodule (k := k) φ)
    (b : I.twistedFixedSubmodule (k := k) ψ) :
    (I.twistedFixedMul (k := k) a b : A) =
      (a : A) * (b : A) :=
  rfl

/-- Bilinear multiplication between twisted fixed components. -/
def twistedFixedMulLinear
    (φ ψ : MulAut P) :
    I.twistedFixedSubmodule (k := k) φ →ₗ[k]
      I.twistedFixedSubmodule (k := k) ψ →ₗ[k]
        I.twistedFixedSubmodule (k := k) (φ * ψ) :=
  LinearMap.mk₂ k
    (I.twistedFixedMul (k := k))
    (fun a b c => by
      apply Subtype.ext
      exact add_mul (a : A) (b : A) (c : A))
    (fun r a b => by
      apply Subtype.ext
      simp [Algebra.smul_def, mul_assoc])
    (fun a b c => by
      apply Subtype.ext
      exact mul_add (a : A) (b : A) (c : A))
    (fun r a b => by
      apply Subtype.ext
      simp only [twistedFixedMul,
        Submodule.coe_smul_of_tower, Algebra.smul_def]
      calc
        (a : A) * (algebraMap k A r * (b : A)) =
            ((a : A) * algebraMap k A r) * (b : A) := by
          rw [mul_assoc]
        _ =
            (algebraMap k A r * (a : A)) * (b : A) := by
          rw [(Algebra.commutes r (a : A)).symm]
        _ =
            algebraMap k A r * ((a : A) * (b : A)) := by
          rw [mul_assoc])

@[simp]
theorem twistedFixedMulLinear_apply
    (φ ψ : MulAut P)
    (a : I.twistedFixedSubmodule (k := k) φ)
    (b : I.twistedFixedSubmodule (k := k) ψ) :
    I.twistedFixedMulLinear (k := k) φ ψ a b =
      I.twistedFixedMul (k := k) a b :=
  rfl

/-- A normalizing unit, regarded as an element of the ambient algebra,
lies in the component indexed by the automorphism it induces on a
faithfully represented interior group. -/
theorem coe_unitNormalizer_mem_twistedFixedSubmodule
    (hI : Function.Injective I.unit)
    (s : I.unitNormalizer) :
    (((s : Aˣ) : A)) ∈
      I.twistedFixedSubmodule (k := k)
        (I.normalizerMulAut hI s) := by
  rw [mem_twistedFixedSubmodule (k := k)]
  intro g
  have h :
      (s : Aˣ) * I.unit g =
        I.unit (I.normalizerMulAut hI s g) * (s : Aˣ) := by
    rw [I.unit_normalizerMulAut]
    simp [mul_assoc]
  change
    ((s : Aˣ) : A) * (I.unit g : A) =
      (I.unit (I.normalizerMulAut hI s g) : A) *
        ((s : Aˣ) : A)
  exact congrArg (Units.coeHom A) h

end InteriorAction
end Representation
