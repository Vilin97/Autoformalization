/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Transport
import McKayConjecture.Statement

/-!
# Character correspondences and the McKay equality

The reduction theorems used in the proof of the McKay conjecture construct
equivariant bijections, which are stronger than the final cardinal equality.
This file isolates the elementary, reusable last step from such a bijection to
`McKayConjecture.Statement`.
-/

noncomputable section

universe u v w

namespace McKayConjecture

variable {G : Type u} {H : Type v} {K : Type w}
variable [Group G] [Group H] [Group K]

/-- A bijection between the irreducible characters of `p'`-degree of two
groups.  Later files attach equivariance and character-triple compatibility to
this core datum. -/
abbrev PPrimeCorrespondence (p : ℕ)
    (G : Type u) (H : Type v)
    [Group G] [Group H] :=
  PPrimeIrreducibleCharacter G p ≃ PPrimeIrreducibleCharacter H p

namespace PPrimeCorrespondence

/-- The identity `p'`-character correspondence. -/
def refl (p : ℕ) (G : Type u) [Group G] :
    PPrimeCorrespondence p G G :=
  Equiv.refl _

/-- Reverse a `p'`-character correspondence. -/
def symm {p : ℕ} (f : PPrimeCorrespondence p G H) :
    PPrimeCorrespondence p H G :=
  Equiv.symm f

/-- Compose two `p'`-character correspondences. -/
def trans {p : ℕ} (f : PPrimeCorrespondence p G H)
    (g : PPrimeCorrespondence p H K) :
    PPrimeCorrespondence p G K :=
  Equiv.trans f g

/-- A group isomorphism gives a `p'`-character correspondence. -/
def ofMulEquiv (p : ℕ) (e : H ≃* G) :
    PPrimeCorrespondence p G H :=
  IrreducibleCharacter.pPrimeComapEquiv p e

/-- A `p'`-character correspondence implies equality of the corresponding
cardinals. -/
theorem cardinal_eq {p : ℕ}
    {G₀ H₀ : Type u} [Group G₀] [Group H₀]
    (f : PPrimeCorrespondence p G₀ H₀) :
    Cardinal.mk (PPrimeIrreducibleCharacter G₀ p) =
      Cardinal.mk (PPrimeIrreducibleCharacter H₀ p) :=
  Cardinal.mk_congr f

end PPrimeCorrespondence

/-- The bijection whose existence is stronger than the McKay cardinal
equality for the fixed Sylow subgroup `P`. -/
abbrev McKayCorrespondence (G : Type u) [Group G] (p : ℕ)
    (P : Sylow p G) :=
  PPrimeCorrespondence p G (SylowNormalizer P)

namespace Statement

/-- Discharge the stated McKay equality from an explicit character
correspondence. -/
theorem of_correspondence [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Sylow p G} (f : McKayCorrespondence G p P) :
    Statement G p P :=
  PPrimeCorrespondence.cardinal_eq f

end Statement

end McKayConjecture
