/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Sylow
import McKayConjecture.IrreducibleCharacter

/-!
# The McKay conjecture

This file states the McKay conjecture for ordinary irreducible complex
characters.  The cardinal equality is used directly, so its meaning does not
silently collapse to `0 = 0` if a finiteness instance has not yet been built.
-/

noncomputable section

universe u

namespace McKayConjecture

variable {G : Type u} [Group G]

/-- The normalizer `N_G(P)` of a Sylow subgroup, regarded as a group in its own right. -/
abbrev SylowNormalizer {p : ℕ} (P : Sylow p G) : Type u :=
  Subgroup.normalizer (P : Set G)

/-- The statement of the McKay conjecture for a finite group `G`, a prime `p`,
and a Sylow `p`-subgroup `P`.

It asserts that the irreducible complex characters of `G` whose degrees are
not divisible by `p` and those of `N_G(P)` have the same cardinality.
-/
def Statement (G : Type u) [Finite G] [Group G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) : Prop :=
  Cardinal.mk (PPrimeIrreducibleCharacter G p) =
    Cardinal.mk (PPrimeIrreducibleCharacter (SylowNormalizer P) p)

end McKayConjecture
