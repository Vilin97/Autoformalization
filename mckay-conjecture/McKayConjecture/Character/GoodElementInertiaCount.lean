/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GoodElementClassTransport
import McKayConjecture.CharacterTriple.Inertia

/-!
# Good-element transport for ordinary inertia fibres

Gallagher's theorem applies to an invariant character of a normal subgroup
inside its ambient group.  An inertia fibre is presented using the original
normal subgroup `N`, whereas the appropriate normal subgroup inside
`I_G(θ)` is the canonical internal copy of `N`.

This file packages that harmless but dependent transport.  Its main theorem
reduces equality of two ordinary inertia-fibre cardinalities to a
multiplicative equivalence of the two inertia quotients that preserves the
extension-semantic good-element predicate pointwise.  Thus an
Okuyama--Wajima application only has to prove the pointwise comparison.
-/

noncomputable section

namespace McKayConjecture
namespace CliffordCorrespondence

open CliffordEquivalence

variable {G H : Type} [Group G] [Group H] [Finite G] [Finite H]

/-- A quotient equivalence preserving good elements pointwise gives equality
of the corresponding ordinary inertia-fibre cardinalities. -/
theorem
    natCard_irreducibleCharactersOverInertia_eq_of_goodQuotientElement_mulEquiv
    (N : Subgroup G) [N.Normal]
    (M : Subgroup H) [M.Normal]
    (θ : IrreducibleCharacter N)
    (φ : IrreducibleCharacter M)
    (e :
      IrreducibleCharacter.inertia N θ ⧸
          inertiaNormalCopy N θ ≃*
        IrreducibleCharacter.inertia M φ ⧸
          inertiaNormalCopy M φ)
    (hgood :
      ∀ q :
          IrreducibleCharacter.inertia N θ ⧸
            inertiaNormalCopy N θ,
        IrreducibleCharacter.IsGoodQuotientElement
              (inertiaNormalCopy N θ)
              (inertiaCopyCharacter N θ) q ↔
          IrreducibleCharacter.IsGoodQuotientElement
              (inertiaNormalCopy M φ)
              (inertiaCopyCharacter M φ) (e q)) :
    Nat.card (IrreducibleCharactersOverInertia N θ) =
      Nat.card (IrreducibleCharactersOverInertia M φ) := by
  let eClasses :=
    IrreducibleCharacter.goodQuotientConjugacyClassesEquivOfMulEquiv
      (inertiaNormalCopy N θ)
      (inertiaNormalCopy M φ)
      (inertiaCopyCharacter N θ)
      (inertiaCopyCharacter M φ)
      e hgood
  have hAlong :
      Nat.card
          (IrreducibleCharactersOverAlong
            (inertiaNormalCopy N θ).subtype
            (inertiaCopyCharacter N θ)) =
        Nat.card
          (IrreducibleCharactersOverAlong
            (inertiaNormalCopy M φ).subtype
            (inertiaCopyCharacter M φ)) :=
    natCard_irreducibleCharactersOverAlong_eq_of_goodQuotientConjugacyClassesEquiv
      (inertiaNormalCopy N θ)
      (inertiaNormalCopy M φ)
      (inertiaCopyCharacter N θ)
      (inertiaCopyCharacter M φ)
      (inertiaCopyCharacter_invariant N θ)
      (inertiaCopyCharacter_invariant M φ)
      eClasses
  calc
    Nat.card (IrreducibleCharactersOverInertia N θ) =
        Nat.card
          (IrreducibleCharactersOverAlong
            (inertiaNormalCopy N θ).subtype
            (inertiaCopyCharacter N θ)) :=
      Nat.card_congr
        (CharacterTriple.irreducibleCharactersOverInertiaEquivTriple
          N θ)
    _ =
        Nat.card
          (IrreducibleCharactersOverAlong
            (inertiaNormalCopy M φ).subtype
            (inertiaCopyCharacter M φ)) :=
      hAlong
    _ = Nat.card (IrreducibleCharactersOverInertia M φ) :=
      (Nat.card_congr
        (CharacterTriple.irreducibleCharactersOverInertiaEquivTriple
          M φ)).symm

end CliffordCorrespondence
end McKayConjecture
