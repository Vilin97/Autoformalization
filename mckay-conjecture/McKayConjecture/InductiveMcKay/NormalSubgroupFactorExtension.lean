/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedFiniteFactorQuotient
import McKayConjecture.InductiveMcKay.Condition
import McKayConjecture.InductiveMcKay.NormalSubgroupJoinCenterReduction

/-!
# Finite factor extensions in the normal-subgroup reduction

For a normal noncentral subgroup `N ◁ G`, put `J = N Z(G)`.  Every
`G`-invariant irreducible character of `J` gives a character triple
`(G,J,ζ)`.  Its canonical associated projective representation has a finite
factor set on `G/J`, and hence defines a finite central extension whose
central index is strictly smaller than that of `G`.

This file formalizes the central-index descent at the start of Rossi's
Lemma 4.1.  The subsequent character-fibre transport through the extension
is kept in separate files.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupFactorExtension

open CharacterTriple
open GroupTheory
open NormalSubgroupJoinCenterReduction

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (N : Subgroup G) [N.Normal]

/-- Conjugation invariance of a character of `N Z(G)`, in the exact form
required by `CharacterTriple`. -/
def IsJoinCenterInvariant
    (ζ : IrreducibleCharacter (joinCenter N)) : Prop :=
  ∀ (g : G) (x : joinCenter N),
    ζ.values
        (conjugateNormalElement
          (joinCenter N) inferInstance g x) =
      ζ.values x

/-- The character triple `(G, N Z(G), ζ)` attached to an invariant
irreducible character of the join-center subgroup. -/
def joinCenterTriple
    (ζ : IrreducibleCharacter (joinCenter N))
    (hζ : IsJoinCenterInvariant N ζ) :
    CharacterTriple G where
  normalSubgroup := joinCenter N
  isNormal := inferInstance
  character := ζ
  isInvariant := hζ

@[simp]
theorem joinCenterTriple_normalSubgroup
    (ζ : IrreducibleCharacter (joinCenter N))
    (hζ : IsJoinCenterInvariant N ζ) :
    (joinCenterTriple N ζ hζ).normalSubgroup =
      joinCenter N :=
  rfl

@[simp]
theorem joinCenterTriple_character
    (ζ : IrreducibleCharacter (joinCenter N))
    (hζ : IsJoinCenterInvariant N ζ) :
    (joinCenterTriple N ζ hζ).character = ζ :=
  rfl

/-- The finite factor-extension group attached to an invariant character
of `N Z(G)`. -/
abbrev ExtensionGroup
    (ζ : IrreducibleCharacter (joinCenter N))
    (hζ : IsJoinCenterInvariant N ζ) :=
  AssociatedProjectiveRepresentation.CanonicalFiniteFactorCentralExtensionGroup
    (joinCenterTriple N ζ hζ)

/-- The canonical central extension of `G/(N Z(G))` attached to `ζ`. -/
def centralExtension
    (ζ : IrreducibleCharacter (joinCenter N))
    (hζ : IsJoinCenterInvariant N ζ) :
    CentralExtension
      (ExtensionGroup N ζ hζ)
      (G ⧸ joinCenter N) :=
  AssociatedProjectiveRepresentation.canonicalFiniteFactorCentralExtension
    (joinCenterTriple N ζ hζ)

/-- Noncentrality of `N` makes the factor extension strictly smaller in
central index than `G`. -/
theorem centralIndex_extension_lt
    (hNnoncentral : ¬N ≤ Subgroup.center G)
    (ζ : IrreducibleCharacter (joinCenter N))
    (hζ : IsJoinCenterInvariant N ζ) :
    centralIndex (ExtensionGroup N ζ hζ) <
      centralIndex G := by
  apply
    AssociatedProjectiveRepresentation.canonicalFiniteFactorCentralExtension_centralIndex_lt
      (joinCenterTriple N ζ hζ)
  exact center_lt_joinCenter N hNnoncentral

omit [Fact p.Prime] in
/-- A full central-index induction hypothesis is therefore available on
every Sylow subgroup of the factor extension. -/
theorem extensionLocalDataOfCentralIndexIH
    (hNnoncentral : ¬N ≤ Subgroup.center G)
    (ζ : IrreducibleCharacter (joinCenter N))
    (hζ : IsJoinCenterInvariant N ζ)
    (ih :
      ∀ (H : Type u) [Group H] [Finite H],
        centralIndex H < centralIndex G →
          ∀ Q : Sylow p H,
            Nonempty (LocalInductiveMcKayData Q))
    (Q : Sylow p (ExtensionGroup N ζ hζ)) :
    Nonempty (LocalInductiveMcKayData Q) :=
  ih (ExtensionGroup N ζ hζ)
    (centralIndex_extension_lt N hNnoncentral ζ hζ) Q

end NormalSubgroupFactorExtension
end InductiveMcKay
end McKayConjecture
