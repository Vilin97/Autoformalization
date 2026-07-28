/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.Condition
import McKayConjecture.InductiveMcKay.NormalSubgroupIntermediateEquivariance

/-!
# Full assembly boundary for Rossi's Proposition 4.2

For an `Aut(G)_P`-invariant normal subgroup `N`, Rossi's Proposition 4.2
constructs an equivariant character bijection from `G` to
`N Z(G) N_G(P)` and a central character-triple relation for every matched
pair.  When this intermediate is proper, those data are exactly a
`LocalInductiveMcKayData P`.

This file performs that final packaging.  It deliberately keeps the two
genuine character-theoretic obligations visible: equivariance of the
assembled bijection and the external semidirect character-triple witness.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupProposition42Assembly

open GroupTheory

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (P : Sylow p G) (N : Subgroup G) [N.Normal]
variable
  (hNinvariant :
    AutomorphismInvariant (SylowAutStabilizer P) N)
variable
  (hproper :
    N ⊔ Subgroup.normalizer (P : Set G) ≠ ⊤)

/-- Package an equivariant Proposition-4.2 character equivalence as the
equivariant numerical part of the local inductive McKay datum. -/
def equivariantLocalCorrespondenceOfCharacterEquiv
    (e :
      PPrimeIrreducibleCharacter G p ≃
        PPrimeIrreducibleCharacter
          (NormalSubgroupJoinCenterReduction.normalizerIntermediate
            P N) p)
    (hequivariant :
      let hH :=
        NormalSubgroupJoinCenterReduction.normalizerIntermediate_invariant
          P N hNinvariant
      letI :=
        SylowAutStabilizer.intermediatePPrimeCharacterMulAction
          P
          (NormalSubgroupJoinCenterReduction.normalizerIntermediate
            P N)
          hH p
      ∀ (a : SylowAutStabilizer P)
        (χ : PPrimeIrreducibleCharacter G p),
        e (a • χ) = a • e χ) :
    EquivariantLocalCorrespondence P where
  toLocalCorrespondence :=
    { intermediate :=
        NormalSubgroupJoinCenterReduction.normalizerIntermediate
          P N
      normalizer_le :=
        NormalSubgroupJoinCenterReduction.normalizer_le_normalizerIntermediate
          P N
      proper_of_normalizer_ne_top := fun _ ↦ by
        apply lt_top_iff_ne_top.mpr
        rw [NormalSubgroupJoinCenterReduction.normalizerIntermediate_eq_normal_sup]
        exact hproper
      correspondence := e }
  intermediate_invariant :=
    NormalSubgroupJoinCenterReduction.normalizerIntermediate_invariant
      P N hNinvariant
  map_smul' := hequivariant

/-- Exact full-strength character data delivered by Proposition 4.2 when
its target is proper. -/
structure CharacterData where
  /-- The assembled prime-to-`p` character bijection. -/
  characterEquiv :
    PPrimeIrreducibleCharacter G p ≃
      PPrimeIrreducibleCharacter
        (NormalSubgroupJoinCenterReduction.normalizerIntermediate
          P N) p
  /-- Equivariance under the full Sylow automorphism stabilizer. -/
  characterEquiv_smul :
    let hH :=
      NormalSubgroupJoinCenterReduction.normalizerIntermediate_invariant
        P N hNinvariant
    letI :=
      SylowAutStabilizer.intermediatePPrimeCharacterMulAction
        P
        (NormalSubgroupJoinCenterReduction.normalizerIntermediate
          P N)
        hH p
    ∀ (a : SylowAutStabilizer P)
      (χ : PPrimeIrreducibleCharacter G p),
      characterEquiv (a • χ) =
        a • characterEquiv χ
  /-- Central character-triple compatibility in the canonical external
  semidirect products. -/
  tripleCompatible :
    ∀ χ : PPrimeIrreducibleCharacter G p,
      (equivariantLocalCorrespondenceOfCharacterEquiv
        P N hNinvariant hproper
        characterEquiv characterEquiv_smul).TripleCompatible χ

namespace CharacterData

/-- The equivariant local correspondence underlying full
Proposition-4.2 data. -/
def toEquivariantLocalCorrespondence
    (d : CharacterData P N hNinvariant hproper) :
    EquivariantLocalCorrespondence P :=
  equivariantLocalCorrespondenceOfCharacterEquiv
    P N hNinvariant hproper
      d.characterEquiv d.characterEquiv_smul

/-- A full Proposition-4.2 datum with proper target is a complete local
inductive-McKay datum. -/
def toLocalInductiveMcKayData
    (d : CharacterData P N hNinvariant hproper) :
    LocalInductiveMcKayData P where
  toEquivariantLocalCorrespondence :=
    d.toEquivariantLocalCorrespondence
  triple_compatible := d.tripleCompatible

@[simp]
theorem toLocalInductiveMcKayData_toEquivariant
    (d : CharacterData P N hNinvariant hproper) :
    d.toLocalInductiveMcKayData.toEquivariant =
      d.toEquivariantLocalCorrespondence :=
  rfl

end CharacterData
end NormalSubgroupProposition42Assembly
end InductiveMcKay
end McKayConjecture
