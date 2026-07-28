/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InternalNormalTransport
import McKayConjecture.GroupTheory.IntermediateQuotientSylowNormalizer
import McKayConjecture.InductiveMcKay.NormalSubgroupJoinCenterReduction

/-!
# Inertia groups in Rossi's normalizer intermediate

Let `J = N Z(G)` and `H = J N_G(P)`.  If a prime-to-`p` character
`θ ∈ Irr(J)` is fixed by `P`, transport `θ` along the identity-on-elements
equivalence from `J` to its internal copy in `H`.

The inertia group of the transported character in `H` is canonically
isomorphic to the full preimage in `I_G(θ)` of the normalizer of the image
of `P` in `I_G(θ) / J`.  Both sides consist of the same ambient elements;
the equivalence below records that fact with exact coercion lemmas.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupIntermediateInertia

open GroupTheory

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (P : Sylow p G)
variable (N : Subgroup G) [N.Normal]

/-- The join-center subgroup used in Rossi's first reduction. -/
abbrev joinCenter : Subgroup G :=
  NormalSubgroupJoinCenterReduction.joinCenter N

/-- Rossi's intermediate subgroup `J N_G(P)`. -/
abbrev intermediate : Subgroup G :=
  NormalSubgroupJoinCenterReduction.normalizerIntermediate P N

/-- The canonical internal copy of `J` in `J N_G(P)`. -/
abbrev internalJoinCenter : Subgroup (intermediate P N) :=
  IrreducibleCharacter.internalNormal
    (joinCenter N) (intermediate P N)

/-- Prime-to-`p` characters of `J`, transported to its internal copy in
`J N_G(P)`. -/
abbrev internalCharacterEquiv :
    PPrimeIrreducibleCharacter (joinCenter N) p ≃
      PPrimeIrreducibleCharacter (internalJoinCenter P N) p :=
  IrreducibleCharacter.internalNormalPPrimeEquiv
    (joinCenter N) (intermediate P N)
    (NormalSubgroupJoinCenterReduction.joinCenter_le_normalizerIntermediate
      P N)
    p

/-- The inertia group in `G` of a character of `J`. -/
abbrev sourceInertia
    (θ : PPrimeIrreducibleCharacter (joinCenter N) p) :
    Subgroup G :=
  IrreducibleCharacter.inertia (joinCenter N) θ.1

/-- The inertia group in `J N_G(P)` of the transported character. -/
abbrev targetInertia
    (θ : PPrimeIrreducibleCharacter (joinCenter N) p) :
    Subgroup (intermediate P N) :=
  IrreducibleCharacter.inertia
    (internalJoinCenter P N)
    (internalCharacterEquiv P N θ).1

/-- The full preimage in `I_G(θ)` of the normalizer of the image of `P`
in the inertia quotient. -/
abbrev quotientNormalizerPreimage
    (θ : PPrimeIrreducibleCharacter (joinCenter N) p)
    (hP : (P : Subgroup G) ≤ sourceInertia N θ) :
    Subgroup (sourceInertia N θ) :=
  GroupTheory.intermediateQuotientNormalizerPreimage
    (sourceInertia N θ) (joinCenter N) P
    (IrreducibleCharacter.subgroup_le_inertia
      (joinCenter N) θ.1)
    hP

/-- The target inertia group and the quotient-normalizer preimage have
the same elements of `G`.  This is the canonical identity-on-elements
group equivalence between them. -/
def targetInertiaEquivQuotientNormalizerPreimage
    (θ : PPrimeIrreducibleCharacter (joinCenter N) p)
    (hP : (P : Subgroup G) ≤ sourceInertia N θ) :
    targetInertia P N θ ≃*
      quotientNormalizerPreimage P N θ hP where
  toFun b := by
    let h : intermediate P N :=
      (b : intermediate P N)
    have hsource :
        (h : G) ∈ sourceInertia N θ := by
      have hb :
          h ∈
            (sourceInertia N θ).comap
              (intermediate P N).subtype := by
        rw [←
          IrreducibleCharacter.inertia_internalNormalPPrimeEquiv_eq_comap
            (joinCenter N) (intermediate P N)
            (NormalSubgroupJoinCenterReduction.joinCenter_le_normalizerIntermediate
              P N)
            p θ]
        exact b.property
      exact hb
    let i : sourceInertia N θ :=
      ⟨(h : G), hsource⟩
    refine ⟨i, ?_⟩
    change
      i ∈
        GroupTheory.intermediateQuotientNormalizerPreimage
          (sourceInertia N θ) (joinCenter N) P
          (IrreducibleCharacter.subgroup_le_inertia
            (joinCenter N) θ.1)
          hP
    rw [
      GroupTheory.intermediateQuotientNormalizerPreimage_eq_subgroupOf
        (sourceInertia N θ) (joinCenter N) P
        (IrreducibleCharacter.subgroup_le_inertia
          (joinCenter N) θ.1)
        hP]
    exact ⟨hsource, h.property⟩
  invFun x := by
    let i : sourceInertia N θ :=
      (x : sourceInertia N θ)
    have hx :
        (i : G) ∈
          sourceInertia N θ ⊓ intermediate P N := by
      have hx' :
          (i : sourceInertia N θ) ∈
            GroupTheory.intermediateQuotientNormalizerPreimage
              (sourceInertia N θ) (joinCenter N) P
              (IrreducibleCharacter.subgroup_le_inertia
                (joinCenter N) θ.1)
              hP :=
        x.property
      rw [
        GroupTheory.intermediateQuotientNormalizerPreimage_eq_subgroupOf
          (sourceInertia N θ) (joinCenter N) P
          (IrreducibleCharacter.subgroup_le_inertia
            (joinCenter N) θ.1)
          hP] at hx'
      exact hx'
    let h : intermediate P N :=
      ⟨(i : G), hx.2⟩
    refine ⟨h, ?_⟩
    change
      h ∈
        IrreducibleCharacter.inertia
          (IrreducibleCharacter.internalNormal
            (joinCenter N) (intermediate P N))
          ((IrreducibleCharacter.internalNormalPPrimeEquiv
            (joinCenter N) (intermediate P N)
            (NormalSubgroupJoinCenterReduction.joinCenter_le_normalizerIntermediate
              P N)
            p) θ).1
    rw [
      IrreducibleCharacter.inertia_internalNormalPPrimeEquiv_eq_comap
        (joinCenter N) (intermediate P N)
        (NormalSubgroupJoinCenterReduction.joinCenter_le_normalizerIntermediate
          P N)
        p θ]
    exact hx.1
  left_inv b := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl
  map_mul' b c := by
    apply Subtype.ext
    rfl

@[simp]
theorem targetInertiaEquivQuotientNormalizerPreimage_apply_coe
    (θ : PPrimeIrreducibleCharacter (joinCenter N) p)
    (hP : (P : Subgroup G) ≤ sourceInertia N θ)
    (b : targetInertia P N θ) :
    (((targetInertiaEquivQuotientNormalizerPreimage
          P N θ hP b :
        quotientNormalizerPreimage P N θ hP) :
      sourceInertia N θ) :
      G) =
        (((b : targetInertia P N θ) :
          intermediate P N) :
          G) :=
  by
    change
      (((targetInertiaEquivQuotientNormalizerPreimage
            P N θ hP b :
          quotientNormalizerPreimage P N θ hP) :
        sourceInertia N θ) :
        G) =
          (((b : targetInertia P N θ) :
            intermediate P N) :
            G)
    rfl

@[simp]
theorem targetInertiaEquivQuotientNormalizerPreimage_symm_apply_coe
    (θ : PPrimeIrreducibleCharacter (joinCenter N) p)
    (hP : (P : Subgroup G) ≤ sourceInertia N θ)
    (x : quotientNormalizerPreimage P N θ hP) :
    ((((targetInertiaEquivQuotientNormalizerPreimage
          P N θ hP).symm x :
        targetInertia P N θ) :
      intermediate P N) :
      G) =
        (((x : quotientNormalizerPreimage P N θ hP) :
          sourceInertia N θ) :
          G) := by
  rfl

end NormalSubgroupIntermediateInertia
end InductiveMcKay
end McKayConjecture
