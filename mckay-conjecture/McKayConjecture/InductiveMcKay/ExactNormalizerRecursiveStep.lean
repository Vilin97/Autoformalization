/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralIsomorphismHomPullback
import McKayConjecture.InductiveMcKay.EquivariantTransport
import McKayConjecture.InductiveMcKay.ExactNormalizerData

/-!
# Recursive exact-normalizer composition

This file strengthens the elementary normalizer-induction step from a bare
character equivalence to an equivariant equivalence, and isolates the sole
extra input needed to retain central character-triple compatibility.

Let `N` be an `Aut(G)_P`-invariant intermediate subgroup containing
`N_G(P)`, and regard `P` as a Sylow subgroup `P_N` of `N`.  An
exact-normalizer datum for `(N,P_N)` supplies a correspondence with
`N_N(P_N)`.  The canonical isomorphism

`N_N(P_N) ≃ N_G(P)`

transports its output to the desired ambient normalizer.  Equivariance of
this composite is proved below, including the required compatibility of the
two normalizer actions.

For character triples, the induction-hypothesis witness is initially indexed
by the full stabilizer inside `Aut(N)_{P_N}`, whereas composition needs its
pullback along the restriction homomorphism from `Aut(G)_P`.  The structure
`RestrictedExactNormalizerCompatibility` records exactly that pulled-back
witness and its canonical embedding.  Once it is supplied, strict automatic
transitivity composes it with the local witness without any further
projective-representation coherence assumption.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple

variable {G : Type u} [Group G] [Finite G] {p : ℕ}
variable {P : Sylow p G}

namespace EquivariantLocalCorrespondence

/-- The ambient Sylow subgroup, regarded inside the intermediate subgroup. -/
abbrev intermediateSylow
    (d : EquivariantLocalCorrespondence P) :
    Sylow p d.intermediate :=
  sylowIn P d.intermediate
    (Subgroup.le_normalizer.trans d.normalizer_le)

/-- The canonical isomorphism from the Sylow normalizer computed in the
intermediate subgroup to the ambient Sylow normalizer. -/
def intermediateNormalizerEquiv
    (d : EquivariantLocalCorrespondence P) :
    SylowNormalizer d.intermediateSylow ≃*
      SylowNormalizer P :=
  normalizerInEquivNormalizer P d.intermediate
    (Subgroup.le_normalizer.trans d.normalizer_le)
    d.normalizer_le

/-- Restriction of an ambient Sylow-stabilizing automorphism to the
intermediate subgroup still stabilizes the Sylow subgroup there. -/
def intermediateSylowAutHom
    (d : EquivariantLocalCorrespondence P) :
    SylowAutStabilizer P →*
      SylowAutStabilizer d.intermediateSylow where
  toFun a :=
    ⟨SylowAutStabilizer.intermediateRestrictionHom
        P d.intermediate d.intermediate_invariant a, by
      rw [SylowAutStabilizer.mem_iff]
      apply Sylow.ext
      change
        ((P : Subgroup G).subgroupOf d.intermediate).map
            (SylowAutStabilizer.intermediateRestrictionHom
              P d.intermediate d.intermediate_invariant a :
                d.intermediate →* d.intermediate) =
          (P : Subgroup G).subgroupOf d.intermediate
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_map] at hx
        obtain ⟨y, hy, hxy⟩ := hx
        have hay :
            a.1 y.1 ∈ (P : Subgroup G).map (a.1 : G →* G) :=
          ⟨y.1, hy, rfl⟩
        rw [SylowAutStabilizer.map_sylow_eq a] at hay
        change x.1 ∈ (P : Subgroup G)
        simpa only using hxy ▸ hay
      · intro hx
        have hxImage :
            x.1 ∈ (P : Subgroup G).map (a.1 : G →* G) := by
          rw [SylowAutStabilizer.map_sylow_eq a]
          exact hx
        obtain ⟨y, hy, hayx⟩ := hxImage
        let yN : d.intermediate :=
          ⟨y, (Subgroup.le_normalizer.trans d.normalizer_le) hy⟩
        refine ⟨yN, hy, ?_⟩
        apply Subtype.ext
        exact hayx⟩
  map_one' := by
    apply Subtype.ext
    ext x
    rfl
  map_mul' a b := by
    apply Subtype.ext
    ext x
    rfl

@[simp]
theorem intermediateSylowAutHom_apply_coe
    (d : EquivariantLocalCorrespondence P)
    (a : SylowAutStabilizer P) :
    (d.intermediateSylowAutHom a).1 =
      SylowAutStabilizer.intermediateRestrictionHom
        P d.intermediate d.intermediate_invariant a :=
  rfl

/-- The canonical normalizer isomorphism intertwines the normalizer
restrictions of the ambient automorphism and its restriction to the
intermediate subgroup. -/
theorem intermediateNormalizerEquiv_congr_restriction
    (d : EquivariantLocalCorrespondence P)
    (a : SylowAutStabilizer P) :
    MulAut.congr d.intermediateNormalizerEquiv
        (SylowAutStabilizer.normalizerRestrictionHom
          d.intermediateSylow
          (d.intermediateSylowAutHom a)) =
      SylowAutStabilizer.normalizerRestrictionHom P a := by
  ext x
  rfl

/-- Character transport across the canonical normalizer isomorphism
intertwines the two restricted automorphism actions. -/
theorem intermediateNormalizerTransport_smul
    (d : EquivariantLocalCorrespondence P)
    (a : SylowAutStabilizer P)
    (ψ : PPrimeIrreducibleCharacter
      (SylowNormalizer d.intermediateSylow) p) :
    IrreducibleCharacter.pPrimeComapEquiv p
        d.intermediateNormalizerEquiv.symm
        ((d.intermediateSylowAutHom a) • ψ) =
      a •
        IrreducibleCharacter.pPrimeComapEquiv p
          d.intermediateNormalizerEquiv.symm ψ := by
  change
    IrreducibleCharacter.pPrimeComapEquiv p
        d.intermediateNormalizerEquiv.symm
        ((SylowAutStabilizer.normalizerRestrictionHom
          d.intermediateSylow
          (d.intermediateSylowAutHom a)) • ψ) =
      (SylowAutStabilizer.normalizerRestrictionHom P a) •
        IrreducibleCharacter.pPrimeComapEquiv p
          d.intermediateNormalizerEquiv.symm ψ
  rw [pPrimeComapEquiv_symm_smul,
    d.intermediateNormalizerEquiv_congr_restriction a]

/-- Restriction sends the stabilizer of an ambient character to the
stabilizer of its local correspondent inside the intermediate subgroup. -/
def intermediateCharacterStabilizerHom
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p) :
    PPrimeCharacterStabilizer P χ →*
      PPrimeCharacterStabilizer d.intermediateSylow
        (d.localCharacter χ) where
  toFun a :=
    ⟨d.intermediateSylowAutHom a.1, by
      rw [PPrimeCharacterStabilizer.mem_iff]
      letI := d.intermediateCharacterMulAction
      have hsource : a.1 • χ = χ :=
        MulAction.mem_stabilizer_iff.mp a.2
      have hlocal := d.map_smul a.1 χ
      rw [hsource] at hlocal
      change
        (SylowAutStabilizer.intermediateRestrictionHom
          P d.intermediate d.intermediate_invariant a.1) •
            d.localCharacter χ =
          d.localCharacter χ
      exact hlocal.symm⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' a b := by
    apply Subtype.ext
    rfl

@[simp]
theorem intermediateCharacterStabilizerHom_apply_coe
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p)
    (a : PPrimeCharacterStabilizer P χ) :
    (d.intermediateCharacterStabilizerHom χ a).1 =
      d.intermediateSylowAutHom a.1 :=
  rfl

/-- The homomorphism from the outer intermediate semidirect product to the
semidirect product indexed by the full inner character stabilizer. -/
def intermediateSemidirectToInner
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p) :
    (d.intermediate ⋊[d.stabilizerIntermediateAction χ]
      PPrimeCharacterStabilizer P χ) →*
      (d.intermediate ⋊[
          PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer d.intermediateSylow
          (d.localCharacter χ)) :=
  SemidirectProduct.map (MonoidHom.id d.intermediate)
    (d.intermediateCharacterStabilizerHom χ) (by
      intro a
      ext x
      rfl)

@[simp]
theorem intermediateSemidirectToInner_left
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p)
    (x : d.intermediate ⋊[d.stabilizerIntermediateAction χ]
      PPrimeCharacterStabilizer P χ) :
    (d.intermediateSemidirectToInner χ x).left = x.left :=
  rfl

@[simp]
theorem intermediateSemidirectToInner_right
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p)
    (x : d.intermediate ⋊[d.stabilizerIntermediateAction χ]
      PPrimeCharacterStabilizer P χ) :
    (d.intermediateSemidirectToInner χ x).right =
      d.intermediateCharacterStabilizerHom χ x.right :=
  rfl

end EquivariantLocalCorrespondence

namespace ExactNormalizerRecursiveStep

variable
  (d : EquivariantLocalCorrespondence P)
  (e : ExactNormalizerInductiveMcKayData d.intermediateSylow)

/-- The action of the outer character stabilizer on the normalizer computed
inside the intermediate subgroup. -/
def localNormalizerAction
    (χ : PPrimeIrreducibleCharacter G p) :
    PPrimeCharacterStabilizer P χ →*
      MulAut (SylowNormalizer d.intermediateSylow) :=
  (PPrimeCharacterStabilizer.normalizerAction
    (P := d.intermediateSylow)
    (χ := d.localCharacter χ)).comp
      (d.intermediateCharacterStabilizerHom χ)

/-- The inner exact-normalizer character is invariant under the restricted
outer stabilizer action. -/
theorem localNormalizerCharacter_invariant
    (χ : PPrimeIrreducibleCharacter G p) :
    CharacterTriple.IsInvariant
      (localNormalizerAction d χ)
      (e.toEquivariant (d.localCharacter χ)).1 := by
  intro a x
  exact
    e.toEquivariant.normalizerCharacter_invariant
      (d.localCharacter χ)
      (d.intermediateCharacterStabilizerHom χ a) x

/-- The inner exact-normalizer triple after restricting its automorphism
stabilizer along the ambient restriction homomorphism. -/
abbrev localNormalizerTriple
    (χ : PPrimeIrreducibleCharacter G p) :
    CharacterTriple
      (SylowNormalizer d.intermediateSylow ⋊[
          localNormalizerAction d χ]
        PPrimeCharacterStabilizer P χ) :=
  CharacterTriple.ofSemidirect
    (localNormalizerAction d χ)
    (e.toEquivariant (d.localCharacter χ)).1
    (localNormalizerCharacter_invariant d e χ)

/-- The homomorphism from the restricted local-normalizer semidirect product
to the one indexed by the full inner character stabilizer. -/
def localNormalizerSemidirectToInner
    (χ : PPrimeIrreducibleCharacter G p) :
    (SylowNormalizer d.intermediateSylow ⋊[
        localNormalizerAction d χ]
      PPrimeCharacterStabilizer P χ) →*
      (SylowNormalizer d.intermediateSylow ⋊[
          PPrimeCharacterStabilizer.normalizerAction]
        PPrimeCharacterStabilizer d.intermediateSylow
          (d.localCharacter χ)) :=
  SemidirectProduct.map
    (MonoidHom.id (SylowNormalizer d.intermediateSylow))
    (d.intermediateCharacterStabilizerHom χ) (by
      intro a
      ext x
      rfl)

@[simp]
theorem localNormalizerSemidirectToInner_left
    (χ : PPrimeIrreducibleCharacter G p)
    (x : SylowNormalizer d.intermediateSylow ⋊[
        localNormalizerAction d χ]
      PPrimeCharacterStabilizer P χ) :
    (localNormalizerSemidirectToInner d χ x).left = x.left :=
  rfl

@[simp]
theorem localNormalizerSemidirectToInner_right
    (χ : PPrimeIrreducibleCharacter G p)
    (x : SylowNormalizer d.intermediateSylow ⋊[
        localNormalizerAction d χ]
      PPrimeCharacterStabilizer P χ) :
    (localNormalizerSemidirectToInner d χ x).right =
      d.intermediateCharacterStabilizerHom χ x.right :=
  rfl


/-- The recursive character equivalence: first use the local
correspondence, then the exact-normalizer correspondence inside the
intermediate subgroup, and finally transport to the ambient normalizer. -/
def characterEquiv :
    PPrimeIrreducibleCharacter G p ≃
      PPrimeIrreducibleCharacter (SylowNormalizer P) p :=
  d.correspondence.trans
    (e.toEquivariant.toEquiv.trans
      (IrreducibleCharacter.pPrimeComapEquiv p
        d.intermediateNormalizerEquiv).symm)

/-- The recursive character equivalence is equivariant under
`Aut(G)_P`. -/
theorem characterEquiv_map_smul :
    IsEquivariantMcKayEquiv P (characterEquiv d e) := by
  letI := d.intermediateCharacterMulAction
  intro a χ
  change
    IrreducibleCharacter.pPrimeComapEquiv p
        d.intermediateNormalizerEquiv.symm
        (e.toEquivariant
          (d.correspondence (a • χ))) =
      a •
        IrreducibleCharacter.pPrimeComapEquiv p
          d.intermediateNormalizerEquiv.symm
          (e.toEquivariant (d.correspondence χ))
  rw [d.map_smul a χ]
  change
    IrreducibleCharacter.pPrimeComapEquiv p
        d.intermediateNormalizerEquiv.symm
        (e.toEquivariant
          ((d.intermediateSylowAutHom a) •
            d.correspondence χ)) =
      _
  rw [e.toEquivariant.map_smul]
  exact d.intermediateNormalizerTransport_smul a
    (e.toEquivariant (d.correspondence χ))

/-- The recursively composed equivariant correspondence to the exact
normalizer. -/
def equivariantEquiv :
    EquivariantMcKayEquiv P where
  toEquiv := characterEquiv d e
  map_smul' := characterEquiv_map_smul d e

end ExactNormalizerRecursiveStep

end InductiveMcKay
end McKayConjecture
