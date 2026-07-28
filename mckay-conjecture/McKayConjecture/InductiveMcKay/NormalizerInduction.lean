/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Transport
import McKayConjecture.InductiveMcKay.Normalizer

/-!
# The abstract normalizer-induction step

Normalizer induction composes three correspondences:

1. a local correspondence from the ambient group to a proper intermediate
   subgroup;
2. the induction-hypothesis correspondence inside that subgroup;
3. transport across the canonical isomorphism between its local normalizer and
   the ambient normalizer.

Only the first two are representation-theoretic inputs.  This file derives the
third from group-isomorphism transport and deliberately does not postulate any
of the deep character-theoretic correspondences used in the proof of the
McKay conjecture.
-/

noncomputable section

universe u v

namespace McKayConjecture.InductiveMcKay

/-- Three composable correspondences forming one abstract normalizer-induction
step.  Keeping the types independent makes this usable before functoriality of
the eventual character model has been developed. -/
structure CorrespondenceStep (ambient intermediate localNormalizer ambientNormalizer : Type v)
    where
  /-- The local correspondence from the ambient object set to the
  intermediate one. -/
  ambientToIntermediate : ambient ≃ intermediate
  /-- The result supplied by induction inside the proper intermediate
  subgroup. -/
  intermediateToLocalNormalizer : intermediate ≃ localNormalizer
  /-- Transport from the normalizer computed inside the intermediate subgroup
  to the ambient normalizer. -/
  localNormalizerToAmbientNormalizer : localNormalizer ≃ ambientNormalizer

namespace CorrespondenceStep

/-- Compose the local correspondence, the induction hypothesis, and
normalizer transport. -/
def equiv {ambient intermediate localNormalizer ambientNormalizer : Type v}
    (step : CorrespondenceStep ambient intermediate localNormalizer ambientNormalizer) :
    ambient ≃ ambientNormalizer :=
  step.ambientToIntermediate.trans
    (step.intermediateToLocalNormalizer.trans step.localNormalizerToAmbientNormalizer)

/-- Cardinal equality obtained from an abstract normalizer-induction step. -/
theorem cardinalMk_eq {ambient intermediate localNormalizer ambientNormalizer : Type v}
    (step : CorrespondenceStep ambient intermediate localNormalizer ambientNormalizer) :
    Cardinal.mk ambient = Cardinal.mk ambientNormalizer :=
  Cardinal.mk_congr step.equiv

end CorrespondenceStep

variable {G : Type u} [Finite G] [Group G] {p : ℕ}

/-- The two character correspondences required at a proper intermediate
subgroup `N` containing `N_G(P)`.

The field `intermediateToLocalNormalizer` is precisely the induction
hypothesis for `N`.  Its legitimacy is witnessed by `proper`, because
`Nat.card N < Nat.card G`.
-/
structure CharacterCorrespondenceStep (P : Sylow p G) where
  /-- The proper intermediate subgroup. -/
  intermediate : Subgroup G
  /-- The intermediate subgroup contains the ambient normalizer, hence also
  `P`. -/
  normalizer_le : Subgroup.normalizer (P : Set G) ≤ intermediate
  /-- The intermediate subgroup is proper. -/
  proper : intermediate < ⊤
  /-- The local character correspondence from `G` to the intermediate
  subgroup. -/
  ambientToIntermediate :
    PPrimeIrreducibleCharacter G p ≃
      PPrimeIrreducibleCharacter intermediate p
  /-- The induction-hypothesis correspondence inside the intermediate
  subgroup. -/
  intermediateToLocalNormalizer :
    PPrimeIrreducibleCharacter intermediate p ≃
      PPrimeIrreducibleCharacter
        (SylowNormalizer (sylowIn P intermediate
          (Subgroup.le_normalizer.trans normalizer_le))) p

namespace CharacterCorrespondenceStep

variable {P : Sylow p G}

/-- A `CharacterCorrespondenceStep` really does recurse to a smaller finite
group. -/
theorem intermediate_natCard_lt (step : CharacterCorrespondenceStep P) :
    Nat.card step.intermediate < Nat.card G :=
  natCard_lt_of_lt_top step.proper

/-- The group isomorphism underlying the explicit character transport field. -/
def normalizerMulEquiv (step : CharacterCorrespondenceStep P) :
    SylowNormalizer
        (sylowIn P step.intermediate
          (Subgroup.le_normalizer.trans step.normalizer_le)) ≃*
      SylowNormalizer P :=
  normalizerInEquivNormalizer P step.intermediate
    (Subgroup.le_normalizer.trans step.normalizer_le) step.normalizer_le

/-- Transport `p'`-degree irreducible characters across the canonical
isomorphism between the local and ambient normalizers. -/
def localNormalizerToAmbientNormalizer (step : CharacterCorrespondenceStep P) :
    PPrimeIrreducibleCharacter
        (SylowNormalizer (sylowIn P step.intermediate
          (Subgroup.le_normalizer.trans step.normalizer_le))) p ≃
      PPrimeIrreducibleCharacter (SylowNormalizer P) p :=
  (IrreducibleCharacter.pPrimeComapEquiv p step.normalizerMulEquiv).symm

/-- Compose the three character correspondences in a normalizer-induction
step. -/
def equiv (step : CharacterCorrespondenceStep P) :
    PPrimeIrreducibleCharacter G p ≃
      PPrimeIrreducibleCharacter (SylowNormalizer P) p :=
  step.ambientToIntermediate.trans
    (step.intermediateToLocalNormalizer.trans
      step.localNormalizerToAmbientNormalizer)

/-- A completed normalizer-induction step proves the McKay cardinality
statement for the ambient group. -/
theorem statement [Fact p.Prime] (step : CharacterCorrespondenceStep P) :
    McKayConjecture.Statement G p P :=
  Cardinal.mk_congr step.equiv

end CharacterCorrespondenceStep

/-- Equivalence-valued strong induction over all subgroups of a finite group.
The induction step receives equivalences for every proper subgroup. -/
theorem exists_equiv_of_subgroup_induction
    {objects : Subgroup G → Type v} {target : Type v}
    (step : ∀ H : Subgroup G,
      (∀ K : Subgroup G, K < H → Nonempty (objects K ≃ target)) →
        Nonempty (objects H ≃ target))
    (H : Subgroup G) : Nonempty (objects H ≃ target) :=
  subgroup_strong_induction step H

/-- Cardinal-equality strong induction over all subgroups of a finite group.
This form is useful when a construction provides only cardinal equalities, not
chosen bijections. -/
theorem cardinalMk_eq_of_subgroup_induction
    {objects : Subgroup G → Type v} {target : Type v}
    (step : ∀ H : Subgroup G,
      (∀ K : Subgroup G, K < H → Cardinal.mk (objects K) = Cardinal.mk target) →
        Cardinal.mk (objects H) = Cardinal.mk target)
    (H : Subgroup G) : Cardinal.mk (objects H) = Cardinal.mk target :=
  subgroup_strong_induction step H

end McKayConjecture.InductiveMcKay
