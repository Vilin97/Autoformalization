/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.FiniteIndexMcKayEquiv
import McKayConjecture.InductiveMcKay.SylowOuterClassNormalizerCharacterAction

/-!
# Propagating finite-index McKay equivariance from outer generators

For fixed ambient and exact-normalizer character enumerations, the
Sylow-stabilizing automorphisms under which a proposed row matching is
equivariant form a subgroup.  Inner automorphisms supplied by the exact
normalizer belong to this subgroup automatically, because inner
automorphisms fix ordinary characters.

Consequently it suffices to check any set of generators modulo the inner
subgroup.  This file packages that propagation and constructs the resulting
`FiniteIndexMcKayEquivCertificate` and `EquivariantMcKayEquiv`.  It contains
no projective-character or factor-set assertion.
-/

noncomputable section

universe u v w x y

namespace McKayConjecture
namespace InductiveMcKay

variable {G : Type u} [Group G] {p : ℕ}

/-- Transport a group action through an arbitrary enumeration, as a
homomorphism to permutations of the enumeration's index type. -/
def transportedIndexActionHom
    {A : Type v}
    {Index : Type w}
    {X : Type x}
    [Group A]
    [MulAction A X]
    (enumeration : Index ≃ X) :
    A →* Equiv.Perm Index where
  toFun a :=
    enumeration.trans
      ((MulAction.toPerm a).trans enumeration.symm)
  map_one' := by
    ext i
    simp
  map_mul' a b := by
    ext i
    simp [mul_smul]

@[simp]
theorem transportedIndexActionHom_apply
    {A : Type v}
    {Index : Type w}
    {X : Type x}
    [Group A]
    [MulAction A X]
    (enumeration : Index ≃ X)
    (a : A)
    (i : Index) :
    transportedIndexActionHom enumeration a i =
      enumeration.symm (a • enumeration i) :=
  rfl

variable
  {P : Sylow p G}
  {AmbientIndex : Type v}
  {NormalizerIndex : Type w}

/-- The ambient character action transported to the proposed ambient row
indices. -/
def finiteIndexAmbientActionHom
    (ambientEnumeration :
      AmbientIndex ≃ PPrimeIrreducibleCharacter G p) :
    SylowAutStabilizer P →* Equiv.Perm AmbientIndex :=
  transportedIndexActionHom ambientEnumeration

/-- The exact-normalizer character action transported back to ambient row
indices through the proposed row matching. -/
def finiteIndexMatchedNormalizerActionHom
    (normalizerEnumeration :
      NormalizerIndex ≃
        PPrimeIrreducibleCharacter (SylowNormalizer P) p)
    (indexEquiv : AmbientIndex ≃ NormalizerIndex) :
    SylowAutStabilizer P →* Equiv.Perm AmbientIndex :=
  transportedIndexActionHom
    (indexEquiv.trans normalizerEnumeration)

/-- The subgroup of Sylow-stabilizing automorphisms for which the proposed
finite row matching is equivariant. -/
def finiteIndexMcKayEquivarianceSubgroup
    (ambientEnumeration :
      AmbientIndex ≃ PPrimeIrreducibleCharacter G p)
    (normalizerEnumeration :
      NormalizerIndex ≃
        PPrimeIrreducibleCharacter (SylowNormalizer P) p)
    (indexEquiv : AmbientIndex ≃ NormalizerIndex) :
    Subgroup (SylowAutStabilizer P) :=
  (finiteIndexAmbientActionHom ambientEnumeration).eqLocus
    (finiteIndexMatchedNormalizerActionHom
      normalizerEnumeration indexEquiv)

/-- Membership in the equivariance subgroup is exactly the usual
pointwise row-index equivariance equation. -/
@[simp]
theorem mem_finiteIndexMcKayEquivarianceSubgroup_iff
    (ambientEnumeration :
      AmbientIndex ≃ PPrimeIrreducibleCharacter G p)
    (normalizerEnumeration :
      NormalizerIndex ≃
        PPrimeIrreducibleCharacter (SylowNormalizer P) p)
    (indexEquiv : AmbientIndex ≃ NormalizerIndex)
    (a : SylowAutStabilizer P) :
    a ∈ finiteIndexMcKayEquivarianceSubgroup
        ambientEnumeration normalizerEnumeration indexEquiv ↔
      ∀ i,
        indexEquiv
            (ambientEnumeration.symm
              (a • ambientEnumeration i)) =
          normalizerEnumeration.symm
            (a • normalizerEnumeration (indexEquiv i)) := by
  constructor
  · intro ha i
    change
      finiteIndexAmbientActionHom ambientEnumeration a =
        finiteIndexMatchedNormalizerActionHom
          normalizerEnumeration indexEquiv a at ha
    have hpoint :=
      congrArg
        (fun σ : Equiv.Perm AmbientIndex ↦ σ i)
        ha
    simpa [
      finiteIndexAmbientActionHom,
      finiteIndexMatchedNormalizerActionHom
    ] using congrArg indexEquiv hpoint
  · intro ha
    change
      finiteIndexAmbientActionHom ambientEnumeration a =
        finiteIndexMatchedNormalizerActionHom
          normalizerEnumeration indexEquiv a
    ext i
    apply indexEquiv.injective
    simpa [
      finiteIndexAmbientActionHom,
      finiteIndexMatchedNormalizerActionHom
    ] using ha i

/-- Conjugation by an element of the exact Sylow normalizer always belongs
to the row-equivariance subgroup. -/
theorem normalizerInner_mem_finiteIndexMcKayEquivarianceSubgroup
    (ambientEnumeration :
      AmbientIndex ≃ PPrimeIrreducibleCharacter G p)
    (normalizerEnumeration :
      NormalizerIndex ≃
        PPrimeIrreducibleCharacter (SylowNormalizer P) p)
    (indexEquiv : AmbientIndex ≃ NormalizerIndex)
    (g : SylowNormalizer P) :
    normalizerInnerSylowAutStabilizerHom P g ∈
      finiteIndexMcKayEquivarianceSubgroup
        ambientEnumeration normalizerEnumeration indexEquiv := by
  rw [mem_finiteIndexMcKayEquivarianceSubgroup_iff]
  intro i
  have hambient :
      normalizerInnerSylowAutStabilizerHom P g •
          ambientEnumeration i =
        ambientEnumeration i := by
    change
      MulAut.conj g.1 • ambientEnumeration i =
        ambientEnumeration i
    exact pPrime_conj_smul p g.1 _
  have hnormalizer :
      normalizerInnerSylowAutStabilizerHom P g •
          normalizerEnumeration (indexEquiv i) =
        normalizerEnumeration (indexEquiv i) := by
    change
      SylowAutStabilizer.normalizerRestrictionHom P
            (normalizerInnerSylowAutStabilizerHom P g) •
          normalizerEnumeration (indexEquiv i) =
        normalizerEnumeration (indexEquiv i)
    rw [
      normalizerRestrictionHom_normalizerInnerSylowAutStabilizerHom,
      pPrime_conj_smul
    ]
  rw [hambient, hnormalizer]
  simp

/-- The entire exact-normalizer inner range lies in the row-equivariance
subgroup. -/
theorem normalizerInner_range_le_finiteIndexMcKayEquivarianceSubgroup
    (ambientEnumeration :
      AmbientIndex ≃ PPrimeIrreducibleCharacter G p)
    (normalizerEnumeration :
      NormalizerIndex ≃
        PPrimeIrreducibleCharacter (SylowNormalizer P) p)
    (indexEquiv : AmbientIndex ≃ NormalizerIndex) :
    (normalizerInnerSylowAutStabilizerHom P).range ≤
      finiteIndexMcKayEquivarianceSubgroup
        ambientEnumeration normalizerEnumeration indexEquiv := by
  rintro _ ⟨g, rfl⟩
  exact
    normalizerInner_mem_finiteIndexMcKayEquivarianceSubgroup
      ambientEnumeration normalizerEnumeration indexEquiv g

/-- Pointwise equivariance checks on a set of stabilizer elements put that
set inside the row-equivariance subgroup. -/
theorem generators_subset_finiteIndexMcKayEquivarianceSubgroup
    (ambientEnumeration :
      AmbientIndex ≃ PPrimeIrreducibleCharacter G p)
    (normalizerEnumeration :
      NormalizerIndex ≃
        PPrimeIrreducibleCharacter (SylowNormalizer P) p)
    (indexEquiv : AmbientIndex ≃ NormalizerIndex)
    (generators : Set (SylowAutStabilizer P))
    (hgeneratorEquivariance :
      ∀ a ∈ generators, ∀ i,
        indexEquiv
            (ambientEnumeration.symm
              (a • ambientEnumeration i)) =
          normalizerEnumeration.symm
            (a • normalizerEnumeration (indexEquiv i))) :
    generators ⊆
      finiteIndexMcKayEquivarianceSubgroup
        ambientEnumeration normalizerEnumeration indexEquiv := by
  intro a ha
  exact
    (mem_finiteIndexMcKayEquivarianceSubgroup_iff
      ambientEnumeration normalizerEnumeration indexEquiv a).2
      (hgeneratorEquivariance a ha)

/-- Generator equivariance plus generation modulo inner automorphisms makes
the row-equivariance subgroup equal to the full Sylow stabilizer. -/
theorem finiteIndexMcKayEquivarianceSubgroup_eq_top_of_generators
    (ambientEnumeration :
      AmbientIndex ≃ PPrimeIrreducibleCharacter G p)
    (normalizerEnumeration :
      NormalizerIndex ≃
        PPrimeIrreducibleCharacter (SylowNormalizer P) p)
    (indexEquiv : AmbientIndex ≃ NormalizerIndex)
    (generators : Set (SylowAutStabilizer P))
    (hgenerates :
      GeneratesSylowAutStabilizerModuloInner P generators)
    (hgeneratorEquivariance :
      ∀ a ∈ generators, ∀ i,
        indexEquiv
            (ambientEnumeration.symm
              (a • ambientEnumeration i)) =
          normalizerEnumeration.symm
            (a • normalizerEnumeration (indexEquiv i))) :
    finiteIndexMcKayEquivarianceSubgroup
        ambientEnumeration normalizerEnumeration indexEquiv =
      ⊤ := by
  rw [GeneratesSylowAutStabilizerModuloInner] at hgenerates
  apply le_antisymm le_top
  rw [← hgenerates]
  apply (Subgroup.closure_le _).2
  apply Set.union_subset
  · exact
      generators_subset_finiteIndexMcKayEquivarianceSubgroup
        ambientEnumeration normalizerEnumeration indexEquiv
        generators hgeneratorEquivariance
  · intro a ha
    have harange :
        a ∈ (normalizerInnerSylowAutStabilizerHom P).range := by
      rw [normalizerInnerSylowAutStabilizerHom_range]
      exact ha
    exact
      normalizerInner_range_le_finiteIndexMcKayEquivarianceSubgroup
        ambientEnumeration normalizerEnumeration indexEquiv
        harange

variable [Fintype AmbientIndex] [Fintype NormalizerIndex]

/-- Construct a full finite-index McKay equivariance certificate from
pointwise checks on generators modulo inner automorphisms. -/
def finiteIndexMcKayEquivCertificate_of_generators
    (ambientEnumeration :
      AmbientIndex ≃ PPrimeIrreducibleCharacter G p)
    (normalizerEnumeration :
      NormalizerIndex ≃
        PPrimeIrreducibleCharacter (SylowNormalizer P) p)
    (indexEquiv : AmbientIndex ≃ NormalizerIndex)
    (generators : Set (SylowAutStabilizer P))
    (hgenerates :
      GeneratesSylowAutStabilizerModuloInner P generators)
    (hgeneratorEquivariance :
      ∀ a ∈ generators, ∀ i,
        indexEquiv
            (ambientEnumeration.symm
              (a • ambientEnumeration i)) =
          normalizerEnumeration.symm
            (a • normalizerEnumeration (indexEquiv i))) :
    FiniteIndexMcKayEquivCertificate
      P AmbientIndex NormalizerIndex where
  ambientEnumeration := ambientEnumeration
  normalizerEnumeration := normalizerEnumeration
  indexEquiv := indexEquiv
  indexEquivariance := by
    intro a i
    apply
      (mem_finiteIndexMcKayEquivarianceSubgroup_iff
        ambientEnumeration normalizerEnumeration indexEquiv a).1
    rw [
      finiteIndexMcKayEquivarianceSubgroup_eq_top_of_generators
        ambientEnumeration normalizerEnumeration indexEquiv
        generators hgenerates hgeneratorEquivariance
    ]
    trivial

/-- Construct the full character-level equivariant McKay equivalence from
pointwise checks on generators modulo inner automorphisms. -/
def equivariantMcKayEquiv_of_generators
    (ambientEnumeration :
      AmbientIndex ≃ PPrimeIrreducibleCharacter G p)
    (normalizerEnumeration :
      NormalizerIndex ≃
        PPrimeIrreducibleCharacter (SylowNormalizer P) p)
    (indexEquiv : AmbientIndex ≃ NormalizerIndex)
    (generators : Set (SylowAutStabilizer P))
    (hgenerates :
      GeneratesSylowAutStabilizerModuloInner P generators)
    (hgeneratorEquivariance :
      ∀ a ∈ generators, ∀ i,
        indexEquiv
            (ambientEnumeration.symm
              (a • ambientEnumeration i)) =
          normalizerEnumeration.symm
            (a • normalizerEnumeration (indexEquiv i))) :
    EquivariantMcKayEquiv P :=
  (finiteIndexMcKayEquivCertificate_of_generators
    ambientEnumeration normalizerEnumeration indexEquiv
    generators hgenerates hgeneratorEquivariance).toEquivariantMcKayEquiv

end InductiveMcKay
end McKayConjecture
