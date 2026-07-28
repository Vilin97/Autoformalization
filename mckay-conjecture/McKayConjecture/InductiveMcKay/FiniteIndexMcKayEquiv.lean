/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AutomorphismStabilizer

/-!
# Finite-index certificates for equivariant McKay bijections

Explicit character tables are normally indexed by small finite types rather
than by the representation-theoretic types used in the inductive McKay
condition.  This file provides the conversion layer.

A certificate consists of

* actual equivalences enumerating the ambient and normalizer `p'`-characters;
* an equivalence between the two finite row-index types; and
* equivariance checked as an equality of row indices.

These data mechanically construct an `EquivariantMcKayEquiv`.  In
particular, no character-level bijectivity or equivariance conclusion is
assumed as a field.
-/

noncomputable section

universe u v w

namespace McKayConjecture
namespace InductiveMcKay

variable {G : Type u} [Group G] {p : ℕ}

/-- A finite table-index certificate for an equivariant McKay
correspondence at the exact Sylow normalizer. -/
structure FiniteIndexMcKayEquivCertificate
    (P : Sylow p G)
    (AmbientIndex : Type v)
    (NormalizerIndex : Type w)
    [Fintype AmbientIndex]
    [Fintype NormalizerIndex] where
  /-- Enumeration of the ambient `p'`-degree irreducible rows. -/
  ambientEnumeration :
    AmbientIndex ≃ PPrimeIrreducibleCharacter G p
  /-- Enumeration of the exact-normalizer `p'`-degree irreducible rows. -/
  normalizerEnumeration :
    NormalizerIndex ≃
      PPrimeIrreducibleCharacter (SylowNormalizer P) p
  /-- The proposed matching of the two finite row sets. -/
  indexEquiv : AmbientIndex ≃ NormalizerIndex
  /-- Equivariance checked entirely at row-index level.

  The two displayed `symm` applications simply recover the row index of the
  character obtained after applying an automorphism. -/
  indexEquivariance :
    ∀ (a : SylowAutStabilizer P) (i : AmbientIndex),
      indexEquiv
          (ambientEnumeration.symm
            (a • ambientEnumeration i)) =
        normalizerEnumeration.symm
          (a • normalizerEnumeration (indexEquiv i))

namespace FiniteIndexMcKayEquivCertificate

variable
  {P : Sylow p G}
  {AmbientIndex : Type v}
  {NormalizerIndex : Type w}
  [Fintype AmbientIndex]
  [Fintype NormalizerIndex]

/-- The ambient row index after applying an automorphism stabilizing the
chosen Sylow subgroup. -/
def ambientIndexAction
    (d :
      FiniteIndexMcKayEquivCertificate
        P AmbientIndex NormalizerIndex)
    (a : SylowAutStabilizer P)
    (i : AmbientIndex) :
    AmbientIndex :=
  d.ambientEnumeration.symm
    (a • d.ambientEnumeration i)

/-- The normalizer row index after applying the restricted automorphism. -/
def normalizerIndexAction
    (d :
      FiniteIndexMcKayEquivCertificate
        P AmbientIndex NormalizerIndex)
    (a : SylowAutStabilizer P)
    (j : NormalizerIndex) :
    NormalizerIndex :=
  d.normalizerEnumeration.symm
    (a • d.normalizerEnumeration j)

/-- Restatement of the certificate's equivariance field using the two
explicit transported index actions. -/
theorem map_indexAction
    (d :
      FiniteIndexMcKayEquivCertificate
        P AmbientIndex NormalizerIndex)
    (a : SylowAutStabilizer P)
    (i : AmbientIndex) :
    d.indexEquiv (d.ambientIndexAction a i) =
      d.normalizerIndexAction a (d.indexEquiv i) :=
  d.indexEquivariance a i

/-- The character equivalence obtained by reading a source row number,
applying the index-level matching, and reading the corresponding target
row. -/
def toCharacterEquiv
    (d :
      FiniteIndexMcKayEquivCertificate
        P AmbientIndex NormalizerIndex) :
    PPrimeIrreducibleCharacter G p ≃
      PPrimeIrreducibleCharacter (SylowNormalizer P) p :=
  d.ambientEnumeration.symm.trans
    (d.indexEquiv.trans d.normalizerEnumeration)

@[simp]
theorem toCharacterEquiv_ambientEnumeration
    (d :
      FiniteIndexMcKayEquivCertificate
        P AmbientIndex NormalizerIndex)
    (i : AmbientIndex) :
    d.toCharacterEquiv (d.ambientEnumeration i) =
      d.normalizerEnumeration (d.indexEquiv i) := by
  simp [toCharacterEquiv]

@[simp]
theorem toCharacterEquiv_symm_normalizerEnumeration
    (d :
      FiniteIndexMcKayEquivCertificate
        P AmbientIndex NormalizerIndex)
    (j : NormalizerIndex) :
    d.toCharacterEquiv.symm (d.normalizerEnumeration j) =
      d.ambientEnumeration (d.indexEquiv.symm j) := by
  simp [toCharacterEquiv]

/-- A finite-index table certificate mechanically gives the character-level
equivariant McKay equivalence required by the exact-normalizer APIs. -/
def toEquivariantMcKayEquiv
    (d :
      FiniteIndexMcKayEquivCertificate
        P AmbientIndex NormalizerIndex) :
    EquivariantMcKayEquiv P where
  toEquiv := d.toCharacterEquiv
  map_smul' := by
    intro a χ
    let i : AmbientIndex :=
      d.ambientEnumeration.symm χ
    have hχ : d.ambientEnumeration i = χ :=
      d.ambientEnumeration.apply_symm_apply χ
    change
      d.normalizerEnumeration
          (d.indexEquiv
            (d.ambientEnumeration.symm (a • χ))) =
        a •
          d.normalizerEnumeration
            (d.indexEquiv
              (d.ambientEnumeration.symm χ))
    rw [← hχ]
    rw [d.indexEquivariance a i]
    simp only [Equiv.apply_symm_apply,
      Equiv.symm_apply_apply]

@[simp]
theorem toEquivariantMcKayEquiv_apply_enumerated
    (d :
      FiniteIndexMcKayEquivCertificate
        P AmbientIndex NormalizerIndex)
    (i : AmbientIndex) :
    d.toEquivariantMcKayEquiv
        (d.ambientEnumeration i) =
      d.normalizerEnumeration (d.indexEquiv i) :=
  d.toCharacterEquiv_ambientEnumeration i

end FiniteIndexMcKayEquivCertificate

end InductiveMcKay
end McKayConjecture
