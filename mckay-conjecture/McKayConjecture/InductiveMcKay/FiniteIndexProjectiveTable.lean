/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.ExactNormalizerProjectiveTableData
import McKayConjecture.InductiveMcKay.FiniteIndexMcKayEquiv

/-!
# Finite-index certificates for exact-normalizer projective tables

This file adds the projective rows to a finite-index McKay equivalence
certificate.  A verifier supplies one
`ExactNormalizerProjectiveRowData` for each ambient table index.  Since the
ambient enumeration is an actual equivalence, these finitely many rows
mechanically produce the universally quantified projective comparison field
of `ExactNormalizerProjectiveTableData`.

The interface separates the two finite computations cleanly:

1. enumerate and equivariantly match the ordinary `p'`-character rows;
2. check factor-set and central-scalar agreement for each matched row.
-/

noncomputable section

universe u v w

namespace McKayConjecture
namespace InductiveMcKay

variable {G : Type u} [Group G] [Finite G] {p : ℕ}

/-- A finite-index certificate containing both the equivariant character
matching and every projective comparison row. -/
structure FiniteIndexExactNormalizerProjectiveTableCertificate
    (P : Sylow p G)
    (AmbientIndex : Type v)
    (NormalizerIndex : Type w)
    [Fintype AmbientIndex]
    [Fintype NormalizerIndex] where
  /-- Enumerations, row matching, and index-level equivariance. -/
  characterCertificate :
    FiniteIndexMcKayEquivCertificate
      P AmbientIndex NormalizerIndex
  /-- The projective factor/scalar calculation for each enumerated ambient
  row. -/
  projectiveRow :
    ∀ i : AmbientIndex,
      ExactNormalizerProjectiveRowData
        characterCertificate.toEquivariantMcKayEquiv
        (characterCertificate.ambientEnumeration i)

namespace FiniteIndexExactNormalizerProjectiveTableCertificate

variable
  {P : Sylow p G}
  {AmbientIndex : Type v}
  {NormalizerIndex : Type w}
  [Fintype AmbientIndex]
  [Fintype NormalizerIndex]

/-- The equivariant McKay equivalence certified by the finite character
tables. -/
def toEquivariantMcKayEquiv
    (d :
      FiniteIndexExactNormalizerProjectiveTableCertificate
        P AmbientIndex NormalizerIndex) :
    EquivariantMcKayEquiv P :=
  d.characterCertificate.toEquivariantMcKayEquiv

@[simp]
theorem toEquivariantMcKayEquiv_apply_enumerated
    (d :
      FiniteIndexExactNormalizerProjectiveTableCertificate
        P AmbientIndex NormalizerIndex)
    (i : AmbientIndex) :
    d.toEquivariantMcKayEquiv
        (d.characterCertificate.ambientEnumeration i) =
      d.characterCertificate.normalizerEnumeration
        (d.characterCertificate.indexEquiv i) :=
  d.characterCertificate.toEquivariantMcKayEquiv_apply_enumerated i

/-- Recover the projective row associated with an arbitrary ambient
`p'`-character by looking up its certified table index. -/
def projectiveComparison
    (d :
      FiniteIndexExactNormalizerProjectiveTableCertificate
        P AmbientIndex NormalizerIndex)
    (χ : PPrimeIrreducibleCharacter G p) :
    ExactNormalizerProjectiveRowData
      d.toEquivariantMcKayEquiv χ := by
  let i : AmbientIndex :=
    d.characterCertificate.ambientEnumeration.symm χ
  have hi :
      d.characterCertificate.ambientEnumeration i = χ :=
    d.characterCertificate.ambientEnumeration.apply_symm_apply χ
  exact hi ▸ d.projectiveRow i

/-- A finite-index projective-table certificate mechanically gives the
existing exact-normalizer projective-table datum. -/
def toExactNormalizerProjectiveTableData
    (d :
      FiniteIndexExactNormalizerProjectiveTableCertificate
        P AmbientIndex NormalizerIndex) :
    ExactNormalizerProjectiveTableData P where
  characterTableEquiv := d.toEquivariantMcKayEquiv
  projectiveComparison := d.projectiveComparison

/-- Directly obtain the full local inductive McKay datum certified by the
finite tables. -/
def toLocalInductiveMcKayData
    (d :
      FiniteIndexExactNormalizerProjectiveTableCertificate
        P AmbientIndex NormalizerIndex) :
    LocalInductiveMcKayData P :=
  d.toExactNormalizerProjectiveTableData.toLocalInductiveMcKayData

/-- Directly obtain the exact-normalizer datum used by recursive
normalizer composition. -/
def toExactNormalizerInductiveMcKayData
    (d :
      FiniteIndexExactNormalizerProjectiveTableCertificate
        P AmbientIndex NormalizerIndex) :
    ExactNormalizerInductiveMcKayData P :=
  d.toExactNormalizerProjectiveTableData
    |>.toExactNormalizerInductiveMcKayData

end FiniteIndexExactNormalizerProjectiveTableCertificate

end InductiveMcKay
end McKayConjecture
