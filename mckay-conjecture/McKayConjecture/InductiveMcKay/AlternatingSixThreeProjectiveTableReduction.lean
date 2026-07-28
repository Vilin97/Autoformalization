/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixThreeFiniteTable
import McKayConjecture.InductiveMcKay.AlternatingSixUniversalCoverReduction
import McKayConjecture.InductiveMcKay.FiniteIndexProjectiveTable

/-!
# Reducing the three-local `A₆` case to finite projective-table rows

The group-theoretic three-local calculation is now exact: the fixed Sylow
subgroup is extraspecial of order `27` and exponent `3`, its ambient
centralizer is the order-six center, and its exact normalizer has order
`216`.  The normalizer modulo its center is identified both with its
order-`36` action image and with the corresponding concrete normalizer in
`A₆`.

This file separates the remaining character-theoretic calculation into:

1. honest finite enumerations of the ambient and actual-normalizer
   `3'`-rows;
2. an equivariant finite row matching; and
3. one `ExactNormalizerProjectiveRowData` certificate for each matched
   ambient row.

No number of rows, character value, matching, projective representation,
or splitting of the normalizer is asserted.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixThreeProjectiveReductionFactPrime :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-! ### Character-level exact-normalizer endpoint -/

/-- Rowwise projective completion of a fixed genuine equivariant
three-local character matching. -/
def AlternatingSixThreeProjectiveCompletion
    (e :
      EquivariantMcKayEquiv
        (alternatingSixUniversalCoverSylow 3)) : Prop :=
  ∀ χ : AlternatingSixThreeAmbientCharacter,
    Nonempty (ExactNormalizerProjectiveRowData e χ)

/-- The exact-normalizer projective-table obligation at three. -/
def AlternatingSixThreeProjectiveTableObligation : Prop :=
  Nonempty
    (ExactNormalizerProjectiveTableData
      (alternatingSixUniversalCoverSylow 3))

/-- The exact-normalizer obligation consists precisely of a genuine
equivariant character matching and all its rowwise projective
certificates. -/
theorem alternatingSixThree_projectiveTableObligation_iff :
    AlternatingSixThreeProjectiveTableObligation ↔
      ∃ e :
          EquivariantMcKayEquiv
            (alternatingSixUniversalCoverSylow 3),
        AlternatingSixThreeProjectiveCompletion e := by
  constructor
  · rintro ⟨d⟩
    exact
      ⟨d.characterTableEquiv,
        fun χ ↦ ⟨d.projectiveComparison χ⟩⟩
  · rintro ⟨e, hrows⟩
    exact
      ⟨{ characterTableEquiv := e
         projectiveComparison := fun χ ↦
           Classical.choice (hrows χ) }⟩

/-- A genuine equivariant ordinary-table matching and every projective row
give the full fixed-cover verification at three. -/
theorem alternatingSixCanonicalCoverVerification_three_of_equivariantTable
    (e :
      EquivariantMcKayEquiv
        (alternatingSixUniversalCoverSylow 3))
    (hrows : AlternatingSixThreeProjectiveCompletion e) :
    AlternatingSixCanonicalCoverVerification 3 := by
  let d :
      ExactNormalizerProjectiveTableData
        (alternatingSixUniversalCoverSylow 3) :=
    { characterTableEquiv := e
      projectiveComparison := fun χ ↦
        Classical.choice (hrows χ) }
  exact ⟨d.toLocalInductiveMcKayData⟩

/-- A checked exact-normalizer projective table directly proves the
canonical-cover verification at three. -/
theorem alternatingSixCanonicalCoverVerification_three_of_projectiveTable
    (d :
      ExactNormalizerProjectiveTableData
        (alternatingSixUniversalCoverSylow 3)) :
    AlternatingSixCanonicalCoverVerification 3 :=
  ⟨d.toLocalInductiveMcKayData⟩

/-! ### Fully split finite-index endpoint -/

variable
  {AmbientIndex NormalizerIndex : Type}
  [Fintype AmbientIndex]
  [Fintype NormalizerIndex]

/-- The projective obligation for one enumerated ambient row after an
honest finite ordinary-table certificate has been fixed. -/
abbrev AlternatingSixThreeFiniteProjectiveRowData
    (d :
      AlternatingSixThreeCharacterTableCertificate
        AmbientIndex NormalizerIndex)
    (i : AmbientIndex) :=
  ExactNormalizerProjectiveRowData
    d.toEquivariantMcKayEquiv
    (d.ambientEnumeration i)

/-- Existence of the rowwise projective comparison for every finite
ambient table index. -/
def AlternatingSixThreeFiniteProjectiveCompletion
    (d :
      AlternatingSixThreeCharacterTableCertificate
        AmbientIndex NormalizerIndex) : Prop :=
  ∀ i : AmbientIndex,
    Nonempty (AlternatingSixThreeFiniteProjectiveRowData d i)

/-- A fully checked finite three-local projective table.  The ordinary and
projective calculations remain separate fields. -/
structure AlternatingSixThreeFiniteProjectiveTableCertificate
    (AmbientIndex NormalizerIndex : Type)
    [Fintype AmbientIndex]
    [Fintype NormalizerIndex] where
  /-- Complete actual ambient/normalizer row enumerations, matching, and
  equivariance. -/
  characterTable :
    AlternatingSixThreeCharacterTableCertificate
      AmbientIndex NormalizerIndex
  /-- Checked projective factor-set and central-scalar data for every
  enumerated ambient row. -/
  projectiveRow :
    ∀ i : AmbientIndex,
      AlternatingSixThreeFiniteProjectiveRowData characterTable i

namespace AlternatingSixThreeFiniteProjectiveTableCertificate

/-- Convert the split three-local certificate to the generic finite-index
exact-normalizer certificate. -/
def toFiniteIndexExactNormalizerProjectiveTableCertificate
    (d :
      AlternatingSixThreeFiniteProjectiveTableCertificate
        AmbientIndex NormalizerIndex) :
    FiniteIndexExactNormalizerProjectiveTableCertificate
      (alternatingSixUniversalCoverSylow 3)
      AmbientIndex NormalizerIndex where
  characterCertificate :=
    d.characterTable.toFiniteIndexMcKayEquivCertificate
  projectiveRow := d.projectiveRow

/-- The local inductive McKay datum mechanically supplied by a fully
checked finite table. -/
def toLocalInductiveMcKayData
    (d :
      AlternatingSixThreeFiniteProjectiveTableCertificate
        AmbientIndex NormalizerIndex) :
    LocalInductiveMcKayData
      (alternatingSixUniversalCoverSylow 3) :=
  d.toFiniteIndexExactNormalizerProjectiveTableCertificate
    |>.toLocalInductiveMcKayData

/-- A fully checked finite table proves the fixed-cover three-local
obligation. -/
theorem alternatingSixCanonicalCoverVerification
    (d :
      AlternatingSixThreeFiniteProjectiveTableCertificate
        AmbientIndex NormalizerIndex) :
    AlternatingSixCanonicalCoverVerification 3 :=
  ⟨d.toLocalInductiveMcKayData⟩

end AlternatingSixThreeFiniteProjectiveTableCertificate

/-- Bundling projective rows is equivalent to an ordinary finite
character-table certificate together with existence of every finite
projective row. -/
theorem nonempty_alternatingSixThreeFiniteProjectiveTableCertificate_iff :
    Nonempty
        (AlternatingSixThreeFiniteProjectiveTableCertificate
          AmbientIndex NormalizerIndex) ↔
      ∃ d :
          AlternatingSixThreeCharacterTableCertificate
            AmbientIndex NormalizerIndex,
        AlternatingSixThreeFiniteProjectiveCompletion d := by
  constructor
  · rintro ⟨d⟩
    exact
      ⟨d.characterTable,
        fun i ↦ ⟨d.projectiveRow i⟩⟩
  · rintro ⟨d, hrows⟩
    exact
      ⟨{ characterTable := d
         projectiveRow := fun i ↦
           Classical.choice (hrows i) }⟩

/-- Strong finite endpoint: honest finite ambient and actual-normalizer row
enumerations, genuine stabilizer equivariance, and every rowwise projective
certificate imply the full fixed-cover verification at three. -/
theorem alternatingSixCanonicalCoverVerification_three_of_finiteTable
    (d :
      AlternatingSixThreeCharacterTableCertificate
        AmbientIndex NormalizerIndex)
    (hrows :
      AlternatingSixThreeFiniteProjectiveCompletion d) :
    AlternatingSixCanonicalCoverVerification 3 := by
  let table :
      AlternatingSixThreeFiniteProjectiveTableCertificate
        AmbientIndex NormalizerIndex :=
    { characterTable := d
      projectiveRow := fun i ↦
        Classical.choice (hrows i) }
  exact table.alternatingSixCanonicalCoverVerification

/-- Bundled form of the finite endpoint. -/
theorem alternatingSixCanonicalCoverVerification_three_of_finiteProjectiveTable
    (d :
      AlternatingSixThreeFiniteProjectiveTableCertificate
        AmbientIndex NormalizerIndex) :
    AlternatingSixCanonicalCoverVerification 3 :=
  d.alternatingSixCanonicalCoverVerification

end InductiveMcKay
end McKayConjecture
