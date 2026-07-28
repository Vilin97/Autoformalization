/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixFiveConcreteFiniteTable
import McKayConjecture.InductiveMcKay.AlternatingSixFiveProjectiveTableReduction

/-!
# Projective-table endpoint with the concrete five-normalizer rows fixed

This file adds the rowwise projective obligations to
`AlternatingSixFiveConcreteCharacterTableCertificate`.  The complete
twenty-four-row local `5'` table is already fixed by the preceding file;
the ambient enumeration, equivariant row matching, and every projective
factor/scalar comparison remain explicit.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixFiveConcreteProjectiveTableFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

variable {AmbientIndex : Type} [Fintype AmbientIndex]

/-- The projective comparison obligation for one ambient row matched
against the fixed concrete normalizer table. -/
abbrev AlternatingSixFiveConcreteProjectiveRowData
    (d :
      AlternatingSixFiveConcreteCharacterTableCertificate
        AmbientIndex)
    (i : AmbientIndex) :=
  ExactNormalizerProjectiveRowData
    d.toEquivariantMcKayEquiv
    (d.ambientEnumeration i)

/-- Existence of the projective factor-set and central-scalar comparison
for every explicitly enumerated ambient row. -/
def AlternatingSixFiveConcreteProjectiveCompletion
    (d :
      AlternatingSixFiveConcreteCharacterTableCertificate
        AmbientIndex) : Prop :=
  ∀ i : AmbientIndex,
    Nonempty (AlternatingSixFiveConcreteProjectiveRowData d i)

/-- The finite projective-table certificate after the proved local
`5'` enumeration has been fixed. -/
structure AlternatingSixFiveConcreteProjectiveTableCertificate
    (AmbientIndex : Type) [Fintype AmbientIndex] where
  /-- The remaining ambient enumeration, row matching, and genuine
  stabilizer-equivariance data. -/
  characterTable :
    AlternatingSixFiveConcreteCharacterTableCertificate AmbientIndex
  /-- One checked projective comparison for every ambient row. -/
  projectiveRow :
    ∀ i : AmbientIndex,
      AlternatingSixFiveConcreteProjectiveRowData characterTable i

namespace AlternatingSixFiveConcreteProjectiveTableCertificate

/-- Convert to the pre-existing five-local finite projective-table
certificate.  Its normalizer enumeration is definitionally the proved
concrete twenty-four-row equivalence. -/
def toAlternatingSixFiveFiniteProjectiveTableCertificate
    (d :
      AlternatingSixFiveConcreteProjectiveTableCertificate
        AmbientIndex) :
    AlternatingSixFiveFiniteProjectiveTableCertificate
      AmbientIndex AlternatingSixFiveConcreteNormalizerRow where
  characterCertificate :=
    d.characterTable.toFiniteIndexMcKayEquivCertificate
  projectiveRow := d.projectiveRow

@[simp]
theorem
    toAlternatingSixFiveFiniteProjectiveTableCertificate_characterCertificate
    (d :
      AlternatingSixFiveConcreteProjectiveTableCertificate
        AmbientIndex) :
    (d.toAlternatingSixFiveFiniteProjectiveTableCertificate
        |>.characterCertificate) =
      d.characterTable.toFiniteIndexMcKayEquivCertificate :=
  rfl

/-- View the concrete table as the generic finite-index exact-normalizer
projective-table certificate. -/
def toFiniteIndexExactNormalizerProjectiveTableCertificate
    (d :
      AlternatingSixFiveConcreteProjectiveTableCertificate
        AmbientIndex) :
    FiniteIndexExactNormalizerProjectiveTableCertificate
      (alternatingSixUniversalCoverSylow 5)
      AmbientIndex AlternatingSixFiveConcreteNormalizerRow :=
  d.toAlternatingSixFiveFiniteProjectiveTableCertificate

/-- A completed concrete finite table supplies the local inductive McKay
datum for the fixed Sylow-five subgroup. -/
def toLocalInductiveMcKayData
    (d :
      AlternatingSixFiveConcreteProjectiveTableCertificate
        AmbientIndex) :
    LocalInductiveMcKayData
      (alternatingSixUniversalCoverSylow 5) :=
  d.toAlternatingSixFiveFiniteProjectiveTableCertificate
    |>.toLocalInductiveMcKayData

/-- A completed concrete finite table proves the five-local
canonical-cover obligation. -/
theorem alternatingSixCanonicalCoverVerification
    (d :
      AlternatingSixFiveConcreteProjectiveTableCertificate
        AmbientIndex) :
    AlternatingSixCanonicalCoverVerification 5 :=
  alternatingSixCanonicalCoverVerification_five_of_finiteProjectiveTable
    d.toAlternatingSixFiveFiniteProjectiveTableCertificate

end AlternatingSixFiveConcreteProjectiveTableCertificate

/-- Bundling projective rows is equivalent to retaining the concrete
`5'`-table data together with existence of every rowwise projective
comparison. -/
theorem
    nonempty_alternatingSixFiveConcreteProjectiveTableCertificate_iff :
    Nonempty
        (AlternatingSixFiveConcreteProjectiveTableCertificate
          AmbientIndex) ↔
      ∃ d :
          AlternatingSixFiveConcreteCharacterTableCertificate
            AmbientIndex,
        AlternatingSixFiveConcreteProjectiveCompletion d := by
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

/-- Concrete reduction theorem: after the local `5'` enumeration has been
discharged by the proved twenty-four-row table, a complete ambient
enumeration, an equivariant matching, and every projective row imply the
five-local verification. -/
theorem alternatingSixCanonicalCoverVerification_five_of_concreteTable
    (d :
      AlternatingSixFiveConcreteCharacterTableCertificate
        AmbientIndex)
    (hrows :
      AlternatingSixFiveConcreteProjectiveCompletion d) :
    AlternatingSixCanonicalCoverVerification 5 := by
  let table :
      AlternatingSixFiveConcreteProjectiveTableCertificate
        AmbientIndex :=
    { characterTable := d
      projectiveRow := fun i ↦
        Classical.choice (hrows i) }
  exact table.alternatingSixCanonicalCoverVerification

/-- Bundled form of the concrete projective-table endpoint. -/
theorem
    alternatingSixCanonicalCoverVerification_five_of_concreteProjectiveTable
    (d :
      AlternatingSixFiveConcreteProjectiveTableCertificate
        AmbientIndex) :
    AlternatingSixCanonicalCoverVerification 5 :=
  d.alternatingSixCanonicalCoverVerification

end InductiveMcKay
end McKayConjecture
