/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixThreeConcreteFiniteTable
import McKayConjecture.InductiveMcKay.AlternatingSixThreeProjectiveTableReduction

/-!
# Projective-table endpoint with the concrete three-normalizer rows fixed

This file adds the rowwise projective obligations to
`AlternatingSixThreeConcreteCharacterTableCertificate`.  The complete
twelve-row local ordinary table is already fixed by the preceding file;
the ambient enumeration, equivariant row matching, and every projective
factor/scalar comparison remain explicit.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixThreeConcreteProjectiveTableFactPrime :
    Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

variable {AmbientIndex : Type} [Fintype AmbientIndex]

/-- The projective comparison obligation for one ambient row matched
against the fixed concrete normalizer table. -/
abbrev AlternatingSixThreeConcreteProjectiveRowData
    (d :
      AlternatingSixThreeConcreteCharacterTableCertificate
        AmbientIndex)
    (i : AmbientIndex) :=
  AlternatingSixThreeFiniteProjectiveRowData
    d.toAlternatingSixThreeCharacterTableCertificate i

/-- Existence of the projective factor-set and central-scalar comparison
for every explicitly enumerated ambient row. -/
def AlternatingSixThreeConcreteProjectiveCompletion
    (d :
      AlternatingSixThreeConcreteCharacterTableCertificate
        AmbientIndex) : Prop :=
  ∀ i : AmbientIndex,
    Nonempty (AlternatingSixThreeConcreteProjectiveRowData d i)

/-- The finite projective-table certificate after the proved local
ordinary enumeration has been fixed. -/
structure AlternatingSixThreeConcreteProjectiveTableCertificate
    (AmbientIndex : Type) [Fintype AmbientIndex] where
  /-- The remaining ambient enumeration, row matching, and genuine
  stabilizer-equivariance data. -/
  characterTable :
    AlternatingSixThreeConcreteCharacterTableCertificate AmbientIndex
  /-- One checked projective comparison for every ambient row. -/
  projectiveRow :
    ∀ i : AmbientIndex,
      AlternatingSixThreeConcreteProjectiveRowData characterTable i

namespace AlternatingSixThreeConcreteProjectiveTableCertificate

/-- Convert to the pre-existing three-local finite projective-table
certificate.  Its normalizer enumeration is definitionally the proved
concrete twelve-row equivalence. -/
def toAlternatingSixThreeFiniteProjectiveTableCertificate
    (d :
      AlternatingSixThreeConcreteProjectiveTableCertificate
        AmbientIndex) :
    AlternatingSixThreeFiniteProjectiveTableCertificate
      AmbientIndex AlternatingSixThreeConcreteNormalizerRow where
  characterTable :=
    d.characterTable.toAlternatingSixThreeCharacterTableCertificate
  projectiveRow := d.projectiveRow

@[simp]
theorem
    toAlternatingSixThreeFiniteProjectiveTableCertificate_characterTable
    (d :
      AlternatingSixThreeConcreteProjectiveTableCertificate
        AmbientIndex) :
    (d.toAlternatingSixThreeFiniteProjectiveTableCertificate
        |>.characterTable) =
      d.characterTable.toAlternatingSixThreeCharacterTableCertificate :=
  rfl

/-- Convert all the way to the generic finite-index exact-normalizer
projective-table certificate. -/
def toFiniteIndexExactNormalizerProjectiveTableCertificate
    (d :
      AlternatingSixThreeConcreteProjectiveTableCertificate
        AmbientIndex) :
    FiniteIndexExactNormalizerProjectiveTableCertificate
      (alternatingSixUniversalCoverSylow 3)
      AmbientIndex AlternatingSixThreeConcreteNormalizerRow :=
  d.toAlternatingSixThreeFiniteProjectiveTableCertificate
    |>.toFiniteIndexExactNormalizerProjectiveTableCertificate

/-- A completed concrete finite table supplies the local inductive McKay
datum for the fixed Sylow-three subgroup. -/
def toLocalInductiveMcKayData
    (d :
      AlternatingSixThreeConcreteProjectiveTableCertificate
        AmbientIndex) :
    LocalInductiveMcKayData
      (alternatingSixUniversalCoverSylow 3) :=
  d.toAlternatingSixThreeFiniteProjectiveTableCertificate
    |>.toLocalInductiveMcKayData

/-- A completed concrete finite table proves the three-local
canonical-cover obligation. -/
theorem alternatingSixCanonicalCoverVerification
    (d :
      AlternatingSixThreeConcreteProjectiveTableCertificate
        AmbientIndex) :
    AlternatingSixCanonicalCoverVerification 3 :=
  d.toAlternatingSixThreeFiniteProjectiveTableCertificate
    |>.alternatingSixCanonicalCoverVerification

end AlternatingSixThreeConcreteProjectiveTableCertificate

/-- Bundling projective rows is equivalent to retaining the concrete
ordinary-table data together with existence of every rowwise projective
comparison. -/
theorem
    nonempty_alternatingSixThreeConcreteProjectiveTableCertificate_iff :
    Nonempty
        (AlternatingSixThreeConcreteProjectiveTableCertificate
          AmbientIndex) ↔
      ∃ d :
          AlternatingSixThreeConcreteCharacterTableCertificate
            AmbientIndex,
        AlternatingSixThreeConcreteProjectiveCompletion d := by
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

/-- Concrete reduction theorem: after the local `3'` enumeration has been
discharged by the proved twelve-row table, a complete ambient
enumeration, an equivariant matching, and every projective row imply the
three-local verification. -/
theorem alternatingSixCanonicalCoverVerification_three_of_concreteTable
    (d :
      AlternatingSixThreeConcreteCharacterTableCertificate
        AmbientIndex)
    (hrows :
      AlternatingSixThreeConcreteProjectiveCompletion d) :
    AlternatingSixCanonicalCoverVerification 3 := by
  let table :
      AlternatingSixThreeConcreteProjectiveTableCertificate
        AmbientIndex :=
    { characterTable := d
      projectiveRow := fun i ↦
        Classical.choice (hrows i) }
  exact table.alternatingSixCanonicalCoverVerification

/-- Bundled form of the concrete projective-table endpoint. -/
theorem
    alternatingSixCanonicalCoverVerification_three_of_concreteProjectiveTable
    (d :
      AlternatingSixThreeConcreteProjectiveTableCertificate
        AmbientIndex) :
    AlternatingSixCanonicalCoverVerification 3 :=
  d.alternatingSixCanonicalCoverVerification

end InductiveMcKay
end McKayConjecture
