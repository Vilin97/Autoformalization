/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixTwoConcreteFiniteTable
import McKayConjecture.InductiveMcKay.AlternatingSixTwoProjectiveTableReduction

/-!
# Projective-table endpoint with the concrete two-normalizer rows fixed

This file adds the rowwise projective obligations to
`AlternatingSixTwoConcreteCharacterTableCertificate`.  The complete
twelve-row local `2'` table is already fixed by the preceding file;
the ambient enumeration, equivariant row matching, and every projective
factor/scalar comparison remain explicit.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixTwoConcreteProjectiveTableFactPrime :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

variable {AmbientIndex : Type} [Fintype AmbientIndex]

/-- The projective comparison obligation for one ambient row matched
against the fixed concrete normalizer table. -/
abbrev AlternatingSixTwoConcreteProjectiveRowData
    (d :
      AlternatingSixTwoConcreteCharacterTableCertificate
        AmbientIndex)
    (i : AmbientIndex) :=
  ExactNormalizerProjectiveRowData
    d.toEquivariantMcKayEquiv
    (d.ambientEnumeration i)

/-- Existence of the projective factor-set and central-scalar comparison
for every explicitly enumerated ambient row. -/
def AlternatingSixTwoConcreteProjectiveCompletion
    (d :
      AlternatingSixTwoConcreteCharacterTableCertificate
        AmbientIndex) : Prop :=
  ∀ i : AmbientIndex,
    Nonempty (AlternatingSixTwoConcreteProjectiveRowData d i)

/-- The finite projective-table certificate after the proved local
`2'` enumeration has been fixed. -/
structure AlternatingSixTwoConcreteProjectiveTableCertificate
    (AmbientIndex : Type) [Fintype AmbientIndex] where
  /-- The remaining ambient enumeration, row matching, and genuine
  stabilizer-equivariance data. -/
  characterTable :
    AlternatingSixTwoConcreteCharacterTableCertificate AmbientIndex
  /-- One checked projective comparison for every ambient row. -/
  projectiveRow :
    ∀ i : AmbientIndex,
      AlternatingSixTwoConcreteProjectiveRowData characterTable i

namespace AlternatingSixTwoConcreteProjectiveTableCertificate

/-- Convert to the pre-existing two-local finite projective-table
certificate.  Its normalizer enumeration is definitionally the proved
concrete twelve-row equivalence. -/
def toAlternatingSixTwoFiniteProjectiveTableCertificate
    (d :
      AlternatingSixTwoConcreteProjectiveTableCertificate
        AmbientIndex) :
    AlternatingSixTwoFiniteProjectiveTableCertificate
      AmbientIndex AlternatingSixTwoConcreteNormalizerRow where
  characterCertificate :=
    d.characterTable.toFiniteIndexMcKayEquivCertificate
  projectiveRow := d.projectiveRow

@[simp]
theorem
    toAlternatingSixTwoFiniteProjectiveTableCertificate_characterCertificate
    (d :
      AlternatingSixTwoConcreteProjectiveTableCertificate
        AmbientIndex) :
    (d.toAlternatingSixTwoFiniteProjectiveTableCertificate
        |>.characterCertificate) =
      d.characterTable.toFiniteIndexMcKayEquivCertificate :=
  rfl

/-- Convert all the way to the generic finite-index exact-normalizer
projective-table certificate. -/
def toFiniteIndexExactNormalizerProjectiveTableCertificate
    (d :
      AlternatingSixTwoConcreteProjectiveTableCertificate
        AmbientIndex) :
    FiniteIndexExactNormalizerProjectiveTableCertificate
      (alternatingSixUniversalCoverSylow 2)
      AmbientIndex AlternatingSixTwoConcreteNormalizerRow :=
  d.toAlternatingSixTwoFiniteProjectiveTableCertificate

/-- A completed concrete finite table supplies the local inductive McKay
datum for the fixed Sylow-two subgroup. -/
def toLocalInductiveMcKayData
    (d :
      AlternatingSixTwoConcreteProjectiveTableCertificate
        AmbientIndex) :
    LocalInductiveMcKayData
      (alternatingSixUniversalCoverSylow 2) :=
  d.toAlternatingSixTwoFiniteProjectiveTableCertificate
    |>.toLocalInductiveMcKayData

/-- A completed concrete finite table proves the two-local
canonical-cover obligation. -/
theorem alternatingSixCanonicalCoverVerification
    (d :
      AlternatingSixTwoConcreteProjectiveTableCertificate
        AmbientIndex) :
    AlternatingSixCanonicalCoverVerification 2 :=
  alternatingSixCanonicalCoverVerification_two_of_finiteProjectiveTable
    d.toAlternatingSixTwoFiniteProjectiveTableCertificate

end AlternatingSixTwoConcreteProjectiveTableCertificate

/-- Bundling projective rows is equivalent to retaining the concrete
`2'`-table data together with existence of every rowwise projective
comparison. -/
theorem
    nonempty_alternatingSixTwoConcreteProjectiveTableCertificate_iff :
    Nonempty
        (AlternatingSixTwoConcreteProjectiveTableCertificate
          AmbientIndex) ↔
      ∃ d :
          AlternatingSixTwoConcreteCharacterTableCertificate
            AmbientIndex,
        AlternatingSixTwoConcreteProjectiveCompletion d := by
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

/-- Concrete reduction theorem: after the local `2'` enumeration has been
discharged by the proved twelve-row table, a complete ambient
enumeration, an equivariant matching, and every projective row imply the
two-local verification. -/
theorem alternatingSixCanonicalCoverVerification_two_of_concreteTable
    (d :
      AlternatingSixTwoConcreteCharacterTableCertificate
        AmbientIndex)
    (hrows :
      AlternatingSixTwoConcreteProjectiveCompletion d) :
    AlternatingSixCanonicalCoverVerification 2 := by
  let table :
      AlternatingSixTwoConcreteProjectiveTableCertificate
        AmbientIndex :=
    { characterTable := d
      projectiveRow := fun i ↦
        Classical.choice (hrows i) }
  exact table.alternatingSixCanonicalCoverVerification

/-- Bundled form of the concrete projective-table endpoint. -/
theorem
    alternatingSixCanonicalCoverVerification_two_of_concreteProjectiveTable
    (d :
      AlternatingSixTwoConcreteProjectiveTableCertificate
        AmbientIndex) :
    AlternatingSixCanonicalCoverVerification 2 :=
  d.alternatingSixCanonicalCoverVerification

end InductiveMcKay
end McKayConjecture
