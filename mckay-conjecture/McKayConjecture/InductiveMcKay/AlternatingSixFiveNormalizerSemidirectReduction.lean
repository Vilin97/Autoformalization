/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixFiveNormalizerSemidirectTable
import McKayConjecture.InductiveMcKay.AlternatingSixUniversalCoverReduction
import McKayConjecture.InductiveMcKay.FiniteIndexProjectiveTable

/-!
# The five-local `A₆` reduction through `C₃ × (C₅ ⋊ C₄)`

This file is the model-facing endpoint of the exact-normalizer reduction at
five.  It reduces `AlternatingSixCanonicalCoverVerification 5` to:

1. finite complete enumerations of the ambient canonical-cover `5'`-rows
   and the concrete `C₃ × (C₅ ⋊ C₄)` normalizer-model `5'`-rows;
2. an index matching equivariant for the transported ambient-stabilizer
   action; and
3. one checked associated-projective-representation comparison for each
   enumerated ambient row.

The proved normalizer group equivalence transports the model rows to the
actual fixed normalizer.  No character enumeration, row matching, or
projective comparison is asserted in this file.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixFiveNormalizerSemidirectReductionFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

variable
  {AmbientIndex NormalizerIndex : Type}
  [Fintype AmbientIndex]
  [Fintype NormalizerIndex]

/-- The projective comparison obligation for one finite ambient/model row
matching.  The local character in each row is the actual-normalizer
transport of the corresponding enumerated semidirect-model character. -/
abbrev AlternatingSixFiveSemidirectProjectiveRowData
    (d :
      AlternatingSixFiveSemidirectCharacterTableCertificate
        AmbientIndex NormalizerIndex)
    (i : AmbientIndex) :=
  ExactNormalizerProjectiveRowData
    d.toEquivariantMcKayEquiv
    (d.ambientEnumeration i)

/-- The exact remaining projective-representation obligation after an
equivariant finite character-table matching has been fixed. -/
def AlternatingSixFiveSemidirectProjectiveCompletion
    (d :
      AlternatingSixFiveSemidirectCharacterTableCertificate
        AmbientIndex NormalizerIndex) : Prop :=
  ∀ i : AmbientIndex,
    Nonempty (AlternatingSixFiveSemidirectProjectiveRowData d i)

/-- A concrete finite projective table whose ordinary local rows are
enumerated in `C₃ × (C₅ ⋊ C₄)`. -/
structure AlternatingSixFiveSemidirectProjectiveTableCertificate
    (AmbientIndex NormalizerIndex : Type)
    [Fintype AmbientIndex]
    [Fintype NormalizerIndex] where
  /-- Ambient/model row enumerations, matching, and equivariance. -/
  characterTable :
    AlternatingSixFiveSemidirectCharacterTableCertificate
      AmbientIndex NormalizerIndex
  /-- Checked projective factor-set and central-scalar compatibility for
  every matched row. -/
  projectiveRow :
    ∀ i : AmbientIndex,
      AlternatingSixFiveSemidirectProjectiveRowData characterTable i

namespace AlternatingSixFiveSemidirectProjectiveTableCertificate

/-- Forget the model presentation after transporting its character rows:
the result is the generic finite-index certificate at the actual exact
normalizer. -/
def toFiniteIndexExactNormalizerProjectiveTableCertificate
    (d :
      AlternatingSixFiveSemidirectProjectiveTableCertificate
        AmbientIndex NormalizerIndex) :
    FiniteIndexExactNormalizerProjectiveTableCertificate
      (alternatingSixUniversalCoverSylow 5)
      AmbientIndex NormalizerIndex where
  characterCertificate :=
    d.characterTable.toFiniteIndexMcKayEquivCertificate
  projectiveRow := d.projectiveRow

/-- A fully checked ambient/model finite projective table supplies local
inductive McKay data at the fixed Sylow-five subgroup. -/
def toLocalInductiveMcKayData
    (d :
      AlternatingSixFiveSemidirectProjectiveTableCertificate
        AmbientIndex NormalizerIndex) :
    LocalInductiveMcKayData
      (alternatingSixUniversalCoverSylow 5) :=
  d.toFiniteIndexExactNormalizerProjectiveTableCertificate
    |>.toLocalInductiveMcKayData

/-- A fully checked ambient/model finite projective table proves the
five-local canonical-cover obligation. -/
theorem alternatingSixCanonicalCoverVerification
    (d :
      AlternatingSixFiveSemidirectProjectiveTableCertificate
        AmbientIndex NormalizerIndex) :
    AlternatingSixCanonicalCoverVerification 5 :=
  ⟨d.toLocalInductiveMcKayData⟩

end AlternatingSixFiveSemidirectProjectiveTableCertificate

/-- The bundled projective-table certificate is equivalent to an
equivariant ambient/model character table together with existence of every
rowwise projective certificate.  This theorem states the residual
calculation without choosing representation spaces prematurely. -/
theorem nonempty_alternatingSixFiveSemidirectProjectiveTableCertificate_iff :
    Nonempty
        (AlternatingSixFiveSemidirectProjectiveTableCertificate
          AmbientIndex NormalizerIndex) ↔
      ∃ d :
          AlternatingSixFiveSemidirectCharacterTableCertificate
            AmbientIndex NormalizerIndex,
        AlternatingSixFiveSemidirectProjectiveCompletion d := by
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

/-- Strong model-facing reduction theorem: finite complete ambient and
`C₃ × (C₅ ⋊ C₄)` row enumerations, transported equivariance, and existence
of the projective comparison for every finite row imply
`AlternatingSixCanonicalCoverVerification 5`. -/
theorem alternatingSixCanonicalCoverVerification_five_of_semidirectTable
    (d :
      AlternatingSixFiveSemidirectCharacterTableCertificate
        AmbientIndex NormalizerIndex)
    (hrows :
      AlternatingSixFiveSemidirectProjectiveCompletion d) :
    AlternatingSixCanonicalCoverVerification 5 := by
  let table :
      AlternatingSixFiveSemidirectProjectiveTableCertificate
        AmbientIndex NormalizerIndex :=
    { characterTable := d
      projectiveRow := fun i ↦
        Classical.choice (hrows i) }
  exact table.alternatingSixCanonicalCoverVerification

/-- Bundled form of the model-facing reduction theorem. -/
theorem alternatingSixCanonicalCoverVerification_five_of_semidirectProjectiveTable
    (d :
      AlternatingSixFiveSemidirectProjectiveTableCertificate
        AmbientIndex NormalizerIndex) :
    AlternatingSixCanonicalCoverVerification 5 :=
  d.alternatingSixCanonicalCoverVerification

end InductiveMcKay
end McKayConjecture
