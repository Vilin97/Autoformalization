/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixTwoNormalizerModelTable
import McKayConjecture.InductiveMcKay.AlternatingSixUniversalCoverReduction
import McKayConjecture.InductiveMcKay.FiniteIndexProjectiveTable

/-!
# The two-local `A₆` reduction through `C₃ × Q₁₆`

This file is the model-facing endpoint of the exact-normalizer reduction at
two.  It reduces `AlternatingSixCanonicalCoverVerification 2` to:

1. finite complete enumerations of the ambient canonical-cover `2'`-rows
   and the concrete `C₃ × Q₁₆` normalizer-model `2'`-rows;
2. an index matching equivariant for the transported ambient-stabilizer
   action; and
3. one checked associated-projective-representation comparison for each
   enumerated ambient row.

The proved normalizer group equivalence transports model rows to the actual
fixed normalizer.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixTwoNormalizerModelReductionFactPrime :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

variable
  {AmbientIndex NormalizerIndex : Type}
  [Fintype AmbientIndex]
  [Fintype NormalizerIndex]

/-- The projective comparison obligation for one finite ambient/model row
matching. -/
abbrev AlternatingSixTwoModelProjectiveRowData
    (d :
      AlternatingSixTwoModelCharacterTableCertificate
        AmbientIndex NormalizerIndex)
    (i : AmbientIndex) :=
  ExactNormalizerProjectiveRowData
    d.toEquivariantMcKayEquiv
    (d.ambientEnumeration i)

/-- The remaining projective-representation obligation after an equivariant
finite character-table matching has been fixed. -/
def AlternatingSixTwoModelProjectiveCompletion
    (d :
      AlternatingSixTwoModelCharacterTableCertificate
        AmbientIndex NormalizerIndex) : Prop :=
  ∀ i : AmbientIndex,
    Nonempty (AlternatingSixTwoModelProjectiveRowData d i)

/-- A concrete finite projective table whose ordinary local rows are
enumerated in `C₃ × Q₁₆`. -/
structure AlternatingSixTwoModelProjectiveTableCertificate
    (AmbientIndex NormalizerIndex : Type)
    [Fintype AmbientIndex]
    [Fintype NormalizerIndex] where
  /-- Ambient/model row enumerations, matching, and equivariance. -/
  characterTable :
    AlternatingSixTwoModelCharacterTableCertificate
      AmbientIndex NormalizerIndex
  /-- Checked projective factor-set and central-scalar compatibility for
  every matched row. -/
  projectiveRow :
    ∀ i : AmbientIndex,
      AlternatingSixTwoModelProjectiveRowData characterTable i

namespace AlternatingSixTwoModelProjectiveTableCertificate

/-- Forget the model presentation after transporting its character rows:
the result is the generic finite-index certificate at the actual exact
normalizer. -/
def toFiniteIndexExactNormalizerProjectiveTableCertificate
    (d :
      AlternatingSixTwoModelProjectiveTableCertificate
        AmbientIndex NormalizerIndex) :
    FiniteIndexExactNormalizerProjectiveTableCertificate
      (alternatingSixUniversalCoverSylow 2)
      AmbientIndex NormalizerIndex where
  characterCertificate :=
    d.characterTable.toFiniteIndexMcKayEquivCertificate
  projectiveRow := d.projectiveRow

/-- A fully checked ambient/model finite projective table supplies local
inductive McKay data at the fixed Sylow-two subgroup. -/
def toLocalInductiveMcKayData
    (d :
      AlternatingSixTwoModelProjectiveTableCertificate
        AmbientIndex NormalizerIndex) :
    LocalInductiveMcKayData
      (alternatingSixUniversalCoverSylow 2) :=
  d.toFiniteIndexExactNormalizerProjectiveTableCertificate
    |>.toLocalInductiveMcKayData

/-- A fully checked ambient/model finite projective table proves the
two-local canonical-cover obligation. -/
theorem alternatingSixCanonicalCoverVerification
    (d :
      AlternatingSixTwoModelProjectiveTableCertificate
        AmbientIndex NormalizerIndex) :
    AlternatingSixCanonicalCoverVerification 2 :=
  ⟨d.toLocalInductiveMcKayData⟩

end AlternatingSixTwoModelProjectiveTableCertificate

/-- The bundled projective-table certificate is equivalent to a model-facing
equivariant character table together with existence of every rowwise
projective certificate. -/
theorem nonempty_alternatingSixTwoModelProjectiveTableCertificate_iff :
    Nonempty
        (AlternatingSixTwoModelProjectiveTableCertificate
          AmbientIndex NormalizerIndex) ↔
      ∃ d :
          AlternatingSixTwoModelCharacterTableCertificate
            AmbientIndex NormalizerIndex,
        AlternatingSixTwoModelProjectiveCompletion d := by
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

/-- Strong model-facing reduction theorem: complete finite ambient and
`C₃ × Q₁₆` row enumerations, transported equivariance, and existence of
the projective comparison for every row imply the two-local verification. -/
theorem alternatingSixCanonicalCoverVerification_two_of_modelTable
    (d :
      AlternatingSixTwoModelCharacterTableCertificate
        AmbientIndex NormalizerIndex)
    (hrows :
      AlternatingSixTwoModelProjectiveCompletion d) :
    AlternatingSixCanonicalCoverVerification 2 := by
  let table :
      AlternatingSixTwoModelProjectiveTableCertificate
        AmbientIndex NormalizerIndex :=
    { characterTable := d
      projectiveRow := fun i ↦
        Classical.choice (hrows i) }
  exact table.alternatingSixCanonicalCoverVerification

/-- Bundled form of the model-facing reduction theorem. -/
theorem alternatingSixCanonicalCoverVerification_two_of_modelProjectiveTable
    (d :
      AlternatingSixTwoModelProjectiveTableCertificate
        AmbientIndex NormalizerIndex) :
    AlternatingSixCanonicalCoverVerification 2 :=
  d.alternatingSixCanonicalCoverVerification

end InductiveMcKay
end McKayConjecture
