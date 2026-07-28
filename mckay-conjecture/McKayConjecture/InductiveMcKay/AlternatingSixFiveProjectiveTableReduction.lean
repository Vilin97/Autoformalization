/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixUniversalCoverFiveLocalStructure
import McKayConjecture.InductiveMcKay.AlternatingSixUniversalCoverReduction
import McKayConjecture.InductiveMcKay.FiniteIndexProjectiveTable

/-!
# Reducing the five-local `A₆` case to one finite projective table

The Schur-cover calculation now fixes all group-theoretic data at `p = 5`:
the canonical cover has order `2160`, its chosen Sylow subgroup is cyclic of
order five, and its exact normalizer has order sixty.  Its Sylow centralizer
is cyclic of order thirty and has index two in the normalizer; the induced
automorphism group of the Sylow subgroup has order two.  Consequently the
remaining `AlternatingSixCanonicalCoverVerification 5` obligation can be
discharged by a finite character calculation at that exact normalizer.

This file gives two interfaces to that calculation:

* an equivariant character-table equivalence together with one projective
  compatibility row for every ambient `5'`-character; and
* the finite-index certificate interface, in which both character sets are
  explicitly enumerated by finite types.

Thus, in this exact-normalizer route, the remaining mathematical obstruction
is not a Schur-multiplier, Sylow, or normalizer-order assertion.  It is
precisely the equivariant `5'`-character matching and its rowwise
factor-set/scalar compatibility.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixFiveProjectiveTableFactPrime :
    Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- The ambient `5'`-irreducible characters in the fixed `A₆` cover
calculation. -/
abbrev AlternatingSixFiveAmbientCharacter :=
  PPrimeIrreducibleCharacter AlternatingSixUniversalCover 5

/-- The local `5'`-irreducible characters at the exact Sylow normalizer. -/
abbrev AlternatingSixFiveNormalizerCharacter :=
  PPrimeIrreducibleCharacter
    (Subgroup.normalizer
      (alternatingSixUniversalCoverSylow 5 :
        Set AlternatingSixUniversalCover))
    5

/-- Rowwise projective completion of a fixed equivariant character-table
matching.  Each row may use its own finite-dimensional representation
spaces. -/
def AlternatingSixFiveProjectiveCompletion
    (e :
      EquivariantMcKayEquiv
        (alternatingSixUniversalCoverSylow 5)) : Prop :=
  ∀ χ : AlternatingSixFiveAmbientCharacter,
    Nonempty (ExactNormalizerProjectiveRowData e χ)

/-- Exact decomposition of the remaining finite-table input: an
exact-normalizer projective table is the same as an equivariant character
matching equipped with every projective comparison row. -/
theorem nonempty_alternatingSixFive_projectiveTableData_iff :
    Nonempty
        (ExactNormalizerProjectiveTableData
          (alternatingSixUniversalCoverSylow 5)) ↔
      ∃ e :
          EquivariantMcKayEquiv
            (alternatingSixUniversalCoverSylow 5),
        AlternatingSixFiveProjectiveCompletion e := by
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

/-- An equivariant `5'`-table matching and all its projective rows give the
full local datum on the canonical cover. -/
theorem alternatingSixCanonicalCoverVerification_five_of_equivariantTable
    (e :
      EquivariantMcKayEquiv
        (alternatingSixUniversalCoverSylow 5))
    (hrows : AlternatingSixFiveProjectiveCompletion e) :
    AlternatingSixCanonicalCoverVerification 5 := by
  let d :
      ExactNormalizerProjectiveTableData
        (alternatingSixUniversalCoverSylow 5) :=
    { characterTableEquiv := e
      projectiveComparison := fun χ ↦
        Classical.choice (hrows χ) }
  exact ⟨d.toLocalInductiveMcKayData⟩

/-- The direct exact-normalizer table interface for the five-local
canonical-cover verification. -/
theorem alternatingSixCanonicalCoverVerification_five_of_projectiveTable
    (d :
      ExactNormalizerProjectiveTableData
        (alternatingSixUniversalCoverSylow 5)) :
    AlternatingSixCanonicalCoverVerification 5 :=
  ⟨d.toLocalInductiveMcKayData⟩

/-- A finite-index projective-table certificate for the fixed five-local
calculation. -/
abbrev AlternatingSixFiveFiniteProjectiveTableCertificate
    (AmbientIndex NormalizerIndex : Type)
    [Fintype AmbientIndex]
    [Fintype NormalizerIndex] :=
  FiniteIndexExactNormalizerProjectiveTableCertificate
    (alternatingSixUniversalCoverSylow 5)
    AmbientIndex NormalizerIndex

/-- Explicit finite row enumerations, an equivariant index matching, and
the checked projective rows prove the full fixed-cover obligation at five. -/
theorem alternatingSixCanonicalCoverVerification_five_of_finiteProjectiveTable
    {AmbientIndex NormalizerIndex : Type}
    [Fintype AmbientIndex]
    [Fintype NormalizerIndex]
    (d :
      AlternatingSixFiveFiniteProjectiveTableCertificate
        AmbientIndex NormalizerIndex) :
    AlternatingSixCanonicalCoverVerification 5 :=
  ⟨d.toLocalInductiveMcKayData⟩

end InductiveMcKay
end McKayConjecture
