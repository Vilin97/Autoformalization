/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixUniversalCoverTwoNormalizerProduct
import McKayConjecture.InductiveMcKay.AlternatingSixUniversalCoverReduction
import McKayConjecture.InductiveMcKay.FiniteIndexProjectiveTable

/-!
# Reducing the two-local `A₆` case to one finite projective table

The group-theoretic part of the canonical-cover calculation at `p = 2` is
now exact:

* the fixed Sylow subgroup has order sixteen and is isomorphic to
  `QuaternionGroup 4`;
* its normalizer has order forty-eight and is the join of the Sylow
  subgroup with the order-six ambient center;
* its centralizer is exactly that ambient center; and
* the normalizer action on the Sylow subgroup has order eight and consists
  entirely of inner automorphisms.

Thus the exact-normalizer route to
`AlternatingSixCanonicalCoverVerification 2` has one remaining input: a
finite equivariant matching of the ambient and normalizer `2'`-character
tables together with the projective factor-set/scalar certificate for each
matched row.  This file states that obligation without asserting any
uncomputed character or projective data.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

local instance alternatingSixTwoProjectiveTableFactPrime :
    Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

/-- The ambient `2'`-irreducible characters in the fixed canonical cover. -/
abbrev AlternatingSixTwoAmbientCharacter :=
  PPrimeIrreducibleCharacter AlternatingSixUniversalCover 2

/-- The local `2'`-irreducible characters at the exact Sylow normalizer. -/
abbrev AlternatingSixTwoNormalizerCharacter :=
  PPrimeIrreducibleCharacter
    (Subgroup.normalizer
      (alternatingSixUniversalCoverSylow 2 :
        Set AlternatingSixUniversalCover))
    2

/-- Rowwise projective completion of a fixed equivariant two-local
character-table matching. -/
def AlternatingSixTwoProjectiveCompletion
    (e :
      EquivariantMcKayEquiv
        (alternatingSixUniversalCoverSylow 2)) : Prop :=
  ∀ χ : AlternatingSixTwoAmbientCharacter,
    Nonempty (ExactNormalizerProjectiveRowData e χ)

/-- The exact finite-table obligation left by the exact-normalizer route
at `p = 2`. -/
def AlternatingSixTwoProjectiveTableObligation : Prop :=
  Nonempty
    (ExactNormalizerProjectiveTableData
      (alternatingSixUniversalCoverSylow 2))

/-- The remaining obligation separates exactly into an equivariant
`2'`-character matching and one projective certificate for every ambient
row. -/
theorem alternatingSixTwo_projectiveTableObligation_iff :
    AlternatingSixTwoProjectiveTableObligation ↔
      ∃ e :
          EquivariantMcKayEquiv
            (alternatingSixUniversalCoverSylow 2),
        AlternatingSixTwoProjectiveCompletion e := by
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

/-- An equivariant two-local character matching and all its projective
rows give the full canonical-cover verification at two. -/
theorem alternatingSixCanonicalCoverVerification_two_of_equivariantTable
    (e :
      EquivariantMcKayEquiv
        (alternatingSixUniversalCoverSylow 2))
    (hrows : AlternatingSixTwoProjectiveCompletion e) :
    AlternatingSixCanonicalCoverVerification 2 := by
  let d :
      ExactNormalizerProjectiveTableData
        (alternatingSixUniversalCoverSylow 2) :=
    { characterTableEquiv := e
      projectiveComparison := fun χ ↦
        Classical.choice (hrows χ) }
  exact ⟨d.toLocalInductiveMcKayData⟩

/-- The exact remaining finite-table obligation is sufficient for the
full canonical-cover verification at two. -/
theorem alternatingSixCanonicalCoverVerification_two_of_projectiveTableObligation
    (h : AlternatingSixTwoProjectiveTableObligation) :
    AlternatingSixCanonicalCoverVerification 2 := by
  obtain ⟨d⟩ := h
  exact ⟨d.toLocalInductiveMcKayData⟩

/-- A checked exact-normalizer projective table directly proves the
canonical-cover verification at two. -/
theorem alternatingSixCanonicalCoverVerification_two_of_projectiveTable
    (d :
      ExactNormalizerProjectiveTableData
        (alternatingSixUniversalCoverSylow 2)) :
    AlternatingSixCanonicalCoverVerification 2 :=
  ⟨d.toLocalInductiveMcKayData⟩

/-- A finite-index projective-table certificate for the fixed two-local
calculation. -/
abbrev AlternatingSixTwoFiniteProjectiveTableCertificate
    (AmbientIndex NormalizerIndex : Type)
    [Fintype AmbientIndex]
    [Fintype NormalizerIndex] :=
  FiniteIndexExactNormalizerProjectiveTableCertificate
    (alternatingSixUniversalCoverSylow 2)
    AmbientIndex NormalizerIndex

/-- Explicit finite row enumerations, an equivariant index matching, and
the checked projective rows prove the full fixed-cover obligation at two. -/
theorem alternatingSixCanonicalCoverVerification_two_of_finiteProjectiveTable
    {AmbientIndex NormalizerIndex : Type}
    [Fintype AmbientIndex]
    [Fintype NormalizerIndex]
    (d :
      AlternatingSixTwoFiniteProjectiveTableCertificate
        AmbientIndex NormalizerIndex) :
    AlternatingSixCanonicalCoverVerification 2 :=
  ⟨d.toLocalInductiveMcKayData⟩

end InductiveMcKay
end McKayConjecture
