/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Data.Finsupp.Defs
import McKayConjecture.Character.ClassFunctionInductionPairing
import McKayConjecture.Character.ElementaryRestriction

/-!
# Reduction of Brauer's local criterion to elementary induction

Brauer's characterization says that a complex class function is an integral
generalized character if its restrictions to all elementary subgroups are
integral generalized characters.  The genuinely group-theoretic input is
Brauer induction: irreducible characters are integral sums of characters
induced from elementary subgroups.

Mathlib currently has neither the representation ring nor Artin--Brauer
induction.  This file isolates the exact missing induction formula and
proves all remaining character-theoretic steps.  It also proves the useful
denominator version: an elementary induction formula with denominator `d`
shows that `d • f` is a generalized character.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture

/-- One summand in an elementary Brauer-induction formula.  The prime is
part of the data because the elementary prime may vary from one summand to
another. -/
structure ElementaryInductionTerm
    (G : Type) [Group G] where
  /-- The prime defining this elementary subgroup. -/
  prime : ℕ
  /-- The displayed number really is prime. -/
  prime_isPrime : prime.Prime
  /-- The elementary subgroup of the ambient group. -/
  subgroup : Subgroup G
  /-- A direct-product presentation of the elementary subgroup. -/
  decomposition :
    PElementaryDecomposition prime subgroup
  /-- The irreducible character to be induced. -/
  character : IrreducibleCharacter subgroup

namespace ElementaryInductionTerm

variable {G : Type} [Group G] [Finite G]

/-- The class function induced by an elementary-induction term. -/
def inducedClassFunction
    (t : ElementaryInductionTerm G) :
    ClassFunction G := by
  letI : Fintype G := Fintype.ofFinite _
  exact
    ClassFunction.induce t.subgroup
      t.character.toClassFunction

end ElementaryInductionTerm

namespace ClassFunction

variable {G : Type} [Group G] [Finite G]

/-- The finite integral combination of elementary induced class functions
encoded by a finitely supported coefficient family. -/
def elementaryInductionCombination
    (c : ElementaryInductionTerm G →₀ ℤ) :
    ClassFunction G :=
  ∑ t ∈ c.support,
    (c t : ℂ) • t.inducedClassFunction

/-- An elementary induction formula with integer denominator `d`.

For `d = 1` this is exactly the character-valued form of Brauer induction
needed for Brauer's local-to-global characterization. -/
def HasElementaryInductionFormula
    (d : ℤ) : Prop :=
  ∀ χ : IrreducibleCharacter G,
    ∃ c : ElementaryInductionTerm G →₀ ℤ,
      (d : ℂ) • χ.toClassFunction =
        elementaryInductionCombination c

/-- The denominator-one elementary induction formula.  Proving this
predicate for every finite group is the remaining Artin--Brauer induction
theorem; it is not present in mathlib. -/
abbrev HasElementaryBrauerInduction : Prop :=
  HasElementaryInductionFormula (G := G) 1

/-- Pulling an elementary-product restriction back through the inverse
multiplication equivalence gives ordinary restriction to the subgroup. -/
theorem isGeneralizedCharacter_comap_subgroup_of_restrictToPElementaryProduct
    {p : ℕ} (S : Subgroup G)
    (D : PElementaryDecomposition p S)
    {f : ClassFunction G}
    (hf :
      IsGeneralizedCharacter
        (restrictToPElementaryProduct S D f)) :
    IsGeneralizedCharacter
      (comapLinearMap S.subtype f) := by
  have hpull :=
    hf.comap D.multiplicationEquiv.symm.toMonoidHom
  convert hpull using 1
  ext s
  change
    f (S.subtype s) =
      f (S.subtype
      (D.multiplicationEquiv
        (D.multiplicationEquiv.symm s)))
  rw [D.multiplicationEquiv.apply_symm_apply]

/-- Local generalizedness on the elementary subgroup makes the pairing
with its induced irreducible character integral. -/
theorem normalizedPairing_inducedClassFunction_integral_of_elementary_local
    {f : ClassFunction G}
    (hlocal :
      ∀ (q : ℕ), q.Prime →
        ∀ (S : Subgroup G)
          (D : PElementaryDecomposition q S),
          IsGeneralizedCharacter
            (restrictToPElementaryProduct S D f))
    (t : ElementaryInductionTerm G) :
    ∃ z : ℤ,
      normalizedPairing f t.inducedClassFunction =
        (z : ℂ) := by
  letI : Fintype G := Fintype.ofFinite _
  change
    ∃ z : ℤ,
      normalizedPairing f
          (induce t.subgroup
            t.character.toClassFunction) =
        (z : ℂ)
  rw [normalizedPairing_induce_right]
  have hres :
      IsGeneralizedCharacter
        (comapLinearMap t.subgroup.subtype f) :=
    isGeneralizedCharacter_comap_subgroup_of_restrictToPElementaryProduct
      t.subgroup t.decomposition
      (hlocal t.prime t.prime_isPrime
        t.subgroup t.decomposition)
  exact
    (isGeneralizedCharacter_iff_pairings_integral
      (comapLinearMap t.subgroup.subtype f)).mp
      hres t.character

/-- A denominator-`d` elementary induction formula plus generalizedness on
all elementary restrictions makes `d • f` a generalized character. -/
theorem isGeneralizedCharacter_zsmul_of_elementary_local
    (d : ℤ)
    (hind : HasElementaryInductionFormula (G := G) d)
    {f : ClassFunction G}
    (hlocal :
      ∀ (q : ℕ), q.Prime →
        ∀ (S : Subgroup G)
          (D : PElementaryDecomposition q S),
          IsGeneralizedCharacter
            (restrictToPElementaryProduct S D f)) :
    IsGeneralizedCharacter (d • f) := by
  rw [isGeneralizedCharacter_iff_pairings_integral]
  intro χ
  obtain ⟨c, hc⟩ := hind χ
  choose z hz using
    fun t : ElementaryInductionTerm G ↦
      normalizedPairing_inducedClassFunction_integral_of_elementary_local
        hlocal t
  refine
    ⟨∑ t ∈ c.support, c t * z t, ?_⟩
  have hscaled :
      normalizedPairing (d • f) χ.toClassFunction =
        normalizedPairing f
          ((d : ℂ) • χ.toClassFunction) := by
    rw [← Int.cast_smul_eq_zsmul ℂ d f]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [hscaled, hc, elementaryInductionCombination]
  simp only [map_sum, map_smul, smul_eq_mul,
    Int.cast_sum, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [hz t]

/-- Two generalized integral multiples with a Bézout relation force the
original class function to be generalized. -/
theorem isGeneralizedCharacter_of_bezout_zsmul
    {f : ClassFunction G}
    (a b d e : ℤ)
    (hbezout : a * d + b * e = 1)
    (hd : IsGeneralizedCharacter (d • f))
    (he : IsGeneralizedCharacter (e • f)) :
    IsGeneralizedCharacter f := by
  have hsum :=
    (hd.zsmul a).add (he.zsmul b)
  have heq :
      a • (d • f) + b • (e • f) = f := by
    rw [smul_smul, smul_smul, ← add_smul,
      hbezout, one_smul]
  rwa [heq] at hsum

/-- Elementary induction formulas with Bézout-coprime denominators already
suffice for Brauer's local-to-global conclusion.  This is useful when
induction is established prime by prime rather than directly with
denominator one. -/
theorem isGeneralizedCharacter_of_elementary_local_of_bezout_denominators
    (a b d e : ℤ)
    (hbezout : a * d + b * e = 1)
    (hd : HasElementaryInductionFormula (G := G) d)
    (he : HasElementaryInductionFormula (G := G) e)
    {f : ClassFunction G}
    (hlocal :
      ∀ (q : ℕ), q.Prime →
        ∀ (S : Subgroup G)
          (D : PElementaryDecomposition q S),
          IsGeneralizedCharacter
            (restrictToPElementaryProduct S D f)) :
    IsGeneralizedCharacter f :=
  isGeneralizedCharacter_of_bezout_zsmul
    a b d e hbezout
    (isGeneralizedCharacter_zsmul_of_elementary_local
      d hd hlocal)
    (isGeneralizedCharacter_zsmul_of_elementary_local
      e he hlocal)

/-- Brauer's elementary-subgroup local-to-global criterion, reduced to its
precise missing group-theoretic input: denominator-one Brauer induction. -/
theorem isGeneralizedCharacter_of_elementary_local
    (hind : HasElementaryBrauerInduction (G := G))
    {f : ClassFunction G}
    (hlocal :
      ∀ (q : ℕ), q.Prime →
        ∀ (S : Subgroup G)
          (D : PElementaryDecomposition q S),
          IsGeneralizedCharacter
            (restrictToPElementaryProduct S D f)) :
    IsGeneralizedCharacter f := by
  have h :=
    isGeneralizedCharacter_zsmul_of_elementary_local
      (G := G) 1 hind hlocal
  simpa using h

/-- Under Brauer induction, elementary-local generalizedness is equivalent
to ambient generalizedness. -/
theorem isGeneralizedCharacter_iff_elementary_local
    (hind : HasElementaryBrauerInduction (G := G))
    (f : ClassFunction G) :
    IsGeneralizedCharacter f ↔
      ∀ (q : ℕ), q.Prime →
        ∀ (S : Subgroup G)
          (D : PElementaryDecomposition q S),
          IsGeneralizedCharacter
            (restrictToPElementaryProduct S D f) := by
  constructor
  · intro hf q _hq S D
    exact hf.restrictToPElementaryProduct S D
  · exact isGeneralizedCharacter_of_elementary_local hind

end ClassFunction
end McKayConjecture
