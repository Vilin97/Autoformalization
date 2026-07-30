/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GallagherCentralizerCommutator
import McKayConjecture.Character.GoodElementClassSum
import McKayConjecture.Character.GoodElementCosetNorm
import McKayConjecture.Character.GoodElementLocalCommutator
import McKayConjecture.GroupTheory.QuotientFiberSum

/-!
# Gallagher's ordinary good-class count

This file assembles the local good-element commutator calculation over the
fibres of `A → A ⧸ N`.  The cyclic coset norm supplies the factor `|N|`,
and comparison with Gallagher's global commutator identity gives the
division-free count

`|A| * |Irr(A | θ)| = ∑ q, if q is θ-good then |D_q| else 0`.

The centralizer-weighted class sum then yields the ordinary equality between
the character fibre over `θ` and the good quotient conjugacy classes.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace CliffordCorrespondence

open IrreducibleCharacter

variable {A : Type} [Group A] [Finite A]

attribute [local instance]
  IrreducibleCharacter.goodElementRatioSumFintype

local instance gallagherGoodClassCountDecidableProp
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The local good/non-good identity at one representative in the canonical
right `N`-coset over `q`. -/
private theorem degree_mul_localCosetCommutatorSum_eq_if_isGood
    (N : Subgroup A) [N.Normal]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ a : A, a • θ = θ)
    (q : A ⧸ N)
    (η : IrreducibleCharacter.CyclicOverExtensions N θ q)
    (n : N) :
    (θ.degree : ℂ) *
        ∑ d :
            IrreducibleCharacter.goodElementCentralizer N q,
          θ.values
            ⟨(((IrreducibleCharacter.cyclicOverQuotientGenerator
                    N q) *
                  IrreducibleCharacter.cyclicOverInclusion
                    N q n :
                IrreducibleCharacter.cyclicOverQuotientElement
                  N q) : A)⁻¹ *
                (d : A)⁻¹ *
                (((IrreducibleCharacter.cyclicOverQuotientGenerator
                    N q) *
                  IrreducibleCharacter.cyclicOverInclusion
                    N q n :
                IrreducibleCharacter.cyclicOverQuotientElement
                  N q) : A) *
                (d : A),
              IrreducibleCharacter.cyclicOverQuotientGenerator_mul_normal_commutator_mem
                N q n d⟩ =
      if IrreducibleCharacter.IsGoodQuotientElement N θ q then
        η.1.values
            ((IrreducibleCharacter.cyclicOverQuotientGenerator
                N q *
              IrreducibleCharacter.cyclicOverInclusion
                N q n)⁻¹) *
          η.1.values
            (IrreducibleCharacter.cyclicOverQuotientGenerator
                N q *
              IrreducibleCharacter.cyclicOverInclusion
                N q n) *
          (Nat.card
            (IrreducibleCharacter.goodElementCentralizer
              N q) : ℂ)
      else 0 := by
  simpa only using
    IrreducibleCharacter.degree_mul_localCommutatorSum_generator_mul_normal_eq_if_isGood
      N θ hinvariant q η n

/-- Summing the local commutator identity over the full fibre above `q`
contributes `|N| |D_q|` when `q` is good and zero otherwise. -/
theorem degree_mul_sum_normalCoset_goodElementCentralizer_commutator
    (N : Subgroup A) [N.Normal]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ a : A, a • θ = θ)
    (q : A ⧸ N)
    (η : IrreducibleCharacter.CyclicOverExtensions N θ q) :
    (θ.degree : ℂ) *
        ∑ n : N,
          ∑ d :
              IrreducibleCharacter.goodElementCentralizer N q,
            θ.values
              ⟨(((IrreducibleCharacter.cyclicOverQuotientGenerator
                      N q) *
                    IrreducibleCharacter.cyclicOverInclusion
                      N q n :
                  IrreducibleCharacter.cyclicOverQuotientElement
                    N q) : A)⁻¹ *
                  (d : A)⁻¹ *
                  (((IrreducibleCharacter.cyclicOverQuotientGenerator
                      N q) *
                    IrreducibleCharacter.cyclicOverInclusion
                      N q n :
                  IrreducibleCharacter.cyclicOverQuotientElement
                    N q) : A) *
                  (d : A),
                IrreducibleCharacter.cyclicOverQuotientGenerator_mul_normal_commutator_mem
                  N q n d⟩ =
      (Nat.card N : ℂ) *
        (if IrreducibleCharacter.IsGoodQuotientElement
            N θ q then
          (Nat.card
            (IrreducibleCharacter.goodElementCentralizer
              N q) : ℂ)
        else 0) := by
  rw [Finset.mul_sum]
  calc
    (∑ n : N,
        (θ.degree : ℂ) *
          ∑ d :
              IrreducibleCharacter.goodElementCentralizer N q,
            θ.values
              ⟨(((IrreducibleCharacter.cyclicOverQuotientGenerator
                      N q) *
                    IrreducibleCharacter.cyclicOverInclusion
                      N q n :
                  IrreducibleCharacter.cyclicOverQuotientElement
                    N q) : A)⁻¹ *
                  (d : A)⁻¹ *
                  (((IrreducibleCharacter.cyclicOverQuotientGenerator
                      N q) *
                    IrreducibleCharacter.cyclicOverInclusion
                      N q n :
                  IrreducibleCharacter.cyclicOverQuotientElement
                    N q) : A) *
                  (d : A),
                IrreducibleCharacter.cyclicOverQuotientGenerator_mul_normal_commutator_mem
                  N q n d⟩) =
        ∑ n : N,
          if IrreducibleCharacter.IsGoodQuotientElement
              N θ q then
            η.1.values
                ((IrreducibleCharacter.cyclicOverQuotientGenerator
                    N q *
                  IrreducibleCharacter.cyclicOverInclusion
                    N q n)⁻¹) *
              η.1.values
                (IrreducibleCharacter.cyclicOverQuotientGenerator
                    N q *
                  IrreducibleCharacter.cyclicOverInclusion
                    N q n) *
              (Nat.card
                (IrreducibleCharacter.goodElementCentralizer
                  N q) : ℂ)
          else 0 := by
      apply Finset.sum_congr rfl
      intro n _
      exact
        degree_mul_localCosetCommutatorSum_eq_if_isGood
          N θ hinvariant q η n
    _ = _ := by
      by_cases hgood :
          IrreducibleCharacter.IsGoodQuotientElement N θ q
      · simp only [hgood, if_true]
        rw [← Finset.sum_mul]
        have hnorm :=
          IrreducibleCharacter.cyclicOverExtension_coset_bilinearNorm
            N θ q η
        have hnorm' :
            (∑ n : N,
              η.1.values
                  ((IrreducibleCharacter.cyclicOverQuotientGenerator
                      N q *
                    IrreducibleCharacter.cyclicOverInclusion
                      N q n)⁻¹) *
                η.1.values
                  (IrreducibleCharacter.cyclicOverQuotientGenerator
                      N q *
                    IrreducibleCharacter.cyclicOverInclusion
                      N q n)) =
              (Nat.card N : ℂ) := by
          calc
            _ =
                ∑ n : N,
                  η.1.values
                      (IrreducibleCharacter.cyclicOverQuotientGenerator
                          N q *
                        IrreducibleCharacter.cyclicOverInclusion
                          N q n) *
                    η.1.values
                      ((IrreducibleCharacter.cyclicOverQuotientGenerator
                          N q *
                        IrreducibleCharacter.cyclicOverInclusion
                          N q n)⁻¹) := by
                apply Finset.sum_congr rfl
                intro n _
                ring
            _ = _ := by
              rw [← hnorm]
              apply Finset.sum_congr
              · ext n
                simp
              · intro n _
                rfl
        rw [hnorm']
      · simp [hgood]

omit [Finite A] in
private theorem quotient_mk_out_mul_normal
    (N : Subgroup A) [N.Normal]
    (q : A ⧸ N) (n : N) :
    QuotientGroup.mk' N
        (Quotient.out q * (n : A)) =
      q :=
  (GroupTheory.quotientFiberEquiv N q n).property

private def normalCommutatorValue
    (N : Subgroup A)
    (θ : IrreducibleCharacter N)
    (x y : A) : ℂ :=
  if hcomm : x⁻¹ * y⁻¹ * x * y ∈ N then
    θ.values ⟨x⁻¹ * y⁻¹ * x * y, hcomm⟩
  else 0

private theorem
    sum_goodElementCentralizer_eq_of_quotient_eq
    (N : Subgroup A) [N.Normal]
    {q r : A ⧸ N} (hqr : q = r)
    (f : A → ℂ) :
    (∑ d :
        IrreducibleCharacter.goodElementCentralizer N q,
      f d) =
      ∑ d :
          IrreducibleCharacter.goodElementCentralizer N r,
        f d := by
  subst r
  rfl

/-- Reindexing the global commutator sum by quotient fibres expresses it as
`|N|` times the centralizer-weighted sum over good quotient elements. -/
theorem
    degree_mul_sum_goodElementCentralizer_commutator_eq_card_mul_goodCentralizerSum
    (N : Subgroup A) [N.Normal]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ a : A, a • θ = θ) :
    (θ.degree : ℂ) *
        ∑ x : A,
          ∑ d :
              IrreducibleCharacter.goodElementCentralizer N
                (QuotientGroup.mk' N x),
            θ.values
              ⟨x⁻¹ * (d : A)⁻¹ * x * (d : A),
                (IrreducibleCharacter.gallagherCommutator_mem_iff_mem_goodElementCentralizer
                  N x (d : A)).mpr d.property⟩ =
      (Nat.card N : ℂ) *
        ∑ q : A ⧸ N,
          if IrreducibleCharacter.IsGoodQuotientElement
              N θ q then
            (Nat.card
              (IrreducibleCharacter.goodElementCentralizer
                N q) : ℂ)
          else 0 := by
  classical
  rw [Finset.mul_sum]
  let f : A → ℂ :=
    fun x =>
      (θ.degree : ℂ) *
        ∑ d :
            IrreducibleCharacter.goodElementCentralizer N
              (QuotientGroup.mk' N x),
          θ.values
            ⟨x⁻¹ * (d : A)⁻¹ * x * (d : A),
              (IrreducibleCharacter.gallagherCommutator_mem_iff_mem_goodElementCentralizer
                N x (d : A)).mpr d.property⟩
  have hreindexRaw :=
    GroupTheory.sum_eq_sum_quotient_mul_subgroup
      N f
  have hreindex :
      (∑ x : A, f x) =
        ∑ q : A ⧸ N, ∑ n : N,
          f (Quotient.out q * (n : A)) := by
    convert hreindexRaw using 1
    · apply Finset.sum_congr
      · ext q
        simp
      · intro q _
        apply Finset.sum_congr
        · ext n
          simp
        · intro n _
          rfl
  change (∑ x : A, f x) = _
  rw [hreindex]
  calc
    (∑ q : A ⧸ N, ∑ n : N,
        f (Quotient.out q * (n : A))) =
        ∑ q : A ⧸ N,
          (Nat.card N : ℂ) *
            (if
              IrreducibleCharacter.IsGoodQuotientElement
                N θ q then
              (Nat.card
                (IrreducibleCharacter.goodElementCentralizer
                  N q) : ℂ)
            else 0) := by
      apply Finset.sum_congr rfl
      intro q _
      let η :=
        Classical.choice
          (IrreducibleCharacter.nonempty_cyclicOverExtensions
            N θ hinvariant q)
      have hlocal :=
        degree_mul_sum_normalCoset_goodElementCentralizer_commutator
          N θ hinvariant q η
      rw [Finset.mul_sum] at hlocal
      have hpoint (n : N) :
          f (Quotient.out q * (n : A)) =
            (θ.degree : ℂ) *
              ∑ d :
                  IrreducibleCharacter.goodElementCentralizer
                    N q,
                θ.values
                  ⟨(((IrreducibleCharacter.cyclicOverQuotientGenerator
                          N q) *
                        IrreducibleCharacter.cyclicOverInclusion
                          N q n :
                      IrreducibleCharacter.cyclicOverQuotientElement
                        N q) : A)⁻¹ *
                      (d : A)⁻¹ *
                      (((IrreducibleCharacter.cyclicOverQuotientGenerator
                          N q) *
                        IrreducibleCharacter.cyclicOverInclusion
                          N q n :
                      IrreducibleCharacter.cyclicOverQuotientElement
                        N q) : A) *
                      (d : A),
                    IrreducibleCharacter.cyclicOverQuotientGenerator_mul_normal_commutator_mem
                      N q n d⟩ := by
        let xA : A := Quotient.out q * (n : A)
        let xU :
            IrreducibleCharacter.cyclicOverQuotientElement
              N q :=
          IrreducibleCharacter.cyclicOverQuotientGenerator
              N q *
            IrreducibleCharacter.cyclicOverInclusion N q n
        let cval : A → ℂ :=
          normalCommutatorValue N θ xA
        have hxquot :
            QuotientGroup.mk' N xA = q :=
          quotient_mk_out_mul_normal N q n
        calc
          f (Quotient.out q * (n : A)) =
              (θ.degree : ℂ) *
                ∑ d :
                    IrreducibleCharacter.goodElementCentralizer
                      N (QuotientGroup.mk' N xA),
                  cval d := by
            dsimp only [f, xA]
            congr 1
            apply Finset.sum_congr rfl
            intro d _
            have hcomm :
                xA⁻¹ * (d : A)⁻¹ * xA * (d : A) ∈ N :=
              (IrreducibleCharacter.gallagherCommutator_mem_iff_mem_goodElementCentralizer
                N xA (d : A)).mpr d.property
            simp only [cval, normalCommutatorValue,
              hcomm, ↓reduceDIte]
            rfl
          _ =
              (θ.degree : ℂ) *
                ∑ d :
                    IrreducibleCharacter.goodElementCentralizer
                      N q,
                  cval d := by
            congr 1
            exact
              sum_goodElementCentralizer_eq_of_quotient_eq
                N hxquot cval
          _ = _ := by
            congr 1
            apply Finset.sum_congr rfl
            intro d _
            have hcomm :
                xA⁻¹ * (d : A)⁻¹ * xA * (d : A) ∈ N := by
              have h :=
                IrreducibleCharacter.cyclicOverQuotientGenerator_mul_normal_commutator_mem
                  N q n d
              change
                (Quotient.out q * (n : A))⁻¹ *
                    (d : A)⁻¹ *
                    (Quotient.out q * (n : A)) *
                    (d : A) ∈ N
                at h
              exact h
            simp only [cval, normalCommutatorValue,
              hcomm, ↓reduceDIte]
            rfl
      calc
        (∑ n : N,
            f (Quotient.out q * (n : A))) =
            ∑ n : N,
              (θ.degree : ℂ) *
                ∑ d :
                    IrreducibleCharacter.goodElementCentralizer
                      N q,
                  θ.values
                    ⟨(((IrreducibleCharacter.cyclicOverQuotientGenerator
                            N q) *
                          IrreducibleCharacter.cyclicOverInclusion
                            N q n :
                        IrreducibleCharacter.cyclicOverQuotientElement
                          N q) : A)⁻¹ *
                        (d : A)⁻¹ *
                        (((IrreducibleCharacter.cyclicOverQuotientGenerator
                            N q) *
                          IrreducibleCharacter.cyclicOverInclusion
                            N q n :
                        IrreducibleCharacter.cyclicOverQuotientElement
                          N q) : A) *
                        (d : A),
                      IrreducibleCharacter.cyclicOverQuotientGenerator_mul_normal_commutator_mem
                        N q n d⟩ := by
          apply Finset.sum_congr rfl
          intro n _
          exact hpoint n
        _ = _ := hlocal
    _ = _ := by
      rw [Finset.mul_sum]

/-- Division-free form of Gallagher's good-element count, before grouping
good quotient elements into conjugacy classes. -/
theorem
    card_mul_natCard_irreducibleCharactersOverAlong_eq_goodElementCentralizerSum
    (N : Subgroup A) [N.Normal]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ a : A, a • θ = θ) :
    Nat.card A *
        Nat.card
          (IrreducibleCharactersOverAlong N.subtype θ) =
      ∑ q : A ⧸ N,
        if IrreducibleCharacter.IsGoodQuotientElement
            N θ q then
          Nat.card
            (IrreducibleCharacter.goodElementCentralizer
              N q)
        else 0 := by
  classical
  have hglobalRaw :=
    degree_mul_sum_goodElementCentralizer_commutator
      N θ hinvariant
  have hglobal :
      (θ.degree : ℂ) *
          ∑ x : A,
            ∑ d :
                IrreducibleCharacter.goodElementCentralizer N
                  (QuotientGroup.mk' N x),
              θ.values
                ⟨x⁻¹ * (d : A)⁻¹ * x * (d : A),
                  (IrreducibleCharacter.gallagherCommutator_mem_iff_mem_goodElementCentralizer
                    N x (d : A)).mpr d.property⟩ =
        (Nat.card A : ℂ) * (Nat.card N : ℂ) *
          (Nat.card
            (IrreducibleCharactersOverAlong
              N.subtype θ) : ℂ) := by
    convert hglobalRaw using 1
  have hlocal :=
    degree_mul_sum_goodElementCentralizer_commutator_eq_card_mul_goodCentralizerSum
      N θ hinvariant
  have heq :
      (Nat.card A : ℂ) * (Nat.card N : ℂ) *
          (Nat.card
            (IrreducibleCharactersOverAlong
              N.subtype θ) : ℂ) =
        (Nat.card N : ℂ) *
          ∑ q : A ⧸ N,
            if IrreducibleCharacter.IsGoodQuotientElement
                N θ q then
              (Nat.card
                (IrreducibleCharacter.goodElementCentralizer
                  N q) : ℂ)
            else 0 :=
    hglobal.symm.trans hlocal
  have hNne : (Nat.card N : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr
      (Nat.card_pos (α := N)).ne'
  have hcancel :
      (Nat.card A : ℂ) *
          (Nat.card
            (IrreducibleCharactersOverAlong
              N.subtype θ) : ℂ) =
        ∑ q : A ⧸ N,
          if IrreducibleCharacter.IsGoodQuotientElement
              N θ q then
            (Nat.card
              (IrreducibleCharacter.goodElementCentralizer
                N q) : ℂ)
          else 0 := by
    apply mul_left_cancel₀ hNne
    calc
      (Nat.card N : ℂ) *
            ((Nat.card A : ℂ) *
              (Nat.card
                (IrreducibleCharactersOverAlong
                  N.subtype θ) : ℂ)) =
          (Nat.card A : ℂ) * (Nat.card N : ℂ) *
            (Nat.card
              (IrreducibleCharactersOverAlong
                N.subtype θ) : ℂ) := by
        ring
      _ = _ := heq
  exact_mod_cast hcancel

/-- Gallagher's ordinary theorem: irreducible characters above an invariant
normal-subgroup character are equinumerous with its good quotient classes. -/
theorem
    natCard_irreducibleCharactersOverAlong_eq_goodQuotientConjugacyClasses
    (N : Subgroup A) [N.Normal]
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ a : A, a • θ = θ) :
    Nat.card
        (IrreducibleCharactersOverAlong N.subtype θ) =
      Nat.card
        (IrreducibleCharacter.GoodQuotientConjugacyClasses
          N θ) := by
  classical
  have hdivisionFree :=
    card_mul_natCard_irreducibleCharactersOverAlong_eq_goodElementCentralizerSum
      N θ hinvariant
  have hclassSum :=
    sum_natCard_goodElementCentralizer_eq_card_mul_natCard_goodQuotientConjugacyClasses
      N θ hinvariant
  apply Nat.eq_of_mul_eq_mul_left
    (Nat.card_pos (α := A))
  exact hdivisionFree.trans hclassSum

end CliffordCorrespondence
end McKayConjecture
