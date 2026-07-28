/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ElementaryBrauerInductionReduction
import McKayConjecture.Character.Transport

/-!
# Automatic elementary Brauer induction cases

If the ambient group is itself displayed as an elementary subgroup, Brauer
induction is immediate: induce the transported irreducible character from
the top subgroup.  This file verifies that base case, including the exact
class-function computation for induction from `⊤`.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace ClassFunction

variable {G : Type} [Group G] [Finite G]

noncomputable local instance elementaryBrauerAutomaticFintypeG :
    Fintype G :=
  Fintype.ofFinite _

/-- Induction from the top subgroup of the pullback of a class function
along `Subgroup.topEquiv` recovers the original class function. -/
theorem induce_top_comap_topEquiv
    (f : ClassFunction G) :
    induce (⊤ : Subgroup G)
        (comapLinearMap
          (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom
          f) =
      f := by
  classical
  apply ClassFunction.ext
  intro g
  rw [induce_apply]
  have hterm :
      ∀ x : G,
        inductionTerm (⊤ : Subgroup G)
            (comapLinearMap
              (Subgroup.topEquiv :
                (⊤ : Subgroup G) ≃* G).toMonoidHom f)
            x g =
          f g := by
    intro x
    have hx : x⁻¹ * g * x ∈ (⊤ : Subgroup G) := by simp
    rw [inductionTerm_of_mem _ _ hx]
    change f (x⁻¹ * g * x) = f g
    have hconj := conj_apply f g x⁻¹
    simpa only [inv_inv] using hconj
  rw [Finset.sum_congr rfl (fun x _hx ↦ hterm x),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  have hcard :
      Nat.card (⊤ : Subgroup G) = Nat.card G :=
    Nat.card_congr Subgroup.topEquiv.toEquiv
  rw [hcard]
  have hne : (Nat.card G : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp

/-- The class function of a character transported to the top subgroup
induces back to the original irreducible character. -/
theorem induce_top_comap_irreducible
    (χ : IrreducibleCharacter G) :
    induce (⊤ : Subgroup G)
        ((χ.comap Subgroup.topEquiv).toClassFunction) =
      χ.toClassFunction := by
  have hcomap :
      (χ.comap Subgroup.topEquiv).toClassFunction =
        comapLinearMap
          (Subgroup.topEquiv :
            (⊤ : Subgroup G) ≃* G).toMonoidHom
          χ.toClassFunction := by
    ext s
    rfl
  rw [hcomap, induce_top_comap_topEquiv]

/-- If the top subgroup has a displayed elementary decomposition, the
denominator-one elementary Brauer-induction formula holds. -/
theorem hasElementaryBrauerInduction_of_top_decomposition
    (q : ℕ) (hq : q.Prime)
    (D : PElementaryDecomposition q (⊤ : Subgroup G)) :
    HasElementaryBrauerInduction (G := G) := by
  intro χ
  classical
  let t : ElementaryInductionTerm G :=
    { prime := q
      prime_isPrime := hq
      subgroup := ⊤
      decomposition := D
      character := χ.comap Subgroup.topEquiv }
  refine ⟨Finsupp.single t 1, ?_⟩
  change
    ((1 : ℤ) : ℂ) • χ.toClassFunction =
      elementaryInductionCombination (Finsupp.single t 1)
  norm_num only [Int.cast_one, one_smul]
  rw [elementaryInductionCombination]
  simp only [Finsupp.support_single _ one_ne_zero,
    Finset.sum_singleton, Finsupp.single_eq_same, Int.cast_one,
    one_smul]
  change
    χ.toClassFunction =
      induce (⊤ : Subgroup G)
        ((χ.comap Subgroup.topEquiv).toClassFunction)
  exact (induce_top_comap_irreducible χ).symm

/-- Brauer's local criterion is unconditional when the ambient group itself
is displayed as elementary. -/
theorem isGeneralizedCharacter_of_elementary_top_local
    (q : ℕ) (hq : q.Prime)
    (D : PElementaryDecomposition q (⊤ : Subgroup G))
    {f : ClassFunction G}
    (hlocal :
      ∀ (r : ℕ), r.Prime →
        ∀ (S : Subgroup G)
          (E : PElementaryDecomposition r S),
          IsGeneralizedCharacter
            (restrictToPElementaryProduct S E f)) :
    IsGeneralizedCharacter f :=
  isGeneralizedCharacter_of_elementary_local
    (hasElementaryBrauerInduction_of_top_decomposition q hq D)
    hlocal

end ClassFunction
end McKayConjecture
