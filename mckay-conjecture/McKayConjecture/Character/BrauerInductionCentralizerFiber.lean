/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerInductionElementaryRegularPart
import McKayConjecture.Character.BrauerInductionTransitivity
import McKayConjecture.Character.PRegularCentralizer

/-!
# Bernstein's regular-fibre function induced from a centralizer

For a `p`-regular element `a`, this file forms the canonical regular-fibre
function inside `C_G(a)` and induces it to `G`.  The local function is
supported exactly on elements of the centralizer whose canonical
`p`-regular part is `a`.  The ambient induced function is consequently
supported on the conjugacy class of `a`.

At every product `a * t`, where `t` is a commuting `p`-element, ambient
induction from the centralizer does not change the local value.  In
particular this value is a natural number prime to `p`.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace ClassFunction

variable {p : ℕ}
variable {G : Type} [Group G] [Finite G] [Fact p.Prime]

noncomputable local instance centralizerFiberFintypeG :
    Fintype G :=
  Fintype.ofFinite _

noncomputable local instance centralizerFiberFintype
    (a : G) :
    Fintype (PRegularCentralizer.group a) :=
  Fintype.ofFinite _

/-- The canonical elementary subgroup in the centralizer of a
`p`-regular ambient element. -/
abbrev centralizerElementarySubgroup
    (a : G) :
    Subgroup (PRegularCentralizer.group a) :=
  centralPRegularElementarySubgroup
    (PRegularCentralizer.element a)
    (PRegularCentralizer.sylow p a)

/-- Bernstein's canonical regular-fibre function after induction to the
centralizer. -/
def centralizerLocalFiber
    (a : G) (ha : IsPRegular p a) :
    ClassFunction (PRegularCentralizer.group a) :=
  induce
    (centralizerElementarySubgroup (p := p) a)
    (centralPRegularFiber
      (PRegularCentralizer.element a)
      (PRegularCentralizer.element_mem_center a)
      (PRegularCentralizer.element_isPRegular p ha)
      (PRegularCentralizer.sylow p a))

/-- The centralizer regular-fibre function induced to the ambient group. -/
def centralizerGlobalFiber
    (a : G) (ha : IsPRegular p a) :
    ClassFunction G :=
  induce (PRegularCentralizer.group a)
    (centralizerLocalFiber (p := p) a ha)

/-- The local centralizer function vanishes unless the canonical
`p`-regular part is the distinguished central element. -/
theorem centralizerLocalFiber_apply_eq_zero_of_regularPart_ne
    (a : G) (ha : IsPRegular p a)
    (y : PRegularCentralizer.group a)
    (hy :
      (PRegularDecomposition.chosen p y).regularPart ≠
        PRegularCentralizer.element a) :
    centralizerLocalFiber (p := p) a ha y = 0 := by
  classical
  let C := PRegularCentralizer.group a
  let aC : C := PRegularCentralizer.element a
  let P : Sylow p C := PRegularCentralizer.sylow p a
  let E : Subgroup C :=
    centralPRegularElementarySubgroup aC P
  let D : PElementaryDecomposition p E :=
    centralPRegularElementaryDecomposition
      aC
      (PRegularCentralizer.element_mem_center a)
      (PRegularCentralizer.element_isPRegular p ha)
      P
  let aD : D.cyclicPart :=
    centralPRegularCyclicCoordinate
      aC
      (PRegularCentralizer.element_mem_center a)
      (PRegularCentralizer.element_isPRegular p ha)
      P
  change
    induce E
        (regularFiber D aD
          (Nat.card D.cyclicPart)) y =
      0
  rw [induce_apply]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro z _hz
  by_cases hzy : z⁻¹ * y * z ∈ E
  · rw [inductionTerm_of_mem E _ hzy]
    let w : E := ⟨z⁻¹ * y * z, hzy⟩
    apply
      regularFiber_apply_eq_zero_of_regularPart_ne
        D aD (Nat.card D.cyclicPart) w
    intro hw
    apply hy
    have hmap :=
      PRegularDecomposition.chosen_regularPart_map
        p w E.subtype
    have hconj :=
      PRegularDecomposition.chosen_regularPart_conj
        p z⁻¹ y
    have hconj' :
        (PRegularDecomposition.chosen
            p (z⁻¹ * y * z)).regularPart =
          z⁻¹ *
            (PRegularDecomposition.chosen p y).regularPart *
            z := by
      rw [inv_inv] at hconj
      exact hconj
    have hmap' :
        (PRegularDecomposition.chosen
          p (E.subtype w)).regularPart =
          PRegularCentralizer.element a := by
      calc
        (PRegularDecomposition.chosen
            p (E.subtype w)).regularPart =
            E.subtype
              (PRegularDecomposition.chosen p w).regularPart := by
          exact hmap
        _ = E.subtype (aD : E) := by rw [hw]
        _ = PRegularCentralizer.element a := by
          exact
            centralPRegularCyclicCoordinate_coe
              aC
              (PRegularCentralizer.element_mem_center a)
              (PRegularCentralizer.element_isPRegular p ha)
              P
    have hconjugated :
        z⁻¹ *
            (PRegularDecomposition.chosen p y).regularPart *
            z =
          PRegularCentralizer.element a := by
      calc
        z⁻¹ *
              (PRegularDecomposition.chosen p y).regularPart *
              z =
            (PRegularDecomposition.chosen
              p (z⁻¹ * y * z)).regularPart := by
          exact hconj'.symm
        _ =
            (PRegularDecomposition.chosen
              p (E.subtype w)).regularPart := by
          rfl
        _ = PRegularCentralizer.element a := hmap'
    have haCenter :
        PRegularCentralizer.element a ∈
          Subgroup.center C :=
      PRegularCentralizer.element_mem_center a
    calc
      (PRegularDecomposition.chosen p y).regularPart =
          z *
            (z⁻¹ *
              (PRegularDecomposition.chosen p y).regularPart *
              z) *
            z⁻¹ := by group
      _ =
          z * PRegularCentralizer.element a * z⁻¹ := by
        rw [hconjugated]
      _ = PRegularCentralizer.element a := by
        rw [Subgroup.mem_center_iff.mp haCenter z,
          mul_assoc, mul_inv_cancel, mul_one]
  · rw [inductionTerm_of_not_mem E _ hzy]

/-- An ambient induction summand vanishes unless the conjugated
`p`-regular part is the distinguished element. -/
theorem inductionTerm_centralizerLocalFiber_eq_zero_of_regularPart_ne
    (a : G) (ha : IsPRegular p a)
    (x g : G)
    (hx :
      x⁻¹ *
          (PRegularDecomposition.chosen p g).regularPart *
          x ≠
        a) :
    inductionTerm
        (PRegularCentralizer.group a)
        (centralizerLocalFiber (p := p) a ha)
        x g =
      0 := by
  let C := PRegularCentralizer.group a
  by_cases hxg : x⁻¹ * g * x ∈ C
  · rw [inductionTerm_of_mem C _ hxg]
    let y : C := ⟨x⁻¹ * g * x, hxg⟩
    apply
      centralizerLocalFiber_apply_eq_zero_of_regularPart_ne
        a ha y
    intro hy
    apply hx
    have hmap :=
      PRegularDecomposition.chosen_regularPart_map
        p y C.subtype
    have hconj :=
      PRegularDecomposition.chosen_regularPart_conj
        p x⁻¹ g
    have hconj' :
        (PRegularDecomposition.chosen
            p (x⁻¹ * g * x)).regularPart =
          x⁻¹ *
            (PRegularDecomposition.chosen p g).regularPart *
            x := by
      rw [inv_inv] at hconj
      exact hconj
    calc
      x⁻¹ *
            (PRegularDecomposition.chosen p g).regularPart *
            x =
          (PRegularDecomposition.chosen
            p (x⁻¹ * g * x)).regularPart := by
        exact hconj'.symm
      _ =
          (PRegularDecomposition.chosen
            p (C.subtype y)).regularPart := by
        rfl
      _ =
          C.subtype
            (PRegularDecomposition.chosen p y).regularPart := by
        exact hmap
      _ = a := by
        rw [hy]
        rfl
  · rw [inductionTerm_of_not_mem C _ hxg]

/-- The ambient centralizer fibre vanishes off the conjugacy class of
the canonical `p`-regular part. -/
theorem centralizerGlobalFiber_apply_eq_zero_of_not_isConj
    (a : G) (ha : IsPRegular p a)
    (g : G)
    (hg :
      ¬ IsConj
        (PRegularDecomposition.chosen p g).regularPart
        a) :
    centralizerGlobalFiber (p := p) a ha g = 0 := by
  rw [centralizerGlobalFiber, induce_apply]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro x _hx
  apply
    inductionTerm_centralizerLocalFiber_eq_zero_of_regularPart_ne
      a ha x g
  intro hconj
  apply hg
  rw [isConj_iff]
  exact ⟨x⁻¹, by simpa using hconj⟩

/-- On a product of the distinguished element with a commuting
`p`-element, induction from the centralizer leaves the local fibre value
unchanged. -/
theorem centralizerGlobalFiber_apply_mul_pElement
    (a : G) (ha : IsPRegular p a)
    (t : G) (ht : IsPElement p t)
    (hat : Commute a t) :
    centralizerGlobalFiber (p := p) a ha (a * t) =
      centralizerLocalFiber (p := p) a ha
        (PRegularCentralizer.element a *
          PRegularCentralizer.commutingElement hat) := by
  classical
  let C := PRegularCentralizer.group a
  let aC : C := PRegularCentralizer.element a
  let tC : C :=
    PRegularCentralizer.commutingElement hat
  let ψ : ClassFunction C :=
    centralizerLocalFiber (p := p) a ha
  have hregular :
      (PRegularDecomposition.chosen
        p (a * t)).regularPart =
        a :=
    PRegularDecomposition.chosen_regularPart_mul_rev
      ht ha hat
  have hterm :
      ∀ x : G,
        inductionTerm C ψ x (a * t) =
          if x ∈ C then
            ψ (aC * tC)
          else 0 := by
    intro x
    by_cases hxC : x ∈ C
    · have hconjugate :
          x⁻¹ * (a * t) * x ∈ C := by
        let xC : C := ⟨x, hxC⟩
        change
          ((xC⁻¹ * (aC * tC) * xC : C) : G) ∈ C
        exact
          (xC⁻¹ * (aC * tC) * xC).property
      rw [inductionTerm_of_mem C ψ hconjugate]
      simp only [hxC, if_pos]
      let xC : C := ⟨x, hxC⟩
      have heq :
          (⟨x⁻¹ * (a * t) * x,
              hconjugate⟩ : C) =
            xC⁻¹ * (aC * tC) * xC := by
        apply Subtype.ext
        rfl
      rw [heq]
      simpa only [inv_inv] using
        ClassFunction.conj_apply ψ
          (aC * tC) xC⁻¹
    · simp only [hxC]
      apply
        inductionTerm_centralizerLocalFiber_eq_zero_of_regularPart_ne
          a ha x (a * t)
      rw [hregular]
      intro hconjugated
      apply hxC
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcommute : a * x = x * a := by
        calc
          a * x =
              x *
                (x⁻¹ * a * x) := by group
          _ = x * a := by rw [hconjugated]
      exact hcommute.symm
  rw [centralizerGlobalFiber, induce_apply]
  change
    (Nat.card C : ℂ)⁻¹ *
        ∑ x : G,
          inductionTerm C ψ x (a * t) =
      ψ (aC * tC)
  simp_rw [hterm]
  have hsum :
    (∑ x : G,
          if x ∈ C then
            ψ (aC * tC)
          else 0) =
        (Nat.card C : ℂ) *
          ψ (aC * tC) := by
    calc
      (∑ x : G,
          if x ∈ C then
            ψ (aC * tC)
          else 0) =
          ∑ x ∈ Finset.univ.filter
              (fun x : G => x ∈ C),
            ψ (aC * tC) := by
        rw [Finset.sum_filter]
      _ =
          ∑ _x : C, ψ (aC * tC) := by
        apply Finset.sum_subtype
        intro x
        simp only [Finset.mem_filter,
          Finset.mem_univ, true_and, C]
      _ =
          (Nat.card C : ℂ) *
            ψ (aC * tC) := by
        simp only [Finset.sum_const, Finset.card_univ,
          ← Nat.card_eq_fintype_card, nsmul_eq_mul]
  rw [hsum]
  have hC : (Nat.card C : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp

/-- The value of the ambient centralizer fibre at `a * t` is a natural
number prime to `p`. -/
theorem exists_coprime_nat_centralizerGlobalFiber_mul_pElement
    (a : G) (ha : IsPRegular p a)
    (t : G) (ht : IsPElement p t)
    (hat : Commute a t) :
    ∃ k : ℕ, p.Coprime k ∧
      centralizerGlobalFiber (p := p) a ha (a * t) =
        (k : ℂ) := by
  rw [centralizerGlobalFiber_apply_mul_pElement
    a ha t ht hat]
  exact
    exists_coprime_nat_induce_centralPRegularFiber
      (PRegularCentralizer.element a)
      (PRegularCentralizer.element_mem_center a)
      (PRegularCentralizer.element_isPRegular p ha)
      (PRegularCentralizer.sylow p a)
      (PRegularCentralizer.commutingElement hat)
      (PRegularCentralizer.commutingElement_isPElement
        p hat ht)

end ClassFunction
end McKayConjecture
