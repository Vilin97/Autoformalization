/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerInductionBernsteinElement
import McKayConjecture.Character.BrauerInductionCyclotomicIdeal

/-!
# The Bernstein element in the elementary-induction ideal

The regular-fibre function on the canonical elementary subgroup is both
integer-valued and a generalized character over any integral cyclotomic
ring whose index is divisible by the order of its cyclic factor.  Transporting
this function from a centralizer into the ambient group therefore gives one
of the defining generators of Bernstein's ideal.

This file packages that local datum for every `p`-regular conjugacy class.
It follows that every global class fibre, their sum (the Bernstein element),
and every positive power of that sum belong to the elementary-induction
ideal in `Q_|G|(G)`.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace ClassFunction

variable {p n : ℕ}
variable {E : Type} [Group E] [Finite E]

/-- A regular-fibre function has rational-integer values. -/
theorem regularFiber_isIntegerValued
    (D : PElementaryDecomposition p E)
    (a : D.cyclicPart)
    (m : ℕ) :
    IsIntegerValued (regularFiber D a m) := by
  intro x
  by_cases hx :
      (D.multiplicationEquiv.symm x).1 = a
  · refine ⟨(m : ℤ), ?_⟩
    simpa using
      regularFiber_apply_of_cyclicCoordinate_eq
        D a m x hx
  · refine ⟨0, ?_⟩
    simpa using
      regularFiber_apply_of_cyclicCoordinate_ne
        D a m x hx

/-- The Fourier formula realizes a regular fibre over every common
cyclotomic coefficient ring whose index is divisible by the cyclic-factor
order. -/
theorem regularFiber_isCyclotomicGeneralizedCharacter
    (n : ℕ) (hn : 0 < n)
    (D : PElementaryDecomposition p E)
    (a : D.cyclicPart)
    (hdiv : Nat.card D.cyclicPart ∣ n) :
    IsCyclotomicGeneralizedCharacter n hn
      (regularFiber D a (Nat.card D.cyclicPart)) := by
  classical
  rw [regularFiber_card_eq_sum_linearCharacters D a]
  apply isCyclotomicGeneralizedCharacter_finset_sum
  intro lam _hlam
  rw [← evaluate_liftedRegularFiberWeightAt
    n hn D a lam hdiv]
  exact
    (isGeneralizedCharacter_irreducible
        (regularFiberLinearCharacter D lam)).isCyclotomic
      n hn
      |>.smul
        (liftedRegularFiberWeightAt
          n hn D a lam hdiv)

/-- A regular fibre is an element of `Q_n(E)` whenever the cyclic-factor
order divides `n`. -/
theorem regularFiber_isCyclotomicIntegerCharacter
    (n : ℕ) (hn : 0 < n)
    (D : PElementaryDecomposition p E)
    (a : D.cyclicPart)
    (hdiv : Nat.card D.cyclicPart ∣ n) :
    IsCyclotomicIntegerCharacter n hn
      (regularFiber D a (Nat.card D.cyclicPart)) :=
  ⟨regularFiber_isCyclotomicGeneralizedCharacter
      n hn D a hdiv,
    regularFiber_isIntegerValued
      D a (Nat.card D.cyclicPart)⟩

/-- Relabelling a cyclotomic integer character across a group equivalence
preserves membership in `Q_n`. -/
theorem IsCyclotomicIntegerCharacter.comapLinearEquiv
    {H : Type} [Group H] [Finite H]
    (hn : 0 < n)
    (e : H ≃* E)
    {f : ClassFunction E}
    (hf : IsCyclotomicIntegerCharacter n hn f) :
    IsCyclotomicIntegerCharacter n hn
      (ClassFunction.comapLinearEquiv e f) := by
  have hcomap :=
    hf.comap e.toMonoidHom
  convert hcomap using 1
  apply ClassFunction.ext
  intro h
  rfl

variable {G : Type} [Group G] [Finite G] [Fact p.Prime]

noncomputable local instance bernsteinIdealMembershipFintypeG :
    Fintype G :=
  Fintype.ofFinite _

noncomputable local instance bernsteinIdealMembershipFiniteClasses :
    Finite (PRegularConjClasses p G) :=
  Finite.of_injective
    Subtype.val Subtype.val_injective

noncomputable local instance bernsteinIdealMembershipFintypeClasses :
    Fintype (PRegularConjClasses p G) :=
  Fintype.ofFinite _

/-- The transported regular fibre attached to a `p`-regular class,
bundled as a local element of `Q_|G|` on its ambient elementary subgroup. -/
def pRegularClassFiberLocalCharacter
    (q : PRegularConjClasses p G) :
    cyclotomicIntegerCharacterSubring
      (G :=
        (centralizerElementarySubgroup
          (p := p) q.representative).map
          (PRegularCentralizer.group
            q.representative).subtype)
      (Nat.card G) Nat.card_pos := by
  let a := q.representative
  let C := PRegularCentralizer.group a
  let aC : C := PRegularCentralizer.element a
  let haC : IsPRegular p aC :=
    PRegularCentralizer.element_isPRegular
      p q.representative_isPRegular
  let P : Sylow p C :=
    PRegularCentralizer.sylow p a
  let E₀ : Subgroup C :=
    centralPRegularElementarySubgroup aC P
  let D : PElementaryDecomposition p E₀ :=
    centralPRegularElementaryDecomposition
      aC
      (PRegularCentralizer.element_mem_center a)
      haC P
  let aD : D.cyclicPart :=
    centralPRegularCyclicCoordinate
      aC
      (PRegularCentralizer.element_mem_center a)
      haC P
  let e :
      E₀ ≃* E₀.map C.subtype :=
    E₀.equivMapOfInjective
      C.subtype C.subtype_injective
  have hdiv : Nat.card D.cyclicPart ∣ Nat.card G :=
    PRegularCentralizer.cyclicPart_card_dvd_ambient
      p q.representative_isPRegular
  have hlocal :
      IsCyclotomicIntegerCharacter
        (Nat.card G) Nat.card_pos
        (centralPRegularFiber
          aC
          (PRegularCentralizer.element_mem_center a)
          haC P) := by
    exact
      regularFiber_isCyclotomicIntegerCharacter
        (Nat.card G) Nat.card_pos D aD hdiv
  refine
    ⟨mapSubtypeClassFunction C E₀
        (centralPRegularFiber
          aC
          (PRegularCentralizer.element_mem_center a)
          haC P),
      ?_⟩
  change
    IsCyclotomicIntegerCharacter
      (Nat.card G) Nat.card_pos
      (ClassFunction.comapLinearEquiv e.symm
        (centralPRegularFiber
          aC
          (PRegularCentralizer.element_mem_center a)
          haC P))
  exact hlocal.comapLinearEquiv Nat.card_pos e.symm

/-- The displayed elementary-induction datum whose induction is the global
fibre attached to a `p`-regular conjugacy class. -/
def pRegularClassFiberDatum
    (q : PRegularConjClasses p G) :
    CyclotomicElementaryInductionDatum
      G (Nat.card G) Nat.card_pos := by
  let a := q.representative
  let C := PRegularCentralizer.group a
  let aC : C := PRegularCentralizer.element a
  let haC : IsPRegular p aC :=
    PRegularCentralizer.element_isPRegular
      p q.representative_isPRegular
  let P : Sylow p C :=
    PRegularCentralizer.sylow p a
  let E₀ : Subgroup C :=
    centralPRegularElementarySubgroup aC P
  let D : PElementaryDecomposition p E₀ :=
    centralPRegularElementaryDecomposition
      aC
      (PRegularCentralizer.element_mem_center a)
      haC P
  let e :
      E₀ ≃* E₀.map C.subtype :=
    E₀.equivMapOfInjective
      C.subtype C.subtype_injective
  exact
    { prime := p
      prime_isPrime := Fact.out
      subgroup := E₀.map C.subtype
      decomposition := D.mapEquiv e
      localCharacter :=
        pRegularClassFiberLocalCharacter q }

/-- The induction of the packaged local datum is exactly the corresponding
global Bernstein class fibre. -/
theorem pRegularClassFiberDatum_induced
    (q : PRegularConjClasses p G) :
    ((pRegularClassFiberDatum q).induced :
        ClassFunction G) =
      pRegularClassFiber q := by
  let a := q.representative
  let C := PRegularCentralizer.group a
  let aC : C := PRegularCentralizer.element a
  let haC : IsPRegular p aC :=
    PRegularCentralizer.element_isPRegular
      p q.representative_isPRegular
  let P : Sylow p C :=
    PRegularCentralizer.sylow p a
  let E₀ : Subgroup C :=
    centralPRegularElementarySubgroup aC P
  let θ : ClassFunction E₀ :=
    centralPRegularFiber
      aC
      (PRegularCentralizer.element_mem_center a)
      haC P
  change
    induce (E₀.map C.subtype)
        (mapSubtypeClassFunction C E₀ θ) =
      induce C (induce E₀ θ)
  exact
    (induce_induce_subgroup C E₀ θ).symm

/-- Every global class fibre belongs to Bernstein's elementary-induction
ideal. -/
theorem pRegularClassFiber_mem_cyclotomicElementaryInductionIdeal
    (q : PRegularConjClasses p G) :
    (⟨pRegularClassFiber q, by
        rw [← pRegularClassFiberDatum_induced q]
        exact (pRegularClassFiberDatum q).induced.property⟩ :
      cyclotomicIntegerCharacterSubring
        (G := G) (Nat.card G) Nat.card_pos) ∈
      cyclotomicElementaryInductionIdeal
        (G := G) (n := Nat.card G)
        (hn := Nat.card_pos) := by
  have hmem :=
    induced_mem_cyclotomicElementaryInductionIdeal
      (pRegularClassFiberDatum q)
  have heq :
      (⟨pRegularClassFiber q, by
          rw [← pRegularClassFiberDatum_induced q]
          exact
            (pRegularClassFiberDatum q).induced.property⟩ :
        cyclotomicIntegerCharacterSubring
          (G := G) (Nat.card G) Nat.card_pos) =
        (pRegularClassFiberDatum q).induced := by
    apply Subtype.ext
    exact (pRegularClassFiberDatum_induced q).symm
  rw [heq]
  exact hmem

/-- The Bernstein element, bundled as an element of `Q_|G|(G)`. -/
def bernsteinElementInCyclotomicIntegerCharacterRing :
    cyclotomicIntegerCharacterSubring
      (G := G) (Nat.card G) Nat.card_pos :=
  ∑ q ∈ (Finset.univ :
      Finset (PRegularConjClasses p G)),
    ⟨pRegularClassFiber q, by
      rw [← pRegularClassFiberDatum_induced q]
      exact (pRegularClassFiberDatum q).induced.property⟩

@[simp]
theorem bernsteinElementInCyclotomicIntegerCharacterRing_coe :
    ((bernsteinElementInCyclotomicIntegerCharacterRing
        (p := p) (G := G) :
      cyclotomicIntegerCharacterSubring
        (G := G) (Nat.card G) Nat.card_pos) :
      ClassFunction G) =
      bernsteinElement (p := p) (G := G) := by
  unfold
    bernsteinElementInCyclotomicIntegerCharacterRing
    bernsteinElement
  apply ClassFunction.ext
  intro g
  simp

/-- The global Bernstein element belongs to the elementary-induction
ideal. -/
theorem bernsteinElement_mem_cyclotomicElementaryInductionIdeal :
    bernsteinElementInCyclotomicIntegerCharacterRing
        (p := p) (G := G) ∈
      cyclotomicElementaryInductionIdeal
        (G := G) (n := Nat.card G)
        (hn := Nat.card_pos) := by
  classical
  apply Ideal.sum_mem
  intro q _hq
  exact
    pRegularClassFiber_mem_cyclotomicElementaryInductionIdeal q

/-- Every natural power of the Bernstein element remains in the
elementary-induction ideal. -/
theorem bernsteinElement_pow_mem_cyclotomicElementaryInductionIdeal
    (m : ℕ) (hm : 0 < m) :
    bernsteinElementInCyclotomicIntegerCharacterRing
          (p := p) (G := G) ^ m ∈
      cyclotomicElementaryInductionIdeal
        (G := G) (n := Nat.card G)
        (hn := Nat.card_pos) := by
  exact
    Ideal.pow_mem_of_mem
      (cyclotomicElementaryInductionIdeal
        (G := G) (n := Nat.card G)
        (hn := Nat.card_pos))
      bernsteinElement_mem_cyclotomicElementaryInductionIdeal
      m hm

/-- In particular, the Euler power used in Bernstein's congruence belongs
to the elementary-induction ideal. -/
theorem bernsteinElement_totientPrimePower_mem_cyclotomicElementaryInductionIdeal
    (k : ℕ) :
    bernsteinElementInCyclotomicIntegerCharacterRing
          (p := p) (G := G) ^ (p ^ k).totient ∈
      cyclotomicElementaryInductionIdeal
        (G := G) (n := Nat.card G)
        (hn := Nat.card_pos) := by
  apply
    bernsteinElement_pow_mem_cyclotomicElementaryInductionIdeal
  exact
    Nat.totient_pos.mpr
      (pow_pos ((Fact.out : p.Prime).pos) k)

end ClassFunction
end McKayConjecture
