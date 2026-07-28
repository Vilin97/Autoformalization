/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ClassFunctionProjectionFormula
import McKayConjecture.Character.CyclotomicIntegerCharacter
import McKayConjecture.Character.ElementaryBrauerInductionReduction

/-!
# The elementary-induction ideal in Bernstein's cyclotomic ring

Let `Q_n(G)` be the ring of integer-valued cyclotomic generalized
characters.  The additive span of all inductions

`Ind_E^G θ`, with `E` elementary and `θ ∈ Q_n(E)`,

is an ideal of `Q_n(G)`.  Closure under multiplication is precisely the
projection formula: multiplication by an ambient element can be moved
inside induction after restriction.

We deliberately define the carrier as an additive closure, rather than as
an abstract ideal span.  This retains an induction principle which later
extracts a finite cyclotomic linear combination of induced irreducible
characters from ideal membership.
-/

noncomputable section

namespace McKayConjecture

open scoped BigOperators

/-- Data for one elementary induction generator in Bernstein's ring. -/
structure CyclotomicElementaryInductionDatum
    (G : Type) [Group G] [Finite G]
    (n : ℕ) (hn : 0 < n) where
  /-- Prime defining the elementary subgroup. -/
  prime : ℕ
  /-- Primality of the displayed prime. -/
  prime_isPrime : prime.Prime
  /-- The inducing subgroup. -/
  subgroup : Subgroup G
  /-- A displayed elementary decomposition of the inducing subgroup. -/
  decomposition :
    PElementaryDecomposition prime subgroup
  /-- The local element of `Q_n(subgroup)`. -/
  localCharacter :
    ClassFunction.cyclotomicIntegerCharacterSubring
      (G := subgroup) n hn

namespace CyclotomicElementaryInductionDatum

variable {G : Type} [Group G] [Finite G]
variable {n : ℕ} {hn : 0 < n}

noncomputable local instance cyclotomicElementaryInductionFintypeG :
    Fintype G :=
  Fintype.ofFinite _

/-- The induced generator, bundled as an element of `Q_n(G)`. -/
def induced
    (d : CyclotomicElementaryInductionDatum G n hn) :
    ClassFunction.cyclotomicIntegerCharacterSubring
      (G := G) n hn :=
  ⟨ClassFunction.induce d.subgroup d.localCharacter,
    d.localCharacter.property.induce d.subgroup⟩

/-- Multiply a generator by an ambient element of `Q_n(G)`, moving the
ambient factor inside induction by restriction. -/
def multiplyLocal
    (d : CyclotomicElementaryInductionDatum G n hn)
    (q :
      ClassFunction.cyclotomicIntegerCharacterSubring
        (G := G) n hn) :
    CyclotomicElementaryInductionDatum G n hn where
  prime := d.prime
  prime_isPrime := d.prime_isPrime
  subgroup := d.subgroup
  decomposition := d.decomposition
  localCharacter :=
    ⟨ClassFunction.comapLinearMap d.subgroup.subtype q *
        d.localCharacter,
      (q.property.comap d.subgroup.subtype).mul
        d.localCharacter.property⟩

/-- The projection formula identifies ambient multiplication of a
generator with the generator obtained by `multiplyLocal`. -/
theorem induced_multiplyLocal
    (d : CyclotomicElementaryInductionDatum G n hn)
    (q :
      ClassFunction.cyclotomicIntegerCharacterSubring
        (G := G) n hn) :
    (multiplyLocal d q).induced = q * d.induced := by
  apply Subtype.ext
  exact
    ClassFunction.induce_comap_mul
      d.subgroup d.localCharacter q

end CyclotomicElementaryInductionDatum

namespace ClassFunction

variable {G : Type} [Group G] [Finite G]
variable {n : ℕ} {hn : 0 < n}

/-- The set of elementary induction generators in `Q_n(G)`. -/
def cyclotomicElementaryInductionGeneratorSet :
    Set
      (cyclotomicIntegerCharacterSubring
        (G := G) n hn) :=
  Set.range
    (fun d : CyclotomicElementaryInductionDatum G n hn =>
      d.induced)

/-- Multiplying a generator by any ambient element of `Q_n(G)` gives
another generator. -/
theorem mul_mem_cyclotomicElementaryInductionGeneratorSet
    (q :
      cyclotomicIntegerCharacterSubring
        (G := G) n hn)
    {x :
      cyclotomicIntegerCharacterSubring
        (G := G) n hn}
    (hx :
      x ∈
        cyclotomicElementaryInductionGeneratorSet
          (G := G) (n := n) (hn := hn)) :
    q * x ∈
      cyclotomicElementaryInductionGeneratorSet
        (G := G) (n := n) (hn := hn) := by
  obtain ⟨d, rfl⟩ := hx
  refine
    ⟨d.multiplyLocal q, ?_⟩
  exact d.induced_multiplyLocal q

/-- The additive closure of elementary generators is stable under
multiplication by arbitrary elements of `Q_n(G)`. -/
theorem mul_mem_cyclotomicElementaryInductionAddClosure
    (q :
      cyclotomicIntegerCharacterSubring
        (G := G) n hn)
    {x :
      cyclotomicIntegerCharacterSubring
        (G := G) n hn}
    (hx :
      x ∈
        AddSubgroup.closure
          (cyclotomicElementaryInductionGeneratorSet
            (G := G) (n := n) (hn := hn))) :
    q * x ∈
      AddSubgroup.closure
        (cyclotomicElementaryInductionGeneratorSet
          (G := G) (n := n) (hn := hn)) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
      exact
        AddSubgroup.subset_closure
          (mul_mem_cyclotomicElementaryInductionGeneratorSet
            q hx)
  | zero =>
      simpa using
        (AddSubgroup.zero_mem
          (AddSubgroup.closure
            (cyclotomicElementaryInductionGeneratorSet
              (G := G) (n := n) (hn := hn))))
  | add x y hx hy ihx ihy =>
      simpa [mul_add] using
        (AddSubgroup.add_mem
          (AddSubgroup.closure
            (cyclotomicElementaryInductionGeneratorSet
              (G := G) (n := n) (hn := hn)))
          ihx ihy)
  | neg x hx ihx =>
      simpa using
        (AddSubgroup.neg_mem
          (AddSubgroup.closure
            (cyclotomicElementaryInductionGeneratorSet
              (G := G) (n := n) (hn := hn)))
          ihx)

/-- Bernstein's elementary-induction ideal `J_n(G) ⊆ Q_n(G)`. -/
def cyclotomicElementaryInductionIdeal :
    Ideal
      (cyclotomicIntegerCharacterSubring
        (G := G) n hn) where
  carrier :=
    AddSubgroup.closure
      (cyclotomicElementaryInductionGeneratorSet
        (G := G) (n := n) (hn := hn))
  zero_mem' :=
    AddSubgroup.zero_mem _
  add_mem' :=
    AddSubgroup.add_mem _
  smul_mem' q x hx := by
    change
      q * x ∈
        AddSubgroup.closure
          (cyclotomicElementaryInductionGeneratorSet
            (G := G) (n := n) (hn := hn))
    exact
      mul_mem_cyclotomicElementaryInductionAddClosure
        q hx

/-- Every displayed elementary induction datum belongs to `J_n(G)`. -/
theorem induced_mem_cyclotomicElementaryInductionIdeal
    (d : CyclotomicElementaryInductionDatum G n hn) :
    d.induced ∈
      cyclotomicElementaryInductionIdeal
        (G := G) (n := n) (hn := hn) :=
  AddSubgroup.subset_closure ⟨d, rfl⟩

end ClassFunction
end McKayConjecture
