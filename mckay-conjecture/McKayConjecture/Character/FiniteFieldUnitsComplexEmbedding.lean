/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Embedding finite-field units into the complex units

The multiplicative group of a finite field is cyclic.  The complex roots
of unity of the same order form a cyclic group with the same cardinality.
Choosing the resulting cyclic-group equivalence and composing with the
subgroup inclusion gives an injective homomorphism

`kˣ →* ℂˣ`.

This is the coefficient-change map needed to transport modular scalar
corrections into characteristic zero in the Dade normalizer argument.
-/

noncomputable section

namespace Representation

variable (k : Type) [Field k] [Finite k]

private instance finiteFieldUnitsCardNeZero :
    NeZero (Nat.card kˣ) :=
  ⟨Nat.card_pos.ne'⟩

/-- A chosen equivalence between the unit group of a finite field and
the complex roots of unity of the same order. -/
def finiteFieldUnitsEquivComplexRoots :
    kˣ ≃* rootsOfUnity (Nat.card kˣ) ℂ :=
  mulEquivOfCyclicCardEq
    (Complex.card_rootsOfUnity
      (Nat.card kˣ)).symm

/-- A chosen homomorphism from finite-field units into
complex units. -/
def finiteFieldUnitsToComplexUnits :
    kˣ →* ℂˣ :=
  (rootsOfUnity (Nat.card kˣ) ℂ).subtype.comp
    (finiteFieldUnitsEquivComplexRoots k).toMonoidHom

/-- The chosen finite-field-unit homomorphism is injective. -/
theorem finiteFieldUnitsToComplexUnits_injective :
    Function.Injective
      (finiteFieldUnitsToComplexUnits k) :=
  (rootsOfUnity (Nat.card kˣ) ℂ).subtype_injective.comp
    (finiteFieldUnitsEquivComplexRoots k).injective

/-- The chosen embedding preserves element orders. -/
theorem orderOf_finiteFieldUnitsToComplexUnits
    (u : kˣ) :
    orderOf (finiteFieldUnitsToComplexUnits k u) =
      orderOf u :=
  orderOf_injective
    (finiteFieldUnitsToComplexUnits k)
    (finiteFieldUnitsToComplexUnits_injective k)
    u

/-- The image of every finite-field unit is a root of unity whose order
divides the size of the source unit group. -/
theorem finiteFieldUnitsToComplexUnits_mem_rootsOfUnity
    (u : kˣ) :
    finiteFieldUnitsToComplexUnits k u ∈
      rootsOfUnity (Nat.card kˣ) ℂ :=
  (finiteFieldUnitsEquivComplexRoots k u).property

/-- Every embedded finite-field unit has order dividing the size of the
finite-field unit group. -/
theorem finiteFieldUnitsToComplexUnits_pow_card_eq_one
    (u : kˣ) :
    finiteFieldUnitsToComplexUnits k u ^
        Nat.card kˣ =
      1 :=
  (mem_rootsOfUnity
    (Nat.card kˣ)
    (finiteFieldUnitsToComplexUnits k u)).mp
      (finiteFieldUnitsToComplexUnits_mem_rootsOfUnity
        k u)

/-- The image is exactly the complex roots of unity whose order divides
the size of the finite-field unit group. -/
theorem finiteFieldUnitsToComplexUnits_range :
    MonoidHom.range
        (finiteFieldUnitsToComplexUnits k) =
      rootsOfUnity (Nat.card kˣ) ℂ := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    exact
      finiteFieldUnitsToComplexUnits_mem_rootsOfUnity
        k u
  · intro hz
    obtain ⟨u, hu⟩ :=
      (finiteFieldUnitsEquivComplexRoots k).surjective
        ⟨z, hz⟩
    refine ⟨u, ?_⟩
    exact congrArg Subtype.val hu

/-- A complex unit has a (necessarily unique) finite-field-unit
preimage precisely when it is killed by the order of the finite-field
unit group.  This gives an exact test for whether a characteristic-zero
projective factor value can be the image of a modular factor value. -/
theorem exists_finiteFieldUnitsToComplexUnits_eq_iff
    (z : ℂˣ) :
    (∃ u : kˣ,
        finiteFieldUnitsToComplexUnits k u = z) ↔
      z ^ Nat.card kˣ = 1 := by
  change
    z ∈ MonoidHom.range
        (finiteFieldUnitsToComplexUnits k) ↔
      z ^ Nat.card kˣ = 1
  rw [finiteFieldUnitsToComplexUnits_range]
  exact mem_rootsOfUnity (Nat.card kˣ) z

/-- The modular scalar lifting a complex unit in the image of the
chosen finite-field embedding is unique. -/
theorem existsUnique_finiteFieldUnitsToComplexUnits_eq_iff
    (z : ℂˣ) :
    (∃! u : kˣ,
        finiteFieldUnitsToComplexUnits k u = z) ↔
      z ^ Nat.card kˣ = 1 := by
  constructor
  · rintro ⟨u, hu, _⟩
    exact
      (exists_finiteFieldUnitsToComplexUnits_eq_iff k z).1
        ⟨u, hu⟩
  · intro hz
    obtain ⟨u, hu⟩ :=
      (exists_finiteFieldUnitsToComplexUnits_eq_iff k z).2 hz
    refine ⟨u, hu, ?_⟩
    intro v hv
    exact
      finiteFieldUnitsToComplexUnits_injective k
        (hv.trans hu.symm)

end Representation
