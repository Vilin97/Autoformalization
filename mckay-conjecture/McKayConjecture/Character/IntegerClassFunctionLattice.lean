/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerInductionArithmetic
import McKayConjecture.Character.BrauerInductionCyclotomicIdeal

/-!
# The lattice of integer-valued class functions

Bernstein's separation argument takes place in the finite-rank lattice
`C_ℤ(G)` of integer-valued class functions, not in the character
coefficient lattice.  This file realizes `C_ℤ(G)` as a `ℤ`-submodule of
`G → ℤ`, embeds it into complex class functions, and maps `Q_n(G)` into
it by taking the unique integral value at every element.

The final theorem packages the lattice-separation step: if the constant
one function is congruent modulo every prime power to the image of
`J_n(G)`, then an actual member of `J_n(G)` is the constant one complex
class function.
-/

noncomputable section

namespace McKayConjecture

/-- Integer-valued functions on `G` which are invariant under
conjugation. -/
def IntegerClassFunction
    (G : Type) [Group G] :
    Submodule ℤ (G → ℤ) where
  carrier := {f |
    ∀ g h : G, f (h * g * h⁻¹) = f g}
  zero_mem' := by
    intro g h
    rfl
  add_mem' := by
    intro f k hf hk g h
    change
      f (h * g * h⁻¹) + k (h * g * h⁻¹) =
        f g + k g
    rw [hf g h, hk g h]
  smul_mem' := by
    intro z f hf g h
    change
      z * f (h * g * h⁻¹) = z * f g
    rw [hf g h]

namespace IntegerClassFunction

variable {G : Type} [Group G]

instance : CoeFun (IntegerClassFunction G)
    (fun _ => G → ℤ) :=
  ⟨fun f => f.1⟩

@[ext]
theorem ext
    {f k : IntegerClassFunction G}
    (h : ∀ g, f g = k g) :
    f = k :=
  Subtype.ext (funext h)

/-- The constant-one integer class function. -/
def one : IntegerClassFunction G :=
  ⟨fun _ => 1, by
    intro g h
    rfl⟩

@[simp]
theorem one_apply (g : G) :
    one (G := G) g = 1 :=
  rfl

/-- Cast an integer class function to a complex class function. -/
def toComplexAddMonoidHom :
    IntegerClassFunction G →+
      ClassFunction G where
  toFun f :=
    ⟨fun g => (f g : ℂ), by
      intro g h
      change
        (f (h * g * h⁻¹) : ℂ) = (f g : ℂ)
      rw [f.property g h]⟩
  map_zero' := by
    apply ClassFunction.ext
    intro g
    simp
  map_add' f k := by
    apply ClassFunction.ext
    intro g
    simp

@[simp]
theorem toComplexAddMonoidHom_apply
    (f : IntegerClassFunction G)
    (g : G) :
    toComplexAddMonoidHom f g = (f g : ℂ) :=
  rfl

/-- Casting integer class functions to `ℂ` is injective. -/
theorem toComplexAddMonoidHom_injective :
    Function.Injective
      (toComplexAddMonoidHom (G := G)) := by
  intro f k h
  apply ext
  intro g
  exact
    Int.cast_injective
      (congrArg (fun q : ClassFunction G => q g) h)

@[simp]
theorem toComplex_one :
    toComplexAddMonoidHom
        (one (G := G)) =
      (1 : ClassFunction G) := by
  apply ClassFunction.ext
  intro g
  simp only [toComplexAddMonoidHom_apply,
    one_apply, ClassFunction.one_apply, Int.cast_one]

variable [Finite G]

/-- The lattice of integer class functions has finite rank. -/
noncomputable instance instAddGroupFG :
    AddGroup.FG (IntegerClassFunction G) :=
  Module.Finite.iff_addGroup_fg.mp inferInstance

end IntegerClassFunction

namespace ClassFunction

variable {G : Type} [Group G] [Finite G]

/-- The unique integer underlying an integer-valued class-function
value. -/
def IsIntegerValued.integerValue
    {f : ClassFunction G}
    (hf : IsIntegerValued f)
    (g : G) : ℤ :=
  Classical.choose (hf g)

/-- Casting the chosen integer value recovers the complex value. -/
theorem IsIntegerValued.cast_integerValue
    {f : ClassFunction G}
    (hf : IsIntegerValued f)
    (g : G) :
    f g = (hf.integerValue g : ℂ) :=
  Classical.choose_spec (hf g)

/-- Regard an integer-valued complex class function as an element of the
integer class-function lattice. -/
def IsIntegerValued.toIntegerClassFunction
    {f : ClassFunction G}
    (hf : IsIntegerValued f) :
    IntegerClassFunction G :=
  ⟨hf.integerValue, by
    intro g h
    apply Int.cast_injective (α := ℂ)
    rw [← hf.cast_integerValue,
      ← hf.cast_integerValue]
    exact ClassFunction.conj_apply f g h⟩

/-- Casting the integral lift of an integer-valued class function back to
`ℂ` recovers the original function. -/
@[simp]
theorem IsIntegerValued.toComplex_toIntegerClassFunction
    {f : ClassFunction G}
    (hf : IsIntegerValued f) :
    IntegerClassFunction.toComplexAddMonoidHom
        hf.toIntegerClassFunction =
      f := by
  apply ClassFunction.ext
  intro g
  exact (hf.cast_integerValue g).symm

/-- The additive embedding of `Q_n(G)` into the integer class-function
lattice. -/
def cyclotomicIntegerCharacterToIntegerClassFunction
    (n : ℕ) (hn : 0 < n) :
    cyclotomicIntegerCharacterSubring
        (G := G) n hn →+
      IntegerClassFunction G where
  toFun q :=
    q.property.2.toIntegerClassFunction
  map_zero' := by
    apply IntegerClassFunction.toComplexAddMonoidHom_injective
    simp
  map_add' q r := by
    apply IntegerClassFunction.toComplexAddMonoidHom_injective
    simp

@[simp]
theorem toComplex_cyclotomicIntegerCharacterToIntegerClassFunction
    (n : ℕ) (hn : 0 < n)
    (q :
      cyclotomicIntegerCharacterSubring
        (G := G) n hn) :
    IntegerClassFunction.toComplexAddMonoidHom
        (cyclotomicIntegerCharacterToIntegerClassFunction
          n hn q) =
      (q : ClassFunction G) :=
  q.property.2.toComplex_toIntegerClassFunction

/-- The image in `C_ℤ(G)` of Bernstein's elementary-induction ideal. -/
def integerElementaryInductionSubgroup
    (n : ℕ) (hn : 0 < n) :
    AddSubgroup (IntegerClassFunction G) :=
  (cyclotomicElementaryInductionIdeal
      (G := G) (n := n) (hn := hn)).toAddSubgroup.map
    (cyclotomicIntegerCharacterToIntegerClassFunction
      n hn)

/-- A member of `J_n(G)` maps into the integer elementary-induction
subgroup. -/
theorem toInteger_mem_integerElementaryInductionSubgroup
    {n : ℕ} {hn : 0 < n}
    (q :
      cyclotomicIntegerCharacterSubring
        (G := G) n hn)
    (hq :
      q ∈ cyclotomicElementaryInductionIdeal
        (G := G) (n := n) (hn := hn)) :
    cyclotomicIntegerCharacterToIntegerClassFunction
        n hn q ∈
      integerElementaryInductionSubgroup
        (G := G) n hn :=
  ⟨q, hq, rfl⟩

/-- Elementwise prime-power separation for one element of a finite-rank
lattice. -/
theorem mem_addSubgroup_of_congruent_mod_prime_powers
    {L : Type} [AddCommGroup L] [AddGroup.FG L]
    (A : AddSubgroup L) (x : L)
    (hcongr :
      ∀ (p : ℕ), p.Prime → ∀ m : ℕ,
        ∃ a ∈ A, ∃ y : L,
          x = a + p ^ m • y) :
    x ∈ A := by
  let q : L →+ L ⧸ A :=
    QuotientAddGroup.mk' A
  have hdiv :
      IsUniversallyPrimePowerDivisible (q x) := by
    intro p hp m
    obtain ⟨a, ha, y, hxy⟩ :=
      hcongr p hp m
    refine ⟨q y, ?_⟩
    rw [hxy, map_add, map_nsmul]
    have hqa : q a = 0 :=
      (QuotientAddGroup.eq_zero_iff a).mpr ha
    rw [hqa, zero_add]
  exact
    (QuotientAddGroup.eq_zero_iff x).mp
      (eq_zero_of_isUniversallyPrimePowerDivisible
        hdiv)

/-- If one is congruent modulo every prime power to an element of
`J_n(G)` in the integer-value lattice, then one itself is represented by
an actual member of `J_n(G)`. -/
theorem exists_cyclotomicIdeal_member_eq_one_of_congruences
    (n : ℕ) (hn : 0 < n)
    (hcongr :
      ∀ (p : ℕ), p.Prime → ∀ m : ℕ,
        ∃ q :
            cyclotomicIntegerCharacterSubring
              (G := G) n hn,
          q ∈ cyclotomicElementaryInductionIdeal
              (G := G) (n := n) (hn := hn) ∧
          ∃ y : IntegerClassFunction G,
            IntegerClassFunction.one =
              cyclotomicIntegerCharacterToIntegerClassFunction
                  n hn q +
                p ^ m • y) :
    ∃ q :
        cyclotomicIntegerCharacterSubring
          (G := G) n hn,
      q ∈ cyclotomicElementaryInductionIdeal
          (G := G) (n := n) (hn := hn) ∧
      (q : ClassFunction G) = 1 := by
  let A :=
    integerElementaryInductionSubgroup
      (G := G) n hn
  have hone :
      IntegerClassFunction.one (G := G) ∈ A := by
    apply mem_addSubgroup_of_congruent_mod_prime_powers
    intro p hp m
    obtain ⟨q, hq, y, hy⟩ :=
      hcongr p hp m
    exact
      ⟨cyclotomicIntegerCharacterToIntegerClassFunction
          n hn q,
        toInteger_mem_integerElementaryInductionSubgroup
          q hq,
        y, hy⟩
  obtain ⟨q, hq, hqone⟩ := hone
  refine ⟨q, hq, ?_⟩
  have hcomplex :=
    congrArg
      IntegerClassFunction.toComplexAddMonoidHom
      hqone
  simpa using hcomplex

end ClassFunction
end McKayConjecture
