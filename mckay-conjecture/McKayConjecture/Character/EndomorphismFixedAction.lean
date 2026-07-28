/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerQuotient
import Mathlib.RepresentationTheory.Intertwining

/-!
# Fixed endomorphisms acting on invariant vectors

An endomorphism fixed by the conjugation action of a group commutes
with that group.  It therefore acts on every invariant subspace and
commutes with relative traces.  These elementary facts are the input
for the natural map from the Brauer quotient of an endomorphism algebra
to the endomorphism algebra of a module Brauer quotient.
-/

noncomputable section

namespace Representation

variable {k P V : Type}
variable [Field k] [Group P] [Fintype P]
variable [AddCommGroup V] [Module k V]

variable (ρ : Representation k P V)

noncomputable local instance endomorphismFixedActionLeftCosetFintype
    (Q : Subgroup P) :
    Fintype (P ⧸ Q) :=
  Fintype.ofFinite (P ⧸ Q)

omit [Fintype P] in
/-- A self-intertwiner commutes with the represented group action. -/
theorem selfIntertwiner_commutes
    (c : ρ.IntertwiningMap ρ)
    (g : P) (v : V) :
    ρ g (c v) = c (ρ g v) :=
  (IntertwiningMap.isIntertwining ρ ρ c g v).symm

/-- A self-intertwiner restricts to the invariant subspace of any
subgroup. -/
def selfIntertwinerOnSubgroupInvariants
    (c : ρ.IntertwiningMap ρ)
    (Q : Subgroup P) :
    Module.End k (invariants (ρ.comp Q.subtype)) where
  toFun x :=
    ⟨c x, fun g ↦ by
      change ρ (g : P) (c (x : V)) = c (x : V)
      rw [selfIntertwiner_commutes ρ c]
      exact congrArg c (x.property g)⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add c (x : V) (y : V)
  map_smul' r x := by
    apply Subtype.ext
    exact map_smul c r (x : V)

omit [Fintype P] in
@[simp]
theorem selfIntertwinerOnSubgroupInvariants_coe
    (c : ρ.IntertwiningMap ρ)
    (Q : Subgroup P)
    (x : invariants (ρ.comp Q.subtype)) :
    (selfIntertwinerOnSubgroupInvariants ρ c Q x : V) =
      c (x : V) :=
  rfl

/-- Restriction of a self-intertwiner to the global invariant
subspace. -/
def selfIntertwinerOnInvariants
    (c : ρ.IntertwiningMap ρ) :
    Module.End k (invariants ρ) where
  toFun x :=
    ⟨c x, fun g ↦ by
      change ρ g (c (x : V)) = c (x : V)
      rw [selfIntertwiner_commutes ρ c]
      exact congrArg c (x.property g)⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add c (x : V) (y : V)
  map_smul' r x := by
    apply Subtype.ext
    exact map_smul c r (x : V)

omit [Fintype P] in
@[simp]
theorem selfIntertwinerOnInvariants_coe
    (c : ρ.IntertwiningMap ρ)
    (x : invariants ρ) :
    (selfIntertwinerOnInvariants ρ c x : V) =
      c (x : V) :=
  rfl

/-- Self-intertwiners commute with relative traces. -/
theorem selfIntertwinerOnInvariants_relativeTrace
    (c : ρ.IntertwiningMap ρ)
    (Q : Subgroup P)
    (x : invariants (ρ.comp Q.subtype)) :
    selfIntertwinerOnInvariants ρ c
        (relativeTrace ρ Q x) =
      relativeTrace ρ Q
        (selfIntertwinerOnSubgroupInvariants ρ c Q x) := by
  apply Subtype.ext
  change
    c (∑ d : P ⧸ Q, ρ d.out (x : V)) =
      ∑ d : P ⧸ Q, ρ d.out (c (x : V))
  rw [map_sum]
  apply Fintype.sum_congr
  intro d
  exact
    IntertwiningMap.isIntertwining
      ρ ρ c d.out (x : V)

end Representation
