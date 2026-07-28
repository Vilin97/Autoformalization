/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.PermutationModuleBasis

/-!
# Orbit sums of a permutation module

For a finite permutation basis, summing the basis vectors in one orbit
produces an invariant vector.  Its coordinates are the characteristic
function of that orbit.
-/

noncomputable section

open scoped BigOperators

namespace Representation
namespace PermutationModuleBasis

variable {k P V ι : Type}
variable [CommRing k] [Group P]
variable [AddCommGroup V] [Module k V]
variable [DistribMulAction P V] [SMulCommClass P k V]
variable [MulAction P ι] [Finite ι]

variable (B : PermutationModuleBasis (k := k) (P := P) (V := V) (ι := ι))

local notation "Ω" =>
  MulAction.orbitRel.Quotient P ι

noncomputable local instance permutationOrbitSumIndexFintype :
    Fintype ι :=
  Fintype.ofFinite ι

noncomputable local instance orbitQuotientDecidableEq :
    DecidableEq Ω :=
  Classical.decEq Ω

noncomputable local instance orbitIndexFintype
    (ω : Ω) :
    Fintype ω.orbit :=
  Fintype.ofFinite ω.orbit

/-- The sum of all basis vectors in one `P`-orbit. -/
def orbitSumValue (ω : Ω) : V :=
  ∑ i : ω.orbit, B.basis (i : ι)

/-- An orbit sum is fixed by `P`. -/
theorem orbitSumValue_mem_invariants
    (ω : Ω) :
    B.orbitSumValue ω ∈ invariants B.representation := by
  intro g
  change g • B.orbitSumValue ω = B.orbitSumValue ω
  rw [orbitSumValue, Finset.smul_sum]
  simp_rw [B.smul_basis]
  change
    (∑ i : ω.orbit, B.basis ((g • i : ω.orbit) : ι)) =
      ∑ i : ω.orbit, B.basis (i : ι)
  exact
    Function.Bijective.sum_comp
      (MulAction.toPerm g).bijective
      (fun i : ω.orbit => B.basis (i : ι))

/-- The invariant vector associated with a `P`-orbit of basis
indices. -/
def orbitSum (ω : Ω) :
    invariants B.representation :=
  ⟨B.orbitSumValue ω, B.orbitSumValue_mem_invariants ω⟩

@[simp]
theorem orbitSum_coe (ω : Ω) :
    (B.orbitSum ω : V) = B.orbitSumValue ω :=
  rfl

omit [SMulCommClass P k V] in
/-- The coefficient of an orbit sum at an index in that orbit is one,
and every other coefficient is zero. -/
theorem coord_orbitSumValue
    (ω : Ω) (i : ι) :
    B.basis.coord i (B.orbitSumValue ω) =
      if Quotient.mk'' i = ω then 1 else 0 := by
  classical
  rw [orbitSumValue, map_sum]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self_apply]
  by_cases hi : Quotient.mk'' i = ω
  · rw [if_pos hi]
    rw [Fintype.sum_eq_single
      (⟨i, MulAction.orbitRel.Quotient.mem_orbit.mpr hi⟩ :
        ω.orbit)]
    · simp
    · intro j hj
      have hne : (j : ι) ≠ i := by
        intro h
        apply hj
        exact Subtype.ext h
      simp [hne]
  · rw [if_neg hi]
    apply Fintype.sum_eq_zero
    intro j
    have hne : (j : ι) ≠ i := by
      intro h
      apply hi
      rw [← h]
      exact MulAction.orbitRel.Quotient.mem_orbit.mp j.property
    simp [hne]

@[simp]
theorem coord_orbitSum
    (ω : Ω) (i : ι) :
    B.basis.coord i (B.orbitSum ω : V) =
      if Quotient.mk'' i = ω then 1 else 0 :=
  B.coord_orbitSumValue ω i

/-- At the chosen representative of its orbit, an orbit sum has
coefficient one. -/
@[simp]
theorem coord_orbitSum_out
    (ω τ : Ω) :
    B.basis.coord ω.out (B.orbitSum τ : V) =
      if ω = τ then 1 else 0 := by
  rw [B.coord_orbitSum]
  rw [Quotient.out_eq']

end PermutationModuleBasis
end Representation
