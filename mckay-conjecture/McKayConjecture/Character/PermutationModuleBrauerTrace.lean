/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.PermutationModuleInvariantBasis
import Mathlib.Algebra.CharP.Basic
import Mathlib.GroupTheory.PGroup

/-!
# Brauer traces in a permutation module

For a finite `p`-group in characteristic `p`, the Brauer trace
submodule of a permutation module is exactly the span of the orbit sums
belonging to nontrivial orbits.
-/

noncomputable section

open scoped BigOperators

namespace Representation
namespace PermutationModuleBasis

variable {p : ℕ} [Fact p.Prime]
variable {k P V ι : Type}
variable [Field k] [CharP k p]
variable [Group P] [Finite P]
variable [AddCommGroup V] [Module k V]
variable [DistribMulAction P V] [SMulCommClass P k V]
variable [MulAction P ι] [Finite ι]

variable (B : PermutationModuleBasis (k := k) (P := P) (V := V) (ι := ι))

local notation "Ω" =>
  MulAction.orbitRel.Quotient P ι

noncomputable local instance brauerTraceGroupFintype :
    Fintype P :=
  Fintype.ofFinite P

noncomputable local instance brauerTraceIndexFintype :
    Fintype ι :=
  Fintype.ofFinite ι

noncomputable local instance brauerTraceOrbitQuotientFintype :
    Fintype Ω :=
  Fintype.ofFinite Ω

noncomputable local instance brauerTraceOrbitQuotientDecidableEq :
    DecidableEq Ω :=
  Classical.decEq Ω

noncomputable local instance stabilizerCosetFintype
    (i : ι) :
    Fintype (P ⧸ MulAction.stabilizer P i) :=
  Fintype.ofFinite (P ⧸ MulAction.stabilizer P i)

noncomputable local instance subgroupCosetFintype
    (Q : Subgroup P) :
    Fintype (P ⧸ Q) :=
  Fintype.ofFinite (P ⧸ Q)

noncomputable local instance brauerTraceOrbitFintype
    (i : ι) :
    Fintype (MulAction.orbit P i) :=
  Fintype.ofFinite (MulAction.orbit P i)

/-- A basis vector is fixed by the stabilizer of its index. -/
def stabilizerFixedBasisVector
    (i : ι) :
    invariants
      (B.representation.comp
        (MulAction.stabilizer P i).subtype) :=
  ⟨B.basis i, fun g => by
    change (g : P) • B.basis i = B.basis i
    rw [B.smul_basis]
    exact congrArg B.basis
      (MulAction.mem_stabilizer_iff.mp g.property)⟩

omit [Finite P] [Finite ι] in
@[simp]
theorem stabilizerFixedBasisVector_coe
    (i : ι) :
    (B.stabilizerFixedBasisVector i : V) =
      B.basis i :=
  rfl

/-- Relative trace from an index stabilizer is the orbit sum of that
index. -/
theorem relativeTrace_stabilizerFixedBasisVector
    (i : ι) :
    relativeTrace B.representation
        (MulAction.stabilizer P i)
        (B.stabilizerFixedBasisVector i) =
      B.orbitSum (Quotient.mk'' i : Ω) := by
  apply Subtype.ext
  rw [relativeTrace_apply_coe]
  change
    (∑ c : P ⧸ MulAction.stabilizer P i,
        c.out • B.basis i) =
      B.orbitSumValue (Quotient.mk'' i : Ω)
  simp_rw [B.smul_basis]
  rw [orbitSumValue]
  symm
  let e :
      MulAction.orbit P i ≃
        P ⧸ MulAction.stabilizer P i :=
    MulAction.orbitEquivQuotientStabilizer P i
  apply Fintype.sum_equiv e
  intro j
  congr 1
  have he :
      ((e.symm (e j) : MulAction.orbit P i) : ι) =
        (j : ι) :=
    congrArg Subtype.val (e.symm_apply_apply j)
  have hout :
      QuotientGroup.mk (s := MulAction.stabilizer P i)
          (e j).out =
        e j :=
    Quotient.out_eq' (e j)
  calc
    (j : ι) =
        ((e.symm (e j) : MulAction.orbit P i) : ι) :=
      he.symm
    _ =
        ((e.symm
          (QuotientGroup.mk (s := MulAction.stabilizer P i)
            (e j).out) :
            MulAction.orbit P i) : ι) := by
      exact
        (congrArg
          (fun c : P ⧸ MulAction.stabilizer P i =>
            ((e.symm c : MulAction.orbit P i) : ι))
          hout).symm
    _ = (e j).out • i := by
      simpa only [e] using
        MulAction.orbitEquivQuotientStabilizer_symm_apply
          P i (e j).out

omit [Finite P] [Finite ι] in
/-- An index which is not globally fixed has a proper stabilizer. -/
theorem stabilizer_lt_top_of_not_fixed
    (i : ι)
    (hi : i ∉ MulAction.fixedPoints P ι) :
    MulAction.stabilizer P i < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  apply hi
  rw [MulAction.mem_fixedPoints]
  intro g
  apply MulAction.mem_stabilizer_iff.mp
  rw [htop]
  exact Subgroup.mem_top g

/-- Every nonfixed orbit sum belongs to the Brauer trace submodule. -/
theorem orbitSum_mem_brauerTraceSubmodule_of_not_fixed
    (i : ι)
    (hi : i ∉ MulAction.fixedPoints P ι) :
    B.orbitSum (Quotient.mk'' i : Ω) ∈
      brauerTraceSubmodule B.representation := by
  rw [← B.relativeTrace_stabilizerFixedBasisVector i]
  exact
    relativeTrace_mem_brauerTraceSubmodule
      B.representation
      (MulAction.stabilizer P i)
      (stabilizer_lt_top_of_not_fixed
        (P := P) i hi)
      (B.stabilizerFixedBasisVector i)

/-- A proper subgroup of a finite `p`-group has index divisible by
`p`. -/
theorem prime_dvd_subgroup_index
    (hP : IsPGroup p P)
    (Q : Subgroup P)
    (hQ : Q < ⊤) :
    p ∣ Q.index := by
  obtain ⟨n, hn⟩ := hP.index Q
  cases n with
  | zero =>
      simp only [pow_zero] at hn
      exact (hQ.ne (Subgroup.index_eq_one.mp hn)).elim
  | succ n =>
      rw [hn, pow_succ']
      exact dvd_mul_right p (p ^ n)

/-- The coordinate at a globally fixed basis index vanishes on every
relative trace from a proper subgroup. -/
theorem coord_fixed_relativeTrace_eq_zero
    (hP : IsPGroup p P)
    (i : MulAction.fixedPoints P ι)
    (Q : Subgroup P)
    (hQ : Q < ⊤)
    (x :
      invariants
        (B.representation.comp Q.subtype)) :
    B.basis.coord i
        (relativeTrace B.representation Q x : V) =
      0 := by
  rw [relativeTrace_apply_coe, map_sum]
  change
    (∑ c : P ⧸ Q,
      B.basis.coord i (c.out • (x : V))) = 0
  have hcoord :
      ∀ c : P ⧸ Q,
        B.basis.coord i (c.out • (x : V)) =
          B.basis.coord i (x : V) := by
    intro c
    rw [B.coord_smul_eq, i.property]
  simp_rw [hcoord]
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul k]
  have hp :
      p ∣ Fintype.card (P ⧸ Q) := by
    rw [← Nat.card_eq_fintype_card, ← Q.index_eq_card]
    exact prime_dvd_subgroup_index hP Q hQ
  rw [(CharP.cast_eq_zero_iff k p _).2 hp, zero_smul]

/-- Every globally fixed basis coordinate vanishes on the total
Brauer trace submodule. -/
theorem coord_fixed_eq_zero_of_mem_brauerTraceSubmodule
    (hP : IsPGroup p P)
    (i : MulAction.fixedPoints P ι)
    (y : invariants B.representation)
    (hy : y ∈ brauerTraceSubmodule B.representation) :
    B.basis.coord i (y : V) = 0 := by
  change
    y ∈
      ⨆ (Q : Subgroup P) (_hQ : Q < ⊤),
        relativeTraceRange B.representation Q at hy
  refine Submodule.iSup_induction
    (fun Q : Subgroup P =>
      ⨆ _hQ : Q < ⊤,
        relativeTraceRange B.representation Q)
    (motive := fun z =>
      B.basis.coord i (z : V) = 0)
    hy ?_ ?_ ?_
  · intro Q z hz
    refine Submodule.iSup_induction
      (fun _hQ : Q < ⊤ =>
        relativeTraceRange B.representation Q)
      (motive := fun w =>
        B.basis.coord i (w : V) = 0)
      hz ?_ ?_ ?_
    · intro hQ w hw
      rcases hw with ⟨x, rfl⟩
      exact B.coord_fixed_relativeTrace_eq_zero
        hP i Q hQ x
    · exact map_zero (B.basis.coord i)
    · intro u v hu hv
      change
        B.basis.coord i ((u : V) + (v : V)) = 0
      rw [map_add, hu, hv, add_zero]
  · exact map_zero (B.basis.coord i)
  · intro u v hu hv
    change
      B.basis.coord i ((u : V) + (v : V)) = 0
    rw [map_add, hu, hv, add_zero]

/-- Orbits whose chosen representative is not globally fixed.  This
condition is independent of the choice of representative because a
fixed point has a singleton orbit. -/
abbrev NonfixedOrbit :=
  {ω : Ω // ω.out ∉ MulAction.fixedPoints P ι}

/-- The family of nonfixed orbit sums. -/
def nonfixedOrbitSum
    (ω : NonfixedOrbit (P := P) (ι := ι)) :
    invariants B.representation :=
  B.orbitSum ω.1

/-- The Brauer trace submodule of a permutation module is precisely
the span of the nonfixed orbit sums. -/
theorem brauerTraceSubmodule_eq_span_nonfixedOrbitSum
    (hP : IsPGroup p P) :
    brauerTraceSubmodule B.representation =
      Submodule.span k (Set.range B.nonfixedOrbitSum) := by
  apply le_antisymm
  · intro y hy
    rw [← B.sum_orbitSum_eq y]
    apply Submodule.sum_mem
    intro ω _
    by_cases hω :
        ω.out ∈ MulAction.fixedPoints P ι
    · have hzero :
          B.basis.coord ω.out (y : V) = 0 :=
        B.coord_fixed_eq_zero_of_mem_brauerTraceSubmodule
          hP ⟨ω.out, hω⟩ y hy
      rw [hzero, zero_smul]
      exact Submodule.zero_mem _
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨⟨ω, hω⟩, ?_⟩
      rfl
  · apply Submodule.span_le.mpr
    rintro z ⟨ω, rfl⟩
    change
      B.orbitSum ω.1 ∈
        brauerTraceSubmodule B.representation
    rw [← Quotient.out_eq' ω.1]
    exact
      B.orbitSum_mem_brauerTraceSubmodule_of_not_fixed
        ω.1.out ω.2

end PermutationModuleBasis
end Representation
