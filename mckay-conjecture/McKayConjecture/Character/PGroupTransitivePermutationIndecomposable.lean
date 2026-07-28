/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.PermutationModuleInvariantBasis
import McKayConjecture.Character.FiniteDimensionalIndecomposable
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.PGroup
import Mathlib.LinearAlgebra.Projection
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Transitive permutation modules for p-groups are indecomposable

Let `P` be a finite `p`-group and let `k` be a field of characteristic
`p`.  A nonzero finite-dimensional `kP`-module has a nonzero fixed
vector.  The proof here does not assume that `k` is finite: starting
from one nonzero vector, it takes the span of its finite `P`-orbit over
the prime field `ZMod p`.  That span is finite, so the usual congruence
between the cardinality of a finite `P`-set and its fixed-point set
applies.

For a transitive permutation module the fixed-vector space is
one-dimensional.  Consequently two nonzero complementary
subrepresentations would supply two nonzero fixed vectors in disjoint
summands of a one-dimensional space, which is impossible.  Thus every
direct summand of a *transitive* permutation module is either zero or
the whole module.

This is the indecomposable-transitive ingredient in the standard proof
that every direct summand of a finite permutation module for a
`p`-group is a permutation module.  Passing from this result to an
arbitrary finite disjoint union of transitive `P`-sets uses the local
one-summand exchange lemma and induction on the dimension of the
retract; full Krull--Schmidt uniqueness is unnecessary.
-/

noncomputable section

namespace Representation

section FixedVector

variable {p : ℕ} [Fact p.Prime]
variable {k P V : Type}
variable [Field k] [CharP k p]
variable [Group P] [Finite P]
variable [AddCommGroup V] [Module k V]

/-- A nonzero module for a finite `p`-group over a field of
characteristic `p` has a nonzero fixed vector.

The module need not be finite-dimensional over `k`.  The proof only
uses the finite-dimensional `ZMod p`-span of one group orbit. -/
theorem exists_nonzero_fixedVector_of_isPGroup
    (ρ : Representation k P V)
    (hP : IsPGroup p P)
    [Nontrivial V] :
    ∃ v : V, v ≠ 0 ∧ ∀ g : P, ρ g v = v := by
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  letI : Module (ZMod p) V :=
    Module.compHom V (algebraMap (ZMod p) k)
  obtain ⟨v : V, hv : v ≠ 0⟩ := exists_ne (0 : V)
  let S : Submodule (ZMod p) V :=
    Submodule.span (ZMod p) (Set.range fun g : P => ρ g v)
  have hS_stable (g : P) {x : V} (hx : x ∈ S) :
      ρ g x ∈ S := by
    change x ∈ Submodule.span (ZMod p)
      (Set.range fun h : P => ρ h v) at hx
    change ρ g x ∈ Submodule.span (ZMod p)
      (Set.range fun h : P => ρ h v)
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨h, rfl⟩ := hx
        apply Submodule.subset_span
        refine ⟨g * h, ?_⟩
        simp only [map_mul, Module.End.mul_apply]
    | zero =>
        simp
    | add x y hx hy ihx ihy =>
        simpa using Submodule.add_mem _ ihx ihy
    | smul c x hx ih =>
        change
          ρ g ((algebraMap (ZMod p) k c) • x) ∈ S
        rw [map_smul]
        exact Submodule.smul_mem S c ih
  letI : MulAction P S :=
    { smul := fun g x => ⟨ρ g x, hS_stable g x.property⟩
      one_smul := fun x => by
        apply Subtype.ext
        change ρ 1 (x : V) = (x : V)
        simp
      mul_smul := fun g h x => by
        apply Subtype.ext
        change ρ (g * h) (x : V) = ρ g (ρ h (x : V))
        simp only [map_mul, Module.End.mul_apply] }
  have hvS : v ∈ S := by
    apply Submodule.subset_span
    exact ⟨1, by simp⟩
  let vS : S := ⟨v, hvS⟩
  have hvS_ne : vS ≠ 0 := by
    intro h
    apply hv
    exact congrArg Subtype.val h
  letI : Nontrivial S := ⟨⟨vS, 0, hvS_ne⟩⟩
  letI : Module.Finite (ZMod p) S := by
    dsimp only [S]
    exact Module.Finite.span_of_finite (ZMod p) (Set.finite_range _)
  letI : Finite S := Module.finite_of_finite (ZMod p)
  have hp_card : p ∣ Nat.card S := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
    exact dvd_pow_self p
      (ne_of_gt (Module.finrank_pos (R := ZMod p) (M := S)))
  have hzero_fixed :
      (0 : S) ∈ MulAction.fixedPoints P S := by
    intro g
    apply Subtype.ext
    change ρ g (0 : V) = 0
    exact map_zero (ρ g)
  obtain ⟨w, hw_fixed, hzero_ne_w⟩ :=
    hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (α := S) hp_card hzero_fixed
  refine ⟨w, ?_, ?_⟩
  · intro hw
    apply hzero_ne_w
    apply Subtype.ext
    simpa using hw.symm
  · intro g
    exact congrArg Subtype.val (hw_fixed g)

end FixedVector

namespace PermutationModuleBasis

variable {p : ℕ} [Fact p.Prime]
variable {k P V ι : Type}
variable [Field k] [CharP k p]
variable [Group P] [Finite P]
variable [AddCommGroup V] [Module k V]
variable [DistribMulAction P V] [SMulCommClass P k V]
variable [MulAction P ι] [Finite ι] [Nonempty ι]
variable [MulAction.IsPretransitive P ι]

variable (B : PermutationModuleBasis
  (k := k) (P := P) (V := V) (ι := ι))

local notation "ρ" => B.representation
local notation "Ω" => MulAction.orbitRel.Quotient P ι

omit [Finite P] in
/-- The invariant space of a transitive permutation basis is
one-dimensional. -/
theorem finrank_invariants_eq_one :
    Module.finrank k (invariants ρ) = 1 := by
  letI : Unique Ω :=
    ((MulAction.pretransitive_iff_unique_quotient_of_nonempty P ι).mp
      (inferInstance : MulAction.IsPretransitive P ι)).some
  rw [Module.finrank_eq_card_basis B.invariantsOrbitBasis]
  exact Fintype.card_unique

/-- A transitive permutation module of a finite `p`-group in
characteristic `p` cannot be written as a direct sum of two nonzero
subrepresentations. -/
theorem isCompl_imp_eq_bot_or_eq_bot
    (hP : IsPGroup p P)
    (U W : Subrepresentation ρ)
    (hUW : IsCompl U.toSubmodule W.toSubmodule) :
    U = ⊥ ∨ W = ⊥ := by
  by_cases hU : U = ⊥
  · exact Or.inl hU
  by_cases hW : W = ⊥
  · exact Or.inr hW
  exfalso
  have hU_ne : U.toSubmodule ≠ ⊥ := by
    intro hUsub
    apply hU
    apply Subrepresentation.toSubmodule_injective
    change U.toSubmodule = (⊥ : Submodule k V)
    exact hUsub
  have hW_ne : W.toSubmodule ≠ ⊥ := by
    intro hWsub
    apply hW
    apply Subrepresentation.toSubmodule_injective
    change W.toSubmodule = (⊥ : Submodule k V)
    exact hWsub
  letI : Nontrivial U.toSubmodule :=
    Submodule.nontrivial_iff_ne_bot.mpr hU_ne
  letI : Nontrivial W.toSubmodule :=
    Submodule.nontrivial_iff_ne_bot.mpr hW_ne
  obtain ⟨u, hu_ne, hu_fixed⟩ :=
    exists_nonzero_fixedVector_of_isPGroup U.toRepresentation hP
  obtain ⟨w, hw_ne, hw_fixed⟩ :=
    exists_nonzero_fixedVector_of_isPGroup W.toRepresentation hP
  let u₀ : invariants ρ :=
    ⟨u, fun g => congrArg Subtype.val (hu_fixed g)⟩
  let w₀ : invariants ρ :=
    ⟨w, fun g => congrArg Subtype.val (hw_fixed g)⟩
  have hu₀_ne : u₀ ≠ 0 := by
    intro hu
    apply hu_ne
    apply Subtype.ext
    exact congrArg (fun x : invariants ρ => (x : V)) hu
  obtain ⟨c, hc⟩ :=
    exists_smul_eq_of_finrank_eq_one
      B.finrank_invariants_eq_one hu₀_ne w₀
  have hcV : c • (u : V) = (w : V) :=
    congrArg (fun x : invariants ρ => (x : V)) hc
  have hw_mem_U : (w : V) ∈ U.toSubmodule := by
    have hcu : (c • (u : V)) ∈ U.toSubmodule :=
      U.toSubmodule.smul_mem c u.property
    rw [← hcV]
    exact hcu
  have hw_zero : (w : V) = 0 := by
    have hw_inf :
        (w : V) ∈ U.toSubmodule ⊓ W.toSubmodule :=
      ⟨hw_mem_U, w.property⟩
    rw [hUW.disjoint.eq_bot] at hw_inf
    exact hw_inf
  exact hw_ne (Subtype.ext hw_zero)

/-- Every direct summand of a transitive permutation module for a
finite `p`-group is either zero or the whole module.  In particular,
the transitive permutation module is indecomposable. -/
theorem eq_bot_or_eq_top_of_isCompl
    (hP : IsPGroup p P)
    (U W : Subrepresentation ρ)
    (hUW : IsCompl U.toSubmodule W.toSubmodule) :
    U = ⊥ ∨ U = ⊤ := by
  rcases B.isCompl_imp_eq_bot_or_eq_bot hP U W hUW with hU | hW
  · exact Or.inl hU
  · right
    apply Subrepresentation.toSubmodule_injective
    have hWsub :
        W.toSubmodule = (⊥ : Submodule k V) := by
      have := congrArg Subrepresentation.toSubmodule hW
      exact this
    have hsup : U.toSubmodule ⊔ W.toSubmodule = ⊤ :=
      hUW.codisjoint.eq_top
    change U.toSubmodule = (⊤ : Submodule k V)
    simpa [hWsub] using hsup

/-- A transitive permutation module for a finite `p`-group in
characteristic `p` is directly indecomposable. -/
theorem isDirectSumIndecomposable_of_transitive
    (hP : IsPGroup p P) :
    Representation.IsDirectSumIndecomposable ρ := by
  haveI : Nontrivial V := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨⟨B.basis i, 0, B.basis.ne_zero i⟩⟩
  exact ⟨inferInstance, fun U W hUW =>
    B.isCompl_imp_eq_bot_or_eq_bot hP U W hUW⟩

/-- Every equivariant endomorphism of a transitive permutation module
for a finite `p`-group is either a unit or nilpotent. -/
theorem equivariantEndomorphism_isUnit_or_isNilpotent
    (hP : IsPGroup p P)
    (f : IntertwiningMap ρ ρ) :
    IsUnit f ∨ IsNilpotent f := by
  letI : FiniteDimensional k V :=
    B.basis.finiteDimensional_of_finite
  exact
    f.isUnit_or_isNilpotent_of_isDirectSumIndecomposable
      (B.isDirectSumIndecomposable_of_transitive hP)

/-- The equivariant endomorphism ring of a transitive permutation
module for a finite `p`-group is local. -/
theorem isLocalRing_equivariantEndomorphisms
    (hP : IsPGroup p P) :
    IsLocalRing (IntertwiningMap ρ ρ) := by
  letI : FiniteDimensional k V :=
    B.basis.finiteDimensional_of_finite
  exact
    isLocalRing_endomorphisms_of_isDirectSumIndecomposable
      (B.isDirectSumIndecomposable_of_transitive hP)

/-- Every equivariant idempotent endomorphism of a transitive
permutation module for a finite `p`-group is zero or the identity.
This is the projection formulation of indecomposability. -/
theorem equivariant_idempotent_eq_zero_or_eq_id
    (hP : IsPGroup p P)
    (e : Module.End k V)
    (he_comm : ∀ g : P,
      e ∘ₗ ρ g = ρ g ∘ₗ e)
    (he_idem : IsIdempotentElem e) :
    e = 0 ∨ e = LinearMap.id := by
  have he_comm_apply (g : P) (v : V) :
      e (ρ g v) = ρ g (e v) :=
    LinearMap.congr_fun (he_comm g) v
  let U : Subrepresentation ρ :=
    { toSubmodule := LinearMap.range e
      apply_mem_toSubmodule := fun g v hv => by
        obtain ⟨x, rfl⟩ := hv
        exact ⟨ρ g x, he_comm_apply g x⟩ }
  let W : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker e
      apply_mem_toSubmodule := fun g v hv => by
        rw [LinearMap.mem_ker] at hv ⊢
        rw [he_comm_apply, hv, map_zero] }
  have he_proj : LinearMap.IsProj (LinearMap.range e) e :=
    LinearMap.IsIdempotentElem.isProj_range e he_idem
  rcases B.eq_bot_or_eq_top_of_isCompl hP U W he_proj.isCompl with
    hU | hU
  · left
    have hrange : LinearMap.range e = ⊥ :=
      congrArg Subrepresentation.toSubmodule hU
    exact he_proj.submodule_eq_bot_iff.mp hrange
  · right
    have hrange : LinearMap.range e = ⊤ :=
      congrArg Subrepresentation.toSubmodule hU
    exact he_proj.submodule_eq_top_iff.mp hrange

end PermutationModuleBasis
end Representation
