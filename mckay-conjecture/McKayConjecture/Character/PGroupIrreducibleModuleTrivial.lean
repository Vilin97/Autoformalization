/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.PGroupTransitivePermutationIndecomposable
import Mathlib.RepresentationTheory.Irreducible

/-!
# Simple modules of a `p`-group in characteristic `p`

Every nonzero module of a finite `p`-group in characteristic `p` has
a nonzero fixed vector.  In an irreducible representation the
subrepresentation of fixed vectors must therefore be the whole
space.  Consequently the only irreducible representation is the
one-dimensional trivial representation.
-/

noncomputable section

namespace Representation

open scoped MonoidAlgebra

variable {p : ℕ} [Fact p.Prime]
variable {k P V : Type}
variable [Field k] [CharP k p]
variable [Group P] [Finite P]
variable [AddCommGroup V] [Module k V]

/-- An irreducible representation of a finite `p`-group in
characteristic `p` is trivial. -/
theorem isTrivial_of_isIrreducible_of_isPGroup
    (rho : Representation k P V)
    [rho.IsIrreducible]
    (hP : IsPGroup p P) :
    rho.IsTrivial := by
  letI : IsSimpleModule k[P] rho.asModule := inferInstance
  letI : Nontrivial V :=
    IsSimpleModule.nontrivial k[P] rho.asModule
  obtain ⟨v, hv, hv_fixed⟩ :=
    exists_nonzero_fixedVector_of_isPGroup rho hP
  let U : Subrepresentation rho :=
    { toSubmodule := invariants rho
      apply_mem_toSubmodule := fun g x hx => by
        rw [hx g]
        exact hx }
  have hU_ne : U ≠ ⊥ := by
    intro hU
    have hvU : v ∈ U := hv_fixed
    rw [hU] at hvU
    change v ∈ (⊥ : Submodule k V) at hvU
    exact hv ((Submodule.mem_bot k).mp hvU)
  have hU_top : U = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top U).resolve_left hU_ne
  refine ⟨fun g => LinearMap.ext fun x => ?_⟩
  change rho g x = x
  have hxU : x ∈ U := by
    rw [hU_top]
    exact Submodule.mem_top
  exact hxU g

/-- A finite-dimensional irreducible representation of a finite
`p`-group in characteristic `p` has dimension one. -/
theorem finrank_eq_one_of_isIrreducible_of_isPGroup
    (rho : Representation k P V)
    [rho.IsIrreducible]
    [FiniteDimensional k V]
    (hP : IsPGroup p P) :
    Module.finrank k V = 1 := by
  letI : rho.IsTrivial :=
    isTrivial_of_isIrreducible_of_isPGroup rho hP
  letI : IsSimpleModule k[P] rho.asModule := inferInstance
  letI : Nontrivial V :=
    IsSimpleModule.nontrivial k[P] rho.asModule
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := exists_ne 0
  let L : Subrepresentation rho :=
    { toSubmodule := k ∙ v
      apply_mem_toSubmodule := fun g x hx => by
        rw [rho.isTrivial_apply]
        exact hx }
  have hL_ne : L ≠ ⊥ := by
    intro hL
    have hvL : v ∈ L :=
      Submodule.mem_span_singleton_self v
    rw [hL] at hvL
    change v ∈ (⊥ : Submodule k V) at hvL
    exact hv ((Submodule.mem_bot k).mp hvL)
  have hL_top : L = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top L).resolve_left hL_ne
  have hsub : L.toSubmodule = ⊤ :=
    congrArg Subrepresentation.toSubmodule hL_top
  rw [← finrank_top k V, ← hsub]
  exact finrank_span_singleton hv

/-- A finite-dimensional representation of a finite `p`-group in
characteristic `p` is irreducible exactly when it is one-dimensional. -/
theorem isIrreducible_iff_finrank_eq_one_of_isPGroup
    (rho : Representation k P V)
    [FiniteDimensional k V]
    (hP : IsPGroup p P) :
    rho.IsIrreducible ↔ Module.finrank k V = 1 := by
  constructor
  · intro hirreducible
    letI : rho.IsIrreducible := hirreducible
    exact
      finrank_eq_one_of_isIrreducible_of_isPGroup rho hP
  · intro hfinrank
    have hfinrankAsModule :
        Module.finrank k rho.asModule = 1 := by
      rw [rho.asModuleEquiv.finrank_eq]
      exact hfinrank
    exact
      (irreducible_iff_isSimpleModule_asModule rho).2
        ((isSimpleModule_iff k[P] rho.asModule).2
          (is_simple_module_of_finrank_eq_one hfinrankAsModule))

/-- Classification of finite-dimensional irreducible representations
of a finite `p`-group in characteristic `p`: they are exactly the
one-dimensional trivial representations. -/
theorem isIrreducible_iff_isTrivial_and_finrank_eq_one_of_isPGroup
    (rho : Representation k P V)
    [FiniteDimensional k V]
    (hP : IsPGroup p P) :
    rho.IsIrreducible ↔
      rho.IsTrivial ∧ Module.finrank k V = 1 := by
  constructor
  · intro hirreducible
    letI : rho.IsIrreducible := hirreducible
    exact
      ⟨isTrivial_of_isIrreducible_of_isPGroup rho hP,
        finrank_eq_one_of_isIrreducible_of_isPGroup rho hP⟩
  · rintro ⟨_, hfinrank⟩
    exact
      (isIrreducible_iff_finrank_eq_one_of_isPGroup rho hP).2
        hfinrank

end Representation
