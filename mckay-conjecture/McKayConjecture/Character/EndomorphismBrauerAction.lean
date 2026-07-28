/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.EndomorphismFixedAction
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Self-intertwiners acting on a module Brauer quotient

A self-intertwiner preserves every relative-trace range, hence the
Brauer trace submodule.  It therefore induces an endomorphism of the
module Brauer quotient.  This construction is additive, multiplicative,
and scalar-compatible, so it bundles as an algebra homomorphism.
-/

noncomputable section

namespace Representation

variable {k P V : Type}
variable [Field k] [Group P] [Fintype P]
variable [AddCommGroup V] [Module k V]

variable (ρ : Representation k P V)

/-- The restriction of a self-intertwiner to invariant vectors
preserves the Brauer trace submodule. -/
theorem selfIntertwinerOnInvariants_mem_brauerTraceSubmodule
    (c : ρ.IntertwiningMap ρ)
    (x : invariants ρ)
    (hx : x ∈ brauerTraceSubmodule ρ) :
    selfIntertwinerOnInvariants ρ c x ∈
      brauerTraceSubmodule ρ := by
  let B := brauerTraceSubmodule ρ
  change _ ∈ B
  refine Submodule.iSup_induction
    (fun Q : Subgroup P ↦
      ⨆ _hQ : Q < ⊤, relativeTraceRange ρ Q)
    (motive := fun y ↦
      selfIntertwinerOnInvariants ρ c y ∈ B)
    hx ?_ ?_ ?_
  · intro Q y hyQ
    refine Submodule.iSup_induction
      (fun _hQ : Q < ⊤ ↦ relativeTraceRange ρ Q)
      (motive := fun z ↦
        selfIntertwinerOnInvariants ρ c z ∈ B)
      hyQ ?_ ?_ ?_
    · intro hQ z hz
      obtain ⟨w, rfl⟩ := hz
      rw [selfIntertwinerOnInvariants_relativeTrace]
      exact relativeTrace_mem_brauerTraceSubmodule
        ρ Q hQ
        (selfIntertwinerOnSubgroupInvariants ρ c Q w)
    · simp
    · intro u v hu hv
      simpa using B.add_mem hu hv
  · simp
  · intro u v hu hv
    simpa using B.add_mem hu hv

/-- Endomorphism induced by a self-intertwiner on the module Brauer
quotient. -/
def selfIntertwinerOnBrauerQuotient
    (c : ρ.IntertwiningMap ρ) :
    Module.End k (BrauerQuotient ρ) :=
  (brauerTraceSubmodule ρ).mapQ
    (brauerTraceSubmodule ρ)
    (selfIntertwinerOnInvariants ρ c)
    (fun x hx ↦
      selfIntertwinerOnInvariants_mem_brauerTraceSubmodule
        ρ c x hx)

@[simp]
theorem selfIntertwinerOnBrauerQuotient_brauerProjection
    (c : ρ.IntertwiningMap ρ)
    (x : invariants ρ) :
    selfIntertwinerOnBrauerQuotient ρ c
        (brauerProjection ρ x) =
      brauerProjection ρ
        (selfIntertwinerOnInvariants ρ c x) :=
  rfl

/-- Natural algebra homomorphism from the self-intertwiner algebra to
endomorphisms of the module Brauer quotient. -/
def selfIntertwinerBrauerAlgHom :
    ρ.IntertwiningMap ρ →ₐ[k]
      Module.End k (BrauerQuotient ρ) where
  toFun := selfIntertwinerOnBrauerQuotient ρ
  map_one' := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := brauerProjection_surjective ρ z
    rfl
  map_mul' c d := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := brauerProjection_surjective ρ z
    rfl
  map_zero' := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := brauerProjection_surjective ρ z
    rfl
  map_add' c d := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := brauerProjection_surjective ρ z
    rfl
  commutes' r := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := brauerProjection_surjective ρ z
    rfl

@[simp]
theorem selfIntertwinerBrauerAlgHom_apply
    (c : ρ.IntertwiningMap ρ) :
    selfIntertwinerBrauerAlgHom ρ c =
      selfIntertwinerOnBrauerQuotient ρ c :=
  rfl

end Representation
