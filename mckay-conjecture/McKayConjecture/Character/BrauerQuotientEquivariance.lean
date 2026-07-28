/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerQuotient
import McKayConjecture.Character.BrauerRelativeTraceEquivariance

/-!
# Equivariance of Brauer quotients

A compatible automorphism of a group representation consists of an
automorphism of the acting group and a linear automorphism of the
representation space which intertwine the action.  Such an automorphism
permutes the relative traces from proper subgroups.  It therefore
preserves the Brauer trace submodule and descends to a linear
automorphism of the Brauer quotient.
-/

noncomputable section

namespace Representation

variable {k P V : Type}
variable [CommRing k] [Group P]
variable [AddCommGroup V] [Module k V]

/-- Compatible automorphisms of the acting group and a representation
space. -/
structure CompatibleAutomorphism
    (rho : Representation k P V) where
  /-- The automorphism of the acting group. -/
  groupEquiv : P ≃* P
  /-- The automorphism of the representation space. -/
  linearEquiv : V ≃ₗ[k] V
  /-- Compatibility with the representation. -/
  compatible :
    ∀ (g : P) (v : V),
      linearEquiv (rho g v) =
        rho (groupEquiv g) (linearEquiv v)

namespace CompatibleAutomorphism

variable {rho : Representation k P V}

/-- The inverse of a compatible automorphism. -/
def symm (e : CompatibleAutomorphism rho) :
    CompatibleAutomorphism rho where
  groupEquiv := e.groupEquiv.symm
  linearEquiv := e.linearEquiv.symm
  compatible g v := by
    apply e.linearEquiv.injective
    simpa using
      (e.compatible (e.groupEquiv.symm g)
        (e.linearEquiv.symm v)).symm

@[simp]
theorem symm_groupEquiv
    (e : CompatibleAutomorphism rho) :
    e.symm.groupEquiv = e.groupEquiv.symm :=
  rfl

@[simp]
theorem symm_linearEquiv
    (e : CompatibleAutomorphism rho) :
    e.symm.linearEquiv = e.linearEquiv.symm :=
  rfl

/-- A compatible automorphism carries invariant vectors to invariant
vectors. -/
theorem linearEquiv_mem_invariants
    (e : CompatibleAutomorphism rho)
    {v : V}
    (hv : v ∈ invariants rho) :
    e.linearEquiv v ∈ invariants rho := by
  intro g
  calc
    rho g (e.linearEquiv v) =
        rho (e.groupEquiv
          (e.groupEquiv.symm g)) (e.linearEquiv v) := by
            rw [e.groupEquiv.apply_symm_apply]
    _ = e.linearEquiv
          (rho (e.groupEquiv.symm g) v) :=
      (e.compatible (e.groupEquiv.symm g) v).symm
    _ = e.linearEquiv v := by
      rw [hv]

/-- A compatible automorphism maps the invariant submodule onto itself. -/
theorem map_invariants_eq
    (e : CompatibleAutomorphism rho) :
    (invariants rho).map e.linearEquiv.toLinearMap =
      invariants rho := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact e.linearEquiv_mem_invariants hv
  · intro v hv
    refine
      ⟨e.linearEquiv.symm v,
        e.symm.linearEquiv_mem_invariants hv, ?_⟩
    exact e.linearEquiv.apply_symm_apply v

/-- The automorphism induced on the invariant submodule. -/
def invariantsEquiv
    (e : CompatibleAutomorphism rho) :
    invariants rho ≃ₗ[k] invariants rho :=
  e.linearEquiv.ofSubmodules
    (invariants rho) (invariants rho)
    e.map_invariants_eq

@[simp]
theorem invariantsEquiv_coe
    (e : CompatibleAutomorphism rho)
    (x : invariants rho) :
    (e.invariantsEquiv x : V) =
      e.linearEquiv (x : V) :=
  rfl

section Finite

variable [Fintype P]

/-- The induced map on invariants carries a relative trace to the trace
from the image subgroup. -/
theorem invariantsEquiv_relativeTrace
    (e : CompatibleAutomorphism rho)
    (Q : Subgroup P)
    (x : invariants (rho.comp Q.subtype)) :
    e.invariantsEquiv (relativeTrace rho Q x) =
      relativeTrace rho
        (Q.map e.groupEquiv.toMonoidHom)
        (transportInvariant rho e.groupEquiv e.linearEquiv
          e.compatible Q x) := by
  apply Subtype.ext
  exact
    relativeTraceValue_equivariant
      rho e.groupEquiv e.linearEquiv e.compatible Q x

/-- The induced map on invariants preserves the Brauer trace
submodule, in the pointwise form used to descend it to the quotient. -/
theorem invariantsEquiv_mem_brauerTraceSubmodule
    (e : CompatibleAutomorphism rho)
    (x : invariants rho)
    (hx : x ∈ brauerTraceSubmodule rho) :
    e.invariantsEquiv x ∈ brauerTraceSubmodule rho := by
  let B := brauerTraceSubmodule rho
  change e.invariantsEquiv x ∈ B
  refine Submodule.iSup_induction
    (fun Q : Subgroup P ↦
      ⨆ _hQ : Q < ⊤, relativeTraceRange rho Q)
    (motive := fun y ↦ e.invariantsEquiv y ∈ B)
    hx ?_ ?_ ?_
  · intro Q y hy
    refine Submodule.iSup_induction
      (fun _hQ : Q < ⊤ ↦ relativeTraceRange rho Q)
      (motive := fun z ↦ e.invariantsEquiv z ∈ B)
      hy ?_ ?_ ?_
    · intro hQ z hz
      obtain ⟨w, rfl⟩ := hz
      rw [e.invariantsEquiv_relativeTrace]
      apply relativeTrace_mem_brauerTraceSubmodule
      rw [← Subgroup.map_top_of_surjective
        e.groupEquiv.toMonoidHom e.groupEquiv.surjective]
      exact
        (Subgroup.map_lt_map_iff_of_injective
          e.groupEquiv.injective).mpr hQ
    · simp
    · intro z w hz hw
      simpa using B.add_mem hz hw
  · simp
  · intro y z hy hz
    simpa using B.add_mem hy hz

/-- The Brauer trace submodule is invariant under a compatible
automorphism. -/
theorem map_brauerTraceSubmodule_eq
    (e : CompatibleAutomorphism rho) :
    (brauerTraceSubmodule rho).map
        e.invariantsEquiv.toLinearMap =
      brauerTraceSubmodule rho := by
  let B := brauerTraceSubmodule rho
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact e.invariantsEquiv_mem_brauerTraceSubmodule x hx
  · intro y hy
    let x : invariants rho :=
      e.symm.invariantsEquiv y
    have hx : x ∈ B :=
      e.symm.invariantsEquiv_mem_brauerTraceSubmodule y hy
    refine ⟨x, hx, ?_⟩
    apply Subtype.ext
    simp [x]

/-- The linear automorphism of the Brauer quotient induced by a
compatible automorphism of the representation. -/
def brauerQuotientEquiv
    (e : CompatibleAutomorphism rho) :
    BrauerQuotient rho ≃ₗ[k] BrauerQuotient rho :=
  Submodule.Quotient.equiv
    (brauerTraceSubmodule rho)
    (brauerTraceSubmodule rho)
    e.invariantsEquiv
    e.map_brauerTraceSubmodule_eq

/-- The quotient equivalence commutes with the canonical Brauer
projection. -/
@[simp]
theorem brauerQuotientEquiv_brauerProjection
    (e : CompatibleAutomorphism rho)
    (x : invariants rho) :
    e.brauerQuotientEquiv (brauerProjection rho x) =
      brauerProjection rho (e.invariantsEquiv x) :=
  rfl

end Finite

end CompatibleAutomorphism

end Representation
