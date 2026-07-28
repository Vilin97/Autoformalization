/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerRelativeTrace

/-!
# Brauer quotients of linear representations

For a representation `ρ` of a finite group `P`, the Brauer trace
submodule is the sum, inside `ρ.invariants`, of the images of all relative
traces from proper subgroups `Q < P`.  The Brauer quotient is

`ρ.invariants / ∑_{Q < P} Tr_Q^P(ρ|_Q.invariants)`.

The definition makes sense over any commutative ring.  Its decisive
properties arise when the coefficient ring has characteristic `p` and
`P` is a finite `p`-group; those hypotheses will be introduced only by
the lemmas that need them.
-/

noncomputable section

namespace Representation

variable {k P V : Type}
variable [CommRing k] [Group P] [Fintype P]
variable [AddCommGroup V] [Module k V]

/-- The contribution to the Brauer trace submodule from one subgroup. -/
def relativeTraceRange
    (rho : Representation k P V)
    (Q : Subgroup P) :
    Submodule k (invariants rho) :=
  LinearMap.range (relativeTrace rho Q)

/-- The sum of the relative-trace images from all proper subgroups. -/
def brauerTraceSubmodule
    (rho : Representation k P V) :
    Submodule k (invariants rho) :=
  ⨆ (Q : Subgroup P) (_hQ : Q < ⊤),
    relativeTraceRange rho Q

/-- Every relative trace from a proper subgroup lands in the Brauer trace
submodule. -/
theorem relativeTraceRange_le_brauerTraceSubmodule
    (rho : Representation k P V)
    (Q : Subgroup P)
    (hQ : Q < ⊤) :
    relativeTraceRange rho Q ≤
      brauerTraceSubmodule rho :=
  le_iSup_of_le Q
    (le_iSup_of_le hQ le_rfl)

/-- Pointwise form of
`relativeTraceRange_le_brauerTraceSubmodule`. -/
theorem relativeTrace_mem_brauerTraceSubmodule
    (rho : Representation k P V)
    (Q : Subgroup P)
    (hQ : Q < ⊤)
    (x : invariants (rho.comp Q.subtype)) :
    relativeTrace rho Q x ∈
      brauerTraceSubmodule rho :=
  relativeTraceRange_le_brauerTraceSubmodule
    rho Q hQ ⟨x, rfl⟩

/-- The Brauer quotient of a linear representation. -/
abbrev BrauerQuotient
    (rho : Representation k P V) :=
  invariants rho ⧸ brauerTraceSubmodule rho

/-- The canonical projection from invariant vectors to the Brauer
quotient. -/
def brauerProjection
    (rho : Representation k P V) :
    invariants rho →ₗ[k] BrauerQuotient rho :=
  Submodule.mkQ (brauerTraceSubmodule rho)

@[simp]
theorem brauerProjection_relativeTrace
    (rho : Representation k P V)
    (Q : Subgroup P)
    (hQ : Q < ⊤)
    (x : invariants (rho.comp Q.subtype)) :
    brauerProjection rho (relativeTrace rho Q x) = 0 := by
  rw [brauerProjection, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact relativeTrace_mem_brauerTraceSubmodule
    rho Q hQ x

/-- The Brauer projection is surjective. -/
theorem brauerProjection_surjective
    (rho : Representation k P V) :
    Function.Surjective (brauerProjection rho) :=
  Submodule.mkQ_surjective _

end Representation
