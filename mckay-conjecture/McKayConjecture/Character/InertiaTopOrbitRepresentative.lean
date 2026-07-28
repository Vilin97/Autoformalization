/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.PPrimeCliffordOrbit

/-!
# Chosen representatives of invariant Clifford orbits

When a normal-subgroup character has full inertia, its conjugation orbit
is a singleton.  Thus the quotient's chosen representative is literally
that character, not merely a conjugate.
-/

noncomputable section

namespace McKayConjecture
namespace CliffordPartition

variable {G : Type} [Group G] [Finite G]
variable (N : Subgroup G) [N.Normal]

/-- A full-inertia character agrees with the chosen representative of
any active orbit that it represents. -/
theorem ActiveOrbit.pPrimeOut_eq_of_mk_eq_of_inertia_eq_top
    {p : ℕ}
    (q : ActiveOrbit N p)
    (θ : PPrimeIrreducibleCharacter N p)
    (hmk :
      (Quotient.mk'' θ.1 : OrbitSpace N) = q.1)
    (hinertia :
      IrreducibleCharacter.inertia N θ.1 = ⊤) :
    q.pPrimeOut N = θ := by
  apply Subtype.ext
  have hmkOut :
      (Quotient.mk'' θ.1 : OrbitSpace N) =
        Quotient.mk'' q.1.out :=
    hmk.trans (Quotient.out_eq' q.1).symm
  have hrel :
      q.1.out ∈ MulAction.orbit G θ.1 := by
    rw [← MulAction.orbitRel_apply]
    exact
      Setoid.symm'
        (MulAction.orbitRel G
          (IrreducibleCharacter N))
        (Quotient.exact hmkOut)
  obtain ⟨g, hg⟩ :=
    MulAction.mem_orbit_iff.mp hrel
  have hfix :
      g • θ.1 = θ.1 :=
    (IrreducibleCharacter.mem_inertia_iff
      N θ.1 g).mp
      (by rw [hinertia]; exact Subgroup.mem_top g)
  exact hg.symm.trans hfix

end CliffordPartition
end McKayConjecture
