/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.PPrimeCliffordOrbit
import McKayConjecture.GroupTheory.SylowCoprimeIndex
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Active Clifford-orbit representatives adapted to a Sylow subgroup

The quotient representative chosen by `Quotient.out` need not have an
inertia subgroup containing a prescribed Sylow subgroup.  For an active
orbit, however, its inertia index is prime to `p`.  Sylow conjugacy therefore
lets us conjugate the representative inside its orbit so that its inertia
subgroup contains the prescribed Sylow subgroup.

This is the representative needed by the fibrewise central-extension
construction in Rossi's normal-subgroup reduction.
-/

noncomputable section

namespace McKayConjecture
namespace CliffordPartition

open GroupTheory
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (N : Subgroup G) [N.Normal]

/-- A conjugator sending the prescribed Sylow subgroup into the inertia
subgroup of the default representative of an active orbit. -/
def ActiveOrbit.sylowConjugator
    (P : Sylow p G)
    (q : ActiveOrbit N p) : G :=
  Classical.choose <| by
    letI : Fintype G := Fintype.ofFinite G
    exact
      GroupTheory.Sylow.exists_smul_le_of_not_dvd_index
        P (IrreducibleCharacter.inertia N q.1.out)
        (activeOrbit_inertia_index_isPPrime N q)

/-- The defining containment for `sylowConjugator`. -/
theorem ActiveOrbit.smul_sylow_le_inertia
    (P : Sylow p G)
    (q : ActiveOrbit N p) :
    (q.sylowConjugator N P • P : Sylow p G) ≤
      IrreducibleCharacter.inertia N q.1.out := by
  letI : Fintype G := Fintype.ofFinite G
  exact Classical.choose_spec <| by
    exact
      GroupTheory.Sylow.exists_smul_le_of_not_dvd_index
        P (IrreducibleCharacter.inertia N q.1.out)
        (activeOrbit_inertia_index_isPPrime N q)

/-- The active-orbit representative obtained by conjugating the default
representative back along `sylowConjugator`. -/
def ActiveOrbit.sylowRepresentative
    (P : Sylow p G)
    (q : ActiveOrbit N p) :
    IrreducibleCharacter N :=
  IrreducibleCharacter.conjBy N
    (q.sylowConjugator N P)⁻¹ q.1.out

/-- The prescribed Sylow subgroup lies in the inertia subgroup of the
adapted representative. -/
theorem ActiveOrbit.sylow_le_inertia_sylowRepresentative
    (P : Sylow p G)
    (q : ActiveOrbit N p) :
    (P : Subgroup G) ≤
      IrreducibleCharacter.inertia N
        (q.sylowRepresentative N P) := by
  intro x hx
  rw [IrreducibleCharacter.mem_inertia_iff]
  change
    x •
        ((q.sylowConjugator N P)⁻¹ • q.1.out) =
      (q.sylowConjugator N P)⁻¹ • q.1.out
  have hconj :
      q.sylowConjugator N P * x *
          (q.sylowConjugator N P)⁻¹ ∈
        IrreducibleCharacter.inertia N q.1.out := by
    apply q.smul_sylow_le_inertia N P
    have hx' :
        (MulAut.conj (q.sylowConjugator N P)) x ∈
          (MulAut.conj (q.sylowConjugator N P)) •
            (P : Subgroup G) :=
      Subgroup.smul_mem_pointwise_smul
        x (MulAut.conj (q.sylowConjugator N P))
          (P : Subgroup G) hx
    simpa only [Sylow.coe_subgroup_smul, MulAut.conj_apply] using hx'
  have hfix :
      (q.sylowConjugator N P * x *
          (q.sylowConjugator N P)⁻¹) • q.1.out =
        q.1.out :=
    (IrreducibleCharacter.mem_inertia_iff
      N q.1.out _).mp hconj
  calc
    x •
        ((q.sylowConjugator N P)⁻¹ • q.1.out) =
      (x * (q.sylowConjugator N P)⁻¹) • q.1.out :=
        (mul_smul _ _ _).symm
    _ =
      ((q.sylowConjugator N P)⁻¹ *
          (q.sylowConjugator N P * x *
            (q.sylowConjugator N P)⁻¹)) • q.1.out := by
        congr 1
        group
    _ =
      (q.sylowConjugator N P)⁻¹ •
        ((q.sylowConjugator N P * x *
          (q.sylowConjugator N P)⁻¹) • q.1.out) := by
        rw [mul_smul]
    _ =
      (q.sylowConjugator N P)⁻¹ • q.1.out := by
        rw [hfix]

/-- The inertia index of the Sylow-adapted representative is prime to
`p`.  This follows directly from the fact that its inertia subgroup
contains an ambient Sylow subgroup. -/
theorem ActiveOrbit.sylowRepresentative_inertia_index_isPPrime
    (P : Sylow p G)
    (q : ActiveOrbit N p) :
    ¬p ∣
      (IrreducibleCharacter.inertia N
        (q.sylowRepresentative N P)).index := by
  intro hdiv
  exact
    P.not_dvd_index
      (hdiv.trans
        (Subgroup.index_dvd_of_le
          (q.sylow_le_inertia_sylowRepresentative N P)))

/-- The adapted representative belongs to the original active orbit. -/
theorem ActiveOrbit.sylowRepresentative_mem_orbit
    (P : Sylow p G)
    (q : ActiveOrbit N p) :
    q.sylowRepresentative N P ∈ q.1.orbit := by
  rw [MulAction.orbitRel.Quotient.mem_orbit]
  calc
    Quotient.mk'' (q.sylowRepresentative N P) =
        Quotient.mk'' q.1.out := by
      apply Quotient.sound
      exact
        MulAction.mem_orbit q.1.out
          (q.sylowConjugator N P)⁻¹
    _ = q.1 := Quotient.out_eq' q.1

/-- Quotient form of membership in the original active orbit. -/
@[simp]
theorem ActiveOrbit.mk_sylowRepresentative
    (P : Sylow p G)
    (q : ActiveOrbit N p) :
    (Quotient.mk'' (q.sylowRepresentative N P) :
        OrbitSpace N) =
      q.1 :=
  MulAction.orbitRel.Quotient.mem_orbit.mp
    (q.sylowRepresentative_mem_orbit N P)

/-- The adapted representative still has prime-to-`p` degree. -/
theorem ActiveOrbit.sylowRepresentative_isPPrimeDegree
    (P : Sylow p G)
    (q : ActiveOrbit N p) :
    (q.sylowRepresentative N P).IsPPrimeDegree p :=
  isPPrimeDegree_of_mem_activeOrbit N q
    (q.sylowRepresentative_mem_orbit N P)

/-- The adapted representative packaged as a prime-to-`p` character. -/
def ActiveOrbit.pPrimeSylowRepresentative
    (P : Sylow p G)
    (q : ActiveOrbit N p) :
    PPrimeIrreducibleCharacter N p :=
  ⟨q.sylowRepresentative N P,
    q.sylowRepresentative_isPPrimeDegree N P⟩

end CliffordPartition
end McKayConjecture
