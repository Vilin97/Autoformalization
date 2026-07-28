/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ActiveOrbitTransport
import McKayConjecture.InductiveMcKay.CentralTripleCliffordAssembly

/-!
# Clifford assembly at adapted orbit representatives

The representative selected by `Quotient.out` is often unsuitable for a
local construction.  In Rossi's normal-subgroup reduction, for example, one
first conjugates the representative so that its inertia subgroup contains a
prescribed Sylow subgroup.

This file lets the source and target representatives vary with the active
orbit.  Equalities in the two orbit quotients repack the corresponding
Clifford blocks before and after applying the central character-triple
equivalence.  Thus the complete central-isomorphism witness is needed only
at the representatives actually used by the local construction.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple
open CliffordCorrespondence
open CliffordEquivalence
open CliffordPartition

variable {G H : Type}
variable [Group G] [Finite G] [Group H] [Finite H]
variable (N : Subgroup G) [N.Normal]
variable (M : Subgroup H) [M.Normal]

noncomputable local instance adaptedCentralTripleAssemblyFintypeG :
    Fintype G :=
  Fintype.ofFinite G

noncomputable local instance adaptedCentralTripleAssemblyFintypeH :
    Fintype H :=
  Fintype.ofFinite H

/-- Active-orbit matching together with complete central witnesses at
chosen, possibly noncanonical representatives. -/
structure AdaptedCentralTripleCliffordAssemblyData (p : ℕ) where
  /-- Matching of the active source and target orbits. -/
  activeOrbitEquiv :
    ActiveOrbit N p ≃ ActiveOrbit M p
  /-- The source representative used for the local construction. -/
  sourceRepresentative :
    ∀ q : ActiveOrbit N p,
      PPrimeIrreducibleCharacter N p
  /-- The chosen source representative belongs to the indexed orbit. -/
  sourceRepresentative_orbit :
    ∀ q : ActiveOrbit N p,
      (Quotient.mk'' (sourceRepresentative q).1 :
          OrbitSpace N) =
        q.1
  /-- Its inertia index is prime to `p`. -/
  sourceInertiaIndex_isPPrime :
    ∀ q : ActiveOrbit N p,
      ¬p ∣
        (IrreducibleCharacter.inertia N
          (sourceRepresentative q).1).index
  /-- The target representative used for the local construction. -/
  targetRepresentative :
    ∀ q : ActiveOrbit N p,
      PPrimeIrreducibleCharacter M p
  /-- The chosen target representative belongs to the matched orbit. -/
  targetRepresentative_orbit :
    ∀ q : ActiveOrbit N p,
      (Quotient.mk'' (targetRepresentative q).1 :
          OrbitSpace M) =
        (activeOrbitEquiv q).1
  /-- Its inertia index is prime to `p`. -/
  targetInertiaIndex_isPPrime :
    ∀ q : ActiveOrbit N p,
      ¬p ∣
        (IrreducibleCharacter.inertia M
          (targetRepresentative q).1).index
  /-- Complete central witnesses at the representatives selected above. -/
  centralWitness :
    ∀ q : ActiveOrbit N p,
      CompleteCentralIsomorphismWitness
        (ofInertia N (sourceRepresentative q).1)
        (ofInertia M (targetRepresentative q).1)

namespace AdaptedCentralTripleCliffordAssemblyData

variable {N M}
variable {p : ℕ} [Fact p.Prime]

/-- The quotient equality used to move the source block from
`Quotient.out` to the adapted representative. -/
theorem sourceOut_orbit_eq
    (d : AdaptedCentralTripleCliffordAssemblyData N M p)
    (q : ActiveOrbit N p) :
    (Quotient.mk'' q.1.out : OrbitSpace N) =
      Quotient.mk'' (d.sourceRepresentative q).1 := by
  calc
    (Quotient.mk'' q.1.out : OrbitSpace N) = q.1 :=
      Quotient.out_eq' q.1
    _ = Quotient.mk'' (d.sourceRepresentative q).1 :=
      (d.sourceRepresentative_orbit q).symm

/-- The quotient equality used to move the target block from the adapted
representative back to the target quotient's `out` representative. -/
theorem target_orbit_eq_out
    (d : AdaptedCentralTripleCliffordAssemblyData N M p)
    (q : ActiveOrbit N p) :
    (Quotient.mk'' (d.targetRepresentative q).1 :
        OrbitSpace M) =
      Quotient.mk'' (d.activeOrbitEquiv q).1.out := by
  calc
    (Quotient.mk'' (d.targetRepresentative q).1 :
        OrbitSpace M) =
        (d.activeOrbitEquiv q).1 :=
      d.targetRepresentative_orbit q
    _ = Quotient.mk'' (d.activeOrbitEquiv q).1.out :=
      (Quotient.out_eq' (d.activeOrbitEquiv q).1).symm

/-- The active Clifford-block equivalence obtained at the adapted
representatives. -/
def blockEquiv
    (d : AdaptedCentralTripleCliffordAssemblyData N M p)
    (q : ActiveOrbit N p) :
    PPrimeOrbitBlock N p q.1 ≃
      PPrimeOrbitBlock M p (d.activeOrbitEquiv q).1 := by
  let θ := d.sourceRepresentative q
  let φ := d.targetRepresentative q
  let C := d.centralWitness q
  letI := C.leftAddCommGroup
  letI := C.leftModule
  letI := C.leftModuleFinite
  letI := C.leftNontrivial
  letI := C.rightAddCommGroup
  letI := C.rightModule
  letI := C.rightModuleFinite
  letI := C.rightNontrivial
  exact
    (pPrimeOrbitBlockEquivOfQuotientMkEq
      N (d.sourceOut_orbit_eq q) p).trans
      ((cliffordPPrimeCorrespondence
        N θ.1 (Fact.out : p.Prime)
          (d.sourceInertiaIndex_isPPrime q)).symm |>.trans
        ((C.witness.pPrimeInertiaEquiv
          N θ.1 M φ.1 (Fact.out : p.Prime)
            θ.2 φ.2).trans
          ((cliffordPPrimeCorrespondence
            M φ.1 (Fact.out : p.Prime)
              (d.targetInertiaIndex_isPPrime q)).trans
            (pPrimeOrbitBlockEquivOfQuotientMkEq
              M (d.target_orbit_eq_out q) p))))

/-- Package the adapted block equivalences as exact orbitwise
correspondence data. -/
def toActivePPrimeOrbitwiseCorrespondence
    (d : AdaptedCentralTripleCliffordAssemblyData N M p) :
    ActivePPrimeOrbitwiseCorrespondence N M p where
  activeOrbitEquiv := d.activeOrbitEquiv
  blockEquiv := d.blockEquiv

/-- Assemble all adapted active-orbit blocks into a global prime-to-`p`
character equivalence. -/
def assembledPPrimeEquiv
    (d : AdaptedCentralTripleCliffordAssemblyData N M p) :
    PPrimeIrreducibleCharacter G p ≃
      PPrimeIrreducibleCharacter H p :=
  d.toActivePPrimeOrbitwiseCorrespondence.assemble

@[simp]
theorem activeOrbitIndex_assembledPPrimeEquiv
    (d : AdaptedCentralTripleCliffordAssemblyData N M p)
    (χ : PPrimeIrreducibleCharacter G p) :
    activeOrbitIndex M (d.assembledPPrimeEquiv χ) =
      d.activeOrbitEquiv (activeOrbitIndex N χ) :=
  d.toActivePPrimeOrbitwiseCorrespondence
    |>.activeOrbitIndex_assemble χ

@[simp]
theorem activeOrbitIndex_assembledPPrimeEquiv_symm
    (d : AdaptedCentralTripleCliffordAssemblyData N M p)
    (ψ : PPrimeIrreducibleCharacter H p) :
    activeOrbitIndex N (d.assembledPPrimeEquiv.symm ψ) =
      d.activeOrbitEquiv.symm (activeOrbitIndex M ψ) :=
  d.toActivePPrimeOrbitwiseCorrespondence
    |>.activeOrbitIndex_assemble_symm ψ

end AdaptedCentralTripleCliffordAssemblyData

end InductiveMcKay
end McKayConjecture
