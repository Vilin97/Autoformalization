/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AdaptedCliffordFibreAssembly

/-!
# Inertia coordinates of an adapted Clifford assembly

This file exposes the exact inertia characters used internally by an
adapted Clifford-fibre assembly.  The source coordinate induces back to
the input ambient character, and the matched target coordinate induces to
the assembled output.  These identities let properties of the fibre
correspondence be lifted through Clifford induction without duplicating
the definition of the global assembly.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CliffordCorrespondence
open CliffordEquivalence
open CliffordPartition

variable {G H : Type}
variable [Group G] [Finite G] [Group H] [Finite H]
variable {N : Subgroup G} [N.Normal]
variable {M : Subgroup H} [M.Normal]
variable {p : ℕ} [Fact p.Prime]

noncomputable local instance adaptedCliffordFibreCoordinatesFintypeG :
    Fintype G :=
  Fintype.ofFinite G

noncomputable local instance adaptedCliffordFibreCoordinatesFintypeH :
    Fintype H :=
  Fintype.ofFinite H

namespace AdaptedCliffordFibreAssemblyData

/-- Forgetting a central-triple assembly to its inertia-fibre equivalences
does not change the assembled ambient correspondence. -/
theorem assembledPPrimeEquiv_ofCentralTriple
    (d : AdaptedCentralTripleCliffordAssemblyData N M p) :
    (ofCentralTriple d).assembledPPrimeEquiv =
      d.assembledPPrimeEquiv :=
  rfl

/-- The source orbit block, rewritten at the representative chosen by the
adapted assembly. -/
def adaptedSourceBlock
    (d : AdaptedCliffordFibreAssemblyData N M p)
    (χ : PPrimeIrreducibleCharacter G p) :
    PPrimeIrreducibleCharactersOverOrbit
      N
      (d.sourceRepresentative
        (activeOrbitIndex N χ)).1 p :=
  pPrimeOrbitBlockEquivOfQuotientMkEq
    N
    (d.sourceOut_orbit_eq
      (activeOrbitIndex N χ))
    p
    (pPrimeActiveOrbitBlockSigmaEquiv N p χ).2

@[simp]
theorem adaptedSourceBlock_apply_coe
    (d : AdaptedCliffordFibreAssemblyData N M p)
    (χ : PPrimeIrreducibleCharacter G p) :
    (d.adaptedSourceBlock χ).1.1 = χ.1 :=
  rfl

/-- The irreducible inertia character selected from the source ambient
character by the inverse Clifford correspondence. -/
def sourceInertiaCharacter
    (d : AdaptedCliffordFibreAssemblyData N M p)
    (χ : PPrimeIrreducibleCharacter G p) :
    PPrimeIrreducibleCharactersOverInertia
      N
      (d.sourceRepresentative
        (activeOrbitIndex N χ)).1 p :=
  (cliffordPPrimeCorrespondence
    N
    (d.sourceRepresentative
      (activeOrbitIndex N χ)).1
    (Fact.out : p.Prime)
    (d.sourceInertiaIndex_isPPrime
      (activeOrbitIndex N χ))).symm
    (d.adaptedSourceBlock χ)

/-- The target inertia character obtained by applying the stored fibre
correspondence to the exact source inertia coordinate. -/
def targetInertiaCharacter
    (d : AdaptedCliffordFibreAssemblyData N M p)
    (χ : PPrimeIrreducibleCharacter G p) :
    PPrimeIrreducibleCharactersOverInertia
      M
      (d.targetRepresentative
        (activeOrbitIndex N χ)).1 p :=
  d.inertiaFibreEquiv
    (activeOrbitIndex N χ)
    (d.sourceInertiaCharacter χ)

/-- Clifford induction of the extracted source inertia coordinate recovers
the original ambient character. -/
theorem induce_sourceInertiaCharacter
    (d : AdaptedCliffordFibreAssemblyData N M p)
    (χ : PPrimeIrreducibleCharacter G p) :
    (induceOverInertiaOrbit
      N
      (d.sourceRepresentative
        (activeOrbitIndex N χ)).1
      (d.sourceInertiaCharacter χ).1).1 =
        χ.1 := by
  let e :=
    cliffordPPrimeCorrespondence
      N
      (d.sourceRepresentative
        (activeOrbitIndex N χ)).1
      (Fact.out : p.Prime)
      (d.sourceInertiaIndex_isPPrime
        (activeOrbitIndex N χ))
  have h :=
    congrArg
      (fun x => x.1.1)
      (e.apply_symm_apply (d.adaptedSourceBlock χ))
  exact h

/-- Clifford induction of the matched target inertia coordinate is the
ambient character produced by the global adapted assembly. -/
theorem induce_targetInertiaCharacter
    (d : AdaptedCliffordFibreAssemblyData N M p)
    (χ : PPrimeIrreducibleCharacter G p) :
    (induceOverInertiaOrbit
      M
      (d.targetRepresentative
        (activeOrbitIndex N χ)).1
      (d.targetInertiaCharacter χ).1).1 =
        (d.assembledPPrimeEquiv χ).1 := by
  have h :=
    congrArg
      (fun x => x.2.1.1)
      (d.toActivePPrimeOrbitwiseCorrespondence
        |>.decompose_assemble χ)
  exact h.symm

end AdaptedCliffordFibreAssemblyData
end InductiveMcKay
end McKayConjecture
