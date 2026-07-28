/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ActiveOrbitTransport
import McKayConjecture.InductiveMcKay.AdaptedCentralTripleCliffordAssembly

/-!
# Clifford assembly from fibre equivalences at adapted representatives

For the numerical normal-subgroup reduction one does not need to package a
central isomorphism between every pair of inertia triples.  It is enough to
construct the resulting equivalence between their prime-to-`p` character
fibres.  This file records that sharper interface.

Both representatives may be chosen independently of `Quotient.out`.
Clifford correspondence and orbit repackaging turn the fibre equivalences
into block equivalences, and the exact active partition then assembles them
globally.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CliffordCorrespondence
open CliffordEquivalence
open CliffordPartition

variable {G H : Type}
variable [Group G] [Finite G] [Group H] [Finite H]
variable (N : Subgroup G) [N.Normal]
variable (M : Subgroup H) [M.Normal]

noncomputable local instance adaptedCliffordFibreAssemblyFintypeG :
    Fintype G :=
  Fintype.ofFinite G

noncomputable local instance adaptedCliffordFibreAssemblyFintypeH :
    Fintype H :=
  Fintype.ofFinite H

/-- Active-orbit matching and equivalences of the corresponding inertia
fibres at chosen representatives. -/
structure AdaptedCliffordFibreAssemblyData (p : ℕ) where
  /-- Matching of active Clifford orbits. -/
  activeOrbitEquiv :
    ActiveOrbit N p ≃ ActiveOrbit M p
  /-- Adapted source representative. -/
  sourceRepresentative :
    ∀ q : ActiveOrbit N p,
      PPrimeIrreducibleCharacter N p
  /-- The source representative lies in `q`. -/
  sourceRepresentative_orbit :
    ∀ q : ActiveOrbit N p,
      (Quotient.mk'' (sourceRepresentative q).1 :
          OrbitSpace N) =
        q.1
  /-- Prime-to-`p` source inertia index. -/
  sourceInertiaIndex_isPPrime :
    ∀ q : ActiveOrbit N p,
      ¬p ∣
        (IrreducibleCharacter.inertia N
          (sourceRepresentative q).1).index
  /-- Adapted target representative. -/
  targetRepresentative :
    ∀ q : ActiveOrbit N p,
      PPrimeIrreducibleCharacter M p
  /-- The target representative lies in the matched orbit. -/
  targetRepresentative_orbit :
    ∀ q : ActiveOrbit N p,
      (Quotient.mk'' (targetRepresentative q).1 :
          OrbitSpace M) =
        (activeOrbitEquiv q).1
  /-- Prime-to-`p` target inertia index. -/
  targetInertiaIndex_isPPrime :
    ∀ q : ActiveOrbit N p,
      ¬p ∣
        (IrreducibleCharacter.inertia M
          (targetRepresentative q).1).index
  /-- The actual prime-to-`p` character-fibre equivalence. -/
  inertiaFibreEquiv :
    ∀ q : ActiveOrbit N p,
      PPrimeIrreducibleCharactersOverInertia
          N (sourceRepresentative q).1 p ≃
        PPrimeIrreducibleCharactersOverInertia
          M (targetRepresentative q).1 p

namespace AdaptedCliffordFibreAssemblyData

variable {N M}
variable {p : ℕ} [Fact p.Prime]

/-- View the common fields of a central-triple assembly package as a
fibrewise package. -/
def ofCentralTriple
    (d : AdaptedCentralTripleCliffordAssemblyData N M p) :
    AdaptedCliffordFibreAssemblyData N M p where
  activeOrbitEquiv := d.activeOrbitEquiv
  sourceRepresentative := d.sourceRepresentative
  sourceRepresentative_orbit :=
    d.sourceRepresentative_orbit
  sourceInertiaIndex_isPPrime :=
    d.sourceInertiaIndex_isPPrime
  targetRepresentative := d.targetRepresentative
  targetRepresentative_orbit :=
    d.targetRepresentative_orbit
  targetInertiaIndex_isPPrime :=
    d.targetInertiaIndex_isPPrime
  inertiaFibreEquiv := fun q ↦ by
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
      C.witness.pPrimeInertiaEquiv
        N (d.sourceRepresentative q).1
        M (d.targetRepresentative q).1
        (Fact.out : p.Prime)
        (d.sourceRepresentative q).2
        (d.targetRepresentative q).2

/-- Source quotient equality for the adapted representative. -/
theorem sourceOut_orbit_eq
    (d : AdaptedCliffordFibreAssemblyData N M p)
    (q : ActiveOrbit N p) :
    (Quotient.mk'' q.1.out : OrbitSpace N) =
      Quotient.mk'' (d.sourceRepresentative q).1 := by
  calc
    (Quotient.mk'' q.1.out : OrbitSpace N) = q.1 :=
      Quotient.out_eq' q.1
    _ = Quotient.mk'' (d.sourceRepresentative q).1 :=
      (d.sourceRepresentative_orbit q).symm

/-- Target quotient equality for the adapted representative. -/
theorem target_orbit_eq_out
    (d : AdaptedCliffordFibreAssemblyData N M p)
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

/-- Turn one adapted inertia-fibre equivalence into the corresponding
active Clifford-block equivalence. -/
def blockEquiv
    (d : AdaptedCliffordFibreAssemblyData N M p)
    (q : ActiveOrbit N p) :
    PPrimeOrbitBlock N p q.1 ≃
      PPrimeOrbitBlock M p (d.activeOrbitEquiv q).1 :=
  (pPrimeOrbitBlockEquivOfQuotientMkEq
    N (d.sourceOut_orbit_eq q) p).trans
    ((cliffordPPrimeCorrespondence
      N (d.sourceRepresentative q).1
        (Fact.out : p.Prime)
        (d.sourceInertiaIndex_isPPrime q)).symm |>.trans
      ((d.inertiaFibreEquiv q).trans
        ((cliffordPPrimeCorrespondence
          M (d.targetRepresentative q).1
            (Fact.out : p.Prime)
            (d.targetInertiaIndex_isPPrime q)).trans
          (pPrimeOrbitBlockEquivOfQuotientMkEq
            M (d.target_orbit_eq_out q) p))))

/-- Package the block equivalences as exact active orbitwise data. -/
def toActivePPrimeOrbitwiseCorrespondence
    (d : AdaptedCliffordFibreAssemblyData N M p) :
    ActivePPrimeOrbitwiseCorrespondence N M p where
  activeOrbitEquiv := d.activeOrbitEquiv
  blockEquiv := d.blockEquiv

/-- Assemble the fibrewise construction into a global character
equivalence. -/
def assembledPPrimeEquiv
    (d : AdaptedCliffordFibreAssemblyData N M p) :
    PPrimeIrreducibleCharacter G p ≃
      PPrimeIrreducibleCharacter H p :=
  d.toActivePPrimeOrbitwiseCorrespondence.assemble

@[simp]
theorem activeOrbitIndex_assembledPPrimeEquiv
    (d : AdaptedCliffordFibreAssemblyData N M p)
    (χ : PPrimeIrreducibleCharacter G p) :
    activeOrbitIndex M (d.assembledPPrimeEquiv χ) =
      d.activeOrbitEquiv (activeOrbitIndex N χ) :=
  d.toActivePPrimeOrbitwiseCorrespondence
    |>.activeOrbitIndex_assemble χ

/-- The ambient source character lies over the adapted representative
selected by its active Clifford orbit. -/
theorem liesOver_sourceRepresentative
    (d : AdaptedCliffordFibreAssemblyData N M p)
    (χ : PPrimeIrreducibleCharacter G p) :
    LiesOverAlong N.subtype
      (d.sourceRepresentative
        (activeOrbitIndex N χ)).1
      χ.1 := by
  let q := activeOrbitIndex N χ
  let θ := d.sourceRepresentative q
  have horbit :
      (Quotient.mk'' θ.1 : OrbitSpace N) =
        Quotient.mk''
          (χ.1.normalSimpleConstituent N) := by
    calc
      (Quotient.mk'' θ.1 : OrbitSpace N) =
          q.1 :=
        d.sourceRepresentative_orbit q
      _ = orbitOf N χ.1 :=
        activeOrbitIndex_coe N χ
      _ =
          Quotient.mk''
            (χ.1.normalSimpleConstituent N) :=
        rfl
  apply
    (liesOverOrbit_iff_liesOver
      N θ.1 χ.1).mp
  exact
    (liesOverOrbit_iff_of_quotient_mk_eq
      N horbit χ.1).mpr
      (liesOverOrbit_of_liesOver
        N (χ.1.normalSimpleConstituent N)
          (χ.1.normalSimpleConstituent_liesOver N))

/-- The assembled target character lies over the target representative
matched to the source active orbit. -/
theorem liesOver_targetRepresentative_assembledPPrimeEquiv
    (d : AdaptedCliffordFibreAssemblyData N M p)
    (χ : PPrimeIrreducibleCharacter G p) :
    LiesOverAlong M.subtype
      (d.targetRepresentative
        (activeOrbitIndex N χ)).1
      (d.assembledPPrimeEquiv χ).1 := by
  let q := activeOrbitIndex N χ
  let ψ := d.assembledPPrimeEquiv χ
  let φ := d.targetRepresentative q
  have horbit :
      (Quotient.mk'' φ.1 : OrbitSpace M) =
        Quotient.mk''
          (ψ.1.normalSimpleConstituent M) := by
    calc
      (Quotient.mk'' φ.1 : OrbitSpace M) =
          (d.activeOrbitEquiv q).1 :=
        d.targetRepresentative_orbit q
      _ = (activeOrbitIndex M ψ).1 := by
        exact congrArg Subtype.val
          (d.activeOrbitIndex_assembledPPrimeEquiv χ).symm
      _ = orbitOf M ψ.1 :=
        activeOrbitIndex_coe M ψ
      _ =
          Quotient.mk''
            (ψ.1.normalSimpleConstituent M) :=
        rfl
  apply
    (liesOverOrbit_iff_liesOver
      M φ.1 ψ.1).mp
  exact
    (liesOverOrbit_iff_of_quotient_mk_eq
      M horbit ψ.1).mpr
      (liesOverOrbit_of_liesOver
        M (ψ.1.normalSimpleConstituent M)
          (ψ.1.normalSimpleConstituent_liesOver M))

end AdaptedCliffordFibreAssemblyData

end InductiveMcKay
end McKayConjecture
