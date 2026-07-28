/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.Inertia
import McKayConjecture.Character.CliffordActivePartition

/-!
# Assembling Clifford correspondences from central inertia triples

An equivalence of active Clifford orbits, together with a complete
central-isomorphism witness between the canonical inertia triples over
each matched pair of chosen orbit representatives, determines an
equivalence on every active `p'`-Clifford block.  The exact active
partition then assembles these block equivalences into a global
equivalence of `p'`-irreducible characters.

The auxiliary representation spaces are bundled with all their type
class data.  They may therefore vary independently from orbit to orbit.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CliffordPartition
open CharacterTriple

variable {G H : Type}
variable [Group G] [Finite G] [Group H] [Finite H]

noncomputable local instance centralTripleCliffordAssemblyFintypeG :
    Fintype G :=
  Fintype.ofFinite G

noncomputable local instance centralTripleCliffordAssemblyFintypeH :
    Fintype H :=
  Fintype.ofFinite H

/-- A central-isomorphism witness bundled together with its two
finite-dimensional representation spaces and all required instances. -/
structure CompleteCentralIsomorphismWitness
    {A B : Type} [Group A] [Finite A] [Group B] [Finite B]
    (T : CharacterTriple A) (U : CharacterTriple B) where
  /-- Representation space for the left canonical projective
  representation. -/
  leftSpace : Type
  /-- Representation space for the right canonical projective
  representation. -/
  rightSpace : Type
  /-- Additive structure on the left representation space. -/
  [leftAddCommGroup : AddCommGroup leftSpace]
  /-- Complex vector-space structure on the left representation
  space. -/
  [leftModule : Module ℂ leftSpace]
  /-- Finite dimensionality of the left representation space. -/
  [leftModuleFinite : Module.Finite ℂ leftSpace]
  /-- Nontriviality of the left representation space. -/
  [leftNontrivial : Nontrivial leftSpace]
  /-- Additive structure on the right representation space. -/
  [rightAddCommGroup : AddCommGroup rightSpace]
  /-- Complex vector-space structure on the right representation
  space. -/
  [rightModule : Module ℂ rightSpace]
  /-- Finite dimensionality of the right representation space. -/
  [rightModuleFinite : Module.Finite ℂ rightSpace]
  /-- Nontriviality of the right representation space. -/
  [rightNontrivial : Nontrivial rightSpace]
  /-- The complete central-isomorphism witness on these spaces. -/
  witness :
    CentralIsomorphismWitness T U leftSpace rightSpace

namespace CompleteCentralIsomorphismWitness

/-- The group embedding stored in a complete witness, exposed without
requiring callers to install its bundled representation-space instances. -/
def embedding
    {A B : Type} [Group A] [Finite A] [Group B] [Finite B]
    {T : CharacterTriple A} {U : CharacterTriple B}
    (C : CompleteCentralIsomorphismWitness T U) :
    B →* A := by
  letI := C.leftAddCommGroup
  letI := C.leftModule
  letI := C.leftModuleFinite
  letI := C.leftNontrivial
  letI := C.rightAddCommGroup
  letI := C.rightModule
  letI := C.rightModuleFinite
  letI := C.rightNontrivial
  exact C.witness.embedding

end CompleteCentralIsomorphismWitness

/-- Orbit matching plus central-isomorphism data for every pair of
matched canonical inertia triples. -/
structure CentralTripleCliffordAssemblyData
    (N : Subgroup G) [N.Normal]
    (M : Subgroup H) [M.Normal]
    (p : ℕ) where
  /-- Equivalence between the exact active Clifford-orbit spaces. -/
  activeOrbitEquiv :
    ActiveOrbit N p ≃ ActiveOrbit M p
  /-- A complete central-isomorphism witness between the canonical
  inertia triples of the chosen representatives of every matched
  active-orbit pair. -/
  centralWitness :
    ∀ q : ActiveOrbit N p,
      CompleteCentralIsomorphismWitness
        (CharacterTriple.ofInertia N q.1.out)
        (CharacterTriple.ofInertia M
          (activeOrbitEquiv q).1.out)

namespace CentralTripleCliffordAssemblyData

variable {N : Subgroup G} [N.Normal]
variable {M : Subgroup H} [M.Normal]
variable {p : ℕ} [Fact p.Prime]

/-- The active `p'`-Clifford block equivalence induced by the stored
central-isomorphism witness for `q`. -/
def blockEquiv
    (d : CentralTripleCliffordAssemblyData N M p)
    (q : ActiveOrbit N p) :
    PPrimeOrbitBlock N p q.1 ≃
      PPrimeOrbitBlock M p (d.activeOrbitEquiv q).1 := by
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
    C.witness.activeOrbitBlockEquiv
      N M (Fact.out : p.Prime) q
        (d.activeOrbitEquiv q)

/-- Package the central-triple block correspondences as exact active
orbitwise correspondence data. -/
def toActivePPrimeOrbitwiseCorrespondence
    (d : CentralTripleCliffordAssemblyData N M p) :
    ActivePPrimeOrbitwiseCorrespondence N M p where
  activeOrbitEquiv := d.activeOrbitEquiv
  blockEquiv := d.blockEquiv

@[simp]
theorem toActivePPrimeOrbitwiseCorrespondence_activeOrbitEquiv
    (d : CentralTripleCliffordAssemblyData N M p) :
    d.toActivePPrimeOrbitwiseCorrespondence.activeOrbitEquiv =
      d.activeOrbitEquiv :=
  rfl

@[simp]
theorem toActivePPrimeOrbitwiseCorrespondence_blockEquiv
    (d : CentralTripleCliffordAssemblyData N M p)
    (q : ActiveOrbit N p) :
    d.toActivePPrimeOrbitwiseCorrespondence.blockEquiv q =
      d.blockEquiv q :=
  rfl

/-- Assemble the orbitwise central-triple correspondences into an
equivalence of all ambient `p'`-irreducible characters. -/
def assembledPPrimeEquiv
    (d : CentralTripleCliffordAssemblyData N M p) :
    PPrimeIrreducibleCharacter G p ≃
      PPrimeIrreducibleCharacter H p :=
  d.toActivePPrimeOrbitwiseCorrespondence.assemble

@[simp]
theorem assembledPPrimeEquiv_apply
    (d : CentralTripleCliffordAssemblyData N M p)
    (χ : PPrimeIrreducibleCharacter G p) :
    d.assembledPPrimeEquiv χ =
      d.toActivePPrimeOrbitwiseCorrespondence.assemble χ :=
  rfl

@[simp]
theorem activeOrbitIndex_assembledPPrimeEquiv
    (d : CentralTripleCliffordAssemblyData N M p)
    (χ : PPrimeIrreducibleCharacter G p) :
    activeOrbitIndex M (d.assembledPPrimeEquiv χ) =
      d.activeOrbitEquiv (activeOrbitIndex N χ) :=
  d.toActivePPrimeOrbitwiseCorrespondence
    |>.activeOrbitIndex_assemble χ

@[simp]
theorem activeOrbitIndex_assembledPPrimeEquiv_symm
    (d : CentralTripleCliffordAssemblyData N M p)
    (ψ : PPrimeIrreducibleCharacter H p) :
    activeOrbitIndex N (d.assembledPPrimeEquiv.symm ψ) =
      d.activeOrbitEquiv.symm (activeOrbitIndex M ψ) :=
  d.toActivePPrimeOrbitwiseCorrespondence
    |>.activeOrbitIndex_assemble_symm ψ

end CentralTripleCliffordAssemblyData
end InductiveMcKay
end McKayConjecture
