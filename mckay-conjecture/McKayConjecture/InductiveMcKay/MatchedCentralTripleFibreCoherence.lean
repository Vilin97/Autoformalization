/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.MatchedCentralFibreCentralAction
import McKayConjecture.InductiveMcKay.MatchedCentralTripleCentralScalarAssembly

/-!
# Numerical fibre coherence from matched central inertia triples

A complete central-isomorphism witness between a pair of canonical inertia
triples already contains the character correspondence on the two inertia
fibres.  If its embedding is the canonical target-to-source inertia
embedding, the central character-triple scalar theorem also proves the
normalized central-value identity required by numerical Clifford assembly.

This file packages those consequences for every matched normal-subgroup
character.  In particular, inertia-fibre equivalences and central-action
intertwiners do not have to be postulated separately once the standard
central-triple form of a correspondence theorem is available.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple
open CliffordCorrespondence

variable {G : Type} [Group G] [Finite G]
variable (N H : Subgroup G) [N.Normal]
variable (M : Subgroup H) [M.Normal]
variable {p : ℕ} [Fact p.Prime]

namespace MatchedCentralTripleCliffordAssemblyData

variable {N H M}

/-- Forget a matched central-triple assembly to its numerical
inertia-fibre equivalences. -/
def toMatchedCentralFibreCliffordAssemblyData
    (d : MatchedCentralTripleCliffordAssemblyData N H M p) :
    MatchedCentralFibreCliffordAssemblyData N H M p where
  sup_eq_top := d.sup_eq_top
  characterEquiv := d.characterEquiv
  characterEquiv_smul := d.characterEquiv_smul
  inertiaFibreEquiv := fun θ ↦ by
    let C := d.centralWitness θ
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
        N θ.1 M (d.characterEquiv θ).1
        (Fact.out : p.Prime) θ.2
        (d.characterEquiv θ).2

@[simp]
theorem toMatchedCentralFibreCliffordAssemblyData_characterEquiv
    (d : MatchedCentralTripleCliffordAssemblyData N H M p) :
    d.toMatchedCentralFibreCliffordAssemblyData.characterEquiv =
      d.characterEquiv :=
  rfl

/-- Canonically embedded central inertia triples imply the exact
central-scalar condition for the forgotten numerical fibre assembly. -/
theorem toMatchedCentralFibreCliffordAssemblyData_preservesCentralScalars
    (d : MatchedCentralTripleCliffordAssemblyData N H M p)
    (hcanonical : d.UsesCanonicalInertiaEmbeddings) :
    d.toMatchedCentralFibreCliffordAssemblyData.PreservesCentralScalars := by
  intro θ ρ z hzcentral hzH
  let f := d.toMatchedCentralFibreCliffordAssemblyData
  let C := d.centralWitness θ
  let zSource := f.sourceInertiaElement θ z hzcentral
  let zTarget := f.targetInertiaElement θ z hzcentral hzH
  letI := C.leftAddCommGroup
  letI := C.leftModule
  letI := C.leftModuleFinite
  letI := C.leftNontrivial
  letI := C.rightAddCommGroup
  letI := C.rightModule
  letI := C.rightModuleFinite
  letI := C.rightNontrivial
  have hembedding :
      C.witness.embedding zTarget = zSource := by
    rw [hcanonical θ]
    apply Subtype.ext
    rfl
  have hzcentralizer :
      C.witness.embedding zTarget ∈
        Subgroup.centralizer
          ((ofInertia N θ.1).normalSubgroup :
            Set (IrreducibleCharacter.inertia N θ.1)) := by
    rw [hembedding, Subgroup.mem_centralizer_iff]
    intro x hx
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hzcentral (x : G)
  have h :=
    C.witness.pPrimeInertiaEquiv_matchedCentral_cross
      N M θ.1 (d.characterEquiv θ).1
      (Fact.out : p.Prime) θ.2
      (d.characterEquiv θ).2 ρ zTarget hzcentralizer
  rw [hembedding] at h
  exact h

/-- Canonically embedded central inertia triples also produce the
representation-level central-action intertwiners used by numerical
Clifford assembly. -/
theorem toMatchedCentralFibreCliffordAssemblyData_hasCentralActionIntertwiners
    (d : MatchedCentralTripleCliffordAssemblyData N H M p)
    (hcanonical : d.UsesCanonicalInertiaEmbeddings) :
    d.toMatchedCentralFibreCliffordAssemblyData.HasCentralActionIntertwiners :=
  d.toMatchedCentralFibreCliffordAssemblyData
    |>.hasCentralActionIntertwiners_of_preservesCentralScalars
      (d.toMatchedCentralFibreCliffordAssemblyData_preservesCentralScalars
        hcanonical)

end MatchedCentralTripleCliffordAssemblyData
end InductiveMcKay
end McKayConjecture
