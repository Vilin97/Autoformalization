/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AdaptedCliffordFibreAssembly
import McKayConjecture.InductiveMcKay.CentralTripleActivityTransport

/-!
# Matched Clifford assembly from numerical inertia fibres

Let `N ◁ G`, let `H ≤ G`, and let `M ◁ H`, with `N H = G`.
An `H`-equivariant equivalence between the prime-to-`p` characters of
`N` and `M` identifies stabilizer indices.  If the corresponding
prime-to-`p` inertia fibres are equivalent, activity is preserved as well.
The resulting active-orbit matching and the same fibre equivalences then
assemble by Clifford theory to a correspondence between `G` and `H`.

This is the numerical analogue of
`MatchedCentralTripleCliffordAssemblyData`: it asks only for the inertia
fibre equivalences that the assembly actually consumes.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CliffordCorrespondence
open CliffordPartition

variable {G : Type} [Group G] [Finite G]
variable (N H : Subgroup G) [N.Normal]
variable (M : Subgroup H) [M.Normal]

noncomputable local instance matchedCentralFibreAssemblyFintypeG :
    Fintype G :=
  Fintype.ofFinite G

noncomputable local instance matchedCentralFibreAssemblyFintypeH :
    Fintype H :=
  Fintype.ofFinite H

/-- The exact numerical input for matched Clifford assembly. -/
structure MatchedCentralFibreCliffordAssemblyData (p : ℕ) where
  /-- The source normal subgroup and target subgroup generate `G`. -/
  sup_eq_top : N ⊔ H = ⊤
  /-- Matching of prime-to-`p` normal-subgroup characters. -/
  characterEquiv :
    PPrimeIrreducibleCharacter N p ≃
      PPrimeIrreducibleCharacter M p
  /-- Equivariance under the target ambient subgroup. -/
  characterEquiv_smul :
    ∀ (h : H) (θ : PPrimeIrreducibleCharacter N p),
      characterEquiv (h • θ) =
        h • characterEquiv θ
  /-- Matching of the prime-to-`p` inertia fibres for every exactly
  matched normal-subgroup character. -/
  inertiaFibreEquiv :
    ∀ θ : PPrimeIrreducibleCharacter N p,
      PPrimeIrreducibleCharactersOverInertia
          N θ.1 p ≃
        PPrimeIrreducibleCharactersOverInertia
          M (characterEquiv θ).1 p

namespace MatchedCentralFibreCliffordAssemblyData

variable {N H M}
variable {p : ℕ} [Fact p.Prime]

/-- A matched numerical inertia-fibre equivalence preserves the exact
activity predicate. -/
theorem isActivePPrimeCharacter_iff
    (d : MatchedCentralFibreCliffordAssemblyData N H M p)
    (θ : PPrimeIrreducibleCharacter N p) :
    @IsActivePPrimeCharacter G _ N _ p θ ↔
      @IsActivePPrimeCharacter H _ M _ p
        (d.characterEquiv θ) := by
  have hindex :
      (IrreducibleCharacter.inertia N θ.1).index =
        (IrreducibleCharacter.inertia
          M (d.characterEquiv θ).1).index :=
    inertia_index_eq_of_equivariant_equiv
      N H M d.sup_eq_top d.characterEquiv
        d.characterEquiv_smul θ
  rw [CliffordPartition.isActivePPrimeCharacter_iff_inertia
      N (Fact.out : p.Prime) θ,
    CliffordPartition.isActivePPrimeCharacter_iff_inertia
      M (Fact.out : p.Prime) (d.characterEquiv θ)]
  constructor
  · rintro ⟨hdegree, ⟨ρ⟩⟩
    refine ⟨?_, ⟨d.inertiaFibreEquiv θ ρ⟩⟩
    rwa [← hindex]
  · rintro ⟨hdegree, ⟨σ⟩⟩
    refine ⟨?_, ⟨(d.inertiaFibreEquiv θ).symm σ⟩⟩
    rwa [hindex]

/-- The induced equivalence of active Clifford orbit spaces. -/
def activeOrbitEquiv
    (d : MatchedCentralFibreCliffordAssemblyData N H M p) :
    ActiveOrbit N p ≃ ActiveOrbit M p :=
  activeOrbitEquivOfEquivariantActivityIff
    N H M d.sup_eq_top d.characterEquiv
      d.characterEquiv_smul d.isActivePPrimeCharacter_iff

@[simp]
theorem activeOrbitEquiv_apply_coe
    (d : MatchedCentralFibreCliffordAssemblyData N H M p)
    (q : ActiveOrbit N p) :
    (d.activeOrbitEquiv q).1 =
      (Quotient.mk''
        (d.characterEquiv (q.pPrimeOut N)).1 :
          OrbitSpace M) :=
  rfl

/-- Package the matched character and inertia-fibre data as adapted
Clifford-fibre assembly data. -/
def toAdaptedCliffordFibreAssemblyData
    (d : MatchedCentralFibreCliffordAssemblyData N H M p) :
    AdaptedCliffordFibreAssemblyData N M p where
  activeOrbitEquiv := d.activeOrbitEquiv
  sourceRepresentative := fun q => q.pPrimeOut N
  sourceRepresentative_orbit := fun q =>
    Quotient.out_eq' q.1
  sourceInertiaIndex_isPPrime := fun q =>
    activeOrbit_inertia_index_isPPrime N q
  targetRepresentative := fun q =>
    d.characterEquiv (q.pPrimeOut N)
  targetRepresentative_orbit := fun _ => rfl
  targetInertiaIndex_isPPrime := fun q => by
    rw [← inertia_index_eq_of_equivariant_equiv
      N H M d.sup_eq_top d.characterEquiv
        d.characterEquiv_smul (q.pPrimeOut N)]
    exact activeOrbit_inertia_index_isPPrime N q
  inertiaFibreEquiv := fun q =>
    d.inertiaFibreEquiv (q.pPrimeOut N)

/-- Assemble the matched numerical fibre data into the ambient
prime-to-`p` character correspondence. -/
def assembledPPrimeEquiv
    (d : MatchedCentralFibreCliffordAssemblyData N H M p) :
    PPrimeIrreducibleCharacter G p ≃
      PPrimeIrreducibleCharacter H p :=
  d.toAdaptedCliffordFibreAssemblyData.assembledPPrimeEquiv

end MatchedCentralFibreCliffordAssemblyData
end InductiveMcKay
end McKayConjecture
