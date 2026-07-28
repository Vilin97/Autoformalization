/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.PGroupTransitivePermutationIndecomposable
import McKayConjecture.Character.PermutationModuleOrbitDecomposition

/-!
# Orbit factors of a permutation module for a p-group

For a finite `p`-group over a field of characteristic `p`, this file
combines the orbit decomposition of a permutation basis with the
indecomposability theorem for transitive permutation modules.  Thus
the canonical orbit factors form an internal direct sum of
indecomposables, and every factor has a local equivariant
endomorphism ring.

This is the full existence-and-locality input for the
Krull--Schmidt proof that a direct summand of a finite permutation
module is again a permutation module.  The remaining input is
uniqueness/cancellation for finite direct sums of modules with local
endomorphism rings.
-/

noncomputable section

namespace Representation
namespace PermutationModuleBasis

variable {p : ℕ} [Fact p.Prime]
variable {k P V ι : Type}
variable [Field k] [CharP k p]
variable [Group P] [Finite P]
variable [AddCommGroup V] [Module k V]
variable [DistribMulAction P V] [SMulCommClass P k V]
variable [MulAction P ι] [Finite ι]

variable (B : PermutationModuleBasis
  (k := k) (P := P) (V := V) (ι := ι))

local notation "Ω" => MulAction.orbitRel.Quotient P ι

/-- Every canonical orbit factor of a finite permutation module for a
`p`-group is directly indecomposable. -/
theorem orbitSubrepresentation_isDirectSumIndecomposable
    (hP : IsPGroup p P) (ω : Ω) :
    (B.orbitSubrepresentation ω).toRepresentation.IsDirectSumIndecomposable := by
  letI : Nonempty ω.orbit := ω.nonempty_orbit.to_subtype
  letI := B.orbitDistribMulAction ω
  letI := B.orbitSMulCommClass ω
  let Bω := B.orbitPermutationModuleBasis ω
  exact Bω.isDirectSumIndecomposable_of_transitive hP

/-- Every equivariant endomorphism of a canonical orbit factor is
either a unit or nilpotent. -/
theorem orbitEndomorphism_isUnit_or_isNilpotent
    (hP : IsPGroup p P) (ω : Ω)
    (f : IntertwiningMap
      (B.orbitSubrepresentation ω).toRepresentation
      (B.orbitSubrepresentation ω).toRepresentation) :
    IsUnit f ∨ IsNilpotent f := by
  letI : FiniteDimensional k
      (B.orbitSubrepresentation ω).toSubmodule := by
    change FiniteDimensional k (B.orbitSubmodule ω)
    exact (B.orbitBasis ω).finiteDimensional_of_finite
  exact
    f.isUnit_or_isNilpotent_of_isDirectSumIndecomposable
      (B.orbitSubrepresentation_isDirectSumIndecomposable hP ω)

/-- Every canonical orbit factor has a local equivariant
endomorphism ring. -/
theorem orbitEndomorphism_isLocalRing
    (hP : IsPGroup p P) (ω : Ω) :
    IsLocalRing
      (IntertwiningMap
        (B.orbitSubrepresentation ω).toRepresentation
        (B.orbitSubrepresentation ω).toRepresentation) := by
  letI : FiniteDimensional k
      (B.orbitSubrepresentation ω).toSubmodule := by
    change FiniteDimensional k (B.orbitSubmodule ω)
    exact (B.orbitBasis ω).finiteDimensional_of_finite
  exact
    isLocalRing_endomorphisms_of_isDirectSumIndecomposable
      (B.orbitSubrepresentation_isDirectSumIndecomposable hP ω)

/-- A useful block-diagonal special case of the direct-summand
theorem: if an equivariant idempotent preserves every orbit factor,
then its restriction to each orbit is either zero or the identity.
Thus the only missing difficulty in the general theorem comes from
off-diagonal blocks between isomorphic indecomposable factors. -/
theorem orbitRestriction_eq_zero_or_eq_id
    (hP : IsPGroup p P)
    (e : Module.End k V)
    (he_comm : ∀ g : P,
      e ∘ₗ B.representation g =
        B.representation g ∘ₗ e)
    (he_idem : IsIdempotentElem e)
    (he_maps : ∀ ω : Ω,
      Set.MapsTo e (B.orbitSubmodule ω) (B.orbitSubmodule ω))
    (ω : Ω) :
    e.restrict (he_maps ω) = 0 ∨
      e.restrict (he_maps ω) = LinearMap.id := by
  letI : Nonempty ω.orbit := ω.nonempty_orbit.to_subtype
  letI := B.orbitDistribMulAction ω
  letI := B.orbitSMulCommClass ω
  let Bω := B.orbitPermutationModuleBasis ω
  apply Bω.equivariant_idempotent_eq_zero_or_eq_id hP
  · intro g
    ext x
    change e (B.representation g (x : V)) =
      B.representation g (e (x : V))
    exact LinearMap.congr_fun (he_comm g) x
  · change IsIdempotentElem (e.restrict (he_maps ω))
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change e (e (x : V)) = e (x : V)
    exact LinearMap.congr_fun he_idem x

end PermutationModuleBasis
end Representation
