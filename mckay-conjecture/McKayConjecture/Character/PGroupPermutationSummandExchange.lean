/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.KrullSchmidtExchange
import McKayConjecture.Character.PGroupPermutationOrbitDecomposition
import McKayConjecture.Character.PermutationModuleOrbitIntertwining

/-!
# Exchange for summands of p-group permutation modules

The orbit factors of a finite permutation module for a finite
`p`-group are indecomposable with local endomorphism rings.  Combining
this with the local exchange lemma shows that every indecomposable
split retract of the permutation module is equivalent to one of its
orbit factors.  In particular, no hypothesis that an idempotent
preserve the individual orbit factors is needed.
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

local notation "ρ" => B.representation
local notation "Ω" => MulAction.orbitRel.Quotient P ι

noncomputable local instance pGroupSummandOrbitFintype :
    Fintype Ω :=
  Fintype.ofFinite Ω

/-- Every directly indecomposable split retract of a finite
permutation module for a finite `p`-group is equivalent to one of the
canonical transitive orbit factors.  This is the one-summand
Krull--Schmidt exchange theorem specialized to permutation modules. -/
theorem exists_orbit_equiv_of_indecomposable_split_retract
    (hP : IsPGroup p P)
    {A : Type*} [AddCommGroup A] [Module k A]
    [FiniteDimensional k A]
    (ρA : Representation k P A)
    (hρA : ρA.IsDirectSumIndecomposable)
    (includeA : IntertwiningMap ρA ρ)
    (retractA : IntertwiningMap ρ ρA)
    (hretract : retractA.comp includeA =
      IntertwiningMap.id ρA) :
    ∃ ω : Ω, Nonempty
      (ρA.Equiv
        (B.orbitSubrepresentation ω).toRepresentation) := by
  letI : Nontrivial A := hρA.1
  letI : IsLocalRing (IntertwiningMap ρA ρA) :=
    isLocalRing_endomorphisms_of_isDirectSumIndecomposable hρA
  exact
    IntertwiningMap.exists_equiv_of_split_retract
      (fun ω : Ω =>
        (B.orbitSubrepresentation ω).toRepresentation)
      (fun ω =>
        B.orbitSubrepresentation_isDirectSumIndecomposable hP ω)
      includeA retractA hretract
      (fun ω => B.orbitInclusionIntertwiningMap ω)
      (fun ω => B.orbitComponentIntertwiningMap ω)
      B.sum_orbitInclusion_comp_orbitComponent

/-- The range inclusion of an equivariant endomorphism. -/
def endomorphismRangeInclusion
    (e : IntertwiningMap ρ ρ) :
    IntertwiningMap e.range.toRepresentation ρ where
  toLinearMap := e.range.toSubmodule.subtype
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    rfl

/-- An equivariant endomorphism, with its codomain restricted to its
range. -/
def endomorphismRangeRetract
    (e : IntertwiningMap ρ ρ) :
    IntertwiningMap ρ e.range.toRepresentation where
  toLinearMap :=
    e.toLinearMap.codRestrict e.range.toSubmodule
      (fun v => ⟨v, rfl⟩)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun (e.isIntertwining' g) v

omit [Finite P] [Finite ι] in
/-- An idempotent restricts to the identity on its range. -/
theorem endomorphismRangeRetract_comp_inclusion
    (e : IntertwiningMap ρ ρ)
    (he : IsIdempotentElem e) :
    (B.endomorphismRangeRetract e).comp
        (B.endomorphismRangeInclusion e) =
      IntertwiningMap.id e.range.toRepresentation := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  obtain ⟨v, hv⟩ := x.property
  change e (x : V) = (x : V)
  rw [← hv]
  simpa only [IntertwiningMap.mul_apply,
    IntertwiningMap.toLinearMap_apply] using
    congrArg (fun t : IntertwiningMap ρ ρ => t v) he

/-- If the image of an arbitrary equivariant idempotent is directly
indecomposable, then it is equivalent to a canonical orbit
permutation module.  The idempotent may have completely arbitrary
off-diagonal orbit blocks. -/
theorem exists_orbit_equiv_range_of_idempotent_of_indecomposable
    (hP : IsPGroup p P)
    (e : IntertwiningMap ρ ρ)
    (he : IsIdempotentElem e)
    (hrange : e.range.toRepresentation.IsDirectSumIndecomposable) :
    ∃ ω : Ω, Nonempty
      (e.range.toRepresentation.Equiv
        (B.orbitSubrepresentation ω).toRepresentation) := by
  letI : FiniteDimensional k V :=
    B.basis.finiteDimensional_of_finite
  exact
    B.exists_orbit_equiv_of_indecomposable_split_retract hP
      e.range.toRepresentation hrange
      (B.endomorphismRangeInclusion e)
      (B.endomorphismRangeRetract e)
      (B.endomorphismRangeRetract_comp_inclusion e he)

end PermutationModuleBasis
end Representation
