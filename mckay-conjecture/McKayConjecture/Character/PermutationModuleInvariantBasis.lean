/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.PermutationModuleOrbitSum

/-!
# An orbit-sum basis of the invariant submodule

If a finite group permutes a finite module basis, its invariant
submodule is free on the sums over the basis-index orbits.  This
statement is characteristic-free.
-/

noncomputable section

open scoped BigOperators

namespace Representation
namespace PermutationModuleBasis

variable {k P V ι : Type}
variable [CommRing k] [Group P]
variable [AddCommGroup V] [Module k V]
variable [DistribMulAction P V] [SMulCommClass P k V]
variable [MulAction P ι] [Finite ι]

variable (B : PermutationModuleBasis (k := k) (P := P) (V := V) (ι := ι))

local notation "Ω" =>
  MulAction.orbitRel.Quotient P ι

noncomputable local instance invariantBasisIndexFintype :
    Fintype ι :=
  Fintype.ofFinite ι

noncomputable local instance orbitQuotientFintype :
    Fintype Ω :=
  Fintype.ofFinite Ω

noncomputable local instance invariantOrbitQuotientDecidableEq :
    DecidableEq Ω :=
  Classical.decEq Ω

/-- Coordinates on the invariant submodule, one coordinate for each
orbit, obtained by evaluating at the chosen representative. -/
def orbitCoordinates :
    invariants B.representation →ₗ[k] (Ω → k) where
  toFun x ω := B.basis.coord ω.out (x : V)
  map_add' x y := by
    funext ω
    exact map_add (B.basis.coord ω.out) (x : V) (y : V)
  map_smul' a x := by
    funext ω
    exact map_smul (B.basis.coord ω.out) a (x : V)

omit [Finite ι] in
@[simp]
theorem orbitCoordinates_apply
    (x : invariants B.representation)
    (ω : Ω) :
    B.orbitCoordinates x ω =
      B.basis.coord ω.out (x : V) :=
  rfl

/-- The orbit-coordinate map is injective. -/
theorem orbitCoordinates_injective :
    Function.Injective B.orbitCoordinates := by
  intro x y hxy
  apply Subtype.ext
  apply B.basis.ext_elem
  intro i
  let ω : Ω := Quotient.mk'' i
  have hout :
      ω.out ∈ MulAction.orbit P i := by
    exact
      MulAction.orbitRel_apply.mp
        (Quotient.exact' (Quotient.out_eq' ω))
  obtain ⟨g, hg⟩ :=
    MulAction.mem_orbit_iff.mp hout
  have hx :
      B.basis.coord ω.out (x : V) =
        B.basis.coord i (x : V) := by
    simpa only [hg] using
      B.coord_eq_of_mem_invariants x.property g i
  have hy :
      B.basis.coord ω.out (y : V) =
        B.basis.coord i (y : V) := by
    simpa only [hg] using
      B.coord_eq_of_mem_invariants y.property g i
  calc
    (B.basis.repr (x : V)) i =
        B.basis.coord i (x : V) :=
          (Module.Basis.coord_apply _ _ _).symm
    _ = B.basis.coord ω.out (x : V) := hx.symm
    _ = B.orbitCoordinates x ω := rfl
    _ = B.orbitCoordinates y ω := congrFun hxy ω
    _ = B.basis.coord ω.out (y : V) := rfl
    _ = B.basis.coord i (y : V) := hy
    _ = (B.basis.repr (y : V)) i :=
      Module.Basis.coord_apply _ _ _

/-- Every assignment of orbit coefficients is realized by the
corresponding linear combination of orbit sums. -/
theorem orbitCoordinates_surjective :
    Function.Surjective B.orbitCoordinates := by
  intro f
  refine ⟨∑ ω : Ω, f ω • B.orbitSum ω, ?_⟩
  funext τ
  change
    B.basis.coord τ.out
        ((↑(∑ ω : Ω, f ω • B.orbitSum ω) : V)) =
      f τ
  simp only [map_sum, Submodule.coe_sum, Submodule.coe_smul_of_tower,
    map_smul, B.coord_orbitSum_out]
  rw [Fintype.sum_eq_single τ]
  · simp
  · intro ω hω
    have hτω : τ ≠ ω := Ne.symm hω
    simp [hτω]

/-- Linear equivalence between invariant vectors and functions on the
set of basis-index orbits. -/
def orbitCoordinatesEquiv :
    invariants B.representation ≃ₗ[k] (Ω → k) :=
  LinearEquiv.ofBijective B.orbitCoordinates
    ⟨B.orbitCoordinates_injective,
      B.orbitCoordinates_surjective⟩

@[simp]
theorem orbitCoordinatesEquiv_apply
    (x : invariants B.representation) :
    B.orbitCoordinatesEquiv x =
      B.orbitCoordinates x :=
  rfl

/-- The basis of the invariant submodule indexed by basis-index
orbits. -/
def invariantsOrbitBasis :
    Module.Basis Ω k (invariants B.representation) :=
  Module.Basis.ofEquivFun B.orbitCoordinatesEquiv

/-- The abstract basis vector attached to an orbit is its concrete
orbit sum. -/
@[simp]
theorem invariantsOrbitBasis_apply
    (ω : Ω) :
    B.invariantsOrbitBasis ω = B.orbitSum ω := by
  apply B.orbitCoordinates_injective
  funext τ
  change
    B.orbitCoordinatesEquiv (B.invariantsOrbitBasis ω) τ =
      B.basis.coord τ.out (B.orbitSum ω : V)
  rw [← Module.Basis.ofEquivFun_repr_apply
    B.orbitCoordinatesEquiv]
  simp only [invariantsOrbitBasis,
    Module.Basis.repr_self_apply, B.coord_orbitSum_out]
  by_cases h : ω = τ <;> simp [h, eq_comm]

/-- Orbit sums span the full invariant submodule. -/
theorem span_range_orbitSum :
    Submodule.span k (Set.range B.orbitSum) = ⊤ := by
  have hfun :
      B.orbitSum =
        (B.invariantsOrbitBasis :
          Ω → invariants B.representation) := by
    funext ω
    exact (B.invariantsOrbitBasis_apply ω).symm
  rw [hfun]
  exact B.invariantsOrbitBasis.span_eq

/-- Explicit orbit-sum expansion of an invariant vector. -/
theorem sum_orbitSum_eq
    (x : invariants B.representation) :
    (∑ ω : Ω,
        B.basis.coord ω.out (x : V) • B.orbitSum ω) =
      x := by
  calc
    (∑ ω : Ω,
        B.basis.coord ω.out (x : V) • B.orbitSum ω) =
      ∑ ω : Ω,
        (B.invariantsOrbitBasis.repr x) ω •
          B.invariantsOrbitBasis ω := by
            apply Finset.sum_congr rfl
            intro ω _
            rw [B.invariantsOrbitBasis_apply]
            congr 1
    _ = x := B.invariantsOrbitBasis.sum_repr x

end PermutationModuleBasis
end Representation
