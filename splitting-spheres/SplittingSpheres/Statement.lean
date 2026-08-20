/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Topology.Connected.Clopen
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# Splitting spheres for the two-component `2`-sphere unlink in `S^4`

This file gives the formal statement of the main theorem of Alison Tatsuoka,
*Splitting spheres for unlinked S^2's in S^4* (arXiv:2502.01817).

The theorem is stated for one explicit standard representative of the two-component unlink.
A diffeomorphism carrying this representative to any given unlink transports splitting spheres
and smooth isotopies in the complement, so the fixed-representative statement is equivalent to
the paper's ambient-diffeomorphism-invariant formulation.  Splitting spheres are unparametrized
embedded submanifolds: both the splitting condition and the isotopy relation depend only on the
range of a parametrization.
-/

@[expose] public section

open Metric Set
open scoped ContDiff Manifold unitInterval

noncomputable section

namespace SplittingSpheres

/-- The standard smooth `n`-sphere, realized as the unit sphere in `ℝ^(n+1)`. -/
abbrev Sphere (n : ℕ) : Type :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- A bundled smooth embedding of the standard `m`-sphere in the standard `n`-sphere. -/
abbrev SmoothSphereEmbedding (m n : ℕ) :=
  TauCeti.SmoothEmbedding (𝓡 m) (𝓡 n) ∞ (Sphere m) (Sphere n)

/-- The two round `2`-spheres used as the fixed standard unlink in `S^4`.

Writing a point of `S^4 ⊆ ℝ^5` as `(x₀,x₁,x₂,x₃,x₄)`, component `0` is cut out by
`x₃ = -1/2, x₄ = 0`, and component `1` by `x₃ = 1/2, x₄ = 0`.  They bound disjoint round
`3`-balls in the equatorial `S^3` given by `x₄ = 0`. -/
def standardUnlinkComponent (i : Fin 2) : Set (Sphere 4) :=
  {x | x.1 3 = (if i = 0 then -(1 / 2 : ℝ) else 1 / 2) ∧ x.1 4 = 0}

/-- The underlying subset of `S^4` of the fixed standard two-component unlink. -/
def standardUnlinkCarrier : Set (Sphere 4) :=
  standardUnlinkComponent 0 ∪ standardUnlinkComponent 1

/-- A subset `S` separates `A` from `B` when it misses both sets and each of `A` and `B` lies in
one connected component of `Sᶜ`, with those two components distinct. -/
def Separates (S A B : Set (Sphere 4)) : Prop :=
  Disjoint S (A ∪ B) ∧
    ∃ a ∈ A, ∃ b ∈ B,
      A ⊆ connectedComponentIn Sᶜ a ∧
      B ⊆ connectedComponentIn Sᶜ b ∧
      connectedComponentIn Sᶜ a ≠ connectedComponentIn Sᶜ b

/-- A smooth embedded `3`-sphere is a splitting sphere for the standard unlink if its image
separates the two standard component subsets. -/
def IsSplittingSphere (S : SmoothSphereEmbedding 3 4) : Prop :=
  Separates (range S) (standardUnlinkComponent 0) (standardUnlinkComponent 1)

/-- A smooth isotopy of unparametrized embedded `3`-spheres in `S^4`.

The endpoint conditions compare ranges, rather than parametrizations, so this is a relation on
embedded submanifolds.  Joint smoothness uses Mathlib's manifold-with-boundary structure on the
unit interval, and every time slice is required to be a smooth embedding. -/
structure SmoothSphereIsotopy (S₀ S₁ : SmoothSphereEmbedding 3 4) where
  /-- The jointly smooth one-parameter family. -/
  toFun : I × Sphere 3 → Sphere 4
  /-- Smoothness jointly in time and the sphere variable, including at the interval boundary. -/
  contMDiff_toFun :
    ContMDiff ((𝓡∂ 1).prod (𝓡 3)) (𝓡 4) ∞ toFun
  /-- Every time slice is a smooth embedding. -/
  isSmoothEmbedding_slice : ∀ t : I,
    Manifold.IsSmoothEmbedding (𝓡 3) (𝓡 4) ∞ (fun x ↦ toFun (t, x))
  /-- At time zero the image is the first unparametrized sphere. -/
  range_zero : range (fun x ↦ toFun (0, x)) = range S₀
  /-- At time one the image is the second unparametrized sphere. -/
  range_one : range (fun x ↦ toFun (1, x)) = range S₁

/-- Two embedded spheres are smoothly isotopic in the complement of the standard unlink if a
smooth isotopy between their images stays disjoint from its carrier at every time. -/
def SmoothlyIsotopicInComplement (S₀ S₁ : SmoothSphereEmbedding 3 4) : Prop :=
  ∃ H : SmoothSphereIsotopy S₀ S₁,
    ∀ p : I × Sphere 3, H.toFun p ∉ standardUnlinkCarrier

/-- The precise fixed-representative form of the paper's main theorem: the standard unlink of two
round `2`-spheres in `S^4` has a countably infinite family of splitting `3`-spheres whose embedded
images are pairwise non-isotopic through the unlink complement.

This proposition is unconditional: proving it also supplies, through each splitting condition,
points on both explicit standard components, so no separate link-existence hypothesis can make the
statement vacuous.  Diffeomorphism invariance transports the conclusion to every unlink in the
ambient diffeomorphism orbit of this fixed representative. -/
def MainTheorem : Prop :=
  ∃ S : ℕ → SmoothSphereEmbedding 3 4,
    (∀ k, IsSplittingSphere (S k)) ∧
    Pairwise fun i j ↦ ¬SmoothlyIsotopicInComplement (S i) (S j)

end SplittingSpheres
