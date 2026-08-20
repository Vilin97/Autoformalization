/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import SplittingSpheres.Foundations.RelativeDiffeomorph

/-!
# Relative mapping classes modulo coordinate four-ball support

An embedded coordinate four-ball is specified by a smooth chart from an open subset of a
four-manifold onto Euclidean four-space.  Its carrier is the inverse image of the closed unit
ball.  This data is stronger than a bare topological ball: it records the smooth extension to an
open neighborhood that later support, capping, and conjugation arguments need.

This file defines relative diffeomorphisms supported in some such ball and the corresponding
normal-closure mapping-class quotient.  It does not assert that an arbitrary topologically
embedded ball admits coordinate data; geometric constructions must exhibit the chart they use.
-/

@[expose] public section

open Function Metric Set
open TopologicalSpace
open scoped ContDiff Manifold Topology

noncomputable section

namespace SplittingSpheres

universe uM

abbrev FourSpace := EuclideanSpace ℝ (Fin 4)

variable {M : Type uM} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]

/-- A smoothly embedded closed four-ball together with a coordinate neighborhood.  The actual
closed carrier is defined below as the pullback of the Euclidean closed unit ball. -/
structure CoordinateFourBall (M : Type uM) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] where
  /-- Open coordinate neighborhood containing the closed ball. -/
  domain : Opens M
  /-- Global coordinates on that neighborhood. -/
  chart : domain ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ FourSpace

namespace CoordinateFourBall

section Transport

variable [IsManifold (𝓡 4) ∞ M]

/-- Image of an open coordinate domain under an ambient diffeomorphism. -/
def imageDomain (e : M ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ M) (U : Opens M) : Opens M :=
  ⟨e '' U, e.toHomeomorph.isOpenMap U U.2⟩

/-- Restriction of an ambient diffeomorphism to an open subset and its image. -/
def domainDiffeomorph (e : M ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ M) (U : Opens M) :
    U ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ imageDomain e U where
  toEquiv := (e.toHomeomorph.image U).toEquiv
  contMDiff_toFun := by
    rw [ContMDiff.iff_comp_isImmersion
      (Manifold.IsSmoothEmbedding.of_opens (imageDomain e U)).isImmersion]
    refine ⟨(e.toHomeomorph.image U).continuous, ?_⟩
    convert e.contMDiff.comp contMDiff_subtype_val using 1
    ext x
    rfl
  contMDiff_invFun := by
    rw [ContMDiff.iff_comp_isImmersion
      (Manifold.IsSmoothEmbedding.of_opens U).isImmersion]
    refine ⟨(e.toHomeomorph.image U).symm.continuous, ?_⟩
    convert e.symm.contMDiff.comp contMDiff_subtype_val using 1
    ext x
    rfl

/-- Transport displayed coordinate-ball data by an ambient diffeomorphism. -/
def transport (B : CoordinateFourBall M)
    (e : M ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ M) : CoordinateFourBall M where
  domain := imageDomain e B.domain
  chart := (domainDiffeomorph e B.domain).symm.trans B.chart

end Transport

/-- The underlying closed-ball carrier inside the ambient manifold. -/
def carrier (B : CoordinateFourBall M) : Set M :=
  Subtype.val '' (B.chart.symm '' closedBall (0 : FourSpace) 1)

/-- Transporting coordinate-ball data transports its carrier by the same ambient
diffeomorphism. -/
theorem carrier_transport [IsManifold (𝓡 4) ∞ M]
    (B : CoordinateFourBall M) (e : M ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ M) :
    (B.transport e).carrier = e '' B.carrier := by
  ext x
  constructor
  · rintro ⟨z, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨B.chart.symm v, ⟨B.chart.symm v, ⟨v, hv, rfl⟩, rfl⟩, ?_⟩
    rfl
  · rintro ⟨_, ⟨z, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩
    refine ⟨(B.transport e).chart.symm v, ⟨v, hv, rfl⟩, ?_⟩
    rfl

/-- The carrier lies in the coordinate domain. -/
theorem carrier_subset_domain (B : CoordinateFourBall M) :
    B.carrier ⊆ B.domain := by
  rintro x ⟨y, _, rfl⟩
  exact y.2

/-- The coordinate center belongs to the ball carrier. -/
theorem center_mem_carrier (B : CoordinateFourBall M) :
    (B.chart.symm 0 : M) ∈ B.carrier := by
  refine ⟨B.chart.symm 0, ?_, rfl⟩
  exact ⟨0, by simp, rfl⟩

/-- Every coordinate four-ball carrier is nonempty. -/
theorem carrier_nonempty (B : CoordinateFourBall M) : B.carrier.Nonempty :=
  ⟨B.chart.symm 0, B.center_mem_carrier⟩

/-- The carrier is compact.  This is the compact support control later used when passing between
the strict link complement and a compact exterior. -/
theorem isCompact_carrier (B : CoordinateFourBall M) : IsCompact B.carrier := by
  exact ((isCompact_closedBall (0 : FourSpace) 1).image B.chart.symm.continuous).image
    continuous_subtype_val

/-- The fixed-ball relative diffeomorphisms supported in `B`. -/
def relativeDiffSupportedIn (s : Set M) (B : CoordinateFourBall M) :
    Set (TauCeti.RelativeDiff (I := 𝓡 4) M ∞ s) :=
  SplittingSpheres.relativeDiffSupportedIn (IM := 𝓡 4) s B.carrier

/-- For a fixed coordinate ball, supported relative diffeomorphisms form a subgroup. -/
def relativeDiffSupportedInSubgroup (s : Set M) (B : CoordinateFourBall M) :
    Subgroup (TauCeti.RelativeDiff (I := 𝓡 4) M ∞ s) :=
  SplittingSpheres.relativeDiffSupportedInSubgroup (IM := 𝓡 4) s B.carrier

end CoordinateFourBall

/-- Relative diffeomorphisms supported in at least one displayed coordinate four-ball. -/
def relativeDiffSupportedInSomeCoordinateFourBall (s : Set M) :
    Set (TauCeti.RelativeDiff (I := 𝓡 4) M ∞ s) :=
  {f | ∃ B : CoordinateFourBall M, DiffeomorphSupportedIn f.1 B.carrier}

namespace DiffeomorphSupportedIn

/-- Conjugation transports a coordinate-ball support witness, including its smooth coordinate
neighborhood. -/
theorem conj_coordinateFourBall [IsManifold (𝓡 4) ∞ M]
    {f h : TauCeti.Diff (𝓡 4) M ∞} (B : CoordinateFourBall M)
    (hf : DiffeomorphSupportedIn f B.carrier) :
    DiffeomorphSupportedIn (h * f * h⁻¹) (B.transport h).carrier := by
  rw [CoordinateFourBall.carrier_transport]
  exact hf.conj

end DiffeomorphSupportedIn

/-- The collection of coordinate-ball-supported relative diffeomorphisms is invariant under
conjugation by relative diffeomorphisms. -/
theorem relativeDiffSupportedInSomeCoordinateFourBall_conj
    [IsManifold (𝓡 4) ∞ M] {s : Set M}
    {f : TauCeti.RelativeDiff (I := 𝓡 4) M ∞ s}
    (h : TauCeti.RelativeDiff (I := 𝓡 4) M ∞ s)
    (hf : f ∈ relativeDiffSupportedInSomeCoordinateFourBall s) :
    h * f * h⁻¹ ∈ relativeDiffSupportedInSomeCoordinateFourBall s := by
  obtain ⟨B, hB⟩ := hf
  exact ⟨B.transport h.1, hB.conj_coordinateFourBall B⟩

/-- Membership in the selected support collection from a fixed displayed coordinate ball. -/
theorem mem_relativeDiffSupportedInSomeCoordinateFourBall
    {s : Set M} {f : TauCeti.RelativeDiff (I := 𝓡 4) M ∞ s}
    (B : CoordinateFourBall M) (hf : DiffeomorphSupportedIn f.1 B.carrier) :
    f ∈ relativeDiffSupportedInSomeCoordinateFourBall s :=
  ⟨B, hf⟩

/-- The relative mapping-class quotient by the normal closure of all displayed coordinate-ball
supported classes. -/
abbrev RelativeMappingClassModCoordinateBall (s : Set M) :=
  RelativeMappingClassMod (IM := 𝓡 4) s
    (relativeDiffSupportedInSomeCoordinateFourBall s)

/-- Canonical class in the coordinate-ball quotient. -/
def relativeMappingClassModCoordinateBallMk (s : Set M) :
    TauCeti.RelativeDiff (I := 𝓡 4) M ∞ s →*
      RelativeMappingClassModCoordinateBall s :=
  relativeMappingClassModMk (IM := 𝓡 4) s
    (relativeDiffSupportedInSomeCoordinateFourBall s)

/-- Every relative diffeomorphism supported in a displayed coordinate ball is trivial in the
coordinate-ball quotient. -/
theorem relativeMappingClassModCoordinateBallMk_eq_one
    {s : Set M} {f : TauCeti.RelativeDiff (I := 𝓡 4) M ∞ s}
    (B : CoordinateFourBall M) (hf : DiffeomorphSupportedIn f.1 B.carrier) :
    relativeMappingClassModCoordinateBallMk s f = 1 :=
  relativeMappingClassModMk_eq_one
    (mem_relativeDiffSupportedInSomeCoordinateFourBall B hf)

/-- Products supported in one displayed coordinate ball remain trivial in the quotient. -/
theorem relativeMappingClassModCoordinateBallMk_mul_eq_one
    {s : Set M} {f g : TauCeti.RelativeDiff (I := 𝓡 4) M ∞ s}
    (B : CoordinateFourBall M)
    (hf : DiffeomorphSupportedIn f.1 B.carrier)
    (hg : DiffeomorphSupportedIn g.1 B.carrier) :
    relativeMappingClassModCoordinateBallMk s (f * g) = 1 := by
  apply relativeMappingClassModCoordinateBallMk_eq_one B
  exact DiffeomorphSupportedIn.mul hf hg

/-- Inverses of coordinate-ball-supported maps are trivial in the quotient. -/
theorem relativeMappingClassModCoordinateBallMk_inv_eq_one
    {s : Set M} {f : TauCeti.RelativeDiff (I := 𝓡 4) M ∞ s}
    (B : CoordinateFourBall M) (hf : DiffeomorphSupportedIn f.1 B.carrier) :
    relativeMappingClassModCoordinateBallMk s f⁻¹ = 1 := by
  apply relativeMappingClassModCoordinateBallMk_eq_one B
  exact DiffeomorphSupportedIn.inv hf

/-- An ordered finite product of maps, each supported in its own displayed coordinate ball, is
trivial in the normal-closure quotient.  No unproved claim that their union lies in a single ball
is needed.  A list is used because relative diffeomorphisms need not commute. -/
theorem relativeMappingClassModCoordinateBallMk_list_prod_eq_one
    {ι : Type*} {s : Set M} (A : List ι)
    (f : ι → TauCeti.RelativeDiff (I := 𝓡 4) M ∞ s)
    (B : ι → CoordinateFourBall M)
    (hf : ∀ i ∈ A, DiffeomorphSupportedIn (f i).1 (B i).carrier) :
    relativeMappingClassModCoordinateBallMk s (A.map f).prod = 1 := by
  induction A with
  | nil => simp
  | cons i A ih =>
      rw [List.map_cons, List.prod_cons, map_mul,
        relativeMappingClassModCoordinateBallMk_eq_one (B i) (hf i (by simp))]
      have htail : ∀ j ∈ A, DiffeomorphSupportedIn (f j).1 (B j).carrier := by
        intro j hj
        exact hf j (by simp [hj])
      rw [ih htail]
      exact mul_one 1

end SplittingSpheres
