/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.CoordinateBallSupport

/-!
# Transporting coordinate four-balls through open diffeomorphisms

A coordinate four-ball only needs an open coordinate neighborhood.  Consequently it can be
transported through a diffeomorphism between open submanifolds; no global ambient diffeomorphism
is required.  This file constructs the target open domain, the restricted diffeomorphism, and the
transported chart, and computes the carrier as an exact image.
-/

@[expose] public section

noncomputable section

open Function Set
open TopologicalSpace
open scoped ContDiff Manifold Topology

namespace SplittingSpheres

universe uM uN

variable {M : Type uM} {N : Type uN}
  [TopologicalSpace M] [ChartedSpace FourSpace M]
  [TopologicalSpace N] [ChartedSpace FourSpace N]

namespace CoordinateFourBall

variable {U : Opens M} {V : Opens N}

/-- The ambient target point obtained by applying an open-submanifold diffeomorphism to a point
of a coordinate-ball domain contained in its source. -/
def openTransportMap (e : U ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ V)
    (B : CoordinateFourBall M) (hBU : B.domain ≤ U) : B.domain → N :=
  fun x ↦ (e ⟨x.1, hBU x.2⟩).1

theorem openTransportMap_injective
    (e : U ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ V)
    (B : CoordinateFourBall M) (hBU : B.domain ≤ U) :
    Injective (openTransportMap e B hBU) := by
  intro x y hxy
  apply Subtype.ext
  have he : e ⟨x.1, hBU x.2⟩ = e ⟨y.1, hBU y.2⟩ :=
    Subtype.ext hxy
  exact congrArg (fun z : U ↦ z.1) (e.injective he)

/-- The image of the coordinate-ball's open domain in the ambient target manifold. -/
def openTransportDomain (e : U ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ V)
    (B : CoordinateFourBall M) (hBU : B.domain ≤ U) : Opens N := by
  refine ⟨range (openTransportMap e B hBU), ?_⟩
  have hsource : IsOpenMap (fun x : B.domain ↦ (⟨x.1, hBU x.2⟩ : U)) :=
    B.domain.2.isOpenMap_subtype_val.codRestrict fun x ↦ hBU x.2
  have hopen : IsOpenMap (openTransportMap e B hBU) := by
    exact V.2.isOpenMap_subtype_val.comp (e.toHomeomorph.isOpenMap.comp hsource)
  simpa only [image_univ] using hopen univ isOpen_univ

@[simp]
theorem mem_openTransportDomain
    (e : U ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ V)
    (B : CoordinateFourBall M) (hBU : B.domain ≤ U) {y : N} :
    y ∈ openTransportDomain e B hBU ↔
      ∃ x : B.domain, openTransportMap e B hBU x = y :=
  Iff.rfl

/-- Every point of the transported open domain lies in the ambient target open set. -/
theorem openTransportDomain_subset_target
    (e : U ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ V)
    (B : CoordinateFourBall M) (hBU : B.domain ≤ U) :
    (openTransportDomain e B hBU : Set N) ⊆ V := by
  rintro y ⟨x, rfl⟩
  exact (e ⟨x.1, hBU x.2⟩).2

/-- Regard a transported-domain point as a point of the target open submanifold. -/
def openTransportTargetPoint
    (e : U ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ V)
    (B : CoordinateFourBall M) (hBU : B.domain ≤ U)
    (y : openTransportDomain e B hBU) : V :=
  ⟨y.1, openTransportDomain_subset_target e B hBU y.2⟩

/-- Pull a transported-domain point back to the original coordinate-ball domain. -/
def openTransportInverse
    (e : U ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ V)
    (B : CoordinateFourBall M) (hBU : B.domain ≤ U)
    (y : openTransportDomain e B hBU) : B.domain := by
  let z : U := e.symm (openTransportTargetPoint e B hBU y)
  refine ⟨z.1, ?_⟩
  rcases y.2 with ⟨x, hx⟩
  have hy : openTransportTargetPoint e B hBU y = e ⟨x.1, hBU x.2⟩ := by
    apply Subtype.ext
    exact hx.symm
  have hz : z = ⟨x.1, hBU x.2⟩ := by
    rw [show z = e.symm (openTransportTargetPoint e B hBU y) from rfl,
      hy, e.symm_apply_apply]
  rw [show z.1 = x.1 from congrArg Subtype.val hz]
  exact x.2

/-- The original coordinate-ball domain is diffeomorphic to its image under the open
submanifold diffeomorphism. -/
def openTransportDiffeomorph
    (e : U ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ V)
    (B : CoordinateFourBall M) (hBU : B.domain ≤ U) :
    B.domain ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ openTransportDomain e B hBU where
  toEquiv :=
    { toFun := fun x ↦ ⟨openTransportMap e B hBU x, ⟨x, rfl⟩⟩
      invFun := openTransportInverse e B hBU
      left_inv := by
        intro x
        apply Subtype.ext
        change (e.symm (e ⟨x.1, hBU x.2⟩)).1 = x.1
        rw [e.symm_apply_apply]
      right_inv := by
        intro y
        apply Subtype.ext
        change (e (e.symm (openTransportTargetPoint e B hBU y))).1 = y.1
        rw [e.apply_symm_apply]
        rfl }
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (openTransportDomain e B hBU) _).mp
    have hsource : ContMDiff (𝓡 4) (𝓡 4) ∞
        (fun x : B.domain ↦ (⟨x.1, hBU x.2⟩ : U)) := by
      apply (ContMDiff.subtypeVal_comp_iff U _).mp
      exact contMDiff_subtype_val
    exact (contMDiff_subtype_val.comp (e.contMDiff.comp hsource)).congr fun _ ↦ rfl
  contMDiff_invFun := by
    have htarget : ContMDiff (𝓡 4) (𝓡 4) ∞
        (openTransportTargetPoint e B hBU) := by
      apply (ContMDiff.subtypeVal_comp_iff V _).mp
      exact contMDiff_subtype_val
    apply (ContMDiff.subtypeVal_comp_iff B.domain _).mp
    exact (contMDiff_subtype_val.comp (e.symm.contMDiff.comp htarget)).congr fun _ ↦ rfl

@[simp]
theorem openTransportDiffeomorph_apply
    (e : U ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ V)
    (B : CoordinateFourBall M) (hBU : B.domain ≤ U) (x : B.domain) :
    (openTransportDiffeomorph e B hBU x).1 = openTransportMap e B hBU x :=
  rfl

/-- Transport coordinate-ball data through a diffeomorphism of open submanifolds. -/
def openTransport
    (e : U ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ V)
    (B : CoordinateFourBall M) (hBU : B.domain ≤ U) :
    CoordinateFourBall N where
  domain := openTransportDomain e B hBU
  chart := (openTransportDiffeomorph e B hBU).symm.trans B.chart

/-- The transported carrier is the exact image of the old carrier under the restricted open
diffeomorphism. -/
theorem carrier_openTransport
    (e : U ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ V)
    (B : CoordinateFourBall M) (hBU : B.domain ≤ U) :
    (B.openTransport e hBU).carrier =
      openTransportMap e B hBU '' (Subtype.val ⁻¹' B.carrier) := by
  ext y
  constructor
  · rintro ⟨z, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨B.chart.symm v, ?_, rfl⟩
    exact ⟨B.chart.symm v, ⟨v, hv, rfl⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨z, ⟨v, hv, rfl⟩, hz⟩
    have hxz : x = B.chart.symm v := Subtype.ext hz.symm
    subst x
    refine ⟨openTransportDiffeomorph e B hBU (B.chart.symm v), ?_, rfl⟩
    exact ⟨v, hv, rfl⟩

end CoordinateFourBall

end SplittingSpheres
