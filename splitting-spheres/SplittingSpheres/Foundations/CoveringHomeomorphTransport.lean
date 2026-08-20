/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.SmoothCoverPullbackAtlas
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Conjugation

/-!
# Transporting covering projections through homeomorphisms

If `p : E → X` is a covering projection, `eE : E ≃ₜ E'`, and `eX : X ≃ₜ X'`, then
the conjugate map

`e' ↦ eX (p (eE.symm e'))`

is again a covering projection.  This file records that elementary transport together with its
exact commutative-square, composition, and deck-transformation laws.

When `X'` is a smooth manifold, the transported topological cover can be fed directly into
`SmoothCoverPullbackAtlas`.  The resulting declarations install a new charted-space structure
on `E'` locally.  In particular, none of the smooth statements below assumes a pre-existing
atlas on `E'`.
-/

@[expose] public section

noncomputable section

open scoped ContDiff Manifold

namespace SplittingSpheres

universe uE uE' uX uX'

variable {E : Type uE} {E' : Type uE'} {X : Type uX} {X' : Type uX'}
variable [TopologicalSpace E] [TopologicalSpace E']
variable [TopologicalSpace X] [TopologicalSpace X']

/-- The map obtained from `p` by changing its total and base spaces through homeomorphisms. -/
def coveringHomeomorphTransportMap
    (p : E → X) (eE : E ≃ₜ E') (eX : X ≃ₜ X') : E' → X' :=
  eX ∘ (p ∘ eE.symm)

/-- Pointwise formula for the transported projection. -/
@[simp]
theorem coveringHomeomorphTransportMap_apply
    (p : E → X) (eE : E ≃ₜ E') (eX : X ≃ₜ X') (e' : E') :
    coveringHomeomorphTransportMap p eE eX e' = eX (p (eE.symm e')) :=
  rfl

/-- The total-space homeomorphism and the base-space homeomorphism form the expected
commutative square. -/
theorem coveringHomeomorphTransportMap_comp_source
    (p : E → X) (eE : E ≃ₜ E') (eX : X ≃ₜ X') :
    coveringHomeomorphTransportMap p eE eX ∘ eE = eX ∘ p := by
  funext e
  simp

/-- Applying the inverse base homeomorphism recovers the old projection after changing the
total-space coordinate. -/
theorem target_symm_comp_coveringHomeomorphTransportMap
    (p : E → X) (eE : E ≃ₜ E') (eX : X ≃ₜ X') :
    eX.symm ∘ coveringHomeomorphTransportMap p eE eX = p ∘ eE.symm := by
  funext e'
  simp

/-- Transport through identity homeomorphisms does not change the map. -/
@[simp]
theorem coveringHomeomorphTransportMap_refl (p : E → X) :
    coveringHomeomorphTransportMap p (Homeomorph.refl E) (Homeomorph.refl X) = p := by
  rfl

/-- Successive changes of coordinates agree with transport through the composite
homeomorphisms. -/
theorem coveringHomeomorphTransportMap_trans
    {E'' X'' : Type*} [TopologicalSpace E''] [TopologicalSpace X'']
    (p : E → X) (eE : E ≃ₜ E') (eE' : E' ≃ₜ E'')
    (eX : X ≃ₜ X') (eX' : X' ≃ₜ X'') :
    coveringHomeomorphTransportMap
        (coveringHomeomorphTransportMap p eE eX) eE' eX' =
      coveringHomeomorphTransportMap p (eE.trans eE') (eX.trans eX') := by
  funext e''
  simp [coveringHomeomorphTransportMap]

/-- Transporting a map and then transporting it back recovers the original map. -/
@[simp]
theorem coveringHomeomorphTransportMap_symm
    (p : E → X) (eE : E ≃ₜ E') (eX : X ≃ₜ X') :
    coveringHomeomorphTransportMap
        (coveringHomeomorphTransportMap p eE eX) eE.symm eX.symm = p := by
  funext e
  simp [coveringHomeomorphTransportMap]

namespace IsCoveringMap

/-- A covering projection remains a covering projection after changing both its total and base
spaces through homeomorphisms. -/
theorem homeomorphTransport {p : E → X} (hp : IsCoveringMap p)
    (eE : E ≃ₜ E') (eX : X ≃ₜ X') :
    IsCoveringMap (coveringHomeomorphTransportMap p eE eX) := by
  exact (hp.comp_homeomorph eE.symm).homeomorph_comp eX

end IsCoveringMap

/-- Changing total and base coordinates preserves and reflects the covering-map property. -/
theorem isCoveringMap_coveringHomeomorphTransportMap_iff
    (p : E → X) (eE : E ≃ₜ E') (eX : X ≃ₜ X') :
    IsCoveringMap (coveringHomeomorphTransportMap p eE eX) ↔ IsCoveringMap p := by
  unfold coveringHomeomorphTransportMap
  rw [IsCoveringMap.homeomorph_comp_iff, IsCoveringMap.comp_homeomorph_iff]

/-! ## Deck transformations -/

/-- Postcomposing a projection with a base homeomorphism leaves its deck subgroup literally
unchanged as a subgroup of the homeomorphism group of the total space. -/
theorem deck_postcomp_homeomorph_eq (p : E → X) (eX : X ≃ₜ X') :
    TauCeti.Deck p = TauCeti.Deck (eX ∘ p) := by
  ext φ
  constructor
  · intro h e
    exact congrArg eX (h e)
  · intro h e
    exact eX.injective (h e)

/-- Transport of total and base coordinates identifies the two deck groups.  This is the native
Tau Ceti over-base conjugation equivalence, preceded by the exact observation that changing the
base coordinate does not change which total-space homeomorphisms preserve the projection. -/
def coveringHomeomorphTransportDeckMulEquiv
    (p : E → X) (eE : E ≃ₜ E') (eX : X ≃ₜ X') :
    TauCeti.Deck p ≃* TauCeti.Deck (coveringHomeomorphTransportMap p eE eX) :=
  (MulEquiv.subgroupCongr (deck_postcomp_homeomorph_eq p eX)).trans
    (TauCeti.Deck.conjMulEquiv eE fun e ↦ by simp)

/-- The transported deck transformation acts by conjugation with the total-space
homeomorphism. -/
@[simp]
theorem coveringHomeomorphTransportDeckMulEquiv_apply_coe
    (p : E → X) (eE : E ≃ₜ E') (eX : X ≃ₜ X')
    (φ : TauCeti.Deck p) (e' : E') :
    ((coveringHomeomorphTransportDeckMulEquiv p eE eX φ).1 e') =
      eE (φ.1 (eE.symm e')) := by
  simp [coveringHomeomorphTransportDeckMulEquiv]

/-- The inverse deck-group transport is conjugation by the inverse total-space
homeomorphism. -/
@[simp]
theorem coveringHomeomorphTransportDeckMulEquiv_symm_apply_coe
    (p : E → X) (eE : E ≃ₜ E') (eX : X ≃ₜ X')
    (ψ : TauCeti.Deck (coveringHomeomorphTransportMap p eE eX)) (e : E) :
    (((coveringHomeomorphTransportDeckMulEquiv p eE eX).symm ψ).1 e) =
      eE.symm (ψ.1 (eE e)) := by
  simp [coveringHomeomorphTransportDeckMulEquiv]

/-! ## The pullback smooth structure on the transported total space -/

universe uH

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {H : Type uH} [TopologicalSpace H]
variable [ChartedSpace H X']
variable (I : ModelWithCorners ℝ V H) (n : ℕ∞ω)

namespace IsCoveringMap

/-- The charted-space structure on `E'` pulled back along the transported covering projection.

There is intentionally no `ChartedSpace` argument or instance on `E'`: this definition creates
the atlas selected by the transported projection. -/
abbrev homeomorphTransportPullbackChartedSpace {p : E → X} (hp : IsCoveringMap p)
    (eE : E ≃ₜ E') (eX : X ≃ₜ X') : ChartedSpace H E' :=
  SplittingSpheres.IsCoveringMap.pullbackChartedSpace
    (SplittingSpheres.IsCoveringMap.homeomorphTransport hp eE eX)

/-- The transported total space is a manifold when equipped with the atlas pulled back from the
new base. -/
theorem isManifold_homeomorphTransportPullbackChartedSpace
    {p : E → X} (hp : IsCoveringMap p) (eE : E ≃ₜ E') (eX : X ≃ₜ X')
    [IsManifold I n X'] :
    letI : ChartedSpace H E' :=
      SplittingSpheres.IsCoveringMap.homeomorphTransportPullbackChartedSpace hp eE eX
    IsManifold I n E' := by
  let _ : ChartedSpace H E' :=
    SplittingSpheres.IsCoveringMap.homeomorphTransportPullbackChartedSpace hp eE eX
  exact SplittingSpheres.IsCoveringMap.isManifold_pullbackChartedSpace I n
    (SplittingSpheres.IsCoveringMap.homeomorphTransport hp eE eX)

/-- With the transported pullback atlas, the transported projection is a local
diffeomorphism. -/
theorem isLocalDiffeomorph_homeomorphTransportPullbackChartedSpace
    {p : E → X} (hp : IsCoveringMap p) (eE : E ≃ₜ E') (eX : X ≃ₜ X')
    [IsManifold I n X'] :
    letI : ChartedSpace H E' :=
      SplittingSpheres.IsCoveringMap.homeomorphTransportPullbackChartedSpace hp eE eX
    letI : IsManifold I n E' :=
      SplittingSpheres.IsCoveringMap.isManifold_homeomorphTransportPullbackChartedSpace
        I n hp eE eX
    IsLocalDiffeomorph I I n (coveringHomeomorphTransportMap p eE eX) := by
  let _ : ChartedSpace H E' :=
    SplittingSpheres.IsCoveringMap.homeomorphTransportPullbackChartedSpace hp eE eX
  let _ : IsManifold I n E' :=
    SplittingSpheres.IsCoveringMap.isManifold_homeomorphTransportPullbackChartedSpace
      I n hp eE eX
  exact SplittingSpheres.IsCoveringMap.isLocalDiffeomorph_pullbackChartedSpace I n
    (SplittingSpheres.IsCoveringMap.homeomorphTransport hp eE eX)

/-- With the transported pullback atlas, the transported projection is smooth. -/
theorem contMDiff_homeomorphTransportPullbackChartedSpace
    {p : E → X} (hp : IsCoveringMap p) (eE : E ≃ₜ E') (eX : X ≃ₜ X')
    [IsManifold I n X'] :
    letI : ChartedSpace H E' :=
      SplittingSpheres.IsCoveringMap.homeomorphTransportPullbackChartedSpace hp eE eX
    letI : IsManifold I n E' :=
      SplittingSpheres.IsCoveringMap.isManifold_homeomorphTransportPullbackChartedSpace
        I n hp eE eX
    ContMDiff I I n (coveringHomeomorphTransportMap p eE eX) := by
  let _ : ChartedSpace H E' :=
    SplittingSpheres.IsCoveringMap.homeomorphTransportPullbackChartedSpace hp eE eX
  let _ : IsManifold I n E' :=
    SplittingSpheres.IsCoveringMap.isManifold_homeomorphTransportPullbackChartedSpace
      I n hp eE eX
  exact SplittingSpheres.IsCoveringMap.contMDiff_pullbackChartedSpace I n
    (SplittingSpheres.IsCoveringMap.homeomorphTransport hp eE eX)

/-- The transported topological cover becomes a smooth cover after selecting the pullback atlas
on its new total space. -/
theorem smoothCover_homeomorphTransportPullbackChartedSpace
    {p : E → X} (hp : IsCoveringMap p) (eE : E ≃ₜ E') (eX : X ≃ₜ X')
    [IsManifold I n X'] :
    letI : ChartedSpace H E' :=
      SplittingSpheres.IsCoveringMap.homeomorphTransportPullbackChartedSpace hp eE eX
    letI : IsManifold I n E' :=
      SplittingSpheres.IsCoveringMap.isManifold_homeomorphTransportPullbackChartedSpace
        I n hp eE eX
    SmoothCover I I n (coveringHomeomorphTransportMap p eE eX) := by
  let _ : ChartedSpace H E' :=
    SplittingSpheres.IsCoveringMap.homeomorphTransportPullbackChartedSpace hp eE eX
  let _ : IsManifold I n E' :=
    SplittingSpheres.IsCoveringMap.isManifold_homeomorphTransportPullbackChartedSpace
      I n hp eE eX
  exact SplittingSpheres.IsCoveringMap.smoothCover_pullbackChartedSpace I n
    (SplittingSpheres.IsCoveringMap.homeomorphTransport hp eE eX)

end IsCoveringMap

end SplittingSpheres
