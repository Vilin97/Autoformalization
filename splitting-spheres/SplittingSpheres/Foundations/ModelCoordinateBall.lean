/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SplittingSpheres.Foundations.CoordinateBallSupport

/-!
# Model-parametric displayed coordinate four-balls

The original `CoordinateFourBall M` is deliberately specialized to manifolds whose ambient model
is `𝓡 4`.  A manifold with boundary generally has a different model with corners even though an
open coordinate neighborhood contained in its interior can be diffeomorphic to `ℝ⁴`.

`ModelCoordinateFourBall IM M` records exactly that situation: its domain inherits the ambient
model `IM`, while its displayed chart lands in `FourSpace`.  Such data transports through a
diffeomorphism between arbitrary open submanifolds, with the target retaining its own model.
When the ambient model is already `𝓡 4`, the data converts definitionally to the original
`CoordinateFourBall` API.
-/

@[expose] public section

noncomputable section

open Function Metric Set
open TopologicalSpace
open scoped ContDiff Manifold Topology

namespace SplittingSpheres

universe uE uF uH uK uM uN

/-- A displayed smooth four-ball in a manifold with arbitrary ambient model `IM`.

The open domain uses the inherited ambient manifold structure, while `chart` identifies that
domain smoothly with the standard Euclidean four-space. -/
structure ModelCoordinateFourBall
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H]
    (IM : ModelWithCorners ℝ E H)
    (M : Type uM) [TopologicalSpace M] [ChartedSpace H M] where
  /-- Open coordinate neighborhood containing the displayed closed ball. -/
  domain : Opens M
  /-- Global Euclidean coordinates on that neighborhood. -/
  chart : domain ≃ₘ^∞⟮IM, 𝓡 4⟯ FourSpace

namespace ModelCoordinateFourBall

section Basic

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H]
  {IM : ModelWithCorners ℝ E H}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]

/-- The closed-ball carrier, pulled back from the standard Euclidean closed unit ball and then
included into the ambient manifold. -/
def carrier (B : ModelCoordinateFourBall IM M) : Set M :=
  Subtype.val '' (B.chart.symm '' closedBall (0 : FourSpace) 1)

/-- The displayed carrier lies in its open coordinate domain. -/
theorem carrier_subset_domain (B : ModelCoordinateFourBall IM M) :
    B.carrier ⊆ B.domain := by
  rintro x ⟨y, _, rfl⟩
  exact y.2

/-- The coordinate center belongs to the displayed carrier. -/
theorem center_mem_carrier (B : ModelCoordinateFourBall IM M) :
    (B.chart.symm 0 : M) ∈ B.carrier := by
  refine ⟨B.chart.symm 0, ?_, rfl⟩
  exact ⟨0, by simp, rfl⟩

/-- Every displayed model-coordinate four-ball has nonempty carrier. -/
theorem carrier_nonempty (B : ModelCoordinateFourBall IM M) : B.carrier.Nonempty :=
  ⟨B.chart.symm 0, B.center_mem_carrier⟩

/-- The displayed carrier is compact in the ambient manifold. -/
theorem isCompact_carrier (B : ModelCoordinateFourBall IM M) : IsCompact B.carrier := by
  exact ((isCompact_closedBall (0 : FourSpace) 1).image B.chart.symm.continuous).image
    continuous_subtype_val

/-- Relative diffeomorphisms supported in one fixed model-coordinate four-ball. -/
def relativeDiffSupportedIn (s : Set M) (B : ModelCoordinateFourBall IM M) :
    Set (TauCeti.RelativeDiff (I := IM) M ∞ s) :=
  SplittingSpheres.relativeDiffSupportedIn (IM := IM) s B.carrier

/-- Relative diffeomorphisms supported in one fixed model-coordinate ball form a subgroup. -/
def relativeDiffSupportedInSubgroup (s : Set M) (B : ModelCoordinateFourBall IM M) :
    Subgroup (TauCeti.RelativeDiff (I := IM) M ∞ s) :=
  SplittingSpheres.relativeDiffSupportedInSubgroup (IM := IM) s B.carrier

end Basic

section OpenTransport

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type uH} [TopologicalSpace H]
  {K : Type uK} [TopologicalSpace K]
  {IM : ModelWithCorners ℝ E H} {IN : ModelWithCorners ℝ F K}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace K N]
  {U : Opens M} {V : Opens N}

/-- The ambient target point obtained by applying an open-submanifold diffeomorphism to a point
of a displayed ball domain contained in its source. -/
def openTransportMap (e : U ≃ₘ^∞⟮IM, IN⟯ V)
    (B : ModelCoordinateFourBall IM M) (hBU : B.domain ≤ U) : B.domain → N :=
  fun x ↦ (e ⟨x.1, hBU x.2⟩).1

/-- The model-parametric open transport map is injective. -/
theorem openTransportMap_injective
    (e : U ≃ₘ^∞⟮IM, IN⟯ V)
    (B : ModelCoordinateFourBall IM M) (hBU : B.domain ≤ U) :
    Injective (openTransportMap e B hBU) := by
  intro x y hxy
  apply Subtype.ext
  have he : e ⟨x.1, hBU x.2⟩ = e ⟨y.1, hBU y.2⟩ :=
    Subtype.ext hxy
  exact congrArg (fun z : U ↦ z.1) (e.injective he)

/-- The image of the displayed ball's open domain in the ambient target manifold. -/
def openTransportDomain (e : U ≃ₘ^∞⟮IM, IN⟯ V)
    (B : ModelCoordinateFourBall IM M) (hBU : B.domain ≤ U) : Opens N := by
  refine ⟨range (openTransportMap e B hBU), ?_⟩
  have hsource : IsOpenMap (fun x : B.domain ↦ (⟨x.1, hBU x.2⟩ : U)) :=
    B.domain.2.isOpenMap_subtype_val.codRestrict fun x ↦ hBU x.2
  have hopen : IsOpenMap (openTransportMap e B hBU) := by
    exact V.2.isOpenMap_subtype_val.comp (e.toHomeomorph.isOpenMap.comp hsource)
  simpa only [image_univ] using hopen univ isOpen_univ

@[simp]
theorem mem_openTransportDomain
    (e : U ≃ₘ^∞⟮IM, IN⟯ V)
    (B : ModelCoordinateFourBall IM M) (hBU : B.domain ≤ U) {y : N} :
    y ∈ openTransportDomain e B hBU ↔
      ∃ x : B.domain, openTransportMap e B hBU x = y :=
  Iff.rfl

/-- Every point of the transported domain lies in the ambient target open set. -/
theorem openTransportDomain_subset_target
    (e : U ≃ₘ^∞⟮IM, IN⟯ V)
    (B : ModelCoordinateFourBall IM M) (hBU : B.domain ≤ U) :
    (openTransportDomain e B hBU : Set N) ⊆ V := by
  rintro y ⟨x, rfl⟩
  exact (e ⟨x.1, hBU x.2⟩).2

/-- Regard a transported-domain point as a point of the target open submanifold. -/
def openTransportTargetPoint
    (e : U ≃ₘ^∞⟮IM, IN⟯ V)
    (B : ModelCoordinateFourBall IM M) (hBU : B.domain ≤ U)
    (y : openTransportDomain e B hBU) : V :=
  ⟨y.1, openTransportDomain_subset_target e B hBU y.2⟩

/-- Pull a transported-domain point back to the original displayed ball domain. -/
def openTransportInverse
    (e : U ≃ₘ^∞⟮IM, IN⟯ V)
    (B : ModelCoordinateFourBall IM M) (hBU : B.domain ≤ U)
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

/-- The original displayed ball domain is diffeomorphic, with its actual ambient model, to its
image carrying the target ambient model. -/
def openTransportDiffeomorph
    (e : U ≃ₘ^∞⟮IM, IN⟯ V)
    (B : ModelCoordinateFourBall IM M) (hBU : B.domain ≤ U) :
    B.domain ≃ₘ^∞⟮IM, IN⟯ openTransportDomain e B hBU where
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
    have hsource : ContMDiff IM IM ∞
        (fun x : B.domain ↦ (⟨x.1, hBU x.2⟩ : U)) := by
      apply (ContMDiff.subtypeVal_comp_iff U _).mp
      exact contMDiff_subtype_val
    exact (contMDiff_subtype_val.comp (e.contMDiff.comp hsource)).congr fun _ ↦ rfl
  contMDiff_invFun := by
    have htarget : ContMDiff IN IN ∞
        (openTransportTargetPoint e B hBU) := by
      apply (ContMDiff.subtypeVal_comp_iff V _).mp
      exact contMDiff_subtype_val
    apply (ContMDiff.subtypeVal_comp_iff B.domain _).mp
    exact (contMDiff_subtype_val.comp (e.symm.contMDiff.comp htarget)).congr fun _ ↦ rfl

@[simp]
theorem openTransportDiffeomorph_apply
    (e : U ≃ₘ^∞⟮IM, IN⟯ V)
    (B : ModelCoordinateFourBall IM M) (hBU : B.domain ≤ U) (x : B.domain) :
    (openTransportDiffeomorph e B hBU x).1 = openTransportMap e B hBU x :=
  rfl

/-- Transport displayed coordinate-ball data through a diffeomorphism of arbitrary open
submanifolds. -/
def openTransport
    (B : ModelCoordinateFourBall IM M) (e : U ≃ₘ^∞⟮IM, IN⟯ V)
    (hBU : B.domain ≤ U) : ModelCoordinateFourBall IN N where
  domain := openTransportDomain e B hBU
  chart := (openTransportDiffeomorph e B hBU).symm.trans B.chart

/-- The transported carrier is exactly the image of the old carrier under the restricted open
diffeomorphism. -/
theorem carrier_openTransport
    (B : ModelCoordinateFourBall IM M) (e : U ≃ₘ^∞⟮IM, IN⟯ V)
    (hBU : B.domain ≤ U) :
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

end OpenTransport

section StandardModel

variable {M : Type uM} [TopologicalSpace M] [ChartedSpace FourSpace M]

/-- Forget the model-parametric wrapper when the ambient model is already standard Euclidean
four-space. -/
def toCoordinateFourBall (B : ModelCoordinateFourBall (𝓡 4) M) :
    CoordinateFourBall M where
  domain := B.domain
  chart := B.chart

@[simp]
theorem toCoordinateFourBall_domain (B : ModelCoordinateFourBall (𝓡 4) M) :
    B.toCoordinateFourBall.domain = B.domain :=
  rfl

@[simp]
theorem toCoordinateFourBall_chart (B : ModelCoordinateFourBall (𝓡 4) M) :
    B.toCoordinateFourBall.chart = B.chart :=
  rfl

/-- Specialization to the standard model preserves the carrier exactly. -/
@[simp]
theorem carrier_toCoordinateFourBall (B : ModelCoordinateFourBall (𝓡 4) M) :
    B.toCoordinateFourBall.carrier = B.carrier :=
  rfl

/-- Regard an existing standard coordinate four-ball as model-parametric data. -/
def ofCoordinateFourBall (B : CoordinateFourBall M) :
    ModelCoordinateFourBall (𝓡 4) M where
  domain := B.domain
  chart := B.chart

@[simp]
theorem carrier_ofCoordinateFourBall (B : CoordinateFourBall M) :
    (ofCoordinateFourBall B).carrier = B.carrier :=
  rfl

@[simp]
theorem toCoordinateFourBall_ofCoordinateFourBall (B : CoordinateFourBall M) :
    (ofCoordinateFourBall B).toCoordinateFourBall = B :=
  rfl

@[simp]
theorem ofCoordinateFourBall_toCoordinateFourBall
    (B : ModelCoordinateFourBall (𝓡 4) M) :
    ofCoordinateFourBall B.toCoordinateFourBall = B :=
  rfl

end StandardModel

end ModelCoordinateFourBall

/-- Relative diffeomorphisms supported in at least one displayed ball for the specified ambient
model. -/
def relativeDiffSupportedInSomeModelCoordinateFourBall
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H]
    (IM : ModelWithCorners ℝ E H)
    (M : Type uM) [TopologicalSpace M] [ChartedSpace H M]
    (s : Set M) : Set (TauCeti.RelativeDiff (I := IM) M ∞ s) :=
  {f | ∃ B : ModelCoordinateFourBall IM M,
    DiffeomorphSupportedIn f.1 B.carrier}

/-- Exhibit membership in the collection supported in some model-coordinate four-ball. -/
theorem mem_relativeDiffSupportedInSomeModelCoordinateFourBall
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H]
    {IM : ModelWithCorners ℝ E H}
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
    {s : Set M} {f : TauCeti.RelativeDiff (I := IM) M ∞ s}
    (B : ModelCoordinateFourBall IM M)
    (hf : DiffeomorphSupportedIn f.1 B.carrier) :
    f ∈ relativeDiffSupportedInSomeModelCoordinateFourBall IM M s :=
  ⟨B, hf⟩

end SplittingSpheres
