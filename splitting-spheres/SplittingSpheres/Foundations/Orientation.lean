/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orientation
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Orientation propagation prerequisites

The pinned libraries provide orientations of a single module (`Orientation` and
`Module.Oriented`), differentials of diffeomorphisms as continuous linear equivalences, and
naturality of the interior and boundary under diffeomorphisms.  They do not yet provide an
orientation of a manifold (an orientation section or an oriented-atlas compatibility condition),
an intrinsic orientation character of a manifold diffeomorphism, or an induced boundary
orientation.

Consequently, the final intrinsic assertion that a self-diffeomorphism of a connected oriented
manifold is orientation-preserving cannot yet be stated using the pinned API.  This file proves
the exact pieces that do exist:

* a locally constant value on a preconnected space is determined by one value;
* equality with the identity on an open set forces the manifold derivative to be the identity
  there;
* transport of a fixed orientation of the *model vector space* is therefore trivial there, and is
  trivial globally whenever that transport is locally constant;
* every diffeomorphism restricts to a homeomorphism of manifold boundaries.

The remaining named bridge is a manifold-orientation structure together with local constancy of
the induced orientation transport.  Boundary-orientation naturality additionally needs a
definition relating ambient, outward-normal, and boundary orientations.  None of those missing
objects is assumed here.
-/

@[expose] public section

open Filter Function Set
open scoped Manifold Topology

noncomputable section

namespace SplittingSpheres

section LocallyConstant

variable {X A : Type*} [TopologicalSpace X]

/-- On a preconnected space, one witnessed value of a locally constant function determines all
of its values.  This is the connectedness step needed after constructing an orientation
character. -/
theorem locallyConstant_eq_everywhere_of_exists_eq [PreconnectedSpace X]
    {sigma : X → A} {a : A} (hsigma : IsLocallyConstant sigma)
    (h : ∃ x, sigma x = a) : ∀ x, sigma x = a := by
  obtain ⟨x, hx⟩ := h
  intro y
  exact (hsigma.apply_eq_of_preconnectedSpace y x).trans hx

/-- A locally constant function on a preconnected space which has a prescribed value on a
nonempty set has that value everywhere. -/
theorem locallyConstant_eq_everywhere_of_eqOn_nonempty [PreconnectedSpace X]
    {sigma : X → A} {a : A} {U : Set X} (hsigma : IsLocallyConstant sigma)
    (hU : U.Nonempty) (hsigmaU : ∀ x ∈ U, sigma x = a) : ∀ x, sigma x = a := by
  apply locallyConstant_eq_everywhere_of_exists_eq hsigma
  obtain ⟨x, hx⟩ := hU
  exact ⟨x, hsigmaU x hx⟩

end LocallyConstant

section IdentityGerm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M]

/-- If a map agrees with the identity on an open neighbourhood of `x`, then its manifold
derivative at `x` is the identity.  No differentiability hypothesis is needed: manifold
derivatives depend only on the germ, and the identity is differentiable. -/
theorem mfderiv_eq_id_of_eqOn_open {f : M → M} {U : Set M}
    (hU : IsOpen U) (hf : Set.EqOn f id U) {x : M} (hx : x ∈ U) :
    mfderiv I I f x = ContinuousLinearMap.id ℝ E := by
  have hfgerm : f =ᶠ[𝓝 x] id := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hf hy
  rw [hfgerm.mfderiv_eq]
  exact mfderiv_id

end IdentityGerm

section ModelOrientation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞} {index : Type*}

set_option backward.isDefEq.respectTransparency false in
/-- The differential of a self-diffeomorphism, regarded as a linear equivalence of the fixed model
vector space.  This wrapper makes explicit Mathlib's underlying identification
`TangentSpace I x = E`. -/
def modelDifferentialLinearEquiv (Phi : M ≃ₘ^n⟮I, I⟯ M) (hn : n ≠ 0) (x : M) :
    E ≃ₗ[ℝ] E :=
  LinearEquiv.ofBijective (mfderiv I I (Phi : M → M) x).toLinearMap (by
    rw [← Phi.mfderivToContinuousLinearEquiv_coe hn]
    exact (Phi.mfderivToContinuousLinearEquiv hn x).bijective)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem modelDifferentialLinearEquiv_apply
    (Phi : M ≃ₘ^n⟮I, I⟯ M) (hn : n ≠ 0) (x : M) (v : E) :
    modelDifferentialLinearEquiv Phi hn x v = mfderiv I I (Phi : M → M) x v :=
  rfl

/-- The result of transporting an orientation of the fixed model vector space by the differential
of a self-diffeomorphism at one point.

This is intentionally named `modelOrientationTransport`: without an oriented-atlas compatibility
condition, it is not an intrinsic orientation transport on the manifold. -/
def modelOrientationTransport (Phi : M ≃ₘ^n⟮I, I⟯ M) (hn : n ≠ 0)
    (o : Orientation ℝ E index) (x : M) : Orientation ℝ E index :=
  Orientation.map index (modelDifferentialLinearEquiv Phi hn x) o

set_option backward.isDefEq.respectTransparency false in
/-- Agreement with the identity on an open set makes model-orientation transport trivial at each
point of that set. -/
theorem modelOrientationTransport_eq_of_eqOn_open
    (Phi : M ≃ₘ^n⟮I, I⟯ M) (hn : n ≠ 0) (o : Orientation ℝ E index)
    {U : Set M} (hU : IsOpen U) (hPhi : Set.EqOn Phi id U)
    {x : M} (hx : x ∈ U) : modelOrientationTransport Phi hn o x = o := by
  have hderiv : mfderiv I I (Phi : M → M) x = ContinuousLinearMap.id ℝ E :=
    mfderiv_eq_id_of_eqOn_open I hU hPhi hx
  have hequiv : modelDifferentialLinearEquiv Phi hn x = LinearEquiv.refl ℝ E := by
    ext v
    rw [modelDifferentialLinearEquiv_apply, hderiv]
    rfl
  change Orientation.map index (modelDifferentialLinearEquiv Phi hn x) o = o
  rw [hequiv]
  exact DFunLike.congr_fun (Orientation.map_refl (R := ℝ) (M := E) index) o

/-- Conditional orientation propagation in the exact form supported by the pinned API.

Once a genuine manifold-orientation API supplies local constancy of the induced transport, this
theorem turns identity on a nonempty open set into global preservation on a preconnected
manifold. -/
theorem modelOrientationTransport_eq_everywhere_of_isLocallyConstant_of_eqOn_open
    [PreconnectedSpace M] (Phi : M ≃ₘ^n⟮I, I⟯ M) (hn : n ≠ 0)
    (o : Orientation ℝ E index)
    (hlocal : IsLocallyConstant (modelOrientationTransport Phi hn o))
    {U : Set M} (hU : IsOpen U) (hUne : U.Nonempty)
    (hPhi : Set.EqOn Phi id U) : ∀ x, modelOrientationTransport Phi hn o x = o := by
  apply locallyConstant_eq_everywhere_of_eqOn_nonempty hlocal hUne
  intro x hx
  exact modelOrientationTransport_eq_of_eqOn_open Phi hn o hU hPhi hx

end ModelOrientation

section BoundaryNaturality

variable {k E E' H H' M N : Type*}
  [NontriviallyNormedField k]
  [NormedAddCommGroup E] [NormedSpace k E]
  [NormedAddCommGroup E'] [NormedSpace k E']
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners k E H} {I' : ModelWithCorners k E' H'}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]
  {n : WithTop ℕ∞}

/-- A diffeomorphism restricts canonically to a homeomorphism of the boundary subtypes.  This is
the boundary naturality currently available; the pinned libraries do not equip these boundary
subtypes with induced orientations. -/
def diffeomorphBoundaryHomeomorph (Phi : M ≃ₘ^n⟮I, I'⟯ N) (hn : n ≠ 0) :
    ↥(I.boundary M) ≃ₜ ↥(I'.boundary N) :=
  Phi.toHomeomorph.sets (Phi.preimage_boundary hn).symm

@[simp]
theorem diffeomorphBoundaryHomeomorph_apply_val
    (Phi : M ≃ₘ^n⟮I, I'⟯ N) (hn : n ≠ 0) (x : ↥(I.boundary M)) :
    ((diffeomorphBoundaryHomeomorph Phi hn x : ↥(I'.boundary N)) : N) = Phi x :=
  rfl

@[simp]
theorem diffeomorphBoundaryHomeomorph_symm_apply_val
    (Phi : M ≃ₘ^n⟮I, I'⟯ N) (hn : n ≠ 0) (y : ↥(I'.boundary N)) :
    (((diffeomorphBoundaryHomeomorph Phi hn).symm y : ↥(I.boundary M)) : M) = Phi.symm y :=
  rfl

end BoundaryNaturality

end SplittingSpheres
