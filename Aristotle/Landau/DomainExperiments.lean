/-
  Domain experiments for the VML steady-state formalization.

  Goal: explore alternatives to the abstract FlatTorus3 typeclass that
  minimize axioms by leveraging Mathlib's existing theory.

  Current FlatTorus3 has 16 axioms. This file tests how many we can
  eliminate with concrete or semi-concrete domain choices.
-/
import Mathlib

open MeasureTheory Matrix Finset BigOperators Real Filter

noncomputable section

-- ============================================================================
-- EXPERIMENT 1: Periodic functions on ℝ³
--
-- Domain: (Fin 3 → ℝ) with periodic functions, integrate over unit cube.
-- Idea: avoid manifold machinery, use standard fderiv.
-- ============================================================================

namespace PeriodicR3

/-- A function on ℝ³ is periodic with period 1 in each coordinate. -/
def IsPeriodic (f : (Fin 3 → ℝ) → ℝ) : Prop :=
  ∀ (x : Fin 3 → ℝ) (i : Fin 3), f (x + Pi.single i 1) = f x

/-- The unit cube [0,1]³ as a set. -/
def unitCube : Set (Fin 3 → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc 0 1)

/-- Integration over the unit cube. -/
def cubeIntegral (f : (Fin 3 → ℝ) → ℝ) : ℝ :=
  ∫ x in unitCube, f x

-- Test: is the unit cube compact?
example : IsCompact unitCube := isCompact_univ_pi (fun _ => isCompact_Icc)

-- Test: can we use fderiv directly for the gradient?
def gradR3 (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => fderiv ℝ f x (Pi.single i 1)

def divR3 (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (x : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ (fun w => F w i) x (Pi.single i 1)

-- Problem: IBP on the unit cube would have boundary terms!
-- For periodic functions, the boundary terms cancel:
--   ∫_{∂[0,1]³} φ·ψ·n = 0  because opposite faces contribute with opposite
--   signs and periodicity makes the values equal.
-- But formalizing this in Lean requires:
-- 1. Set integral over boundary of cube
-- 2. Periodicity matching on opposite faces
-- 3. This is doable but tedious.

-- VERDICT: Workable but requires significant boundary-matching formalization.
-- The integration-over-cube theory in Mathlib is limited to box integrals
-- (Henstock-Kurzweil style), not Bochner integrals on subsets.

end PeriodicR3

-- ============================================================================
-- EXPERIMENT 2: AddCircle product (concrete torus)
--
-- Domain: AddCircle T × AddCircle T × AddCircle T
-- Mathlib provides: CompactSpace, T2Space, MeasureSpace, IsManifold.
-- ============================================================================

namespace TorusDomain

-- The 3-torus with period 1 in each direction
abbrev Torus3 := AddCircle (1 : ℝ) × AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

-- Basic instances come for free:
example : CompactSpace Torus3 := inferInstance
example : T2Space Torus3 := inferInstance
example : MeasureSpace Torus3 := inferInstance
example : TopologicalSpace Torus3 := inferInstance

-- Finite measure (compact + Haar):
example : IsFiniteMeasure (volume : Measure Torus3) := inferInstance

-- SigmaFinite (from IsFiniteMeasure):
example : SigmaFinite (volume : Measure Torus3) := inferInstance

-- This means Fubini works! For spatial × velocity integration:
-- integral_integral_swap would apply if we can show joint integrability.

-- PROBLEM: How to define gradient, divergence, curl?
-- AddCircle is a quotient group, so functions on it are periodic functions on ℝ.
-- We'd need to:
-- 1. Lift functions to ℝ³ via the quotient map
-- 2. Take fderiv on ℝ³
-- 3. Show the result descends back to the torus
--
-- The manifold derivative (mfderiv) should work, but AddCircle's
-- manifold structure uses charted spaces with local charts.

-- Let's check what manifold structure is available:
-- AddCircle has IsManifold (modelWithCornersSelf ℝ ℝ) (AddCircle p)
-- when p ≠ 0 (it's a 1-dimensional manifold modeled on ℝ)

-- For Torus3 = AddCircle × AddCircle × AddCircle, we'd use:
-- IsManifold (I₁.prod I₂) (M₁ × M₂) for products

-- But mfderiv returns TangentSpace → TangentSpace, which is more abstract
-- than what we need (simple partial derivatives in coordinate directions).

-- Let's try a different approach: use the quotient map.

/-- The quotient map ℝ → AddCircle 1. -/
def toCircle : ℝ → AddCircle (1 : ℝ) := QuotientAddGroup.mk

/-- The product quotient map ℝ³ → T³. -/
def toTorus (x : Fin 3 → ℝ) : Torus3 :=
  (toCircle (x 0), toCircle (x 1), toCircle (x 2))

-- A "smooth function on the torus" is a periodic smooth function on ℝ³.
-- We could define:

/-- A function on T³ can be lifted to a periodic function on ℝ³. -/
class HasPeriodicLift (f : Torus3 → ℝ) where
  lift : (Fin 3 → ℝ) → ℝ
  periodic : ∀ x i, lift (x + Pi.single i 1) = lift x
  compat : ∀ x, f (toTorus x) = lift x

-- Then gradX would be defined via fderiv of the lift.
-- This works but every function needs a HasPeriodicLift instance,
-- which is bookkeeping overhead.

-- VERDICT: Concrete and principled, but requires significant infrastructure
-- to connect torus functions ↔ periodic functions ↔ fderiv.
-- The manifold approach (mfderiv) would be cleaner but needs more Mathlib glue.

end TorusDomain

-- ============================================================================
-- EXPERIMENT 3: Fin 3 → AddCircle (pointwise product torus)
--
-- Potentially cleaner than nested products.
-- ============================================================================

namespace PointwiseTorus

abbrev Torus3' := Fin 3 → AddCircle (1 : ℝ)

-- Basic instances:
example : CompactSpace Torus3' := inferInstance
example : T2Space Torus3' := inferInstance
example : TopologicalSpace Torus3' := inferInstance

-- MeasureSpace via product measure:
example : MeasureSpace Torus3' := inferInstance

-- IsFiniteMeasure?
-- For Pi types, we need MeasureTheory.Measure.pi which gives product measure.
-- On compact spaces with finite measures on each factor, the product is finite.
example : IsFiniteMeasure (volume : Measure Torus3') := inferInstance

-- SigmaFinite:
example : SigmaFinite (volume : Measure Torus3') := inferInstance

-- Great! All the measure theory instances we need are available.

-- Now: can we define the gradient?
-- The quotient map: (Fin 3 → ℝ) → (Fin 3 → AddCircle 1)
def toTorus' (x : Fin 3 → ℝ) : Torus3' :=
  fun i => QuotientAddGroup.mk (x i)

-- For functions f : Torus3' → ℝ, we can try to compose with toTorus'
-- and differentiate the composite:

-- Gradient via pullback to ℝ³. For f : T³ → ℝ, define
-- (grad f)(x) = fderiv of (f ∘ toTorus') at any lift of x.
-- This is well-defined because f ∘ toTorus' is periodic.

-- PROBLEM: fderiv (f ∘ toTorus') requires differentiability of toTorus'.
-- But toTorus' = QuotientAddGroup.mk on each coordinate, which is
-- continuous but may not be differentiable in the Fréchet sense
-- (it's a quotient map, not a linear map).

-- Actually, QuotientAddGroup.mk : ℝ → ℝ/ℤ is a smooth covering map.
-- It should be smooth. Let's check:

-- The key issue: `AddCircle p` uses the quotient topology,
-- and the manifold structure is via local sections of the projection.
-- Differentiating requires working in charts.

-- VERDICT: Same issues as Experiment 2, but with cleaner type for the domain.
-- The `Fin 3 → AddCircle 1` type is nicer than nested products.

end PointwiseTorus

-- ============================================================================
-- EXPERIMENT 4: Keep abstract operators, add topological structure
--
-- Idea: FlatTorus3 extends MeasureSpace X, and we require
-- [CompactSpace X] [T2Space X] at the use sites.
-- This lets us use Mathlib's integral_add, Fubini, etc.
-- ============================================================================

namespace EnrichedAbstract

-- What axioms could we eliminate if X is compact?

-- (a) hSpatialAdd: ∫(f+g) = ∫f + ∫g
-- With CompactSpace + T2Space + IsFiniteMeasure:
-- We need `Integrable f` and `Integrable g`.
-- On a compact space, continuous functions are integrable
-- (ContinuousOn.integrableOn_compact). But our functions
-- (like gradX outputs) might not be continuous without further axioms.
-- If we assume "all relevant functions are integrable" or
-- "gradX produces continuous functions", we can drop this axiom.

-- (b) hSpatialVelocityFubini: ∫_X ∫_v F x v = ∫_v ∫_X F x v
-- With SigmaFinite (from CompactSpace + IsFiniteMeasure):
-- Mathlib's integral_integral_swap requires joint Integrable (uncurry F).
-- This is a stronger condition than our current axiom (which only needs
-- pointwise integrability ∀ x, Integrable (F x)).
-- We'd need to add joint integrability as a hypothesis, but can drop the axiom.

-- (c) hSpatialPos: (∀ x, 0 < g x) → 0 < ∫ g
-- This needs the measure to be "full" (give positive mass to all open sets).
-- On a compact group with Haar measure, this holds.
-- Mathlib has: integral_pos_of_pos_of_support? Let's check...
-- We'd need: `∫ x, g x > 0` when `g > 0` and measure is non-degenerate.
-- This follows from: `0 < volume (Set.univ : Set X)` + `g > 0` + continuity of g.
-- But again, we'd need continuity of g.

-- (d) hSpatialNonnegZero: (∀ x, 0 ≤ g x) → ∫ g = 0 → ∀ x, g x = 0
-- This needs: the measure gives positive mass to every open set.
-- With CompactSpace + Haar measure:
-- `integral_eq_zero_iff_of_nonneg` + openness argument.
-- Again needs continuity of g.

-- KEY INSIGHT: Most axiom eliminations require the abstract operator outputs
-- to be continuous. We could add:
-- hGradCont : ∀ φ, Continuous φ → Continuous (fun x => gradX φ x i)
-- hDivCont : ∀ F, (∀ i, Continuous (fun x => F x i)) → Continuous (divX F)
-- etc.
-- But this is MORE axioms, not fewer!

-- VERDICT: Adding CompactSpace helps with measure theory (Fubini, integral_add),
-- but eliminating the analysis axioms (hSpatialPos, hSpatialNonnegZero)
-- additionally requires continuity of operator outputs, which adds complexity.

-- The net effect: we can eliminate ~2 axioms (hSpatialAdd, hSpatialVelocityFubini)
-- by adding CompactSpace/T2Space, but the "analysis on compact manifold" axioms
-- (hSpatialPos, hSpatialNonnegZero, hLaplacianMaxNonpos, hHarmonic_const)
-- stay unless we add even more structure.

end EnrichedAbstract

-- ============================================================================
-- EXPERIMENT 5: Minimal abstract approach — what do we REALLY need?
--
-- Instead of a "FlatTorus3", define only the properties we use.
-- Group axioms by what they express mathematically.
-- ============================================================================

namespace MinimalAbstract

-- Looking at the axiom usage audit:
--
-- NEVER USED: hStokes (0 direct calls!)
-- USED ONCE: hCurlZeroDivZeroHarmonic, hKillingToHarmonic,
--            hSpatialVelocityFubini, hSpatialNonnegZero
--
-- These are the "hard" axioms. Can we restructure to avoid them?
--
-- hStokes: Not used at all! Can be removed immediately.
--
-- hKillingToHarmonic: Used once in VMLInputDerive.lean:155 to show
--   b_loc is harmonic. This axiom encodes flatness. On a general
--   curved manifold, Killing fields don't have harmonic components.
--   This is genuinely needed for the flat torus result.
--
-- hCurlZeroDivZeroHarmonic: Used once in Section8.lean:48 to show
--   B field components are harmonic. On a flat manifold,
--   curl=0 + div=0 → each component is harmonic. This also encodes flatness.
--
-- hSpatialVelocityFubini: Used once in Section4.lean:300 for the
--   spatial-velocity integral swap. If X were concrete and compact,
--   this could come from Mathlib.
--
-- hSpatialNonnegZero: Used once in Theorem42.lean:160 for the key step
--   "entropy dissipation ≥ 0 everywhere, integral = 0, therefore = 0 pointwise".
--   This is measure-theoretic and needs non-degenerate measure.

-- Here's a more minimal version that separates concerns:

/-- Smooth compact domain with differential operators.
    Fewer axioms than FlatTorus3 by removing hStokes and splitting
    the remaining axioms into tiers. -/
class SmoothCompactDomain (X : Type*) extends MeasureSpace X where
  -- Differential operators
  gradX : (X → ℝ) → X → (Fin 3 → ℝ)
  divX : (X → (Fin 3 → ℝ)) → X → ℝ
  curlX : (X → (Fin 3 → ℝ)) → X → (Fin 3 → ℝ)
  -- Basic calculus (7 axioms — these are "easy" and could be proved
  -- for any smooth manifold with concrete operators)
  hDivLinear : ∀ (α : ℝ) (G : X → (Fin 3 → ℝ)),
    ∀ x, divX (fun y => α • G y) x = α * divX G x
  hGradConst : ∀ (φ : X → ℝ), (∀ x y, φ x = φ y) → ∀ x, gradX φ x = 0
  hGradAdd : ∀ (f g : X → ℝ),
    ∀ x, gradX (fun y => f y + g y) x = gradX f x + gradX g x
  hGradScalarMul : ∀ (c : ℝ) (f : X → ℝ),
    ∀ x, gradX (fun y => c * f y) x = c • gradX f x
  hGradChainExp : ∀ (φ : X → ℝ),
    ∀ x i, gradX (fun y => Real.exp (φ y)) x i = Real.exp (φ x) * gradX φ x i
  -- Compact manifold without boundary (3 axioms)
  hIBP_spatial : ∀ (φ ψ : X → ℝ) (i : Fin 3),
    (∫ x, φ x * gradX ψ x i) = -(∫ x, ψ x * gradX φ x i)
  hCurlIntZero : ∀ (F : X → Fin 3 → ℝ) (u : Fin 3 → ℝ),
    ∫ x, dotProduct u (curlX F x) = 0
  -- Analysis on compact domain (3 axioms — need measure non-degeneracy)
  hHarmonic_const : ∀ φ : X → ℝ, (∀ x, divX (gradX φ) x = 0) → ∀ x y, φ x = φ y
  hLaplacianMaxNonpos : ∀ (φ : X → ℝ) (x₀ : X),
    (∀ x, φ x ≤ φ x₀) → divX (gradX φ) x₀ ≤ 0
  hSpatialPos : ∀ g : X → ℝ, (∀ x, 0 < g x) → 0 < ∫ x, g x
  -- Integral properties (2 axioms — could be eliminated with CompactSpace)
  hSpatialVelocityFubini : ∀ (F : X → (Fin 3 → ℝ) → ℝ),
    (∀ x, Integrable (F x)) →
    (∫ x, ∫ v, F x v) = ∫ v, ∫ x, F x v
  hSpatialAdd : ∀ (g₁ g₂ : X → ℝ),
    (∫ x, (g₁ x + g₂ x)) = (∫ x, g₁ x) + ∫ x, g₂ x

-- This has 15 axioms (removed hStokes).
-- But we're still missing hKillingToHarmonic and hCurlZeroDivZeroHarmonic
-- which encode FLATNESS. These could be added as a separate mixin:

/-- Additional axioms encoding flatness of the metric.
    These fail on curved manifolds. -/
class FlatMetric (X : Type*) [SmoothCompactDomain X] where
  hKillingToHarmonic : ∀ (b : X → Fin 3 → ℝ),
    (∀ x i j, SmoothCompactDomain.gradX (fun y => b y j) x i +
               SmoothCompactDomain.gradX (fun y => b y i) x j = 0) →
    ∀ j : Fin 3, ∀ x, SmoothCompactDomain.divX
      (SmoothCompactDomain.gradX (fun y => b y j)) x = 0
  hCurlZeroDivZeroHarmonic : ∀ F : X → (Fin 3 → ℝ),
    (∀ x, SmoothCompactDomain.curlX F x = 0) →
    (∀ x, SmoothCompactDomain.divX F x = 0) →
    ∀ i, ∀ x, SmoothCompactDomain.divX
      (SmoothCompactDomain.gradX (fun y => F y i)) x = 0

-- We also need hSpatialNonnegZero, which was in FlatTorus3.
-- This is really a measure-theoretic property, not a differential-geometric one.
-- It could go in SmoothCompactDomain or be derived from CompactSpace + regularity.

-- VERDICT: 15 + 2 = 17 axioms total (one MORE than current 16, because
-- we split into two classes). But conceptually cleaner: SmoothCompactDomain
-- (13 axioms) + FlatMetric (2 axioms) + hSpatialNonnegZero (1).
-- Net: same complexity, better organization.

end MinimalAbstract

-- ============================================================================
-- EXPERIMENT 6: Hybrid — concrete operators, abstract topology
--
-- Key insight: the "easy" axioms (hGradAdd, hGradScalarMul, etc.) are
-- just properties of fderiv. If gradX IS fderiv (or a wrapper), we get
-- these for free. The "hard" axioms (IBP, harmonic→const, Killing) are
-- topological/geometric and genuinely need the torus.
--
-- Idea: Define operators IN TERMS OF fderiv, keep topology abstract.
-- ============================================================================

namespace HybridApproach

-- For this to work, our domain X needs to:
-- 1. Be a normed space (for fderiv to make sense)
-- 2. OR: have smooth functions X → ℝ whose derivatives can be computed

-- Problem: if X is AddCircle, it's not a normed vector space.
-- fderiv only works for maps between normed spaces.
-- mfderiv works for manifolds but returns tangent space maps.

-- What if X is actually (Fin 3 → ℝ) but we restrict to periodic functions?
-- Then fderiv works natively!

-- The key idea: separate the FUNCTIONS from the DOMAIN.
-- Functions live on ℝ³ (where fderiv works).
-- Integration is over a fundamental domain (unit cube or torus).
-- Periodicity is a constraint on the functions.

-- Let's formalize this:

/-- A spatial domain for periodic functions on ℝ³.
    Functions are defined on all of ℝ³ but are periodic.
    Integration is over the fundamental domain [0,1)³.
    Differential operators use standard fderiv on ℝ³. -/
structure PeriodicDomain where
  -- The integration measure (restricted to fundamental domain)
  μ : Measure (Fin 3 → ℝ)
  -- Integration is over [0,1)³ with Lebesgue measure
  hμ : μ = volume.restrict (Set.pi Set.univ (fun _ => Set.Ico 0 1))

-- With this setup:
-- gradX f x = fun i => fderiv ℝ f x (Pi.single i 1)
-- divX F x = ∑ i, fderiv ℝ (F · i) x (Pi.single i 1)
-- curlX = standard curl formula

-- The "periodic function" constraint:
def PeriodicDomain.Periodic (f : (Fin 3 → ℝ) → ℝ) : Prop :=
  ∀ x i, f (x + Pi.single i 1) = f x

-- Advantages:
-- + All "easy" axioms (hGradAdd, hGradScalarMul, hGradChainExp, etc.)
--   are PROVABLE from fderiv properties in Mathlib!
-- + No need for abstract operators
-- + The operators ARE the standard ones

-- What about the "hard" axioms?
-- hIBP_spatial: ∫_{[0,1)³} φ · ∂ψ/∂xᵢ = -∫_{[0,1)³} ψ · ∂φ/∂xᵢ
--   This follows from 1D IBP + Fubini + periodicity (boundary terms cancel).
--   The 1D version: ∫₀¹ φ·ψ' = [φ·ψ]₀¹ - ∫₀¹ φ'·ψ
--   With periodicity: [φ·ψ]₀¹ = φ(1)·ψ(1) - φ(0)·ψ(0) = 0.
--   This is PROVABLE but requires work.

-- hHarmonic_const: harmonic periodic function is constant.
--   This follows from the maximum principle on ℝ³:
--   a periodic harmonic function attains its max on the compact cube,
--   so by the strong maximum principle it's constant.
--   This is a REAL THEOREM that needs to be formalized.

-- hKillingToHarmonic: on FLAT ℝ³ with periodic BC, Killing → harmonic.
--   This is: if ∂bⱼ/∂xᵢ + ∂bᵢ/∂xⱼ = 0, then Δbⱼ = 0.
--   Proof: ∂²bⱼ/∂xᵢ² = -∂²bᵢ/∂xᵢ∂xⱼ = ∂²bⱼ/∂xⱼ² (using Killing + symmetry)
--   Wait, that's not quite right. The actual argument is:
--   Δbⱼ = Σᵢ ∂²bⱼ/∂xᵢ² = Σᵢ (-∂²bᵢ/∂xᵢ∂xⱼ) = -∂/∂xⱼ(Σᵢ ∂bᵢ/∂xᵢ) = -∂(div b)/∂xⱼ
--   So if div(b) = const (which follows from the Killing equation taking trace),
--   then Δbⱼ = 0. On flat space this is straightforward.
--   This is PROVABLE from fderiv properties + Clairaut's theorem.

-- ASSESSMENT of provability from Mathlib:
-- ✅ Provable: hGradAdd, hGradScalarMul, hGradConst, hGradChainExp, hDivLinear
--   (all from fderiv linearity/chain rule)
-- ⚠️ Needs work: hIBP_spatial (1D IBP + Fubini + periodicity)
-- ⚠️ Needs work: hHarmonic_const (strong maximum principle for periodic harmonic)
-- ⚠️ Needs work: hLaplacianMaxNonpos (second derivative test — should be in Mathlib?)
-- ⚠️ Needs work: hKillingToHarmonic (Clairaut + trace of Killing eq)
-- ⚠️ Needs work: hCurlZeroDivZeroHarmonic (Hodge on flat space)
-- ✅ Trivially: hSpatialAdd (integral_add on measurable set)
-- ⚠️ Needs work: hSpatialVelocityFubini (Fubini for cube × ℝ³)
-- ✅ Likely: hSpatialPos, hSpatialNonnegZero (Lebesgue measure on cube)
-- ⚠️ Needs work: hCurlIntZero (Stokes on cube with periodic BC)

-- VERDICT: This is the most promising approach!
-- ~7 axioms become free from Mathlib
-- ~8 need nontrivial proofs but are mathematically clear
-- The domain is completely concrete (no abstract types)

-- HOWEVER: the main files currently use `{X : Type*} [FlatTorus3 X]`,
-- with `X` appearing in types of `f : X → (Fin 3 → ℝ) → ℝ`, etc.
-- Switching to `(Fin 3 → ℝ)` as the spatial domain means ALL spatial
-- functions become `(Fin 3 → ℝ) → whatever` with periodicity constraints.
-- This is a MASSIVE refactor of the entire proof.

end HybridApproach

-- ============================================================================
-- EXPERIMENT 7: Pragmatic middle ground
--
-- Keep FlatTorus3 abstract but:
-- 1. Remove hStokes (unused)
-- 2. Prove hSpatialAdd from CompactSpace (if we add it)
-- 3. Keep everything else
-- 4. Add [CompactSpace X] [T2Space X] as type class assumptions
--    at use sites (Theorem42) rather than in FlatTorus3 itself
--
-- This is the SMALLEST change that improves things.
-- ============================================================================

namespace Pragmatic

-- Current state: 16 axioms in FlatTorus3
-- Immediately removable: hStokes (0 usage) → 15 axioms

-- If we add [CompactSpace X] [T2Space X] [BorelSpace X] as additional
-- typeclass assumptions at use sites:

-- Can remove hSpatialAdd IF we also assume integrability of operator outputs.
-- Can remove hSpatialVelocityFubini IF we assume joint integrability.
-- These are traded for integrability hypotheses at call sites.

-- Net: 15 - 2 = 13 axioms + some integrability hypotheses at call sites.

-- The 13 remaining axioms would be:
-- Basic calculus (5): hDivLinear, hGradConst, hGradAdd, hGradScalarMul, hGradChainExp
-- Compact manifold (4): hIBP_spatial, hCurlIntZero, hHarmonic_const, hLaplacianMaxNonpos
-- Measure (2): hSpatialPos, hSpatialNonnegZero
-- Flatness (2): hKillingToHarmonic, hCurlZeroDivZeroHarmonic

-- This is clean! The 5 calculus axioms are "boring" (true for any smooth manifold).
-- The 4 compact manifold axioms are standard topology.
-- The 2 measure axioms are measure theory.
-- The 2 flatness axioms are geometry.

-- VERDICT: Best cost/benefit ratio. Minimal changes, clear improvement.

end Pragmatic

-- ============================================================================
-- SUMMARY OF EXPERIMENTS
-- ============================================================================

/-
## Comparison Table

| Approach | Axioms | Refactor Effort | Mathlib Usage | Notes |
|----------|--------|-----------------|---------------|-------|
| Current FlatTorus3 | 16 | None | Minimal | Working baseline |
| Periodic ℝ³ (Exp 1) | ~8 sorry | Very large | High | Need cube integral theory |
| AddCircle product (Exp 2) | ~8 sorry | Very large | High | Need manifold derivatives |
| Fin 3 → AddCircle (Exp 3) | ~8 sorry | Very large | High | Same as Exp 2, cleaner type |
| Enriched abstract (Exp 4) | ~14 | Small | Medium | Need continuity of operators |
| Minimal abstract (Exp 5) | 15+2 | Small | Same | Better organization, same count |
| Hybrid periodic (Exp 6) | ~8 sorry | Very large | Highest | Most principled, biggest refactor |
| Pragmatic (Exp 7) | 13 | Small | Medium | Best cost/benefit |

## Recommendations

### For immediate improvement (Experiment 7 — Pragmatic):
1. Remove hStokes (unused) → 15 axioms
2. Add [CompactSpace X] [T2Space X] at Theorem42 use site (already there!)
3. Replace hSpatialAdd with integral_add + integrability hypotheses → 14 axioms
4. Replace hSpatialVelocityFubini with Mathlib's Fubini + integrability → 13 axioms
5. Total: 13 axioms, minimal code changes

### For future work (Experiment 6 — Hybrid):
If we want to maximize Mathlib usage, the periodic-ℝ³ approach is best:
- Domain = (Fin 3 → ℝ), operators = fderiv/div/curl from Mathlib
- ~7 axioms become free, ~8 need proofs but are mathematically straightforward
- Requires large refactor: X becomes (Fin 3 → ℝ), all spatial functions need
  periodicity constraints, integration becomes cube integrals
- This could be a separate PR/branch

### What periodicity buys us:
Periodicity is used for:
- IBP without boundary terms (opposite face contributions cancel)
- Harmonic → constant (compact periodic domain, no boundary)
- Stokes theorem (∫ div = 0 on closed manifold)
- None of the algebraic steps (polynomial matching, etc.) need periodicity

Without periodicity (e.g., on a general compact manifold with boundary):
- IBP would have boundary terms
- Harmonic functions might not be constant (depend on BC)
- The entire H-theorem transport argument would need modification

So periodicity IS essential for the mathematical argument, not just an artifact.
-/

end
