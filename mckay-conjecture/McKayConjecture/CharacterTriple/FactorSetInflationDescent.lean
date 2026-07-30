/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FactorSetCohomology
import McKayConjecture.CharacterTriple.FactorSetCentralExtensionNormalizer

/-!
# Descent of explicit splittings along a surjective homomorphism

Let `f : U →* Q` be surjective and let `α` be a factor set on `Q`.
A splitting of the inflated factor `α.comap f` does not in general imply
that `α` splits: inflation on second cohomology need not be injective.

There is, however, an elementary cochain-level descent statement.  If a
chosen splitting cochain is constant on the fibers of `f` (equivalently,
invariant under right multiplication by `ker f`), then it is the pullback
of a cochain on `Q`.  The resulting quotient cochain splits `α`.

The API below deliberately keeps this extra compatibility hypothesis
visible.  It is intended for arguments where representation theory supplies
a distinguished splitting cochain and proves that it is constant on kernel
cosets.
-/

noncomputable section

universe u v w

namespace McKayConjecture
namespace CharacterTriple
namespace FactorSet

variable {U : Type u} {Q : Type v} {A : Type w}
variable [Group U] [Group Q]

/-- A cochain on `U` is constant on the fibers of `f : U →* Q`. -/
def Cochain.IsFiberConstantAlong
    (f : U →* Q) (c : U → A) : Prop :=
  ∀ x y : U, f x = f y → c x = c y

/-- A cochain on `U` is invariant under right multiplication by the kernel
of `f`.  For group homomorphisms this is equivalent to fiber constancy. -/
def Cochain.IsRightKernelInvariant
    (f : U →* Q) (c : U → A) : Prop :=
  ∀ (x : U) (k : f.ker), c (x * (k : U)) = c x

/-- Fiber constancy implies invariance under right multiplication by the
kernel. -/
theorem Cochain.IsFiberConstantAlong.isRightKernelInvariant
    {f : U →* Q} {c : U → A}
    (hc : Cochain.IsFiberConstantAlong f c) :
    Cochain.IsRightKernelInvariant f c := by
  intro x k
  apply hc
  have hk : f (k : U) = 1 :=
    MonoidHom.mem_ker.mp k.property
  simp only [map_mul, hk, mul_one]

/-- Invariance under right multiplication by the kernel implies fiber
constancy. -/
theorem Cochain.IsRightKernelInvariant.isFiberConstantAlong
    {f : U →* Q} {c : U → A}
    (hc : Cochain.IsRightKernelInvariant f c) :
    Cochain.IsFiberConstantAlong f c := by
  intro x y hxy
  let k : f.ker :=
    ⟨x⁻¹ * y, by
      apply MonoidHom.mem_ker.mpr
      rw [map_mul, map_inv, hxy, inv_mul_cancel]⟩
  have hkernel := hc x k
  have hproduct : x * (k : U) = y := by
    dsimp [k]
    group
  rw [hproduct] at hkernel
  exact hkernel.symm

/-- Fiber constancy is equivalent to invariance under right multiplication
by the kernel. -/
theorem cochain_isFiberConstantAlong_iff_isRightKernelInvariant
    (f : U →* Q) (c : U → A) :
    Cochain.IsFiberConstantAlong f c ↔
      Cochain.IsRightKernelInvariant f c :=
  ⟨Cochain.IsFiberConstantAlong.isRightKernelInvariant,
    Cochain.IsRightKernelInvariant.isFiberConstantAlong⟩

/-- Descend a cochain by evaluating it on a fixed choice of preimage.
Fiber constancy makes this choice immaterial. -/
def descendedCochain
    (f : U →* Q) (hf : Function.Surjective f)
    (c : U → A) : Q → A :=
  fun q ↦ c (Function.surjInv hf q)

/-- Pulling the descended cochain back along `f` recovers the original
fiber-constant cochain. -/
theorem descendedCochain_comp
    (f : U →* Q) (hf : Function.Surjective f)
    (c : U → A)
    (hc : Cochain.IsFiberConstantAlong f c)
    (x : U) :
    descendedCochain f hf c (f x) = c x := by
  exact hc _ _ (Function.surjInv_eq hf (f x))

/-- A fiber-constant cochain factors through a surjective homomorphism. -/
theorem cochain_isFiberConstantAlong_iff_exists_comp
    (f : U →* Q) (hf : Function.Surjective f)
    (c : U → A) :
    Cochain.IsFiberConstantAlong f c ↔
      ∃ d : Q → A, c = d ∘ f := by
  constructor
  · intro hc
    refine ⟨descendedCochain f hf c, ?_⟩
    funext x
    exact (descendedCochain_comp f hf c hc x).symm
  · rintro ⟨d, rfl⟩
    intro x y hxy
    exact congrArg d hxy

variable [CommGroup A]

/-- If the original cochain is one at the identity, so is its descent. -/
theorem descendedCochain_one
    (f : U →* Q) (hf : Function.Surjective f)
    (c : U → A)
    (hc : Cochain.IsFiberConstantAlong f c)
    (hc_one : c 1 = 1) :
    descendedCochain f hf c 1 = 1 := by
  simpa using
    (descendedCochain_comp f hf c hc (1 : U)).trans hc_one

/-- Pullback of factor sets along a surjective homomorphism is injective at
the level of actual factor sets.  This elementary fact is distinct from
injectivity of inflation on cohomology classes. -/
theorem comap_injective_of_surjective
    (f : U →* Q) (hf : Function.Surjective f) :
    Function.Injective
      (fun α : FactorSet Q A ↦ α.comap f) := by
  intro α β h
  apply FactorSet.ext
  intro q r
  obtain ⟨x, rfl⟩ := hf q
  obtain ⟨y, rfl⟩ := hf r
  exact congrArg (fun γ : FactorSet U A ↦ γ x y) h

@[simp]
theorem one_comap (f : U →* Q) :
    (FactorSet.one : FactorSet Q A).comap f =
      (FactorSet.one : FactorSet U A) := by
  apply FactorSet.ext
  intro x y
  rfl

/-- A gauge equality between two pullbacks descends when its cochain is
constant on fibers. -/
theorem gauge_eq_of_comap_gauge_eq_of_surjective
    (α β : FactorSet Q A)
    (f : U →* Q) (hf : Function.Surjective f)
    (c : U → A)
    (hc : Cochain.IsFiberConstantAlong f c)
    (hgauge :
      (α.comap f).gauge c = β.comap f) :
    α.gauge (descendedCochain f hf c) = β := by
  apply comap_injective_of_surjective f hf
  change
    (α.gauge (descendedCochain f hf c)).comap f =
      β.comap f
  rw [comap_gauge]
  have hcomp :
      (fun x : U ↦ descendedCochain f hf c (f x)) = c := by
    funext x
    exact descendedCochain_comp f hf c hc x
  rw [hcomp]
  exact hgauge

/-- A fiber-compatible gauge between pullbacks gives cohomology of the
original factor sets. -/
theorem cohomologous_of_comap_gauge_eq_of_surjective
    (α β : FactorSet Q A)
    (f : U →* Q) (hf : Function.Surjective f)
    (c : U → A)
    (hc : Cochain.IsFiberConstantAlong f c)
    (hgauge :
      (α.comap f).gauge c = β.comap f) :
    α.Cohomologous β := by
  refine ⟨descendedCochain f hf c, ?_⟩
  exact
    (gauge_eq_of_comap_gauge_eq_of_surjective
      α β f hf c hc hgauge).symm

/-- Explicit data certifying that a splitting of `α.comap f` genuinely
descends through the surjection `f`. -/
structure ComapSplittingDescentDatum
    (α : FactorSet Q A) (f : U →* Q) where
  /-- The chosen splitting cochain upstairs. -/
  cochain : U → A
  /-- The chosen cochain trivializes the pulled-back factor. -/
  gauge_eq_one :
    (α.comap f).gauge cochain =
      (FactorSet.one : FactorSet U A)
  /-- The extra descent condition, not a consequence of splitting. -/
  fiber_constant :
    Cochain.IsFiberConstantAlong f cochain

namespace ComapSplittingDescentDatum

variable {α : FactorSet Q A} {f : U →* Q}

/-- The quotient cochain selected by a splitting descent datum. -/
def descended
    (D : ComapSplittingDescentDatum α f)
    (hf : Function.Surjective f) : Q → A :=
  descendedCochain f hf D.cochain

/-- The descended cochain pulls back to the specified splitting cochain. -/
theorem descended_comp
    (D : ComapSplittingDescentDatum α f)
    (hf : Function.Surjective f)
    (x : U) :
    D.descended hf (f x) = D.cochain x :=
  descendedCochain_comp
    f hf D.cochain D.fiber_constant x

/-- The quotient cochain supplied by the datum splits the original factor
set. -/
theorem gauge_descended_eq_one
    (D : ComapSplittingDescentDatum α f)
    (hf : Function.Surjective f) :
    α.gauge (D.descended hf) =
      (FactorSet.one : FactorSet Q A) := by
  apply
    gauge_eq_of_comap_gauge_eq_of_surjective
      α FactorSet.one f hf D.cochain D.fiber_constant
  simpa using D.gauge_eq_one

/-- A descending splitting of the pullback proves that the original factor
is cohomologous to one. -/
theorem cohomologous_one
    (D : ComapSplittingDescentDatum α f)
    (hf : Function.Surjective f) :
    α.Cohomologous (FactorSet.one : FactorSet Q A) := by
  refine ⟨D.descended hf, ?_⟩
  exact (D.gauge_descended_eq_one hf).symm

/-- For a normalized factor set, the specified splitting cochain upstairs
is automatically one at the identity. -/
theorem cochain_one
    (D : ComapSplittingDescentDatum α f)
    (hα : α.IsNormalized) :
    D.cochain 1 = 1 := by
  have hvalue :=
    congrArg
      (fun β : FactorSet U A ↦ β 1 1)
      D.gauge_eq_one
  simpa [FactorSet.gauge_apply, hα.1 1] using hvalue

/-- For a normalized factor set, the descended splitting cochain is
normalized at the identity. -/
theorem descended_one
    (D : ComapSplittingDescentDatum α f)
    (hf : Function.Surjective f)
    (hα : α.IsNormalized) :
    D.descended hf 1 = 1 :=
  descendedCochain_one
    f hf D.cochain D.fiber_constant (D.cochain_one hα)

end ComapSplittingDescentDatum

/-! The cohomology bridge currently has the same `Type` universe restriction
as `FactorSet.h2Class`. -/

section Cohomology

variable {U Q A : Type}
variable [Group U] [Group Q] [CommGroup A]
variable {α : FactorSet Q A} {f : U →* Q}

/-- A descending explicit splitting of the pullback kills the original
second-cohomology class. -/
theorem ComapSplittingDescentDatum.h2Class_eq_zero
    (D : ComapSplittingDescentDatum α f)
    (hf : Function.Surjective f) :
    letI := trivialMulDistribMulAction Q A
    α.h2Class = 0 := by
  letI := trivialMulDistribMulAction Q A
  exact
    (FactorSet.h2Class_eq_of_cohomologous
      (D.cohomologous_one hf)).trans
        FactorSet.h2Class_one

/-- General cohomology-level descent: a fiber-compatible gauge equality
between two pullbacks proves equality of the original `H²` classes. -/
theorem h2Class_eq_of_comap_gauge_eq_of_fiberConstant
    (α β : FactorSet Q A)
    (f : U →* Q) (hf : Function.Surjective f)
    (c : U → A)
    (hgauge :
      (α.comap f).gauge c = β.comap f)
    (hc : Cochain.IsFiberConstantAlong f c) :
    letI := trivialMulDistribMulAction Q A
    α.h2Class = β.h2Class := by
  letI := trivialMulDistribMulAction Q A
  exact
    FactorSet.h2Class_eq_of_cohomologous
      (cohomologous_of_comap_gauge_eq_of_surjective
        α β f hf c hc hgauge)

/-- Direct unbundled form of cochain-level inflation descent. -/
theorem h2Class_eq_zero_of_comap_gauge_eq_one_of_fiberConstant
    (α : FactorSet Q A)
    (f : U →* Q) (hf : Function.Surjective f)
    (c : U → A)
    (hgauge :
      (α.comap f).gauge c =
        (FactorSet.one : FactorSet U A))
    (hc : Cochain.IsFiberConstantAlong f c) :
    letI := trivialMulDistribMulAction Q A
    α.h2Class = 0 :=
  (ComapSplittingDescentDatum.mk c hgauge hc).h2Class_eq_zero hf

/-- Kernel-coset form of cochain-level inflation descent. -/
theorem h2Class_eq_zero_of_comap_gauge_eq_one_of_rightKernelInvariant
    (α : FactorSet Q A)
    (f : U →* Q) (hf : Function.Surjective f)
    (c : U → A)
    (hgauge :
      (α.comap f).gauge c =
        (FactorSet.one : FactorSet U A))
    (hc : Cochain.IsRightKernelInvariant f c) :
    letI := trivialMulDistribMulAction Q A
    α.h2Class = 0 :=
  h2Class_eq_zero_of_comap_gauge_eq_one_of_fiberConstant
    α f hf c hgauge hc.isFiberConstantAlong

/-- Quotient-group specialization.  Here the compatibility condition is
stated directly as constancy on right cosets of the normal subgroup. -/
theorem h2Class_eq_zero_of_quotient_comap_gauge_eq_one_of_cosetInvariant
    {G A : Type} [Group G] [CommGroup A]
    (N : Subgroup G) [N.Normal]
    (α : FactorSet (G ⧸ N) A)
    (c : G → A)
    (hgauge :
      (α.comap (QuotientGroup.mk' N)).gauge c =
        (FactorSet.one : FactorSet G A))
    (hc : ∀ (g : G) (n : N), c (g * (n : G)) = c g) :
    letI := trivialMulDistribMulAction (G ⧸ N) A
    α.h2Class = 0 := by
  apply
    h2Class_eq_zero_of_comap_gauge_eq_one_of_rightKernelInvariant
      α (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
      c hgauge
  intro g k
  let n : N :=
    ⟨(k : G), by
      exact
        (QuotientGroup.eq_one_iff (N := N) (k : G)).mp
          (MonoidHom.mem_ker.mp k.property)⟩
  exact hc g n

end Cohomology

end FactorSet
end CharacterTriple
end McKayConjecture
