/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.QuotientEquivalenceTransport
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionAmbientProjectiveComparison

/-!
# The residual centralizer quotient in Proposition 4.5

Put `N = CS` and `H = N_X(S)` in the central-intersection branch of
Proposition 4.5.  The centralizer `C_X(N)` lies in `H`.  Its part lying in
the normal subgroup `N ∩ H` is exactly `Z(N)`.  Consequently the
group-theoretic quotient supporting the residual projective scalar
character is canonically

`C_X(CS) / Z(CS)`.

The hypotheses of Proposition 4.5 do **not** force this quotient to be
trivial.  For example, take `q = 2`,

`X = S₃ × C₃`, `C = A₃ × 1`, and `S = ⟨((12), 1)⟩`.

Then `C ◁ X`, `C ∩ S = 1`, and
`C N_X(S) = X`.  However, `CS = S₃ × 1`,
`C_X(CS) = 1 × C₃`, and `Z(CS) = 1`; hence the residual quotient is
isomorphic to `C₃`.  This example is recorded only as mathematical
documentation.  The Lean results below establish the general canonical
identification, without depending on a choice of characters.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction

open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The ambient centralizer `C_X(CS)`. -/
abbrev productAmbientCentralizer : Subgroup X :=
  Subgroup.centralizer (product S C : Set X)

/-- The ambient centralizer, represented inside `N_X(S)`. -/
abbrev productCentralizerInAmbientNormalizer :
    Subgroup (ambientNormalizer S) :=
  (productAmbientCentralizer S C).comap
    (ambientNormalizer S).subtype

/-- The part of `C_X(CS)`, represented inside `N_X(S)`, which also lies
in the internal subgroup `CS ∩ N_X(S)`. -/
abbrev productNormalizerPartInCentralizer :
    Subgroup (productCentralizerInAmbientNormalizer S C) :=
  (internalProductNormalizer S C).comap
    (productCentralizerInAmbientNormalizer S C).subtype

/-- The part of `C_X(CS)` which lies in `CS`. -/
abbrev productPartInAmbientCentralizer :
    Subgroup (productAmbientCentralizer S C) :=
  (product S C).comap
    (productAmbientCentralizer S C).subtype

omit [Finite X] [Fact q.Prime] [C.Normal] in
/-- Restricting the inclusion `N_X(S) → X` identifies the copy of
`C_X(CS)` inside `N_X(S)` with the ambient centralizer itself. -/
def productCentralizerInAmbientNormalizerEquiv :
    productCentralizerInAmbientNormalizer S C ≃*
      productAmbientCentralizer S C where
  toFun x :=
    ⟨((x.1 : ambientNormalizer S) : X), x.2⟩
  invFun x := by
    have hxNormalizer :
        (x.1 : X) ∈ ambientNormalizer S :=
      centralizer_product_le_ambientNormalizer S C x.2
    exact
      ⟨⟨(x.1 : X), hxNormalizer⟩, x.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    rfl

omit [Finite X] [Fact q.Prime] [C.Normal] in
@[simp]
theorem productCentralizerInAmbientNormalizerEquiv_apply_coe
    (x : productCentralizerInAmbientNormalizer S C) :
    ((productCentralizerInAmbientNormalizerEquiv S C x :
        productAmbientCentralizer S C) : X) =
      ((x.1 : ambientNormalizer S) : X) :=
  rfl

omit [Finite X] [Fact q.Prime] [C.Normal] in
/-- The normalizer-side normal part and the ambient part of the centralizer
are canonically isomorphic. -/
def productNormalizerPartInCentralizerEquivProductPart :
    productNormalizerPartInCentralizer S C ≃*
      productPartInAmbientCentralizer S C where
  toFun x := by
    refine ⟨⟨((x.1.1 : ambientNormalizer S) : X), x.1.2⟩, ?_⟩
    have hx := x.2
    change
      (((x.1.1 : ambientNormalizer S) : X) ∈ product S C) at hx
    exact hx
  invFun x := by
    have hxNormalizer :
        (x.1.1 : X) ∈ ambientNormalizer S :=
      centralizer_product_le_ambientNormalizer S C x.1.2
    refine
      ⟨⟨⟨(x.1.1 : X), hxNormalizer⟩, x.1.2⟩, ?_⟩
    have hx := x.2
    change ((x.1.1 : X) ∈ product S C) at hx
    exact hx
  left_inv x := by
    apply Subtype.ext
    exact
      (productCentralizerInAmbientNormalizerEquiv S C
        ).symm_apply_apply x.1
  right_inv x := by
    apply Subtype.ext
    exact
      (productCentralizerInAmbientNormalizerEquiv S C
        ).apply_symm_apply x.1
  map_mul' x y := by
    apply Subtype.ext
    exact
      (productCentralizerInAmbientNormalizerEquiv S C).map_mul
        x.1 y.1

omit [Finite X] [Fact q.Prime] [C.Normal] in
/-- The preceding two equivalences commute with the subgroup inclusions. -/
theorem productCentralizerEquiv_normalPart_commutes :
    (productCentralizerInAmbientNormalizerEquiv S C).toMonoidHom.comp
        (productNormalizerPartInCentralizer S C).subtype =
      (productPartInAmbientCentralizer S C).subtype.comp
        (productNormalizerPartInCentralizerEquivProductPart
          S C).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  rfl

omit [Finite X] [Fact q.Prime] [C.Normal] in
/-- The natural embedding `Z(CS) → C_X(CS)`. -/
def productCenterToAmbientCentralizer :
    Subgroup.center (product S C) →*
      productAmbientCentralizer S C where
  toFun z := by
    refine ⟨((z.1 : product S C) : X), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    let yProduct : product S C := ⟨y, hy⟩
    exact
      congrArg Subtype.val
        ((Subgroup.mem_center_iff.mp z.2) yProduct)
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' z w := by
    apply Subtype.ext
    rfl

omit [Finite X] [Fact q.Prime] [C.Normal] in
theorem productCenterToAmbientCentralizer_injective :
    Function.Injective
      (productCenterToAmbientCentralizer S C) := by
  intro z w h
  have hx :
      ((z.1 : product S C) : X) =
        ((w.1 : product S C) : X) :=
    congrArg
      (fun y : productAmbientCentralizer S C ↦ (y : X)) h
  exact Subtype.ext (Subtype.ext hx)

omit [Finite X] [Fact q.Prime] [C.Normal] in
/-- Inside `C_X(CS)`, the elements lying in `CS` are exactly the image of
`Z(CS)`. -/
theorem productCenterToAmbientCentralizer_range :
    MonoidHom.range
        (productCenterToAmbientCentralizer S C) =
      productPartInAmbientCentralizer S C := by
  apply le_antisymm
  · intro x hx
    obtain ⟨z, rfl⟩ := hx
    exact z.1.2
  · intro x hx
    let zProduct : product S C :=
      ⟨(x.1 : X), hx⟩
    have hzCenter :
        zProduct ∈ Subgroup.center (product S C) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact
        (Subgroup.mem_centralizer_iff.mp x.2)
          (y : X) y.2
    let z : Subgroup.center (product S C) :=
      ⟨zProduct, hzCenter⟩
    exact
      ⟨z, by
        apply Subtype.ext
        rfl⟩

omit [Finite X] [Fact q.Prime] [C.Normal] in
/-- Equivalently, the intersection `C_X(CS) ∩ CS`, mapped back to `X`,
is the ambient image of `Z(CS)`. -/
theorem map_productPartInAmbientCentralizer :
    (productPartInAmbientCentralizer S C).map
        (productAmbientCentralizer S C).subtype =
      (Subgroup.center (product S C)).map
        (product S C).subtype := by
  rw [← productCenterToAmbientCentralizer_range S C]
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, z.2, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    let zCenter : Subgroup.center (product S C) :=
      ⟨z, hz⟩
    exact
      ⟨productCenterToAmbientCentralizer S C zCenter,
        ⟨zCenter, rfl⟩, rfl⟩

omit [Finite X] [Fact q.Prime] [C.Normal] in
/-- The centralizer part lying in `CS` is central in `C_X(CS)`, hence is a
normal subgroup and may be quotiented out. -/
instance productPartInAmbientCentralizer_normal :
    (productPartInAmbientCentralizer S C).Normal := by
  refine ⟨?_⟩
  intro n hn g
  have hcomm :
      g * n = n * g := by
    apply Subtype.ext
    exact
      ((Subgroup.mem_centralizer_iff.mp g.2)
        (n : X) hn).symm
  have hconj :
      g * n * g⁻¹ = n := by
    calc
      g * n * g⁻¹ = n * g * g⁻¹ := by rw [hcomm]
      _ = n := by
        rw [mul_assoc, mul_inv_cancel, mul_one]
  rw [hconj]
  exact hn

omit [Finite X] [Fact q.Prime] [C.Normal] in
/-- The corresponding normalizer-side subgroup is likewise normal. -/
instance productNormalizerPartInCentralizer_normal :
    (productNormalizerPartInCentralizer S C).Normal := by
  refine ⟨?_⟩
  intro n hn g
  have hcomm :
      g * n = n * g := by
    apply Subtype.ext
    apply Subtype.ext
    have hnProduct :
        (((n.1 : ambientNormalizer S) : X) ∈
          product S C) := by
      have hn' := hn
      change
        (((n.1 : ambientNormalizer S) : X) ∈
          product S C) at hn'
      exact hn'
    exact
      ((Subgroup.mem_centralizer_iff.mp g.2)
        (((n.1 : ambientNormalizer S) : X))
        hnProduct).symm
  have hconj :
      g * n * g⁻¹ = n := by
    calc
      g * n * g⁻¹ = n * g * g⁻¹ := by rw [hcomm]
      _ = n := by
        rw [mul_assoc, mul_inv_cancel, mul_one]
  rw [hconj]
  exact hn

omit [Finite X] [Fact q.Prime] [C.Normal] in
instance productCenterToAmbientCentralizer_range_normal :
    (MonoidHom.range
      (productCenterToAmbientCentralizer S C)).Normal := by
  rw [productCenterToAmbientCentralizer_range S C]
  infer_instance

/-- The residual quotient represented inside `N_X(S)`. -/
abbrev productNormalizerResidualCentralizerQuotient :=
  productCentralizerInAmbientNormalizer S C ⧸
    productNormalizerPartInCentralizer S C

/-- The ambient presentation `C_X(CS) / (C_X(CS) ∩ CS)`. -/
abbrev productAmbientResidualCentralizerQuotient :=
  productAmbientCentralizer S C ⧸
    productPartInAmbientCentralizer S C

omit [Finite X] [Fact q.Prime] [C.Normal] in
/-- The normalizer-side residual quotient is canonically the ambient
centralizer quotient. -/
def productNormalizerResidualCentralizerQuotientEquivAmbient :
    productNormalizerResidualCentralizerQuotient S C ≃*
      productAmbientResidualCentralizerQuotient S C :=
  quotientMulEquivOfSubgroupEquiv
    (productCentralizerInAmbientNormalizerEquiv S C)
    (productNormalizerPartInCentralizerEquivProductPart S C)
    (productCentralizerEquiv_normalPart_commutes S C)

omit [Finite X] [Fact q.Prime] [C.Normal] in
/-- Replacing `C_X(CS) ∩ CS` by its equal presentation as the embedded
center gives the literal quotient `C_X(CS) / Z(CS)`. -/
def productAmbientResidualCentralizerQuotientEquivCenter :
    productAmbientResidualCentralizerQuotient S C ≃*
      (productAmbientCentralizer S C ⧸
        MonoidHom.range
          (productCenterToAmbientCentralizer S C)) :=
  QuotientGroup.quotientMulEquivOfEq
    (productCenterToAmbientCentralizer_range S C).symm

omit [Finite X] [Fact q.Prime] [C.Normal] in
/-- The complete canonical identification of the residual quotient with
`C_X(CS) / Z(CS)`. -/
def productResidualCentralizerQuotientEquiv :
    productNormalizerResidualCentralizerQuotient S C ≃*
      (productAmbientCentralizer S C ⧸
        MonoidHom.range
          (productCenterToAmbientCentralizer S C)) :=
  (productNormalizerResidualCentralizerQuotientEquivAmbient
    S C).trans
      (productAmbientResidualCentralizerQuotientEquivCenter S C)

end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
