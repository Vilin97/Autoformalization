/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanProjectiveMultiplicity
import McKayConjecture.Character.OkuyamaWajimaCanonicalBaseExtension
import McKayConjecture.Character.OkuyamaWajimaPrimeAwayOriginal
import McKayConjecture.GroupTheory.NormalProductSylowQuotient

/-!
# The printed Okuyama--Wajima extension theorem: source-level boundary

Okuyama--Wajima, Theorem 2(3), is an induction theorem, not an arbitrary
external-action statement.  Its proof uses the following ingredients.

* determinant-normalized extensions to `K P` and `C_K(P) P`;
* a `p`-complement `M` in `N_G(P)` and a subgroup `U` with `M / U`
  cyclic;
* the subgroup-compatible Glauberman theorem, Isaacs Theorem 13.29, in
  the centralizer branch;
* cyclic extension and Isaacs, Corollary 11.31; and
* two strictly smaller normalizer problems in the other branch.

The repository already contains the determinant-normalized extensions,
the ordinary Glauberman correspondence, cyclic extension, Gallagher
twists, the elementary complement constructions, the exact boundary for
Theorem 13.29 together with its proof, and the corrected
invariant-subfibre cardinality squeeze.  The resulting full-fixed branch
does not need Theorem 13.28.  The proper-branch recursive extension chain
is also formalized, but the complete subgroup-coordinate construction and
strong-induction assembly used on pp. 803--804 are still being connected.
This file therefore does not yet assert the printed theorem.

Instead it records three useful, source-faithful milestones.

1. The product hypothesis `G = K N_G(P)` makes `K P` normal.  This is
   proved below from the exact quotient-normalizer API.
2. The local scope already forces the displayed subgroup `W` to normalize
   `Q`; this removes an otherwise hidden hypothesis from every subsequent
   construction.
3. The shorter projective reformulation has one precise missing input:
   the canonical Glauberman multiplicity mismatch must be `p`-primary.
   Once supplied, the existing determinant calculation kills its `H²`
   class.  This is a genuine representation-theoretic milestone, but it is
   deliberately not identified with the full printed induction theorem.

Finally, an adapter shows that the already existing factor-matching input
would imply the printed extension conclusion on every local scope.  This
last result is only an alternate stronger route; it is not used to relabel
factor matching as Okuyama--Wajima, Theorem 2(3).
-/

noncomputable section

namespace McKayConjecture

open CharacterTriple
open GroupTheory

/-! ## The normal product in the printed scope -/

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- The Frattini product hypothesis in the printed theorem makes the
normal product `K P` normal.

Indeed, after quotienting by `K`, the image of `N_G(P)` is the full
normalizer of the image Sylow subgroup.  The product hypothesis makes
that image normalizer equal to the whole quotient. -/
theorem normal_sup_sylow_normal_of_sup_normalizer_eq_top
    (K : Subgroup G) [K.Normal]
    (P : Sylow p G)
    (hproduct :
      K ⊔ Subgroup.normalizer ((P : Subgroup G) : Set G) = ⊤) :
    (K ⊔ (P : Subgroup G)).Normal := by
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  have hmap :
      (Subgroup.normalizer ((P : Subgroup G) : Set G)).map q =
        ⊤ := by
    have h :=
      congrArg (Subgroup.map q) hproduct
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self,
      bot_sup_eq,
      Subgroup.map_top_of_surjective q
        (QuotientGroup.mk'_surjective K)] at h
    exact h
  have hnormalizerMap :
      Subgroup.normalizer
          (Sylow.mapQuotient P K : Set (G ⧸ K)) =
        ⊤ := by
    calc
      Subgroup.normalizer
            (Sylow.mapQuotient P K : Set (G ⧸ K)) =
          (Subgroup.normalizer
            ((P : Subgroup G) : Set G)).map
              (QuotientGroup.mk' K) :=
        (Sylow.map_normalizer_eq_normalizer_mapQuotient
          P K).symm
      _ = ⊤ := by simpa [q] using hmap
  have hPbarNormal :
      (Sylow.mapQuotient P K :
        Subgroup (G ⧸ K)).Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    exact hnormalizerMap
  exact
    (normalProductQuotientSylow_normal_iff K P).mp
      hPbarNormal

/-! ## Consequences of `InvariantOkuyamaWajimaPrintedLocalScope` -/

variable {A : Type} [Group A] [Finite A]
variable (K Q W : Subgroup A) [K.Normal]

omit [Finite A] [Fact p.Prime] [K.Normal] in
/-- A displayed local scope forces `W ≤ N_A(Q)`.  Thus normalizer
containment need not be added to the printed-theorem input. -/
theorem InvariantOkuyamaWajimaPrintedLocalScope.subgroup_le_normalizer
    (scope :
      InvariantOkuyamaWajimaPrintedLocalScope
        (p := p) K Q W) :
    W ≤ Subgroup.normalizer (Q : Set A) := by
  let L : Subgroup A := K ⊔ (Q ⊔ W)
  have hQL : Q ≤ L :=
    le_sup_left.trans le_sup_right
  have hinternal :
      Subgroup.normalizer
          ((Q.subgroupOf L : Subgroup L) : Set L) =
        (Q ⊔ W).subgroupOf L := by
    rw [← scope.sylow_eq]
    exact scope.normalizer_eq
  intro w hw
  let x : L :=
    ⟨w,
      (show W ≤ K ⊔ (Q ⊔ W) from
        le_sup_right.trans le_sup_right) hw⟩
  have hxRight :
      x ∈ (Q ⊔ W).subgroupOf L :=
    (show W ≤ Q ⊔ W from le_sup_right) hw
  have hxInternal :
      x ∈ Subgroup.normalizer
        ((Q.subgroupOf L : Subgroup L) : Set L) := by
    rw [hinternal]
    exact hxRight
  have hnormalizerCopy :
      (Subgroup.normalizer (Q : Set A)).subgroupOf L =
        Subgroup.normalizer
          ((Q.subgroupOf L : Subgroup L) : Set L) :=
    Subgroup.subgroupOf_normalizer_eq hQL
  have hxCopy :
      x ∈ (Subgroup.normalizer (Q : Set A)).subgroupOf L := by
    rw [hnormalizerCopy]
    exact hxInternal
  exact hxCopy

omit [Finite A] [Fact p.Prime] [K.Normal] in
/-- The whole displayed Sylow normalizer `Q W` normalizes `Q`. -/
theorem InvariantOkuyamaWajimaPrintedLocalScope.sup_le_normalizer
    (scope :
      InvariantOkuyamaWajimaPrintedLocalScope
        (p := p) K Q W) :
    Q ⊔ W ≤ Subgroup.normalizer (Q : Set A) :=
  sup_le Subgroup.le_normalizer
    scope.subgroup_le_normalizer

/-- Internally to the local group `K(QW)`, the normal product `KQ` is
normal.  This supplies the normality premise used by the canonical
determinant-normalized base-extension construction. -/
theorem InvariantOkuyamaWajimaPrintedLocalScope.normalProduct_normal
    (scope :
      InvariantOkuyamaWajimaPrintedLocalScope
        (p := p) K Q W) :
    ((K ⊔ Q).subgroupOf
      (K ⊔ (Q ⊔ W) : Subgroup A)).Normal := by
  let L : Subgroup A := K ⊔ (Q ⊔ W)
  let K₀ : Subgroup L := K.subgroupOf L
  have hK₀ : K₀.Normal :=
    (inferInstance : K.Normal).subgroupOf L
  letI : K₀.Normal := hK₀
  have hnormal :
      (K₀ ⊔
        (scope.sylow : Subgroup L)).Normal :=
    normal_sup_sylow_normal_of_sup_normalizer_eq_top
      K₀ scope.sylow scope.product_eq_top
  have hsubgroup :
      K₀ ⊔ (scope.sylow : Subgroup L) =
        (K ⊔ Q).subgroupOf L := by
    rw [scope.sylow_eq, ← Subgroup.subgroupOf_sup
      (show K ≤ L from le_sup_left)
      (show Q ≤ L from le_sup_left.trans le_sup_right)]
  rw [hsubgroup] at hnormal
  exact hnormal

/-! ## The precise projective multiplicity seam -/

/-- Conjugation by a subgroup `U` on the normal `p'`-kernel `K`. -/
def okuyamaWajimaKernelConjugationAction
    (K U : Subgroup A) [K.Normal] :
    U →* MulAut K :=
  (MulAut.conjNormal (H := K)).comp U.subtype

/-- Conjugation by `U ≤ N_A(Q)` on `C_K(Q)`. -/
def okuyamaWajimaFixedPointConjugationAction
    (K Q U : Subgroup A) [K.Normal]
    (hU : U ≤ Subgroup.normalizer (Q : Set A)) :
    U →* MulAut (coprimeFixedPoints K Q) :=
  (coprimeFixedPoints K Q).normalizerMonoidHom.comp
    (Subgroup.inclusion
      (hU.trans
        (normalizer_le_normalizer_coprimeFixedPoints K Q)))

omit [Finite A] [Fact p.Prime] in
/-- The two conjugation actions commute with the fixed-point inclusion. -/
theorem okuyamaWajimaConjugationActions_compatible
    (K Q U : Subgroup A) [K.Normal]
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (u : U) (x : coprimeFixedPoints K Q) :
    coprimeFixedPointsInclusion K Q
        (okuyamaWajimaFixedPointConjugationAction
          K Q U hU u x) =
      okuyamaWajimaKernelConjugationAction K U u
        (coprimeFixedPointsInclusion K Q x) := by
  apply Subtype.ext
  rfl

omit [Finite A] [Fact p.Prime] in
/-- Ambient invariance gives invariance for the restricted kernel
conjugation action. -/
theorem okuyamaWajimaKernelConjugationAction_invariant
    (K Q U : Subgroup A) [K.Normal]
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) :
    IsInvariant
      (okuyamaWajimaKernelConjugationAction K U)
      theta.1.1 := by
  intro u x
  have hfixed := hinvariant (u : A)⁻¹
  have hvalue :=
    congrArg
      (fun chi : IrreducibleCharacter K ↦ chi.values x)
      hfixed
  rw [IrreducibleCharacter.conjBy_values] at hvalue
  convert hvalue using 1
  apply congrArg theta.1.1.values
  apply Subtype.ext
  simp only [okuyamaWajimaKernelConjugationAction,
    MonoidHom.comp_apply, Subgroup.coe_subtype,
    MulAut.conjNormal_apply, MulAut.conjNormal_symm_apply, inv_inv]

/-- Equivariance of the Glauberman correspondence gives invariance of
the correspondent for the restricted fixed-point action. -/
theorem okuyamaWajimaFixedPointConjugationAction_invariant
    (K Q U : Subgroup A) [K.Normal]
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) :
    IsInvariant
      (okuyamaWajimaFixedPointConjugationAction K Q U hU)
      (d.characterEquiv theta).1 := by
  intro u x
  have hfixed :=
    okuyamaWajimaTargetInvariant K Q U hU d theta
      hinvariant u⁻¹
  have hvalue :=
    congrArg
      (fun chi : IrreducibleCharacter
          (coprimeFixedPoints K Q) ↦ chi.values x)
      hfixed
  rw [IrreducibleCharacter.smul_values] at hvalue
  convert hvalue using 1
  apply congrArg (d.characterEquiv theta).1.values
  apply Subtype.ext
  rw [coprimeFixedPointsNormalizerAction_symm_apply_coe]
  simp only [Subgroup.coe_inv, inv_inv]
  rfl

/-- A precise stronger representation-theoretic input for the optional
obstruction route: the canonical Glauberman multiplicity mismatch for the
normalizing subgroup `U` is `p`-primary.

This is strictly a named missing input.  The current repository does not
derive it from the centralizer dichotomy and normalizer induction on
pp. 803--804, and that induction proves extension equivalence directly
rather than this obstruction-class statement. -/
def InvariantOkuyamaWajimaPrintedProjectiveMultiplicityPPrimary
    (K Q U : Subgroup A) [K.Normal]
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) : Prop :=
  GlaubermanCorrespondence.ProjectiveMultiplicityMismatchIsPPrimary
    (okuyamaWajimaKernelConjugationAction K U)
    (okuyamaWajimaFixedPointConjugationAction K Q U hU)
    d theta
    (okuyamaWajimaKernelConjugationAction_invariant
      K Q U theta hinvariant)
    (okuyamaWajimaFixedPointConjugationAction_invariant
      K Q U hU d theta hinvariant)

/-- Once the missing `p`-primary statement is supplied, the existing
Glauberman multiplicity determinant argument kills the canonical mismatch
class. -/
theorem okuyamaWajimaPrintedProjectiveMultiplicityFactorSet_h2Class_eq_zero
    (K Q U : Subgroup A) [K.Normal]
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hprimary :
      InvariantOkuyamaWajimaPrintedProjectiveMultiplicityPPrimary
        K Q U hU d theta hinvariant) :
    letI := trivialMulDistribMulAction U ℂˣ
    (GlaubermanCorrespondence.ProjectiveMultiplicityFactorSet
      (okuyamaWajimaKernelConjugationAction K U)
      (okuyamaWajimaFixedPointConjugationAction K Q U hU)
      d theta
      (okuyamaWajimaKernelConjugationAction_invariant
        K Q U theta hinvariant)
      (okuyamaWajimaFixedPointConjugationAction_invariant
        K Q U hU d theta hinvariant)).h2Class =
      0 := by
  exact
    d.projectiveMultiplicityFactorSet_h2Class_eq_zero_of_pPrimary
        (okuyamaWajimaKernelConjugationAction K U)
        (okuyamaWajimaFixedPointConjugationAction K Q U hU)
        (okuyamaWajimaConjugationActions_compatible
          K Q U hU)
        theta
        (okuyamaWajimaKernelConjugationAction_invariant
          K Q U theta hinvariant)
        (okuyamaWajimaFixedPointConjugationAction_invariant
          K Q U hU d theta hinvariant)
        hprimary

/-! ## Honest adapter through the existing factor-matching API -/

/-- Literal factor matching on every printed local scope implies the
printed extension input.

This is an adapter around the already named projective comparison input;
it does not assert that the induction in the 1980 paper supplies literal
factor matching. -/
theorem invariantOkuyamaWajimaPrintedExtensionTheoremInput_of_factorMatching
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hmatching :
      ∀ (W : Subgroup A)
          (hCW : coprimeFixedPoints K Q ≤ W)
          (scope :
            InvariantOkuyamaWajimaPrintedLocalScope
              (p := p) K Q W),
        invariantOkuyamaWajimaFactorMatchingInput
          K Q (Q ⊔ W)
          scope.sup_le_normalizer
          (hCW.trans le_sup_right)
          d theta hinvariant) :
    InvariantOkuyamaWajimaPrintedExtensionTheoremInput
      K Q hQ hK d theta hinvariant := by
  intro W hCW scope
  exact
    okuyamaWajimaExtensionConclusion_of_factorMatching
      K Q (Q ⊔ W) hQ hK
      scope.sup_le_normalizer
      (hCW.trans le_sup_right)
      d theta hinvariant
      (hmatching W hCW scope)

end McKayConjecture
