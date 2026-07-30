/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanEquivariance
import McKayConjecture.CharacterTriple.FactorMatchedExtension
import McKayConjecture.CharacterTriple.NormalHallPPrimeExtension
import McKayConjecture.CharacterTriple.SubgroupRestriction
import McKayConjecture.GroupTheory.OkuyamaWajimaQuotient
import McKayConjecture.InductiveMcKay.CentralTripleFactorMatchedCharacterEquiv
import Mathlib.GroupTheory.Commutator.Basic

/-!
# Factor-matched reduction of the Okuyama--Wajima extension theorem

Let `K` be a normal `p'`-subgroup, let `Q` be a `p`-subgroup, put
`C = C_K(Q)`, and suppose `C ≤ U ≤ N_A(Q)`.  For an ambient-invariant
irreducible character `theta` of `K`, this file constructs the two character
triples

* `(UK, K, theta)`, and
* `(U, C, theta*)`,

where `theta*` is the Glauberman correspondent.  The canonical embedding
`U → UK` satisfies all three ordinary subgroup conditions needed by the
factor-matched character correspondence.  Consequently, factor-matched
projective lifts immediately imply the Okuyama--Wajima equivalence between
extension existence on the two sides.

The remaining input is deliberately exposed as
`invariantOkuyamaWajimaFactorMatchingInput`.  Proving that input from
normality of `KQ` and commutativity of `U/C` is the substantive
Okuyama--Wajima argument; it is not asserted in this file.
-/

noncomputable section

namespace McKayConjecture

open CharacterTriple
open GroupTheory

variable {A : Type} [Group A] [Finite A]
variable {p : ℕ} [Fact p.Prime]
variable (K Q U : Subgroup A) [K.Normal]

/-- The extension-existence conclusion of the ordinary Okuyama--Wajima
argument, written using the canonical copies of `K` and `C_K(Q)`. -/
def okuyamaWajimaExtensionConclusion
    (hCU : coprimeFixedPoints K Q ≤ U)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p) : Prop :=
  (∃ psi : IrreducibleCharacter (U ⊔ K : Subgroup A),
      IrreducibleCharacter.IsExtensionAlong
        (Subgroup.inclusion le_sup_right)
        theta.1.1 psi) ↔
    ∃ phi : IrreducibleCharacter U,
      IrreducibleCharacter.IsExtensionAlong
        (Subgroup.inclusion hCU)
        (d.characterEquiv theta).1 phi

/-- Ambient invariance of a source character implies invariance of its
Glauberman correspondent under every element of `U ≤ N_A(Q)`. -/
theorem okuyamaWajimaTargetInvariant
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (u : U) :
    coprimeFixedPointsNormalizerAction K Q
        ⟨u, hU u.2⟩ • (d.characterEquiv theta).1 =
      (d.characterEquiv theta).1 := by
  let g : Subgroup.normalizer (Q : Set A) :=
    ⟨u, hU u.2⟩
  have hsource :
      invariantCharacterConjByNormalizer K Q g theta =
        theta := by
    apply Subtype.ext
    apply Subtype.ext
    exact hinvariant (u : A)
  have hcovariance :=
    d.characterEquiv_conjByNormalizer K Q g theta
  rw [hsource] at hcovariance
  exact congrArg Subtype.val hcovariance.symm

omit [Finite A] in
/-- The inverse fixed-point normalizer action is ambient conjugation by the
inverse normalizer element. -/
theorem coprimeFixedPointsNormalizerAction_symm_apply_coe
    (g : Subgroup.normalizer (Q : Set A))
    (x : coprimeFixedPoints K Q) :
    ((coprimeFixedPointsNormalizerAction K Q g).symm x : A) =
      (g : A)⁻¹ * (x : A) * (g : A) := by
  let y :=
    (coprimeFixedPointsNormalizerAction K Q g).symm x
  have h :=
    coprimeFixedPointsNormalizerAction_apply_coe K Q g y
  have hy :
      coprimeFixedPointsNormalizerAction K Q g y = x :=
    MulEquiv.apply_symm_apply
      (coprimeFixedPointsNormalizerAction K Q g) x
  have hycoe :=
    congrArg
      (fun z : coprimeFixedPoints K Q => (z : A)) hy
  change (y : A) = _
  calc
    (y : A) =
        (g : A)⁻¹ *
            ((g : A) * (y : A) * (g : A)⁻¹) *
          (g : A) := by group
    _ = (g : A)⁻¹ * (x : A) * (g : A) := by
      rw [← h, hycoe]

/-- The source character triple `(UK, K, theta)` in canonical subgroup
coordinates. -/
def invariantOkuyamaWajimaSourceTriple
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) :
    CharacterTriple (U ⊔ K : Subgroup A) := by
  have hinertia :
      IrreducibleCharacter.inertia K theta.1.1 = ⊤ := by
    apply top_unique
    intro a _ha
    rw [IrreducibleCharacter.mem_inertia_iff]
    exact hinvariant a
  exact
    (CharacterTriple.ofInertiaTop K theta.1.1 hinertia).restrictTo
      (U ⊔ K : Subgroup A) le_sup_right

/-- The target character triple `(U, C_K(Q), theta*)` in canonical subgroup
coordinates. -/
def invariantOkuyamaWajimaTargetTriple
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (hCU : coprimeFixedPoints K Q ≤ U)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) :
    CharacterTriple U where
  normalSubgroup :=
    (coprimeFixedPoints K Q).subgroupOf U
  isNormal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (hU.trans
        (normalizer_le_normalizer_inf_centralizer K Q))
  character :=
    (d.characterEquiv theta).1.comap
      (Subgroup.subgroupOfEquivOfLe hCU)
  isInvariant := by
    intro u x
    let g : Subgroup.normalizer (Q : Set A) :=
      ⟨(u : A)⁻¹, hU (U.inv_mem u.2)⟩
    have hfixed :=
      okuyamaWajimaTargetInvariant K Q U hU d theta
        hinvariant (u⁻¹)
    have hvalue :=
      congrArg
        (fun chi : IrreducibleCharacter (coprimeFixedPoints K Q) =>
          chi.values (Subgroup.subgroupOfEquivOfLe hCU x))
        hfixed
    rw [IrreducibleCharacter.smul_values] at hvalue
    change
      (d.characterEquiv theta).1.values
          (Subgroup.subgroupOfEquivOfLe hCU
            (conjugateNormalElement
              ((coprimeFixedPoints K Q).subgroupOf U)
              _ u x)) =
        (d.characterEquiv theta).1.values
          (Subgroup.subgroupOfEquivOfLe hCU x)
    convert hvalue using 1
    apply congrArg (d.characterEquiv theta).1.values
    apply Subtype.ext
    rw [coprimeFixedPointsNormalizerAction_symm_apply_coe]
    simp only [Subgroup.coe_inv, inv_inv]
    rfl

omit [Finite A] in
/-- Replace an extension along `N → B` by the same extension along the
canonical internal copy `N.subgroupOf B → B`. -/
theorem exists_extensionAlong_inclusion_iff_subgroupOf
    (N B : Subgroup A)
    (hNB : N ≤ B)
    (chi : IrreducibleCharacter N) :
    (∃ psi : IrreducibleCharacter B,
        IrreducibleCharacter.IsExtensionAlong
          (Subgroup.inclusion hNB) chi psi) ↔
      ∃ psi : IrreducibleCharacter B,
        IrreducibleCharacter.IsExtensionAlong
          (N.subgroupOf B).subtype
          (chi.comap (Subgroup.subgroupOfEquivOfLe hNB))
          psi := by
  constructor
  · rintro ⟨psi, hpsi⟩
    refine ⟨psi, ?_⟩
    intro x
    exact hpsi (Subgroup.subgroupOfEquivOfLe hNB x)
  · rintro ⟨psi, hpsi⟩
    refine ⟨psi, ?_⟩
    intro n
    let b : B := ⟨n, hNB n.2⟩
    let x : N.subgroupOf B := ⟨b, n.2⟩
    exact hpsi x

/-- The canonical embedding `U → UK` satisfies the ordinary product and
intersection hypotheses for the factor-matched character correspondence.
No centralizer-containment hypothesis is needed. -/
theorem invariantOkuyamaWajimaFactorMatchedGroupData
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (hCU : coprimeFixedPoints K Q ≤ U)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) :
    InductiveMcKay.FactorMatchedRestrictionGroupData
      (invariantOkuyamaWajimaSourceTriple
        K Q U theta hinvariant)
      (invariantOkuyamaWajimaTargetTriple
        K Q U hU hCU d theta hinvariant)
      (Subgroup.inclusion le_sup_left) where
  embedding_injective :=
    Subgroup.inclusion_injective le_sup_left
  ambient_eq_product := by
    intro a
    have ha : (a : A) ∈ K ⊔ U := by
      simpa only [sup_comm] using a.2
    obtain ⟨k, hk, u, hu, hku⟩ :=
      Subgroup.mem_sup_of_normal_left.mp ha
    let x :
        (invariantOkuyamaWajimaSourceTriple
          K Q U theta hinvariant).normalSubgroup :=
      ⟨⟨k, Subgroup.mem_sup_right hk⟩, hk⟩
    let y : U := ⟨u, hu⟩
    exact ⟨x, y, Subtype.ext hku⟩
  intersection_eq := by
    change
      K.subgroupOf (U ⊔ K) ⊓
          MonoidHom.range (Subgroup.inclusion le_sup_left) =
        ((coprimeFixedPoints K Q).subgroupOf U).map
          (Subgroup.inclusion le_sup_left)
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf,
      MonoidHom.mem_range, Subgroup.mem_map]
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨hxK, u, rfl⟩
      have huK : (u : A) ∈ K := hxK
      have huC :
          (u : A) ∈ coprimeFixedPoints K Q := by
        change
          (u : A) ∈
            K ⊓ Subgroup.centralizer (Q : Set A)
        rw [← pPrimeKernel_inf_eq_fixedPoints
          K Q hQ hK U hU hCU]
        exact ⟨huK, u.2⟩
      exact ⟨u, huC, rfl⟩
    · rintro ⟨c, hcC, hcx⟩
      constructor
      · rw [← hcx]
        exact hcC.1
      · exact ⟨c, hcx⟩

/-- The exact remaining representation-theoretic input: associated
projective lifts for the two canonical triples whose factor sets agree on
the canonical copy of `U`.

This proposition does not assert that the input exists. -/
def invariantOkuyamaWajimaFactorMatchingInput
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (hCU : coprimeFixedPoints K Q ≤ U)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) : Prop :=
  Nonempty
    (InductiveMcKay.CompleteFactorMatchedProjectiveComparisonData
      (invariantOkuyamaWajimaSourceTriple
        K Q U theta hinvariant)
      (invariantOkuyamaWajimaTargetTriple
        K Q U hU hCU d theta hinvariant)
      (Subgroup.inclusion le_sup_left))

/-- Formal statement of the still-missing abelian-quotient
Okuyama--Wajima projective comparison. -/
def InvariantOkuyamaWajimaAbelianQuotientFactorMatching
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (hCU : coprimeFixedPoints K Q ≤ U)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) : Prop :=
  (K ⊔ Q).Normal →
    _root_.commutator U ≤
      (coprimeFixedPoints K Q).subgroupOf U →
    invariantOkuyamaWajimaFactorMatchingInput
      K Q U hU hCU d theta hinvariant

/-- Factor-matched projective lifts imply the desired extension
equivalence. -/
theorem okuyamaWajimaExtensionConclusion_of_factorMatching
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (hCU : coprimeFixedPoints K Q ≤ U)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hmatching :
      invariantOkuyamaWajimaFactorMatchingInput
        K Q U hU hCU d theta hinvariant) :
    okuyamaWajimaExtensionConclusion
      K Q U hCU d theta := by
  rw [okuyamaWajimaExtensionConclusion]
  rw [exists_extensionAlong_inclusion_iff_subgroupOf]
  rw [exists_extensionAlong_inclusion_iff_subgroupOf]
  let S :=
    invariantOkuyamaWajimaSourceTriple
      K Q U theta hinvariant
  let T :=
    invariantOkuyamaWajimaTargetTriple
      K Q U hU hCU d theta hinvariant
  change
    (∃ psi : IrreducibleCharacter (U ⊔ K : Subgroup A),
      IrreducibleCharacter.IsExtensionAlong
        S.normalSubgroup.subtype S.character psi) ↔
    ∃ phi : IrreducibleCharacter U,
      IrreducibleCharacter.IsExtensionAlong
        T.normalSubgroup.subtype T.character phi
  obtain ⟨D⟩ := hmatching
  let C :=
    D.toCompleteFactorMatchedIsomorphismWitness
      (invariantOkuyamaWajimaFactorMatchedGroupData
        K Q U hQ hK hU hCU d theta hinvariant)
  letI := C.leftAddCommGroup
  letI := C.leftModule
  letI := C.leftModuleFinite
  letI := C.leftNontrivial
  letI := C.rightAddCommGroup
  letI := C.rightModule
  letI := C.rightModuleFinite
  letI := C.rightNontrivial
  exact C.witness.exists_extension_iff

/-- The named missing abelian-quotient factor-matching proposition is
exactly sufficient for the invariant Okuyama--Wajima extension
conclusion. -/
theorem okuyamaWajimaExtensionConclusion_of_abelianQuotientFactorMatching
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (hKQ : (K ⊔ Q).Normal)
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (hCU : coprimeFixedPoints K Q ≤ U)
    (habelian :
      _root_.commutator U ≤
        (coprimeFixedPoints K Q).subgroupOf U)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (how :
      InvariantOkuyamaWajimaAbelianQuotientFactorMatching
        K Q U hU hCU d theta hinvariant) :
    okuyamaWajimaExtensionConclusion
      K Q U hCU d theta :=
  okuyamaWajimaExtensionConclusion_of_factorMatching
    K Q U hQ hK hU hCU d theta hinvariant
    (how hKQ habelian)

end McKayConjecture
