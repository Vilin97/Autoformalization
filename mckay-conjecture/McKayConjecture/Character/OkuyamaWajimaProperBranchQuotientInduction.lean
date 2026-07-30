/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.OkuyamaWajimaPrintedInduction

/-!
# The quotient induction adapter in the proper Okuyama--Wajima branch

This file constructs the literal character coordinates for the first
recursive call in the proper branch.  Put

* `X = N_G(Q)`;
* `Q_X` for the copy of `Q` in `X`;
* `J_X` for the copy of `J = C_K(Q)` in `X`;
* `Xbar = X / Q_X`;
* `Jbar` for the image of `J_X` in `Xbar`; and
* `Pbar = P / Q`.

The quotient map is injective on `J_X`, since `J ≤ K`, `Q ≤ P`, and the
`p`-group `P` is disjoint from the `p'`-group `K`.  Thus the intermediate
Glauberman character `psi` transports canonically to `Jbar`.

The final adapter theorem below isolates only the two extension-coordinate
comparisons across the quotient map.  All group-theoretic hypotheses of the
recursive printed statement, and its source character, are constructed here.
-/

noncomputable section

namespace McKayConjecture

open CharacterTriple
open GroupTheory
open scoped commutatorElement

namespace CharacterTriple

variable {A : Type} [Group A] [Finite A]

/-- The character of a character triple has full ambient inertia. -/
theorem inertia_character_eq_top (T : CharacterTriple A) :
    IrreducibleCharacter.inertia T.normalSubgroup T.character = ⊤ := by
  apply top_unique
  intro a _ha
  rw [IrreducibleCharacter.mem_inertia_iff]
  apply IrreducibleCharacter.ext
  funext x
  rw [IrreducibleCharacter.conjBy_values]
  have hvalue := T.isInvariant a⁻¹ x
  convert hvalue using 1
  apply congrArg T.character.values
  apply Subtype.ext
  simp [conjugateNormalElement]

end CharacterTriple

section QuotientCoordinates

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (K : Subgroup G) [K.Normal]
variable (P : Sylow p G)
variable (Q : Subgroup P) [Q.Normal]

local instance properBranchQuotientPConjugationAction :
    MulDistribMulAction P K :=
  subgroupConjugationMulDistribMulAction K (P : Subgroup G)

variable
  (theta :
    PInvariantPPrimeIrreducibleCharacter
      K (P : Subgroup G) p)
  (hinvariant :
    ∀ g : G, g • theta.1.1 = theta.1.1)
  (gQ :
    GlaubermanCorrespondence K
      (okuyamaWajimaProperBranchQ P Q) p)

/-- The ambient group `X = N_G(Q)` of the first recursive call. -/
abbrev okuyamaWajimaProperBranchQuotientAmbient :=
  okuyamaWajimaProperBranchQNormalizer P Q

/-- The quotient kernel `Q_X ◁ X`. -/
abbrev okuyamaWajimaProperBranchQuotientKernel :
    Subgroup (okuyamaWajimaProperBranchQuotientAmbient P Q) :=
  okuyamaWajimaProperBranchQInNormalizer P Q

/-- The intermediate `p'`-kernel `J_X = C_K(Q)` inside `X`. -/
abbrev okuyamaWajimaProperBranchQuotientSourceKernel :
    Subgroup (okuyamaWajimaProperBranchQuotientAmbient P Q) :=
  (okuyamaWajimaProperBranchPsiNormalizerTriple
    K P Q theta hinvariant gQ).normalSubgroup

/-- The quotient map `X → X / Q_X`. -/
abbrev okuyamaWajimaProperBranchQuotientMap :
    okuyamaWajimaProperBranchQuotientAmbient P Q →*
      okuyamaWajimaProperBranchNormalizerQuotient P Q :=
  QuotientGroup.mk'
    (okuyamaWajimaProperBranchQuotientKernel P Q)

/-- The literal normal `p'`-kernel `Jbar ≤ X / Q_X`. -/
abbrev okuyamaWajimaProperBranchQuotientImageKernel :
    Subgroup (okuyamaWajimaProperBranchNormalizerQuotient P Q) :=
  (okuyamaWajimaProperBranchQuotientSourceKernel
      K P Q theta hinvariant gQ).map
    (okuyamaWajimaProperBranchQuotientMap P Q)

omit [Q.Normal] in
/-- The quotient map is injective on `J_X`.

This is the exact coprime intersection argument `J_X ∩ Q_X = 1`. -/
theorem okuyamaWajimaProperBranchQuotientMap_injective_on_sourceKernel
    (hK : IsPPrimeGroup p K) :
    Function.Injective
      ((okuyamaWajimaProperBranchQuotientMap P Q).domRestrict
        (okuyamaWajimaProperBranchQuotientSourceKernel
          K P Q theta hinvariant gQ)) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  change
    okuyamaWajimaProperBranchQuotientMap P Q
        (x : okuyamaWajimaProperBranchQuotientAmbient P Q) =
      okuyamaWajimaProperBranchQuotientMap P Q
        (y : okuyamaWajimaProperBranchQuotientAmbient P Q) at hxy
  have hquot :
      okuyamaWajimaProperBranchQuotientMap P Q
          ((x : okuyamaWajimaProperBranchQuotientAmbient P Q) *
            (y : okuyamaWajimaProperBranchQuotientAmbient P Q)⁻¹) =
        1 := by
    rw [map_mul, map_inv, hxy]
    simp
  have hQ :
      (((x : okuyamaWajimaProperBranchQuotientSourceKernel
            K P Q theta hinvariant gQ) :
          okuyamaWajimaProperBranchQuotientAmbient P Q) : G) *
          (((y : okuyamaWajimaProperBranchQuotientSourceKernel
              K P Q theta hinvariant gQ) :
            okuyamaWajimaProperBranchQuotientAmbient P Q) : G)⁻¹ ∈
        okuyamaWajimaProperBranchQ P Q := by
    exact
      (QuotientGroup.eq_one_iff
        (N := okuyamaWajimaProperBranchQuotientKernel P Q)
        ((x : okuyamaWajimaProperBranchQuotientAmbient P Q) *
          (y : okuyamaWajimaProperBranchQuotientAmbient P Q)⁻¹)).mp
        hquot
  have hP :
      (((x : okuyamaWajimaProperBranchQuotientSourceKernel
            K P Q theta hinvariant gQ) :
          okuyamaWajimaProperBranchQuotientAmbient P Q) : G) *
          (((y : okuyamaWajimaProperBranchQuotientSourceKernel
              K P Q theta hinvariant gQ) :
            okuyamaWajimaProperBranchQuotientAmbient P Q) : G)⁻¹ ∈
        (P : Subgroup G) :=
    okuyamaWajimaProperBranchAmbientQ_le_P
      (P : Subgroup G) Q hQ
  have hKmem :
      (((x : okuyamaWajimaProperBranchQuotientSourceKernel
            K P Q theta hinvariant gQ) :
          okuyamaWajimaProperBranchQuotientAmbient P Q) : G) *
          (((y : okuyamaWajimaProperBranchQuotientSourceKernel
              K P Q theta hinvariant gQ) :
            okuyamaWajimaProperBranchQuotientAmbient P Q) : G)⁻¹ ∈
        K := by
    exact (x * y⁻¹).property.1
  have hdisjoint :
      Disjoint (P : Subgroup G) K :=
    IsPGroup.disjoint_of_isPPrimeGroup P.isPGroup' hK
  have hone :
      (((x : okuyamaWajimaProperBranchQuotientSourceKernel
            K P Q theta hinvariant gQ) :
          okuyamaWajimaProperBranchQuotientAmbient P Q) : G) *
          (((y : okuyamaWajimaProperBranchQuotientSourceKernel
              K P Q theta hinvariant gQ) :
            okuyamaWajimaProperBranchQuotientAmbient P Q) : G)⁻¹ =
        1 := by
    exact
      (Subgroup.mem_bot.mp
        (hdisjoint.le_bot ⟨hP, hKmem⟩))
  exact mul_inv_eq_one.mp hone

/-- The quotient map, restricted and corestricted from `J_X` to `Jbar`. -/
def okuyamaWajimaProperBranchQuotientSourceKernelHom :
    okuyamaWajimaProperBranchQuotientSourceKernel
        K P Q theta hinvariant gQ →*
      okuyamaWajimaProperBranchQuotientImageKernel
        K P Q theta hinvariant gQ :=
  ((okuyamaWajimaProperBranchQuotientMap P Q).domRestrict
      (okuyamaWajimaProperBranchQuotientSourceKernel
        K P Q theta hinvariant gQ)).codRestrict
    (okuyamaWajimaProperBranchQuotientImageKernel
      K P Q theta hinvariant gQ)
    (fun x ↦ ⟨x, x.property, rfl⟩)

omit [Q.Normal] in
/-- The restricted quotient map is surjective onto its literal image. -/
theorem okuyamaWajimaProperBranchQuotientSourceKernelHom_surjective :
    Function.Surjective
      (okuyamaWajimaProperBranchQuotientSourceKernelHom
        K P Q theta hinvariant gQ) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := y.property
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  exact hxy

/-- Canonical identification `J_X ≃ Jbar`. -/
def okuyamaWajimaProperBranchQuotientSourceKernelEquiv
    (hK : IsPPrimeGroup p K) :
    okuyamaWajimaProperBranchQuotientSourceKernel
        K P Q theta hinvariant gQ ≃*
      okuyamaWajimaProperBranchQuotientImageKernel
        K P Q theta hinvariant gQ :=
  MulEquiv.ofBijective
    (okuyamaWajimaProperBranchQuotientSourceKernelHom
      K P Q theta hinvariant gQ)
    ⟨fun x y hxy ↦
        okuyamaWajimaProperBranchQuotientMap_injective_on_sourceKernel
          K P Q theta hinvariant gQ hK
          (congrArg Subtype.val hxy),
      okuyamaWajimaProperBranchQuotientSourceKernelHom_surjective
        K P Q theta hinvariant gQ⟩

omit [Q.Normal] in
@[simp]
theorem okuyamaWajimaProperBranchQuotientSourceKernelEquiv_apply_coe
    (hK : IsPPrimeGroup p K)
    (x :
      okuyamaWajimaProperBranchQuotientSourceKernel
        K P Q theta hinvariant gQ) :
    ((okuyamaWajimaProperBranchQuotientSourceKernelEquiv
        K P Q theta hinvariant gQ hK x :
      okuyamaWajimaProperBranchQuotientImageKernel
        K P Q theta hinvariant gQ) :
      okuyamaWajimaProperBranchNormalizerQuotient P Q) =
        okuyamaWajimaProperBranchQuotientMap P Q
          (x : okuyamaWajimaProperBranchQuotientAmbient P Q) :=
  rfl

/-- The intermediate character `psi`, transported to the literal quotient
kernel `Jbar`. -/
def okuyamaWajimaProperBranchQuotientSourceCharacter
    (hK : IsPPrimeGroup p K) :
    PPrimeIrreducibleCharacter
      (okuyamaWajimaProperBranchQuotientImageKernel
        K P Q theta hinvariant gQ) p :=
  IrreducibleCharacter.pPrimeComapEquiv p
    (okuyamaWajimaProperBranchQuotientSourceKernelEquiv
      K P Q theta hinvariant gQ hK).symm
    ⟨(okuyamaWajimaProperBranchPsiNormalizerTriple
        K P Q theta hinvariant gQ).character,
      okuyamaWajimaProperBranchPsiTriple_character_isPPrimeDegree
        K P Q theta hinvariant gQ⟩

/-- The quotient character triple `(Xbar, Jbar, psibar)`.

Invariance is transported directly from the already constructed
`N_G(Q)`-invariant triple. -/
def okuyamaWajimaProperBranchQuotientSourceTriple
    (hK : IsPPrimeGroup p K) :
    CharacterTriple
      (okuyamaWajimaProperBranchNormalizerQuotient P Q) where
  normalSubgroup :=
    okuyamaWajimaProperBranchQuotientImageKernel
      K P Q theta hinvariant gQ
  isNormal := inferInstance
  character :=
    (okuyamaWajimaProperBranchQuotientSourceCharacter
      K P Q theta hinvariant gQ hK).1
  isInvariant := by
    intro a z
    obtain ⟨x, rfl⟩ :=
      QuotientGroup.mk'_surjective
        (okuyamaWajimaProperBranchQuotientKernel P Q) a
    let e :=
      okuyamaWajimaProperBranchQuotientSourceKernelEquiv
        K P Q theta hinvariant gQ hK
    let j :
        okuyamaWajimaProperBranchQuotientSourceKernel
          K P Q theta hinvariant gQ :=
      e.symm z
    have hconj :
        e.symm
            (conjugateNormalElement
              (okuyamaWajimaProperBranchQuotientImageKernel
                K P Q theta hinvariant gQ)
              (by infer_instance)
              (okuyamaWajimaProperBranchQuotientMap P Q x) z) =
          conjugateNormalElement
            (okuyamaWajimaProperBranchQuotientSourceKernel
              K P Q theta hinvariant gQ)
            (okuyamaWajimaProperBranchPsiNormalizerTriple
              K P Q theta hinvariant gQ).isNormal
            x j := by
      apply e.injective
      rw [e.apply_symm_apply]
      apply Subtype.ext
      rw [
        okuyamaWajimaProperBranchQuotientSourceKernelEquiv_apply_coe
          K P Q theta hinvariant gQ hK]
      have hz :
          (z :
              okuyamaWajimaProperBranchNormalizerQuotient P Q) =
            okuyamaWajimaProperBranchQuotientMap P Q
              (j :
                okuyamaWajimaProperBranchQuotientAmbient P Q) := by
        rw [←
          okuyamaWajimaProperBranchQuotientSourceKernelEquiv_apply_coe
            K P Q theta hinvariant gQ hK j]
        exact congrArg Subtype.val (e.apply_symm_apply z).symm
      change
        okuyamaWajimaProperBranchQuotientMap P Q x *
            (z :
              okuyamaWajimaProperBranchNormalizerQuotient P Q) *
            (okuyamaWajimaProperBranchQuotientMap P Q x)⁻¹ =
          okuyamaWajimaProperBranchQuotientMap P Q
            (x * (j :
              okuyamaWajimaProperBranchQuotientAmbient P Q) * x⁻¹)
      rw [map_mul, map_mul, map_inv, hz]
    change
      (okuyamaWajimaProperBranchPsiNormalizerTriple
          K P Q theta hinvariant gQ).character.values
          (e.symm
            (conjugateNormalElement
              (okuyamaWajimaProperBranchQuotientImageKernel
                K P Q theta hinvariant gQ)
              (by infer_instance)
              (okuyamaWajimaProperBranchQuotientMap P Q x) z)) =
        (okuyamaWajimaProperBranchPsiNormalizerTriple
          K P Q theta hinvariant gQ).character.values
          (e.symm z)
    rw [hconj]
    exact
      (okuyamaWajimaProperBranchPsiNormalizerTriple
        K P Q theta hinvariant gQ).isInvariant x j

/-- The quotient source character, bundled with invariance under
`Pbar = P / Q`. -/
def okuyamaWajimaProperBranchQuotientInvariantSourceCharacter
    (hK : IsPPrimeGroup p K) :
    PInvariantPPrimeIrreducibleCharacter
      (okuyamaWajimaProperBranchQuotientImageKernel
        K P Q theta hinvariant gQ)
      (okuyamaWajimaProperBranchQuotientSylow P Q :
        Subgroup
          (okuyamaWajimaProperBranchNormalizerQuotient P Q))
      p := by
  let thetaBar :=
    okuyamaWajimaProperBranchQuotientSourceCharacter
      K P Q theta hinvariant gQ hK
  have hinertia :
      IrreducibleCharacter.inertia
          (okuyamaWajimaProperBranchQuotientImageKernel
            K P Q theta hinvariant gQ)
          thetaBar.1 =
        ⊤ := by
    simpa only [
      okuyamaWajimaProperBranchQuotientSourceTriple]
      using
        (okuyamaWajimaProperBranchQuotientSourceTriple
          K P Q theta hinvariant gQ hK).inertia_character_eq_top
  exact
    ⟨thetaBar, by
      rw [hinertia]
      exact le_top⟩

@[simp]
theorem okuyamaWajimaProperBranchQuotientInvariantSourceCharacter_coe
    (hK : IsPPrimeGroup p K) :
    (okuyamaWajimaProperBranchQuotientInvariantSourceCharacter
        K P Q theta hinvariant gQ hK).1 =
      okuyamaWajimaProperBranchQuotientSourceCharacter
        K P Q theta hinvariant gQ hK := by
  rfl

omit [Q.Normal] in
/-- The literal quotient kernel `Jbar` is a `p'`-group. -/
theorem okuyamaWajimaProperBranchQuotientImageKernel_isPPrime
    (hK : IsPPrimeGroup p K) :
    IsPPrimeGroup p
      (okuyamaWajimaProperBranchQuotientImageKernel
        K P Q theta hinvariant gQ) := by
  exact
    (okuyamaWajimaProperBranchPsiTriple_kernel_isPPrime
      K P Q theta hinvariant gQ hK).of_equiv
      (okuyamaWajimaProperBranchQuotientSourceKernelEquiv
        K P Q theta hinvariant gQ hK)

omit [Finite G] [Fact p.Prime] [Q.Normal] in
/-- The ambient copy of `Q` is a `p`-group. -/
theorem okuyamaWajimaProperBranchAmbientQ_isPGroup :
    IsPGroup p (okuyamaWajimaProperBranchQ P Q) :=
  (P.isPGroup'.to_subgroup Q).map (P : Subgroup G).subtype

/-- An element of `N_G(Q)` which lies in `K P` lies in
`C_K(Q) P`, in the exact internal subgroup coordinates.

The `K`-part of a decomposition `x = k s`, `s ∈ P`, still normalizes
`Q`; coprimality therefore forces it to centralize `Q`. -/
theorem
    okuyamaWajimaProperBranch_mem_sourceKernel_sup_sylow_of_mem_normalProduct
    (hK : IsPPrimeGroup p K)
    (x : okuyamaWajimaProperBranchQuotientAmbient P Q)
    (hx :
      (x : G) ∈ K ⊔ (P : Subgroup G)) :
    x ∈
      okuyamaWajimaProperBranchQuotientSourceKernel
          K P Q theta hinvariant gQ ⊔
        (okuyamaWajimaProperBranchSylowInQNormalizer P Q :
          Subgroup
            (okuyamaWajimaProperBranchQuotientAmbient P Q)) := by
  obtain ⟨k, hkK, s, hsP, hks⟩ :=
    Subgroup.mem_sup_of_normal_left.mp hx
  have hsN :
      s ∈ okuyamaWajimaProperBranchQuotientAmbient P Q :=
    okuyamaWajimaProperBranchP_le_QNormalizer P Q hsP
  have hkEq : k = (x : G) * s⁻¹ := by
    rw [← hks]
    group
  have hkN :
      k ∈ okuyamaWajimaProperBranchQuotientAmbient P Q := by
    rw [hkEq]
    exact
      (okuyamaWajimaProperBranchQuotientAmbient P Q).mul_mem
        x.property
        ((okuyamaWajimaProperBranchQuotientAmbient P Q).inv_mem hsN)
  have hkC :
      k ∈
        Subgroup.centralizer
          (okuyamaWajimaProperBranchQ P Q : Set G) :=
    inf_normalizer_le_centralizer_of_normal_isPPrime
      (p := p)
      (okuyamaWajimaProperBranchQ P Q) K
      (okuyamaWajimaProperBranchAmbientQ_isPGroup P Q)
      hK ⟨hkK, hkN⟩
  let kJ :
      okuyamaWajimaProperBranchQuotientSourceKernel
        K P Q theta hinvariant gQ :=
    ⟨⟨k, hkN⟩, ⟨hkK, hkC⟩⟩
  let sP :
      (okuyamaWajimaProperBranchSylowInQNormalizer P Q :
        Subgroup
          (okuyamaWajimaProperBranchQuotientAmbient P Q)) :=
    ⟨⟨s, hsN⟩, hsP⟩
  letI :
      (okuyamaWajimaProperBranchQuotientSourceKernel
        K P Q theta hinvariant gQ).Normal :=
    (okuyamaWajimaProperBranchPsiNormalizerTriple
      K P Q theta hinvariant gQ).isNormal
  refine
    (Subgroup.mem_sup_of_normal_left
      (s :=
        okuyamaWajimaProperBranchQuotientSourceKernel
          K P Q theta hinvariant gQ)
      (t :=
        (okuyamaWajimaProperBranchSylowInQNormalizer P Q :
          Subgroup
            (okuyamaWajimaProperBranchQuotientAmbient P Q)))).mpr
      ⟨kJ, kJ.property, sP, sP.property, ?_⟩
  apply Subtype.ext
  exact hks

/-- The original commutator condition descends to the exact quotient
normal product `Jbar Pbar`. -/
theorem okuyamaWajimaProperBranchQuotient_commutator_le
    (hK : IsPPrimeGroup p K)
    (hcommutativeQuotient :
      _root_.commutator G ≤ K ⊔ (P : Subgroup G)) :
    _root_.commutator
        (okuyamaWajimaProperBranchNormalizerQuotient P Q) ≤
      okuyamaWajimaProperBranchQuotientImageKernel
          K P Q theta hinvariant gQ ⊔
        (okuyamaWajimaProperBranchQuotientSylow P Q :
          Subgroup
            (okuyamaWajimaProperBranchNormalizerQuotient P Q)) := by
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro a _ha b _hb
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (okuyamaWajimaProperBranchQuotientKernel P Q) a
  obtain ⟨y, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (okuyamaWajimaProperBranchQuotientKernel P Q) b
  rw [← map_commutatorElement]
  let c :
      okuyamaWajimaProperBranchQuotientAmbient P Q :=
    ⁅x, y⁆
  have hcInternalCommutator :
      c ∈ _root_.commutator
        (okuyamaWajimaProperBranchQuotientAmbient P Q) := by
    rw [_root_.commutator_def]
    change
      ⁅x, y⁆ ∈
        ⁅(⊤ :
            Subgroup
              (okuyamaWajimaProperBranchQuotientAmbient P Q)),
          (⊤ :
            Subgroup
              (okuyamaWajimaProperBranchQuotientAmbient P Q))⁆
    exact
      Subgroup.commutator_mem_commutator
        (Subgroup.mem_top x) (Subgroup.mem_top y)
  have hcMap :
      (c : G) ∈
        (_root_.commutator
          (okuyamaWajimaProperBranchQuotientAmbient P Q)).map
            (okuyamaWajimaProperBranchQuotientAmbient P Q).subtype :=
    Subgroup.mem_map_of_mem
      (okuyamaWajimaProperBranchQuotientAmbient P Q).subtype
      hcInternalCommutator
  rw [Subgroup.map_subtype_commutator] at hcMap
  have hcAmbientCommutator :
      (c : G) ∈ _root_.commutator G := by
    exact
      (Subgroup.commutator_mono le_top le_top) hcMap
  have hcNormalProduct :
      (c : G) ∈ K ⊔ (P : Subgroup G) :=
    hcommutativeQuotient hcAmbientCommutator
  have hcSourceProduct :
      c ∈
        okuyamaWajimaProperBranchQuotientSourceKernel
            K P Q theta hinvariant gQ ⊔
          (okuyamaWajimaProperBranchSylowInQNormalizer P Q :
            Subgroup
              (okuyamaWajimaProperBranchQuotientAmbient P Q)) :=
    okuyamaWajimaProperBranch_mem_sourceKernel_sup_sylow_of_mem_normalProduct
      K P Q theta hinvariant gQ hK c hcNormalProduct
  have hcMapped :=
    Subgroup.mem_map_of_mem
      (okuyamaWajimaProperBranchQuotientMap P Q)
      hcSourceProduct
  rw [Subgroup.map_sup] at hcMapped
  change
    okuyamaWajimaProperBranchQuotientMap P Q c ∈
      okuyamaWajimaProperBranchQuotientImageKernel
          K P Q theta hinvariant gQ ⊔
        (okuyamaWajimaProperBranchQuotientSylow P Q :
          Subgroup
            (okuyamaWajimaProperBranchNormalizerQuotient P Q))
    at hcMapped
  simpa [c] using hcMapped

/-- The quotient recursive problem has the printed generation form
`Jbar ⊔ N_Xbar(Pbar) = top`. -/
theorem okuyamaWajimaProperBranchQuotient_kernel_sup_normalizer_eq_top
    (hK : IsPPrimeGroup p K)
    (hcommutativeQuotient :
      _root_.commutator G ≤ K ⊔ (P : Subgroup G)) :
    okuyamaWajimaProperBranchQuotientImageKernel
          K P Q theta hinvariant gQ ⊔
        Subgroup.normalizer
          ((okuyamaWajimaProperBranchQuotientSylow P Q :
            Subgroup
              (okuyamaWajimaProperBranchNormalizerQuotient P Q)) :
            Set
              (okuyamaWajimaProperBranchNormalizerQuotient P Q)) =
      ⊤ := by
  let Jbar :=
    okuyamaWajimaProperBranchQuotientImageKernel
      K P Q theta hinvariant gQ
  let Pbar :=
    okuyamaWajimaProperBranchQuotientSylow P Q
  have hcomm :
      _root_.commutator
          (okuyamaWajimaProperBranchNormalizerQuotient P Q) ≤
        Jbar ⊔ (Pbar :
          Subgroup
            (okuyamaWajimaProperBranchNormalizerQuotient P Q)) :=
    okuyamaWajimaProperBranchQuotient_commutator_le
      K P Q theta hinvariant gQ hK hcommutativeQuotient
  letI :
      (Jbar ⊔ (Pbar :
        Subgroup
          (okuyamaWajimaProperBranchNormalizerQuotient P Q))).Normal :=
    Subgroup.Normal.of_commutator_le
      (G := okuyamaWajimaProperBranchNormalizerQuotient P Q)
      hcomm
  have hfrattini :
      Subgroup.normalizer
            ((Pbar :
              Subgroup
                (okuyamaWajimaProperBranchNormalizerQuotient P Q)) :
              Set
                (okuyamaWajimaProperBranchNormalizerQuotient P Q)) ⊔
          (Jbar ⊔ (Pbar :
            Subgroup
              (okuyamaWajimaProperBranchNormalizerQuotient P Q))) =
        ⊤ :=
    Pbar.normalizer_sup_eq_top'
      (show
        (Pbar :
            Subgroup
              (okuyamaWajimaProperBranchNormalizerQuotient P Q)) ≤
          Jbar ⊔ (Pbar :
            Subgroup
              (okuyamaWajimaProperBranchNormalizerQuotient P Q))
        from le_sup_right)
  have habsorb :
      Subgroup.normalizer
            ((Pbar :
              Subgroup
                (okuyamaWajimaProperBranchNormalizerQuotient P Q)) :
              Set
                (okuyamaWajimaProperBranchNormalizerQuotient P Q)) ⊔
          (Jbar ⊔ (Pbar :
            Subgroup
              (okuyamaWajimaProperBranchNormalizerQuotient P Q))) =
        Subgroup.normalizer
            ((Pbar :
              Subgroup
                (okuyamaWajimaProperBranchNormalizerQuotient P Q)) :
              Set
                (okuyamaWajimaProperBranchNormalizerQuotient P Q)) ⊔
          Jbar := by
    apply le_antisymm
    · exact
        sup_le
          (le_sup_left)
          (sup_le le_sup_right
            (Subgroup.le_normalizer.trans le_sup_left))
    · exact
        sup_le
          le_sup_left
          (le_sup_left.trans le_sup_right)
  rw [habsorb] at hfrattini
  rw [sup_comm]
  exact hfrattini

/-- A canonical ordinary Glauberman correspondence for the quotient
recursive problem. -/
noncomputable def
    okuyamaWajimaProperBranchQuotientGlaubermanCorrespondence
    (hK : IsPPrimeGroup p K) :
    GlaubermanCorrespondence
      (okuyamaWajimaProperBranchQuotientImageKernel
        K P Q theta hinvariant gQ)
      (okuyamaWajimaProperBranchQuotientSylow P Q :
        Subgroup
          (okuyamaWajimaProperBranchNormalizerQuotient P Q))
      p :=
  Classical.choice
    (exists_glaubermanCorrespondence_of_cyclicStrongAction
      (okuyamaWajimaProperBranchQuotientImageKernel
        K P Q theta hinvariant gQ)
      (okuyamaWajimaProperBranchQuotientSylow P Q :
        Subgroup
          (okuyamaWajimaProperBranchNormalizerQuotient P Q))
      cyclicStrongActionGlaubermanHypothesis
      (okuyamaWajimaProperBranchQuotientSylow P Q).isPGroup'
      (okuyamaWajimaProperBranchQuotientImageKernel_isPPrime
        K P Q theta hinvariant gQ hK))

/-- Full ambient invariance of the transported quotient source character. -/
theorem okuyamaWajimaProperBranchQuotientSourceCharacter_invariant
    (hK : IsPPrimeGroup p K)
    (a : okuyamaWajimaProperBranchNormalizerQuotient P Q) :
    a •
        (okuyamaWajimaProperBranchQuotientInvariantSourceCharacter
          K P Q theta hinvariant gQ hK).1.1 =
      (okuyamaWajimaProperBranchQuotientInvariantSourceCharacter
        K P Q theta hinvariant gQ hK).1.1 := by
  rw [
    okuyamaWajimaProperBranchQuotientInvariantSourceCharacter_coe
      K P Q theta hinvariant gQ hK]
  rw [← IrreducibleCharacter.mem_inertia_iff]
  have hinertia :
      IrreducibleCharacter.inertia
          (okuyamaWajimaProperBranchQuotientImageKernel
            K P Q theta hinvariant gQ)
          (okuyamaWajimaProperBranchQuotientSourceCharacter
            K P Q theta hinvariant gQ hK).1 =
        ⊤ := by
    simpa only [
      okuyamaWajimaProperBranchQuotientSourceTriple]
      using
        (okuyamaWajimaProperBranchQuotientSourceTriple
          K P Q theta hinvariant gQ hK).inertia_character_eq_top
  rw [hinertia]
  exact Subgroup.mem_top a

variable
  (gP :
    GlaubermanCorrespondence K (P : Subgroup G) p)

/-- The two exact extension-coordinate comparisons still needed after the
quotient group and character data have been constructed.

The `source` field is descent/ascent between the transported `psibar` on
`N_G(Q)/Q` and `psi` on `N_G(Q)`.  The `target` field combines the exact
normalizer quotient coordinate with strong Glauberman transitivity, thereby
identifying the quotient correspondent with the original `P`-correspondent
`phi`.

These are deliberately extension propositions, rather than arbitrary
character equalities: they are precisely the two semantic endpoints needed
to consume the recursive printed theorem. -/
structure
    OkuyamaWajimaProperBranchQuotientExtensionCoordinateComparison
    (hK : IsPPrimeGroup p K) : Prop where
  /-- The quotient source extension problem is the original intermediate
  extension problem. -/
  source :
    OkuyamaWajimaProperBranchThetaExtendsToG
        (okuyamaWajimaProperBranchQuotientImageKernel
          K P Q theta hinvariant gQ)
        (okuyamaWajimaProperBranchQuotientSylow P Q)
        (okuyamaWajimaProperBranchQuotientInvariantSourceCharacter
          K P Q theta hinvariant gQ hK)
        (okuyamaWajimaProperBranchQuotientSourceCharacter_invariant
          K P Q theta hinvariant gQ hK) ↔
      OkuyamaWajimaProperBranchPsiExtendsToQNormalizer
        K P Q theta hinvariant gQ
  /-- The quotient target extension problem is the original final
  normalizer extension problem. -/
  target :
    OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
        (okuyamaWajimaProperBranchQuotientImageKernel
          K P Q theta hinvariant gQ)
        (okuyamaWajimaProperBranchQuotientSylow P Q)
        (okuyamaWajimaProperBranchQuotientInvariantSourceCharacter
          K P Q theta hinvariant gQ hK)
        (okuyamaWajimaProperBranchQuotientSourceCharacter_invariant
          K P Q theta hinvariant gQ hK)
        (okuyamaWajimaProperBranchQuotientGlaubermanCorrespondence
          K P Q theta hinvariant gQ hK) ↔
      OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
        K P theta hinvariant gP

/-- The universal theorem on `N_G(Q)/Q` gives the exact first recursive
conclusion once the two quotient extension-coordinate comparisons are
available.

All data passed to the smaller printed theorem are canonical:

* normal kernel `Jbar`;
* Sylow subgroup `Pbar`;
* transported globally invariant `p'`-degree character `psibar`;
* an ordinary Glauberman correspondence;
* the derived generation equality; and
* the descended commutator containment.
-/
theorem okuyamaWajimaProperBranchQuotientInductionHypothesis_of_statement
    (hK : IsPPrimeGroup p K)
    (hcommutativeQuotient :
      _root_.commutator G ≤ K ⊔ (P : Subgroup G))
    (coordinates :
      OkuyamaWajimaProperBranchQuotientExtensionCoordinateComparison
        K P Q theta hinvariant gQ gP hK)
    (smallerStatement :
      OkuyamaWajimaPrintedExtensionStatement
        (p := p)
        (okuyamaWajimaProperBranchNormalizerQuotient P Q)) :
    OkuyamaWajimaProperBranchQuotientInductionHypothesis
      K P Q theta hinvariant gQ gP := by
  let Jbar :=
    okuyamaWajimaProperBranchQuotientImageKernel
      K P Q theta hinvariant gQ
  let Pbar :=
    okuyamaWajimaProperBranchQuotientSylow P Q
  let thetaBar :=
    okuyamaWajimaProperBranchQuotientInvariantSourceCharacter
      K P Q theta hinvariant gQ hK
  let hinvariantBar :=
    okuyamaWajimaProperBranchQuotientSourceCharacter_invariant
      K P Q theta hinvariant gQ hK
  let gBar :=
    okuyamaWajimaProperBranchQuotientGlaubermanCorrespondence
      K P Q theta hinvariant gQ hK
  have hrecursive :
      OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
          Jbar Pbar thetaBar hinvariantBar gBar ↔
        OkuyamaWajimaProperBranchThetaExtendsToG
          Jbar Pbar thetaBar hinvariantBar :=
    smallerStatement
      Jbar Pbar
      (okuyamaWajimaProperBranchQuotientImageKernel_isPPrime
        K P Q theta hinvariant gQ hK)
      (okuyamaWajimaProperBranchQuotient_kernel_sup_normalizer_eq_top
        K P Q theta hinvariant gQ hK hcommutativeQuotient)
      (okuyamaWajimaProperBranchQuotient_commutator_le
        K P Q theta hinvariant gQ hK hcommutativeQuotient)
      thetaBar hinvariantBar gBar
  exact
    coordinates.target.symm.trans
      (hrecursive.trans coordinates.source)

/-- Function-valued form of the quotient induction adapter, ready for the
`quotient` field of `OkuyamaWajimaProperBranchInductionAdapters`. -/
theorem okuyamaWajimaProperBranchQuotientInductionAdapter
    (hK : IsPPrimeGroup p K)
    (hcommutativeQuotient :
      _root_.commutator G ≤ K ⊔ (P : Subgroup G))
    (coordinates :
      OkuyamaWajimaProperBranchQuotientExtensionCoordinateComparison
        K P Q theta hinvariant gQ gP hK) :
    OkuyamaWajimaPrintedExtensionStatement
        (p := p)
        (okuyamaWajimaProperBranchNormalizerQuotient P Q) →
      OkuyamaWajimaProperBranchQuotientInductionHypothesis
        K P Q theta hinvariant gQ gP :=
  okuyamaWajimaProperBranchQuotientInductionHypothesis_of_statement
    K P Q theta hinvariant gQ gP hK
      hcommutativeQuotient coordinates

end QuotientCoordinates

end McKayConjecture
