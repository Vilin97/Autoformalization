/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InternalNormalTransport
import McKayConjecture.Character.OkuyamaWajimaPrintedInduction

/-!
# The subgroup recursive call in the proper Okuyama--Wajima branch

This file transports the universal printed extension statement on

`H = Q M K`

to the literal subgroup-coordinate equivalence used by the proper-branch
recursion.  The construction is deliberately normality-free: `H` is only
an ambient subgroup, and no instance or premise `H.Normal` occurs.

The normal `p'`-kernel in the recursive problem is the canonical internal
copy `K.subgroupOf H`, while the recursive Sylow subgroup is the copy of
`Q` supplied by `OkuyamaWajimaProperBranchGroupScope`.  The source
character is transported along `K.subgroupOf H ≃* K`.  On the target,
the internal fixed-point subgroup and Sylow normalizer are transported to
the already established ambient-intersection coordinates for `C_K(Q)` and
`N_H(Q)`.
-/

noncomputable section

namespace McKayConjecture

open CharacterTriple
open CliffordCorrespondence
open GroupTheory

private theorem exists_extensionAlong_comap_equiv_iff
    {A A' B B' : Type}
    [Group A] [Group A'] [Group B] [Group B']
    [Finite A] [Finite A'] [Finite B] [Finite B']
    (f : B →* A) (f' : B' →* A')
    (eA : A' ≃* A) (eB : B' ≃* B)
    (hcomm :
      eA.toMonoidHom.comp f' =
        f.comp eB.toMonoidHom)
    (chi : IrreducibleCharacter B) :
    (∃ eta : IrreducibleCharacter A,
        IrreducibleCharacter.IsExtensionAlong
          f chi eta) ↔
      ∃ eta' : IrreducibleCharacter A',
        IrreducibleCharacter.IsExtensionAlong
          f' (chi.comap eB) eta' := by
  constructor
  · rintro ⟨eta, heta⟩
    exact
      ⟨eta.comap eA,
        IrreducibleCharacter.IsExtensionAlong.comap_equiv
          eA eB hcomm heta⟩
  · rintro ⟨eta', heta'⟩
    have hcomm' :
        eA.symm.toMonoidHom.comp f =
          f'.comp eB.symm.toMonoidHom := by
      apply MonoidHom.ext
      intro b
      apply eA.injective
      have hpoint :=
        congrArg
          (fun k : B' →* A ↦ k (eB.symm b))
          hcomm
      change
        eA (eA.symm (f b)) =
          eA (f' (eB.symm b))
      rw [eA.apply_symm_apply]
      simpa using hpoint.symm
    refine ⟨eta'.comap eA.symm, ?_⟩
    have hback :=
      IrreducibleCharacter.IsExtensionAlong.comap_equiv
        eA.symm eB.symm hcomm' heta'
    simpa using hback

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (K : Subgroup G) [K.Normal]
variable (P : Sylow p G)
variable (Q : Subgroup P) [Q.Normal]
variable (M : Subgroup G)

local instance properBranchSubgroupInductionPConjugationAction :
    MulDistribMulAction P K :=
  subgroupConjugationMulDistribMulAction K (P : Subgroup G)

variable
  (theta :
    PInvariantPPrimeIrreducibleCharacter
      K (P : Subgroup G) p)
variable
  (hinvariant :
    ∀ g : G, g • theta.1.1 = theta.1.1)
variable
  (gQ :
    GlaubermanCorrespondence K
      (okuyamaWajimaProperBranchQ P Q) p)

abbrev properBranchSubgroupAmbient :
    Subgroup G :=
  okuyamaWajimaProperBranchH K P Q M

abbrev properBranchSubgroupKernel :
    Subgroup (properBranchSubgroupAmbient K P Q M) :=
  K.subgroupOf (properBranchSubgroupAmbient K P Q M)

abbrev properBranchSubgroupAmbientQ :
    Subgroup G :=
  okuyamaWajimaProperBranchQ P Q

abbrev properBranchSubgroupFixedKernel :
    Subgroup G :=
  okuyamaWajimaProperBranchJ K P Q

omit [Q.Normal] in
/-- The internal copy of `K` in `H` is normal. -/
private instance properBranchSubgroupKernel_normal :
    (properBranchSubgroupKernel K P Q M).Normal :=
  (inferInstance : K.Normal).subgroupOf
    (properBranchSubgroupAmbient K P Q M)

omit [Finite G] [Fact p.Prime] [Q.Normal] in
/-- The internal copy of the source kernel remains a `p'`-group. -/
theorem properBranchSubgroupKernel_isPPrime
    (hK : IsPPrimeGroup p K) :
    IsPPrimeGroup p
      (properBranchSubgroupKernel K P Q M) := by
  exact
    hK.of_equiv
      (Subgroup.subgroupOfEquivOfLe
        (okuyamaWajimaProperBranchK_le_H K P Q M)).symm

omit [Finite G] [Fact p.Prime] [Q.Normal] in
/-- The ambient commutator hypothesis restricts to the exact normal product
`K_H Q_H` in `H`.

The proof only uses membership in `H`.  After writing an ambient
commutator as `k q` with `k ∈ K` and `q ∈ P`, membership of both the
commutator and `k` in `H` forces `q ∈ P ∩ H = Q`. -/
theorem properBranchSubgroup_commutator_le_kernel_sup_sylow
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M)
    (hcommutativeQuotient :
      _root_.commutator G ≤ K ⊔ (P : Subgroup G)) :
    _root_.commutator
        (properBranchSubgroupAmbient K P Q M) ≤
      properBranchSubgroupKernel K P Q M ⊔
        (scope.sylowInH :
          Subgroup (properBranchSubgroupAmbient K P Q M)) := by
  let H := properBranchSubgroupAmbient K P Q M
  let QA := properBranchSubgroupAmbientQ P Q
  intro x hx
  have hxmap :
      ((x : H) : G) ∈
        (_root_.commutator H).map H.subtype :=
    Subgroup.mem_map_of_mem H.subtype hx
  rw [Subgroup.map_subtype_commutator] at hxmap
  have hxG :
      ((x : H) : G) ∈ _root_.commutator G :=
    (Subgroup.commutator_mono le_top le_top) hxmap
  have hxKP :
      ((x : H) : G) ∈ K ⊔ (P : Subgroup G) :=
    hcommutativeQuotient hxG
  obtain ⟨k, hkK, q, hqP, hkq⟩ :=
    Subgroup.mem_sup_of_normal_left.mp hxKP
  have hkH : k ∈ H :=
    okuyamaWajimaProperBranchK_le_H K P Q M hkK
  have hqH : q ∈ H := by
    have hprod : k⁻¹ * ((x : H) : G) = q := by
      rw [← hkq]
      group
    rw [← hprod]
    exact H.mul_mem (H.inv_mem hkH) x.2
  have hqQA : q ∈ QA := by
    have hqInf : q ∈ (P : Subgroup G) ⊓ H :=
      ⟨hqP, hqH⟩
    rw [scope.sylow_inf_H_eq] at hqInf
    exact hqInf
  let kH : H := ⟨k, hkH⟩
  let qH : H := ⟨q, hqH⟩
  have hkInternal :
      kH ∈ properBranchSubgroupKernel K P Q M :=
    hkK
  have hqSylow :
      qH ∈
        (scope.sylowInH : Subgroup H) := by
    rw [scope.coe_sylowInH]
    exact hqQA
  apply Subgroup.mem_sup_of_normal_left.mpr
  refine ⟨kH, hkInternal, qH, hqSylow, ?_⟩
  apply Subtype.ext
  exact hkq

/-- The source character transported to the internal copy of `K` in `H`,
bundled with its invariance under the recursive Sylow subgroup. -/
noncomputable def properBranchSubgroupTheta
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M) :
    PInvariantPPrimeIrreducibleCharacter
      (properBranchSubgroupKernel K P Q M)
      (scope.sylowInH :
        Subgroup (properBranchSubgroupAmbient K P Q M))
      p := by
  let H := properBranchSubgroupAmbient K P Q M
  let hKH : K ≤ H :=
    okuyamaWajimaProperBranchK_le_H K P Q M
  let eTheta :=
    IrreducibleCharacter.internalNormalPPrimeEquiv
      K H hKH p
  refine ⟨eTheta theta.1, ?_⟩
  rw [
    IrreducibleCharacter.inertia_internalNormalPPrimeEquiv_eq_comap
      K H hKH p theta.1]
  intro h _hh
  change
    ((h : H) : G) ∈
      IrreducibleCharacter.inertia K theta.1.1
  rw [IrreducibleCharacter.mem_inertia_iff]
  exact hinvariant ((h : H) : G)

omit [Finite G] [Fact p.Prime] [Q.Normal] in
/-- The recursively transported source character is invariant under every
element of `H`, as required by the universal printed statement. -/
theorem properBranchSubgroupTheta_invariant
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M)
    (h :
      properBranchSubgroupAmbient K P Q M) :
    h •
        (properBranchSubgroupTheta
          K P Q M theta hinvariant scope).1.1 =
      (properBranchSubgroupTheta
        K P Q M theta hinvariant scope).1.1 := by
  let H := properBranchSubgroupAmbient K P Q M
  let hKH : K ≤ H :=
    okuyamaWajimaProperBranchK_le_H K P Q M
  let eTheta :=
    IrreducibleCharacter.internalNormalPPrimeEquiv
      K H hKH p
  have hsource :
      (((h : H) : G) • theta.1) = theta.1 := by
    apply Subtype.ext
    exact hinvariant ((h : H) : G)
  have htransport :=
    congrArg eTheta hsource
  rw [
    IrreducibleCharacter.internalNormalPPrimeEquiv_smul
      K H hKH p h theta.1] at htransport
  exact congrArg Subtype.val htransport

/-! ## Fixed-point and normalizer coordinates -/

/-- The fixed points of the internal Sylow copy on the internal kernel are
the ambient fixed-point kernel `J = C_K(Q)`.

Both directions are identity on underlying elements.  The only substantive
coordinate change is `scope.coe_sylowInH`, which identifies the recursive
Sylow subgroup with `Q.subgroupOf H`. -/
def properBranchSubgroupFixedKernelEquiv
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M) :
    coprimeFixedPoints
        (properBranchSubgroupKernel K P Q M)
        (scope.sylowInH :
          Subgroup (properBranchSubgroupAmbient K P Q M)) ≃*
      properBranchSubgroupFixedKernel K P Q := by
  let H := properBranchSubgroupAmbient K P Q M
  let QA := properBranchSubgroupAmbientQ P Q
  let J := properBranchSubgroupFixedKernel K P Q
  have hQH : QA ≤ H :=
    okuyamaWajimaProperBranchQ_le_H K P Q M
  have hJH : J ≤ H :=
    okuyamaWajimaProperBranchJ_le_H K P Q M
  refine
    { toFun := fun x ↦
        ⟨((x.1 : H) : G), ?_⟩
      invFun := fun y ↦
        ⟨⟨(y : G), hJH y.2⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }
  · refine ⟨x.2.1, ?_⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro q hq
    let qH : H := ⟨q, hQH hq⟩
    have hqSylow :
        qH ∈ (scope.sylowInH : Subgroup H) := by
      rw [scope.coe_sylowInH]
      exact hq
    have hcentral :=
      Subgroup.mem_centralizer_iff.mp x.2.2 qH hqSylow
    exact congrArg Subtype.val hcentral
  · refine ⟨y.2.1, ?_⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro q hq
    have hqQA :
        ((q : H) : G) ∈ QA := by
      have hq' := hq
      rw [scope.coe_sylowInH] at hq'
      exact hq'
    have hcentral :=
      Subgroup.mem_centralizer_iff.mp y.2.2
        ((q : H) : G) hqQA
    apply Subtype.ext
    exact hcentral
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro y
    apply Subtype.ext
    rfl
  · intro x y
    apply Subtype.ext
    rfl

omit [Finite G] [Fact p.Prime] [Q.Normal] in
@[simp]
theorem properBranchSubgroupFixedKernelEquiv_apply_coe
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M)
    (x :
      coprimeFixedPoints
        (properBranchSubgroupKernel K P Q M)
        (scope.sylowInH :
          Subgroup (properBranchSubgroupAmbient K P Q M))) :
    ((properBranchSubgroupFixedKernelEquiv
        K P Q M scope x :
      properBranchSubgroupFixedKernel K P Q) : G) =
      ((x :
        properBranchSubgroupAmbient K P Q M) : G) :=
  rfl

/-- The internal recursive Sylow normalizer, in the literal subtype
coordinate used by the universal statement. -/
abbrev properBranchSubgroupInternalNormalizer
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M) :
    Subgroup (properBranchSubgroupAmbient K P Q M) :=
  Subgroup.normalizer
    ((scope.sylowInH :
      Subgroup (properBranchSubgroupAmbient K P Q M)) :
      Set (properBranchSubgroupAmbient K P Q M))

/-- The internal normalizer `N_H(Q)` is isomorphic to the exact
intersection coordinate inside `N_G(Q)` used by the recursion module. -/
def properBranchSubgroupInternalNormalizerEquiv
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M) :
    properBranchSubgroupInternalNormalizer K P Q M scope ≃*
      okuyamaWajimaProperBranchHNormalizerInQNormalizer
        K P Q M := by
  let H := properBranchSubgroupAmbient K P Q M
  let QA := properBranchSubgroupAmbientQ P Q
  let NQ := okuyamaWajimaProperBranchQNormalizer P Q
  let B :=
      okuyamaWajimaProperBranchHNormalizerInQNormalizer
      K P Q M
  have hQA :
      (scope.sylowInH : Subgroup H) =
        QA.subgroupOf H :=
    scope.coe_sylowInH
  have hnormalizer :
      Subgroup.normalizer
          (((QA.subgroupOf H : Subgroup H)) : Set H) =
        NQ.subgroupOf H :=
    okuyamaWajimaProperBranch_normalizerInH_eq
      K P Q M
  refine
    { toFun := fun x ↦
        ⟨⟨((x : H) : G), ?_⟩, ?_⟩
      invFun := fun y ↦
        ⟨⟨((y : NQ) : G), ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }
  · change ((x : H) : G) ∈ NQ
    have hx :
        x.1 ∈ NQ.subgroupOf H := by
      rw [← hnormalizer, ← hQA]
      exact x.2
    exact hx
  · change ((x : H) : G) ∈ H ⊓ NQ
    refine ⟨x.1.2, ?_⟩
    have hx :
        x.1 ∈ NQ.subgroupOf H := by
      rw [← hnormalizer, ← hQA]
      exact x.2
    exact hx
  · exact y.2.1
  · change
      (⟨((y : NQ) : G), y.2.1⟩ : H) ∈
        Subgroup.normalizer
          (((scope.sylowInH : Subgroup H)) : Set H)
    rw [hQA, hnormalizer]
    exact y.1.2
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro y
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro x y
    apply Subtype.ext
    apply Subtype.ext
    rfl

omit [Finite G] [Fact p.Prime] [K.Normal] [Q.Normal] in
@[simp]
theorem properBranchSubgroupInternalNormalizerEquiv_apply_coe
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M)
    (x :
      properBranchSubgroupInternalNormalizer K P Q M scope) :
    (((properBranchSubgroupInternalNormalizerEquiv
        K P Q M scope x :
      okuyamaWajimaProperBranchHNormalizerInQNormalizer
        K P Q M) :
      okuyamaWajimaProperBranchQNormalizer P Q) : G) =
      ((x :
        properBranchSubgroupAmbient K P Q M) : G) :=
  rfl

/-! ## Transporting the Glauberman correspondent -/

/-- A Glauberman correspondence for the recursive internal kernel and
Sylow subgroup.  Existence is automatic from the already proved cyclic
strong-action theorem. -/
noncomputable def properBranchSubgroupGlaubermanCorrespondence
    (hK : IsPPrimeGroup p K)
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M) :
    GlaubermanCorrespondence
      (properBranchSubgroupKernel K P Q M)
      (scope.sylowInH :
        Subgroup (properBranchSubgroupAmbient K P Q M))
      p :=
  Classical.choice
    (exists_glaubermanCorrespondence_of_cyclicStrongAction
      (properBranchSubgroupKernel K P Q M)
      (scope.sylowInH :
        Subgroup (properBranchSubgroupAmbient K P Q M))
      cyclicStrongActionGlaubermanHypothesis
      scope.sylowInH.isPGroup'
      (properBranchSubgroupKernel_isPPrime
        K P Q M hK))

/-- The ambient intermediate correspondent `psi`, pulled back to the
internal fixed-point kernel of the recursive problem. -/
noncomputable def properBranchSubgroupPsi
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M) :
    PPrimeIrreducibleCharacter
      (coprimeFixedPoints
        (properBranchSubgroupKernel K P Q M)
        (scope.sylowInH :
          Subgroup (properBranchSubgroupAmbient K P Q M)))
      p :=
  IrreducibleCharacter.pPrimeComapEquiv p
    (properBranchSubgroupFixedKernelEquiv
      K P Q M scope)
    (okuyamaWajimaProperBranchPsi
      K P Q theta gQ)

omit [Fact p.Prime] [Q.Normal] in
/-- The defining restriction multiplicity of the transported `psi` is
prime to `p`.

This is the only numerical transport needed in the subgroup recursive
call.  It follows from the commuting identity-on-elements square formed by
the two fixed-point inclusions. -/
theorem properBranchSubgroupPsi_multiplicity_isPPrime
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M) :
    ¬p ∣
      restrictionMultiplicity
        (coprimeFixedPointsInclusion
          (properBranchSubgroupKernel K P Q M)
          (scope.sylowInH :
            Subgroup (properBranchSubgroupAmbient K P Q M)))
        (properBranchSubgroupPsi
          K P Q M theta gQ scope).1
        (properBranchSubgroupTheta
          K P Q M theta hinvariant scope).1.1 := by
  let H := properBranchSubgroupAmbient K P Q M
  let QA := properBranchSubgroupAmbientQ P Q
  let KH := properBranchSubgroupKernel K P Q M
  let SH : Subgroup H :=
    (scope.sylowInH : Subgroup H)
  let CH := coprimeFixedPoints KH SH
  let J := properBranchSubgroupFixedKernel K P Q
  let hKH : K ≤ H :=
    okuyamaWajimaProperBranchK_le_H K P Q M
  let eK : KH ≃* K :=
    Subgroup.subgroupOfEquivOfLe hKH
  let eC : CH ≃* J :=
    properBranchSubgroupFixedKernelEquiv
      K P Q M scope
  have hcomm :
      eK.toMonoidHom.comp
          (coprimeFixedPointsInclusion KH SH) =
        (coprimeFixedPointsInclusion K QA).comp
          eC.toMonoidHom := by
    ext x
    rfl
  have htransport :=
    restrictionMultiplicity_comap_equiv
      eK eC
      (coprimeFixedPointsInclusion K QA)
      (coprimeFixedPointsInclusion KH SH)
      hcomm
      (okuyamaWajimaProperBranchPsi
        K P Q theta gQ).1
      theta.1.1
  change
    ¬p ∣
      restrictionMultiplicity
        (coprimeFixedPointsInclusion KH SH)
        ((okuyamaWajimaProperBranchPsi
          K P Q theta gQ).1.comap eC)
        (theta.1.1.comap eK)
  rw [htransport]
  exact
    gQ.multiplicity_isPPrime
      (okuyamaWajimaProperBranchAmbientQInvariantCharacter
        K (P : Subgroup G) Q theta)

omit [Q.Normal] in
/-- The recursive Glauberman correspondence sends the transported source
character to the transported ambient character `psi`.

The result is independent of the arbitrary chosen realization of the
recursive correspondence: uniqueness follows from its defining
prime-to-`p` restriction multiplicity. -/
theorem properBranchSubgroupGlaubermanCorrespondent_eq_psi
    (hK : IsPPrimeGroup p K)
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M) :
    (properBranchSubgroupGlaubermanCorrespondence
        K P Q M hK scope).characterEquiv
        (properBranchSubgroupTheta
          K P Q M theta hinvariant scope) =
      properBranchSubgroupPsi
        K P Q M theta gQ scope := by
  symm
  exact
    (properBranchSubgroupGlaubermanCorrespondence
      K P Q M hK scope).eq_correspondent_of_multiplicity_isPPrime
        (properBranchSubgroupTheta
          K P Q M theta hinvariant scope)
        (properBranchSubgroupPsi
          K P Q M theta gQ scope)
        (properBranchSubgroupPsi_multiplicity_isPPrime
          K P Q M theta hinvariant gQ scope)

/-- Transport from the recursive fixed-point kernel to the copy of
`J = C_K(Q)` used as the normal subgroup of the ambient `psi` triple. -/
def properBranchSubgroupFixedKernelToPsiKernelEquiv
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M) :
    coprimeFixedPoints
        (properBranchSubgroupKernel K P Q M)
        (scope.sylowInH :
          Subgroup (properBranchSubgroupAmbient K P Q M)) ≃*
      (properBranchSubgroupFixedKernel K P Q).subgroupOf
        (okuyamaWajimaProperBranchQNormalizer P Q) :=
  (properBranchSubgroupFixedKernelEquiv
    K P Q M scope).trans
      (Subgroup.subgroupOfEquivOfLe
        (okuyamaWajimaProperBranchJ_le_QNormalizer
          K P Q)).symm

omit [Finite G] [Fact p.Prime] [K.Normal] [Q.Normal] in
/-- The recursive fixed-point kernel lies in its internal Sylow
normalizer. -/
theorem properBranchSubgroupFixedKernel_le_internalNormalizer
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M) :
    coprimeFixedPoints
        (properBranchSubgroupKernel K P Q M)
        (scope.sylowInH :
          Subgroup (properBranchSubgroupAmbient K P Q M)) ≤
      properBranchSubgroupInternalNormalizer
        K P Q M scope :=
  inf_le_right.trans
    (Subgroup.centralizer_le_normalizer
      ((scope.sylowInH :
        Subgroup (properBranchSubgroupAmbient K P Q M)) :
        Set (properBranchSubgroupAmbient K P Q M)))

/-- The two inclusions in the target extension problem form a commuting
square under the fixed-kernel and normalizer equivalences. -/
theorem properBranchSubgroup_target_inclusion_square
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M) :
    (properBranchSubgroupInternalNormalizerEquiv
        K P Q M scope).toMonoidHom.comp
        (Subgroup.inclusion
          (properBranchSubgroupFixedKernel_le_internalNormalizer
            K P Q M scope)) =
      (Subgroup.inclusion
        (okuyamaWajimaProperBranchPsiKernel_le_HNormalizer
          K P Q M theta hinvariant gQ)).comp
        (properBranchSubgroupFixedKernelToPsiKernelEquiv
          K P Q M scope).toMonoidHom := by
  ext x
  rfl

omit [Q.Normal] in
/-- Pulling the recursive Glauberman correspondent to the ambient
`J.subgroupOf N_G(Q)` coordinate gives exactly the distinguished
character of the existing `psi` normalizer triple. -/
theorem properBranchSubgroupCorrespondent_comap_eq_psiNormalizerCharacter
    (hK : IsPPrimeGroup p K)
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M) :
    ((properBranchSubgroupGlaubermanCorrespondence
        K P Q M hK scope).characterEquiv
          (properBranchSubgroupTheta
            K P Q M theta hinvariant scope)).1.comap
        (properBranchSubgroupFixedKernelToPsiKernelEquiv
          K P Q M scope).symm =
      (okuyamaWajimaProperBranchPsiNormalizerTriple
        K P Q theta hinvariant gQ).character := by
  rw [
    properBranchSubgroupGlaubermanCorrespondent_eq_psi
      K P Q M theta hinvariant gQ hK scope]
  change
    (((okuyamaWajimaProperBranchPsi
        K P Q theta gQ).1.comap
          (properBranchSubgroupFixedKernelEquiv
            K P Q M scope)).comap
      (properBranchSubgroupFixedKernelToPsiKernelEquiv
        K P Q M scope).symm) =
      (okuyamaWajimaProperBranchPsi
        K P Q theta gQ).1.comap
          (Subgroup.subgroupOfEquivOfLe
            (okuyamaWajimaProperBranchJ_le_QNormalizer
              K P Q))
  rw [IrreducibleCharacter.comap_trans]
  apply congrArg
    (fun e =>
      (okuyamaWajimaProperBranchPsi
        K P Q theta gQ).1.comap e)
  ext x
  rfl

omit [Q.Normal] in
/-- The inverse form of the preceding character-coordinate equality. -/
theorem properBranchSubgroupPsiNormalizerCharacter_comap_eq_correspondent
    (hK : IsPPrimeGroup p K)
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M) :
    (okuyamaWajimaProperBranchPsiNormalizerTriple
        K P Q theta hinvariant gQ).character.comap
        (properBranchSubgroupFixedKernelToPsiKernelEquiv
          K P Q M scope) =
      ((properBranchSubgroupGlaubermanCorrespondence
        K P Q M hK scope).characterEquiv
          (properBranchSubgroupTheta
            K P Q M theta hinvariant scope)).1 := by
  have h :=
    congrArg
      (fun chi =>
        chi.comap
          (properBranchSubgroupFixedKernelToPsiKernelEquiv
            K P Q M scope))
      (properBranchSubgroupCorrespondent_comap_eq_psiNormalizerCharacter
        K P Q M theta hinvariant gQ hK scope)
  simpa using h.symm

omit [Q.Normal] in
/-- The source extension proposition in the recursive printed theorem is
definitionally the restricted source triple already used by the proper
branch. -/
theorem properBranchSubgroupThetaExtendsToH_iff_recursiveThetaExtends
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M) :
    OkuyamaWajimaProperBranchThetaExtendsToG
        (properBranchSubgroupKernel K P Q M)
        scope.sylowInH
        (properBranchSubgroupTheta
          K P Q M theta hinvariant scope)
        (properBranchSubgroupTheta_invariant
          K P Q M theta hinvariant scope) ↔
      OkuyamaWajimaProperBranchThetaExtendsToH
        K P Q M theta hinvariant := by
  rfl

/-- Extension of the recursive Glauberman correspondent to the internal
normalizer is equivalent to the existing literal proposition that `psi`
extends to the ambient-intersection copy of `N_H(Q)`. -/
theorem properBranchSubgroupCorrespondentExtends_iff_psiExtendsToHNormalizer
    (hK : IsPPrimeGroup p K)
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M) :
    OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
        (properBranchSubgroupKernel K P Q M)
        scope.sylowInH
        (properBranchSubgroupTheta
          K P Q M theta hinvariant scope)
        (properBranchSubgroupTheta_invariant
          K P Q M theta hinvariant scope)
        (properBranchSubgroupGlaubermanCorrespondence
          K P Q M hK scope) ↔
      OkuyamaWajimaProperBranchPsiExtendsToHNormalizer
        K P Q M theta hinvariant gQ := by
  rw [
    okuyamaWajimaProperBranchPhi_extendsToPNormalizer_iff,
    okuyamaWajimaProperBranchPsi_extendsToHNormalizer_iff]
  let CH :=
    coprimeFixedPoints
      (properBranchSubgroupKernel K P Q M)
      (scope.sylowInH :
        Subgroup (properBranchSubgroupAmbient K P Q M))
  let NH :=
    properBranchSubgroupInternalNormalizer
      K P Q M scope
  let D :=
    (okuyamaWajimaProperBranchPsiNormalizerTriple
      K P Q theta hinvariant gQ).normalSubgroup
  let B :=
    okuyamaWajimaProperBranchHNormalizerInQNormalizer
      K P Q M
  let eN : NH ≃* B :=
    properBranchSubgroupInternalNormalizerEquiv
      K P Q M scope
  let eD : CH ≃* D :=
    properBranchSubgroupFixedKernelToPsiKernelEquiv
      K P Q M scope
  let hDN : D ≤ B :=
    okuyamaWajimaProperBranchPsiKernel_le_HNormalizer
      K P Q M theta hinvariant gQ
  let hCHN : CH ≤ NH :=
    properBranchSubgroupFixedKernel_le_internalNormalizer
      K P Q M scope
  have hsquare :
      eN.toMonoidHom.comp (Subgroup.inclusion hCHN) =
        (Subgroup.inclusion hDN).comp eD.toMonoidHom :=
    properBranchSubgroup_target_inclusion_square
      K P Q M theta hinvariant gQ scope
  have hcoord :=
    exists_extensionAlong_comap_equiv_iff
      (Subgroup.inclusion hDN)
      (Subgroup.inclusion hCHN)
      eN eD hsquare
      (okuyamaWajimaProperBranchPsiNormalizerTriple
        K P Q theta hinvariant gQ).character
  have hcharacter :
      (okuyamaWajimaProperBranchPsiNormalizerTriple
          K P Q theta hinvariant gQ).character.comap eD =
        ((properBranchSubgroupGlaubermanCorrespondence
          K P Q M hK scope).characterEquiv
            (properBranchSubgroupTheta
              K P Q M theta hinvariant scope)).1 :=
    properBranchSubgroupPsiNormalizerCharacter_comap_eq_correspondent
      K P Q M theta hinvariant gQ hK scope
  rw [hcharacter] at hcoord
  exact hcoord.symm

/-! ## The automatic subgroup induction adapter -/

/-- The universal printed theorem on the smaller group `H = Q M K`
supplies the exact subgroup induction hypothesis required by the proper
branch.

All structural inputs are derived:

* `K.subgroupOf H` is normal and `p'`;
* `Q.subgroupOf H` is the selected Sylow subgroup;
* `H = K N_H(Q)` is `scope.kernel_sup_normalizerInH_eq_top`; and
* the commutator containment is inherited from the ambient printed
  hypothesis using `P ∩ H = Q`.

No normality of `H` is assumed or used. -/
theorem okuyamaWajimaProperBranchSubgroupInductionHypothesis_of_printedStatement
    (hK : IsPPrimeGroup p K)
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M)
    (hcommutativeQuotient :
      _root_.commutator G ≤ K ⊔ (P : Subgroup G))
    (hprinted :
      OkuyamaWajimaPrintedExtensionStatement
        (p := p)
        (properBranchSubgroupAmbient K P Q M)) :
    OkuyamaWajimaProperBranchSubgroupInductionHypothesis
      K P Q M theta hinvariant gQ := by
  let H := properBranchSubgroupAmbient K P Q M
  let KH := properBranchSubgroupKernel K P Q M
  let thetaH :=
    properBranchSubgroupTheta
      K P Q M theta hinvariant scope
  let hinvariantH :=
    properBranchSubgroupTheta_invariant
      K P Q M theta hinvariant scope
  let gH :=
    properBranchSubgroupGlaubermanCorrespondence
      K P Q M hK scope
  have hrecursive :
      OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
          KH scope.sylowInH thetaH hinvariantH gH ↔
        OkuyamaWajimaProperBranchThetaExtendsToG
          KH scope.sylowInH thetaH hinvariantH :=
    hprinted
      KH scope.sylowInH
      (properBranchSubgroupKernel_isPPrime
        K P Q M hK)
      scope.kernel_sup_normalizerInH_eq_top
      (properBranchSubgroup_commutator_le_kernel_sup_sylow
        K P Q M scope hcommutativeQuotient)
      thetaH hinvariantH gH
  have htarget :
      OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
          KH scope.sylowInH thetaH hinvariantH gH ↔
        OkuyamaWajimaProperBranchPsiExtendsToHNormalizer
          K P Q M theta hinvariant gQ :=
    properBranchSubgroupCorrespondentExtends_iff_psiExtendsToHNormalizer
      K P Q M theta hinvariant gQ hK scope
  have hsource :
      OkuyamaWajimaProperBranchThetaExtendsToG
          KH scope.sylowInH thetaH hinvariantH ↔
        OkuyamaWajimaProperBranchThetaExtendsToH
          K P Q M theta hinvariant :=
    properBranchSubgroupThetaExtendsToH_iff_recursiveThetaExtends
      K P Q M theta hinvariant scope
  exact htarget.symm.trans (hrecursive.trans hsource)

end McKayConjecture
