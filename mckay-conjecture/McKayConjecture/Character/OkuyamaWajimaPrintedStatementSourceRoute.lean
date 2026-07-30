/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.OkuyamaWajimaPrintedExtension
import McKayConjecture.Character.OkuyamaWajimaProperBranchSubgroupInduction

/-!
# From the universal printed statement to the source-route input

The universal Okuyama--Wajima printed extension statement applies to the
finite local group

`L = K ⊔ (Q ⊔ W)`.

For a displayed `InvariantOkuyamaWajimaPrintedLocalScope`, the normal
`p'`-kernel in that application is the internal copy `K.subgroupOf L`,
the selected Sylow subgroup is the displayed copy of `Q`, and its
normalizer is the internal copy of `Q ⊔ W`.

This file transports the source and target extension propositions in
that recursive application back to the ambient subgroup coordinates used
by `InvariantOkuyamaWajimaPrintedExtensionTheoremInput`.
-/

noncomputable section

namespace McKayConjecture
namespace OkuyamaWajimaPrintedStatementSourceRoute

open CharacterTriple
open CliffordCorrespondence
open GroupTheory

variable {A : Type} [Group A] [Finite A]
variable {p : ℕ} [Fact p.Prime]
variable (K Q W : Subgroup A) [K.Normal]

private theorem exists_extensionAlong_equiv_iff
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
      ext b
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

/-- The finite local ambient group to which the universal printed
statement is specialized. -/
abbrev localAmbient : Subgroup A :=
  K ⊔ (Q ⊔ W)

/-- The canonical internal copy of the normal kernel in the local
ambient group. -/
abbrev localKernel : Subgroup (localAmbient K Q W) :=
  K.subgroupOf (localAmbient K Q W)

local instance localKernel_normal :
    (localKernel K Q W).Normal :=
  (inferInstance : K.Normal).subgroupOf
    (localAmbient K Q W)

omit [Finite A] [Fact p.Prime] [K.Normal] in
/-- The internal kernel remains a `p'`-group. -/
theorem localKernel_isPPrime
    (hK : IsPPrimeGroup p K) :
    IsPPrimeGroup p (localKernel K Q W) :=
  hK.of_equiv
    (Subgroup.subgroupOfEquivOfLe
      (show K ≤ localAmbient K Q W from le_sup_left)).symm

/-- Transport the ambient source character to the internal copy of `K`
and bundle its invariance under the displayed local Sylow subgroup. -/
def localTheta
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (scope :
      InvariantOkuyamaWajimaPrintedLocalScope
        (p := p) K Q W) :
    PInvariantPPrimeIrreducibleCharacter
      (localKernel K Q W) scope.sylow p := by
  let L := localAmbient K Q W
  let hKL : K ≤ L := le_sup_left
  let eTheta :=
    IrreducibleCharacter.internalNormalPPrimeEquiv
      K L hKL p
  refine ⟨eTheta theta.1, ?_⟩
  rw [
    IrreducibleCharacter.inertia_internalNormalPPrimeEquiv_eq_comap
      K L hKL p theta.1]
  intro s _hs
  change
    ((s : L) : A) ∈
      IrreducibleCharacter.inertia K theta.1.1
  rw [IrreducibleCharacter.mem_inertia_iff]
  exact hinvariant ((s : L) : A)

omit [Finite A] [Fact p.Prime] in
/-- The transported local source character is invariant under every
element of the local ambient group. -/
theorem localTheta_invariant
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (scope :
      InvariantOkuyamaWajimaPrintedLocalScope
        (p := p) K Q W)
    (l : localAmbient K Q W) :
    l • (localTheta K Q W theta hinvariant scope).1.1 =
      (localTheta K Q W theta hinvariant scope).1.1 := by
  let L := localAmbient K Q W
  let hKL : K ≤ L := le_sup_left
  let eTheta :=
    IrreducibleCharacter.internalNormalPPrimeEquiv
      K L hKL p
  have hsource :
      (((l : L) : A) • theta.1) = theta.1 := by
    apply Subtype.ext
    exact hinvariant ((l : L) : A)
  have htransport :=
    congrArg eTheta hsource
  rw [
    IrreducibleCharacter.internalNormalPPrimeEquiv_smul
      K L hKL p l theta.1] at htransport
  exact congrArg Subtype.val htransport

/-- The fixed points of the displayed internal Sylow subgroup on the
internal kernel are canonically the ambient fixed points `C_K(Q)`.
Both directions are the identity on underlying elements. -/
def localFixedKernelEquiv
    (scope :
      InvariantOkuyamaWajimaPrintedLocalScope
        (p := p) K Q W) :
    coprimeFixedPoints
        (localKernel K Q W)
        (scope.sylow :
          Subgroup (localAmbient K Q W)) ≃*
      coprimeFixedPoints K Q := by
  let L := localAmbient K Q W
  have hQL : Q ≤ L :=
    (show Q ≤ Q ⊔ W from le_sup_left).trans le_sup_right
  have hCL : coprimeFixedPoints K Q ≤ L :=
    inf_le_left.trans le_sup_left
  refine
    { toFun := fun x ↦
        ⟨((x.1 : L) : A), ?_⟩
      invFun := fun y ↦
        ⟨⟨(y : A), hCL y.2⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }
  · refine ⟨x.2.1, ?_⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro q hq
    let qL : L := ⟨q, hQL hq⟩
    have hqSylow :
        qL ∈ (scope.sylow : Subgroup L) := by
      rw [scope.sylow_eq]
      exact hq
    have hcentral :=
      Subgroup.mem_centralizer_iff.mp x.2.2 qL hqSylow
    exact congrArg Subtype.val hcentral
  · refine ⟨y.2.1, ?_⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro s hs
    have hsQ :
        ((s : L) : A) ∈ Q := by
      have hs' := hs
      rw [scope.sylow_eq] at hs'
      exact hs'
    have hcentral :=
      Subgroup.mem_centralizer_iff.mp y.2.2
        ((s : L) : A) hsQ
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

omit [Finite A] [Fact p.Prime] [K.Normal] in
@[simp]
theorem localFixedKernelEquiv_apply_coe
    (scope :
      InvariantOkuyamaWajimaPrintedLocalScope
        (p := p) K Q W)
    (x :
      coprimeFixedPoints
        (localKernel K Q W)
        (scope.sylow :
          Subgroup (localAmbient K Q W))) :
    ((localFixedKernelEquiv K Q W scope x :
      coprimeFixedPoints K Q) : A) =
        ((x : localAmbient K Q W) : A) :=
  rfl

/-- The internal normalizer of the displayed local Sylow subgroup. -/
abbrev localSylowNormalizer
    (scope :
      InvariantOkuyamaWajimaPrintedLocalScope
        (p := p) K Q W) :
    Subgroup (localAmbient K Q W) :=
  Subgroup.normalizer
    ((scope.sylow :
      Subgroup (localAmbient K Q W)) :
      Set (localAmbient K Q W))

/-- The local scope identifies the internal Sylow normalizer with the
ambient subgroup `Q ⊔ W`. -/
def localSylowNormalizerEquiv
    (scope :
      InvariantOkuyamaWajimaPrintedLocalScope
        (p := p) K Q W) :
    localSylowNormalizer K Q W scope ≃* (Q ⊔ W : Subgroup A) :=
  (MulEquiv.subgroupCongr scope.normalizer_eq).trans
    (Subgroup.subgroupOfEquivOfLe
      (show Q ⊔ W ≤ localAmbient K Q W from le_sup_right))

omit [Finite A] [Fact p.Prime] [K.Normal] in
@[simp]
theorem localSylowNormalizerEquiv_apply_coe
    (scope :
      InvariantOkuyamaWajimaPrintedLocalScope
        (p := p) K Q W)
    (x : localSylowNormalizer K Q W scope) :
    ((localSylowNormalizerEquiv K Q W scope x :
      (Q ⊔ W : Subgroup A)) : A) =
        ((x : localAmbient K Q W) : A) :=
  rfl

/-- A Glauberman correspondence for the internal local kernel and the
displayed local Sylow subgroup. -/
def localGlaubermanCorrespondence
    (hK : IsPPrimeGroup p K)
    (scope :
      InvariantOkuyamaWajimaPrintedLocalScope
        (p := p) K Q W) :
    GlaubermanCorrespondence
      (localKernel K Q W) scope.sylow p :=
  Classical.choice
    (exists_glaubermanCorrespondence_of_cyclicStrongAction
      (localKernel K Q W) scope.sylow
      cyclicStrongActionGlaubermanHypothesis
      scope.sylow.isPGroup'
      (localKernel_isPPrime K Q W hK))

/-- Pull the original Glauberman correspondent back to the fixed kernel
of the internal local problem. -/
def localCorrespondent
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (scope :
      InvariantOkuyamaWajimaPrintedLocalScope
        (p := p) K Q W) :
    PPrimeIrreducibleCharacter
      (coprimeFixedPoints
        (localKernel K Q W)
        (scope.sylow :
          Subgroup (localAmbient K Q W))) p :=
  IrreducibleCharacter.pPrimeComapEquiv p
    (localFixedKernelEquiv K Q W scope)
    (d.characterEquiv theta)

omit [Fact p.Prime] in
/-- The transported original correspondent has prime-to-`p`
restriction multiplicity in the internal local problem. -/
theorem localCorrespondent_multiplicity_isPPrime
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (scope :
      InvariantOkuyamaWajimaPrintedLocalScope
        (p := p) K Q W) :
    ¬p ∣
      restrictionMultiplicity
        (coprimeFixedPointsInclusion
          (localKernel K Q W)
          (scope.sylow :
            Subgroup (localAmbient K Q W)))
        (localCorrespondent K Q W d theta scope).1
        (localTheta K Q W theta hinvariant scope).1.1 := by
  let L := localAmbient K Q W
  let KL := localKernel K Q W
  let S : Subgroup L := scope.sylow
  let CL := coprimeFixedPoints KL S
  let C := coprimeFixedPoints K Q
  let hKL : K ≤ L := le_sup_left
  let eK : KL ≃* K :=
    Subgroup.subgroupOfEquivOfLe hKL
  let eC : CL ≃* C :=
    localFixedKernelEquiv K Q W scope
  have hcomm :
      eK.toMonoidHom.comp
          (coprimeFixedPointsInclusion KL S) =
        (coprimeFixedPointsInclusion K Q).comp
          eC.toMonoidHom := by
    ext x
    rfl
  have htransport :=
    restrictionMultiplicity_comap_equiv
      eK eC
      (coprimeFixedPointsInclusion K Q)
      (coprimeFixedPointsInclusion KL S)
      hcomm
      (d.characterEquiv theta).1
      theta.1.1
  change
    ¬p ∣
      restrictionMultiplicity
        (coprimeFixedPointsInclusion KL S)
        ((d.characterEquiv theta).1.comap eC)
        (theta.1.1.comap eK)
  rw [htransport]
  exact d.multiplicity_isPPrime theta

/-- The arbitrary internal correspondence sends the transported source
character to the transported original correspondent.  This follows from
the uniqueness clause of the ordinary Glauberman correspondence. -/
theorem localGlaubermanCorrespondent_eq
    (hK : IsPPrimeGroup p K)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (scope :
      InvariantOkuyamaWajimaPrintedLocalScope
        (p := p) K Q W) :
    (localGlaubermanCorrespondence K Q W hK scope).characterEquiv
        (localTheta K Q W theta hinvariant scope) =
      localCorrespondent K Q W d theta scope := by
  symm
  exact
    (localGlaubermanCorrespondence
      K Q W hK scope).eq_correspondent_of_multiplicity_isPPrime
        (localTheta K Q W theta hinvariant scope)
        (localCorrespondent K Q W d theta scope)
        (localCorrespondent_multiplicity_isPPrime
          K Q W d theta hinvariant scope)

omit [Finite A] [Fact p.Prime] [K.Normal] in
/-- The internal fixed kernel lies in the internal Sylow normalizer. -/
theorem localFixedKernel_le_sylowNormalizer
    (scope :
      InvariantOkuyamaWajimaPrintedLocalScope
        (p := p) K Q W) :
    coprimeFixedPoints
        (localKernel K Q W)
        (scope.sylow :
          Subgroup (localAmbient K Q W)) ≤
      localSylowNormalizer K Q W scope :=
  inf_le_right.trans
    (Subgroup.centralizer_le_normalizer
      ((scope.sylow :
        Subgroup (localAmbient K Q W)) :
        Set (localAmbient K Q W)))

omit [Finite A] [Fact p.Prime] [K.Normal] in
/-- The internal and ambient fixed-kernel inclusions commute with the
fixed-kernel and normalizer equivalences. -/
theorem localTarget_inclusion_square
    (hCW : coprimeFixedPoints K Q ≤ W)
    (scope :
      InvariantOkuyamaWajimaPrintedLocalScope
        (p := p) K Q W) :
    (localSylowNormalizerEquiv K Q W scope).toMonoidHom.comp
        (Subgroup.inclusion
          (localFixedKernel_le_sylowNormalizer
            K Q W scope)) =
      (Subgroup.inclusion
        (hCW.trans le_sup_right)).comp
          (localFixedKernelEquiv K Q W scope).toMonoidHom := by
  ext x
  rfl

/-- Reordering the two factors identifies the internal local ambient
group with the source group used by
`okuyamaWajimaExtensionConclusion`. -/
def localSourceAmbientEquiv :
    localAmbient K Q W ≃*
      ((Q ⊔ W) ⊔ K : Subgroup A) :=
  MulEquiv.subgroupCongr (by
    change K ⊔ (Q ⊔ W) = (Q ⊔ W) ⊔ K
    exact sup_comm _ _)

omit [Finite A] [Fact p.Prime] [K.Normal] in
@[simp]
theorem localSourceAmbientEquiv_apply_coe
    (x : localAmbient K Q W) :
    ((localSourceAmbientEquiv K Q W x :
      ((Q ⊔ W) ⊔ K : Subgroup A)) : A) =
        (x : A) :=
  rfl

omit [Finite A] [Fact p.Prime] [K.Normal] in
/-- The external and internal source-kernel inclusions commute with the
kernel and reordered-ambient equivalences. -/
theorem localSource_inclusion_square :
    (localSourceAmbientEquiv K Q W).toMonoidHom.comp
        (localKernel K Q W).subtype =
      (Subgroup.inclusion
        (show K ≤ (Q ⊔ W) ⊔ K from le_sup_right)).comp
          (Subgroup.subgroupOfEquivOfLe
            (show K ≤ localAmbient K Q W from le_sup_left)).toMonoidHom := by
  ext x
  rfl

omit [Fact p.Prime] in
/-- The recursive source extension proposition is exactly the external
source half of `okuyamaWajimaExtensionConclusion`. -/
theorem localThetaExtends_iff_sourceExtension
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (scope :
      InvariantOkuyamaWajimaPrintedLocalScope
        (p := p) K Q W) :
    OkuyamaWajimaProperBranchThetaExtendsToG
        (localKernel K Q W) scope.sylow
        (localTheta K Q W theta hinvariant scope)
        (localTheta_invariant K Q W theta hinvariant scope) ↔
      ∃ psi :
          IrreducibleCharacter
            ((Q ⊔ W) ⊔ K : Subgroup A),
        IrreducibleCharacter.IsExtensionAlong
          (Subgroup.inclusion le_sup_right)
          theta.1.1 psi := by
  let L := localAmbient K Q W
  let KL := localKernel K Q W
  let eL : L ≃* ((Q ⊔ W) ⊔ K : Subgroup A) :=
    localSourceAmbientEquiv K Q W
  let eK : KL ≃* K :=
    Subgroup.subgroupOfEquivOfLe le_sup_left
  have hsquare :
      eL.toMonoidHom.comp KL.subtype =
        (Subgroup.inclusion
          (show K ≤ (Q ⊔ W) ⊔ K from le_sup_right)).comp
            eK.toMonoidHom :=
    localSource_inclusion_square K Q W
  have htransport :=
    exists_extensionAlong_equiv_iff
      (Subgroup.inclusion
        (show K ≤ (Q ⊔ W) ⊔ K from le_sup_right))
      KL.subtype eL eK hsquare theta.1.1
  change
    (∃ eta : IrreducibleCharacter L,
      IrreducibleCharacter.IsExtensionAlong
        KL.subtype
        (theta.1.1.comap eK) eta) ↔
      ∃ psi :
          IrreducibleCharacter
            ((Q ⊔ W) ⊔ K : Subgroup A),
        IrreducibleCharacter.IsExtensionAlong
          (Subgroup.inclusion le_sup_right)
          theta.1.1 psi
  exact htransport.symm

/-- The recursive target extension proposition is exactly the external
target half of `okuyamaWajimaExtensionConclusion`. -/
theorem localPhiExtends_iff_targetExtension
    (hK : IsPPrimeGroup p K)
    (hCW : coprimeFixedPoints K Q ≤ W)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (scope :
      InvariantOkuyamaWajimaPrintedLocalScope
        (p := p) K Q W) :
    OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
        (localKernel K Q W) scope.sylow
        (localTheta K Q W theta hinvariant scope)
        (localTheta_invariant K Q W theta hinvariant scope)
        (localGlaubermanCorrespondence K Q W hK scope) ↔
      ∃ phi : IrreducibleCharacter (Q ⊔ W : Subgroup A),
        IrreducibleCharacter.IsExtensionAlong
          (Subgroup.inclusion (hCW.trans le_sup_right))
          (d.characterEquiv theta).1 phi := by
  rw [okuyamaWajimaProperBranchPhi_extendsToPNormalizer_iff]
  change
    (∃ eta :
        IrreducibleCharacter
          (localSylowNormalizer K Q W scope),
      IrreducibleCharacter.IsExtensionAlong
        (Subgroup.inclusion
          (localFixedKernel_le_sylowNormalizer
            K Q W scope))
        ((localGlaubermanCorrespondence
            K Q W hK scope).characterEquiv
          (localTheta K Q W theta hinvariant scope)).1
        eta) ↔
      ∃ phi : IrreducibleCharacter (Q ⊔ W : Subgroup A),
        IrreducibleCharacter.IsExtensionAlong
          (Subgroup.inclusion (hCW.trans le_sup_right))
          (d.characterEquiv theta).1 phi
  let CL :=
    coprimeFixedPoints
      (localKernel K Q W)
      (scope.sylow :
        Subgroup (localAmbient K Q W))
  let NL := localSylowNormalizer K Q W scope
  let C := coprimeFixedPoints K Q
  let B := (Q ⊔ W : Subgroup A)
  let eN : NL ≃* B :=
    localSylowNormalizerEquiv K Q W scope
  let eC : CL ≃* C :=
    localFixedKernelEquiv K Q W scope
  let hCLN : CL ≤ NL :=
    localFixedKernel_le_sylowNormalizer K Q W scope
  let hCB : C ≤ B := hCW.trans le_sup_right
  have hsquare :
      eN.toMonoidHom.comp (Subgroup.inclusion hCLN) =
        (Subgroup.inclusion hCB).comp eC.toMonoidHom :=
    localTarget_inclusion_square K Q W hCW scope
  have htransport :=
    exists_extensionAlong_equiv_iff
      (Subgroup.inclusion hCB)
      (Subgroup.inclusion hCLN)
      eN eC hsquare (d.characterEquiv theta).1
  rw [localGlaubermanCorrespondent_eq
    K Q W hK d theta hinvariant scope]
  exact htransport.symm

omit [Finite A] [Fact p.Prime] [K.Normal] in
/-- The local scope's quotient-abelian coordinate has exactly the
normal-product form expected by the universal printed statement. -/
theorem local_commutator_le_kernel_sup_sylow
    (scope :
      InvariantOkuyamaWajimaPrintedLocalScope
        (p := p) K Q W) :
    _root_.commutator (localAmbient K Q W) ≤
      localKernel K Q W ⊔
        (scope.sylow :
          Subgroup (localAmbient K Q W)) := by
  rw [scope.sylow_eq,
    ← Subgroup.subgroupOf_sup
      (show K ≤ localAmbient K Q W from le_sup_left)
      ((show Q ≤ Q ⊔ W from le_sup_left).trans le_sup_right)]
  exact scope.quotient_abelian

/-- The printed statement for the single finite local group
`K ⊔ (Q ⊔ W)` supplies the source-route extension conclusion on `Q ⊔ W`.

This is the exact local milestone behind the universal adapter below. -/
theorem localExtensionConclusion_of_printedStatement
    (hK : IsPPrimeGroup p K)
    (hCW : coprimeFixedPoints K Q ≤ W)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (scope :
      InvariantOkuyamaWajimaPrintedLocalScope
        (p := p) K Q W)
    (hprinted :
      OkuyamaWajimaPrintedExtensionStatement
        (p := p) (localAmbient K Q W)) :
    okuyamaWajimaExtensionConclusion
      K Q (Q ⊔ W) (hCW.trans le_sup_right) d theta := by
  let L := localAmbient K Q W
  let KL := localKernel K Q W
  let thetaL :=
    localTheta K Q W theta hinvariant scope
  let hinvariantL :=
    localTheta_invariant K Q W theta hinvariant scope
  let gL :=
    localGlaubermanCorrespondence K Q W hK scope
  have hrecursive :
      OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
          KL scope.sylow thetaL hinvariantL gL ↔
        OkuyamaWajimaProperBranchThetaExtendsToG
          KL scope.sylow thetaL hinvariantL :=
    hprinted
      KL scope.sylow
      (localKernel_isPPrime K Q W hK)
      scope.product_eq_top
      (local_commutator_le_kernel_sup_sylow
        K Q W scope)
      thetaL hinvariantL gL
  have hsource :
      OkuyamaWajimaProperBranchThetaExtendsToG
          KL scope.sylow thetaL hinvariantL ↔
        ∃ psi :
            IrreducibleCharacter
              ((Q ⊔ W) ⊔ K : Subgroup A),
          IrreducibleCharacter.IsExtensionAlong
            (Subgroup.inclusion le_sup_right)
            theta.1.1 psi :=
    localThetaExtends_iff_sourceExtension
      K Q W theta hinvariant scope
  have htarget :
      OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
          KL scope.sylow thetaL hinvariantL gL ↔
        ∃ phi : IrreducibleCharacter (Q ⊔ W : Subgroup A),
          IrreducibleCharacter.IsExtensionAlong
            (Subgroup.inclusion (hCW.trans le_sup_right))
            (d.characterEquiv theta).1 phi :=
    localPhiExtends_iff_targetExtension
      K Q W hK hCW d theta hinvariant scope
  rw [okuyamaWajimaExtensionConclusion]
  exact
    hsource.symm.trans
      (hrecursive.symm.trans htarget)

/-- A proof of the universal printed extension statement for every
finite group supplies the exact source-route theorem input.

For each `W` and local scope, the universal statement is specialized to
the subtype group `K ⊔ (Q ⊔ W)`; no extra character-coordinate or
normalizer hypothesis remains. -/
theorem invariantOkuyamaWajimaPrintedExtensionTheoremInput_of_universal
    (hQ : IsPGroup p Q)
    (hK : IsPPrimeGroup p K)
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hprinted :
      ∀ (G : Type) [Group G] [Finite G],
        OkuyamaWajimaPrintedExtensionStatement
          (p := p) G) :
    InvariantOkuyamaWajimaPrintedExtensionTheoremInput
      K Q hQ hK d theta hinvariant := by
  intro W hCW scope
  exact
    localExtensionConclusion_of_printedStatement
      K Q W hK hCW d theta hinvariant scope
      (hprinted (localAmbient K Q W))

end OkuyamaWajimaPrintedStatementSourceRoute
end McKayConjecture
