/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanActionStrongTransitivity
import McKayConjecture.Character.GlaubermanStrongRealization
import McKayConjecture.Character.GlaubermanActionEquivariance
import McKayConjecture.Character.GlaubermanEquivariance
import McKayConjecture.GroupTheory.OkuyamaWajimaCyclicQuotientSubgroup

/-!
# Glauberman transitivity in the Okuyama--Wajima proper branch

In the proper branch of the printed Okuyama--Wajima proof, a normal
subgroup `Q ◁ P` is selected inside the acting `p`-group.  If `theta` is
`P`-invariant, let `psi` be its `Q`-Glauberman correspondent and let
`phi` be the `(P / Q)`-Glauberman correspondent of `psi`.  After the
canonical identification of iterated fixed points with the `P`-fixed
points, `phi` is the `P`-Glauberman correspondent of `theta`.

This file packages precisely that step.  It uses strong action
correspondences, so no auxiliary hypothesis on the degrees of all
characters of the intermediate fixed-point group is needed.  The second
part supplies the canonical ambient conjugation coordinates

`(K^Q)^({P / Q}) ≃ K^P = C_K(P)`

and identifies the two-stage output with any ordinary ambient
Glauberman correspondence.  Finally, normalizer equivariance is stated
with the exact minimal extra condition needed in a recursive
Okuyama--Wajima problem: the source character must be fixed by the
normalizer under consideration.
-/

noncomputable section

namespace McKayConjecture

open CliffordCorrespondence

section Action

variable (P K : Type) [Group P] [Group K]
variable [MulDistribMulAction P K]
variable [Finite P] [Finite K]
variable (Q : Subgroup P) [Q.Normal]
variable {p : ℕ} [Fact p.Prime]

private noncomputable local instance :
    Fintype (IrreducibleCharacter
      (FixedPoints.subgroup Q K)) :=
  Fintype.ofFinite _

/-- The first-stage `Q`-Glauberman correspondent in the proper branch. -/
def okuyamaWajimaProperBranchQCorrespondent
    (dQ : StrongActionGlaubermanCorrespondence Q K p)
    (theta : ActionInvariantPPrimeIrreducibleCharacter P K p) :
    PPrimeIrreducibleCharacter
      (FixedPoints.subgroup Q K) p :=
  dQ.characterEquiv
    (actionInvariantCharacterOfSubgroup P K Q theta)

/-- Equivariance makes the first-stage correspondent invariant under the
quotient action of `P / Q`.  This is the exact character fed to the
second Glauberman correspondence. -/
def okuyamaWajimaProperBranchQuotientInvariantCorrespondent
    (dQ : StrongActionGlaubermanCorrespondence Q K p)
    (theta : ActionInvariantPPrimeIrreducibleCharacter P K p) :
    ActionInvariantPPrimeIrreducibleCharacter
      (P ⧸ Q) (FixedPoints.subgroup Q K) p :=
  quotientInvariantCorrespondent P K Q dQ.toAction theta

omit [Fact p.Prime] in
@[simp]
theorem okuyamaWajimaProperBranchQuotientInvariantCorrespondent_coe
    (dQ : StrongActionGlaubermanCorrespondence Q K p)
    (theta : ActionInvariantPPrimeIrreducibleCharacter P K p) :
    (okuyamaWajimaProperBranchQuotientInvariantCorrespondent
      P K Q dQ theta).1 =
      okuyamaWajimaProperBranchQCorrespondent
        P K Q dQ theta := by
  apply Subtype.ext
  rfl

/-- The second-stage `(P / Q)`-Glauberman correspondent, before
transport from iterated fixed points. -/
def okuyamaWajimaProperBranchQuotientCorrespondent
    (dQ : StrongActionGlaubermanCorrespondence Q K p)
    (dQuot :
      StrongActionGlaubermanCorrespondence
        (P ⧸ Q) (FixedPoints.subgroup Q K) p)
    (theta : ActionInvariantPPrimeIrreducibleCharacter P K p) :
    PPrimeIrreducibleCharacter
      (FixedPoints.subgroup (P ⧸ Q)
        (FixedPoints.subgroup Q K)) p :=
  dQuot.characterEquiv
    (okuyamaWajimaProperBranchQuotientInvariantCorrespondent
      P K Q dQ theta)

/-- The two-stage correspondent, transported through the canonical
identification `(K^Q)^(P/Q) ≃ K^P`. -/
def okuyamaWajimaProperBranchIteratedCorrespondent
    (dQ : StrongActionGlaubermanCorrespondence Q K p)
    (dQuot :
      StrongActionGlaubermanCorrespondence
        (P ⧸ Q) (FixedPoints.subgroup Q K) p)
    (theta : ActionInvariantPPrimeIrreducibleCharacter P K p) :
    PPrimeIrreducibleCharacter
      (FixedPoints.subgroup P K) p :=
  IrreducibleCharacter.pPrimeComapEquiv p
      (GroupTheory.iteratedFixedPointsEquiv P K Q).symm
    (okuyamaWajimaProperBranchQuotientCorrespondent
      P K Q dQ dQuot theta)

omit [Finite P] [Finite K] [Q.Normal] [Fact p.Prime] in
/-- The first-stage restriction multiplicity is prime to `p`. -/
theorem okuyamaWajimaProperBranchQ_multiplicity_isPPrime
    (dQ : StrongActionGlaubermanCorrespondence Q K p)
    (theta : ActionInvariantPPrimeIrreducibleCharacter P K p) :
    ¬p ∣
      restrictionMultiplicity
        (actionFixedPointsInclusion Q K)
        (okuyamaWajimaProperBranchQCorrespondent
          P K Q dQ theta).1
        theta.1.1 :=
  dQ.multiplicity_isPPrime
    (actionInvariantCharacterOfSubgroup P K Q theta)

omit [Fact p.Prime] in
/-- The second-stage restriction multiplicity is prime to `p`. -/
theorem okuyamaWajimaProperBranchQuotient_multiplicity_isPPrime
    (dQ : StrongActionGlaubermanCorrespondence Q K p)
    (dQuot :
      StrongActionGlaubermanCorrespondence
        (P ⧸ Q) (FixedPoints.subgroup Q K) p)
    (theta : ActionInvariantPPrimeIrreducibleCharacter P K p) :
    ¬p ∣
      restrictionMultiplicity
        (actionFixedPointsInclusion
          (P ⧸ Q) (FixedPoints.subgroup Q K))
        (okuyamaWajimaProperBranchQuotientCorrespondent
          P K Q dQ dQuot theta).1
        (okuyamaWajimaProperBranchQCorrespondent
          P K Q dQ theta).1 :=
  dQuot.multiplicity_isPPrime
    (okuyamaWajimaProperBranchQuotientInvariantCorrespondent
      P K Q dQ theta)

/-- The transported two-stage correspondent has restriction
multiplicity prime to `p` directly from `K` to `K^P`. -/
theorem okuyamaWajimaProperBranchIterated_multiplicity_isPPrime
    (dQ : StrongActionGlaubermanCorrespondence Q K p)
    (dQuot :
      StrongActionGlaubermanCorrespondence
        (P ⧸ Q) (FixedPoints.subgroup Q K) p)
    (theta : ActionInvariantPPrimeIrreducibleCharacter P K p) :
    ¬p ∣
      restrictionMultiplicity
        (actionFixedPointsInclusion P K)
        (okuyamaWajimaProperBranchIteratedCorrespondent
          P K Q dQ dQuot theta).1
        theta.1.1 :=
  strongIteratedGlaubermanCharacterEquiv_multiplicity_isPPrime
    P K Q dQ dQuot theta

/-- Strong uniqueness identifies the two-stage output with the output of
every strong `P`-Glauberman correspondence. -/
theorem okuyamaWajimaProperBranchIterated_eq_fullCorrespondent
    (dQ : StrongActionGlaubermanCorrespondence Q K p)
    (dQuot :
      StrongActionGlaubermanCorrespondence
        (P ⧸ Q) (FixedPoints.subgroup Q K) p)
    (dP : StrongActionGlaubermanCorrespondence P K p)
    (theta : ActionInvariantPPrimeIrreducibleCharacter P K p) :
    okuyamaWajimaProperBranchIteratedCorrespondent
        P K Q dQ dQuot theta =
      dP.characterEquiv theta := by
  apply Subtype.ext
  symm
  exact
    eq_strongIteratedGlaubermanCharacterEquiv_of_multiplicity_isPPrime
      P K Q dQ dQuot theta
      (dP.characterEquiv theta).1
      (dP.multiplicity_isPPrime theta)

/-- The strong `Q`-correspondence used in the proper branch exists
unconditionally in the coprime `p`-group setting. -/
def okuyamaWajimaProperBranchQStrongCorrespondence
    (hP : IsPGroup p P)
    (hK : GroupTheory.IsPPrimeGroup p K) :
    StrongActionGlaubermanCorrespondence Q K p :=
  Classical.choice
    (strongActionGlaubermanCorrespondenceOfPGroup
      cyclicStrongActionGlaubermanHypothesis
      Q K (hP.to_subgroup Q) hK)

/-- The strong `(P / Q)`-correspondence used in the second stage exists
unconditionally. -/
def okuyamaWajimaProperBranchQuotientStrongCorrespondence
    (hP : IsPGroup p P)
    (hK : GroupTheory.IsPPrimeGroup p K) :
    StrongActionGlaubermanCorrespondence
      (P ⧸ Q) (FixedPoints.subgroup Q K) p :=
  Classical.choice
    (strongActionGlaubermanCorrespondenceOfPGroup
      cyclicStrongActionGlaubermanHypothesis
      (P ⧸ Q) (FixedPoints.subgroup Q K)
      (hP.to_quotient Q)
      (hK.to_subgroup (FixedPoints.subgroup Q K)))

end Action

section AmbientConjugation

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (K P : Subgroup G) [K.Normal]
variable (Q : Subgroup P) [Q.Normal]

/-- The proper-branch subgroup `Q ≤ P`, viewed in the original ambient
group. -/
abbrev okuyamaWajimaProperBranchAmbientQ :
    Subgroup G :=
  Q.map P.subtype

/-- The canonical isomorphism from the internal subgroup `Q ≤ P` to its
ambient copy. -/
def okuyamaWajimaProperBranchAmbientQEquiv :
    Q ≃*
      okuyamaWajimaProperBranchAmbientQ P Q :=
  Subgroup.equivMapOfInjective
    Q P.subtype P.subtype_injective

omit [Finite G] [Q.Normal] in
@[simp]
theorem okuyamaWajimaProperBranchAmbientQEquiv_apply_coe
    (q : Q) :
    ((okuyamaWajimaProperBranchAmbientQEquiv
      P Q q :
        okuyamaWajimaProperBranchAmbientQ P Q) : G) =
      (q.1 : G) :=
  rfl

omit [Finite G] [Q.Normal] in
/-- The ambient copy of `Q` lies in `P`. -/
theorem okuyamaWajimaProperBranchAmbientQ_le_P :
    okuyamaWajimaProperBranchAmbientQ P Q ≤ P := by
  rintro _ ⟨q, _hq, rfl⟩
  exact q.2

local instance properBranchPConjugationAction :
    MulDistribMulAction P K :=
  subgroupConjugationMulDistribMulAction K P

local instance properBranchAmbientQConjugationAction :
    MulDistribMulAction
      (okuyamaWajimaProperBranchAmbientQ P Q) K :=
  subgroupConjugationMulDistribMulAction K
    (okuyamaWajimaProperBranchAmbientQ P Q)

/-- The action-level `Q`-fixed points are canonically the ambient
subgroup `C_K(Q)`. -/
def okuyamaWajimaProperBranchQFixedPointsEquiv :
    FixedPoints.subgroup Q K ≃*
      coprimeFixedPoints K
        (okuyamaWajimaProperBranchAmbientQ P Q) := by
  let eQ :=
    okuyamaWajimaProperBranchAmbientQEquiv P Q
  let eK : K ≃* K := MulEquiv.refl K
  have hequivariant :
      ∀ q : Q, ∀ k : K,
        eK (q • k) = eQ q • eK k := by
    intro q k
    apply Subtype.ext
    rfl
  exact
    (actionFixedPointsEquivOfEquivariant
        (okuyamaWajimaProperBranchAmbientQ P Q)
        Q K K eQ eK hequivariant).trans
      (subgroupConjugationFixedPointsEquiv K
        (okuyamaWajimaProperBranchAmbientQ P Q))

omit [Finite G] [Q.Normal] in
@[simp]
theorem okuyamaWajimaProperBranchQFixedPointsEquiv_apply_coe
    (x : FixedPoints.subgroup Q K) :
    ((okuyamaWajimaProperBranchQFixedPointsEquiv
      K P Q x :
        coprimeFixedPoints K
          (okuyamaWajimaProperBranchAmbientQ P Q)) : G) =
      ((x : K) : G) :=
  rfl

/-- Iterated action fixed points, transported all the way to the ambient
fixed-point subgroup `C_K(P)`. -/
def okuyamaWajimaProperBranchIteratedFixedPointsEquiv :
    FixedPoints.subgroup (P ⧸ Q)
        (FixedPoints.subgroup Q K) ≃*
      coprimeFixedPoints K P :=
  (GroupTheory.iteratedFixedPointsEquiv P K Q).trans
    (subgroupConjugationFixedPointsEquiv K P)

omit [Finite G] in
@[simp]
theorem okuyamaWajimaProperBranchIteratedFixedPointsEquiv_apply_coe
    (x :
      FixedPoints.subgroup (P ⧸ Q)
        (FixedPoints.subgroup Q K)) :
    ((okuyamaWajimaProperBranchIteratedFixedPointsEquiv
      K P Q x : coprimeFixedPoints K P) : G) =
      (((x : FixedPoints.subgroup Q K) : K) : G) :=
  rfl

/-- A `P`-invariant source character is invariant under the ambient copy
of every proper-branch subgroup `Q ≤ P`. -/
def okuyamaWajimaProperBranchAmbientQInvariantCharacter
    (theta : PInvariantPPrimeIrreducibleCharacter K P p) :
    PInvariantPPrimeIrreducibleCharacter K
      (okuyamaWajimaProperBranchAmbientQ P Q) p :=
  ⟨theta.1,
    fun _g hg ↦
      theta.2
        (okuyamaWajimaProperBranchAmbientQ_le_P
          P Q hg)⟩

/-- Transport the first-stage action correspondent to the literal
ambient subgroup `C_K(Q)`. -/
def okuyamaWajimaProperBranchAmbientQCorrespondent
    (dQ : StrongActionGlaubermanCorrespondence Q K p)
    (theta : PInvariantPPrimeIrreducibleCharacter K P p) :
    PPrimeIrreducibleCharacter
      (coprimeFixedPoints K
        (okuyamaWajimaProperBranchAmbientQ P Q)) p :=
  IrreducibleCharacter.pPrimeComapEquiv p
      (okuyamaWajimaProperBranchQFixedPointsEquiv
        K P Q).symm
    (okuyamaWajimaProperBranchQCorrespondent
      P K Q dQ
      (pInvariantCharacterEquivActionInvariant K P theta))

/-- Transport the two-stage action correspondent to the literal ambient
subgroup `C_K(P)`. -/
def okuyamaWajimaProperBranchAmbientIteratedCorrespondent
    (dQ : StrongActionGlaubermanCorrespondence Q K p)
    (dQuot :
      StrongActionGlaubermanCorrespondence
        (P ⧸ Q) (FixedPoints.subgroup Q K) p)
    (theta : PInvariantPPrimeIrreducibleCharacter K P p) :
    PPrimeIrreducibleCharacter (coprimeFixedPoints K P) p :=
  IrreducibleCharacter.pPrimeComapEquiv p
      (subgroupConjugationFixedPointsEquiv K P).symm
    (okuyamaWajimaProperBranchIteratedCorrespondent
      P K Q dQ dQuot
      (pInvariantCharacterEquivActionInvariant K P theta))

omit [Fact p.Prime] [Q.Normal] in
/-- The ambient first-stage output is the ordinary `Q`-Glauberman
correspondent, for every ordinary correspondence. -/
theorem okuyamaWajimaProperBranchAmbientQCorrespondent_eq
    (dQ : StrongActionGlaubermanCorrespondence Q K p)
    (gQ :
      GlaubermanCorrespondence K
        (okuyamaWajimaProperBranchAmbientQ P Q) p)
    (theta : PInvariantPPrimeIrreducibleCharacter K P p) :
    okuyamaWajimaProperBranchAmbientQCorrespondent
        K P Q dQ theta =
      gQ.characterEquiv
        (okuyamaWajimaProperBranchAmbientQInvariantCharacter
          K P Q theta) := by
  apply gQ.eq_correspondent_of_multiplicity_isPPrime
  change
    ¬p ∣
      restrictionMultiplicity
        (coprimeFixedPointsInclusion K
          (okuyamaWajimaProperBranchAmbientQ P Q))
        ((okuyamaWajimaProperBranchQCorrespondent
          P K Q dQ
          (pInvariantCharacterEquivActionInvariant
            K P theta)).1.comap
          (okuyamaWajimaProperBranchQFixedPointsEquiv
            K P Q).symm)
        theta.1.1
  let eQ :=
    okuyamaWajimaProperBranchAmbientQEquiv P Q
  let eK : K ≃* K := MulEquiv.refl K
  have hequivariant :
      ∀ q : Q, ∀ k : K,
        eK (q • k) = eQ q • eK k := by
    intro q k
    apply Subtype.ext
    rfl
  let eAction :=
    actionFixedPointsEquivOfEquivariant
      (okuyamaWajimaProperBranchAmbientQ P Q)
      Q K K eQ eK hequivariant
  let eAmbient :=
    subgroupConjugationFixedPointsEquiv K
      (okuyamaWajimaProperBranchAmbientQ P Q)
  have hmultAction :=
    dQ.multiplicity_isPPrime
      (actionInvariantCharacterOfSubgroup P K Q
        (pInvariantCharacterEquivActionInvariant K P theta))
  have htransport :
      restrictionMultiplicity
          (coprimeFixedPointsInclusion K
            (okuyamaWajimaProperBranchAmbientQ P Q))
          ((okuyamaWajimaProperBranchQCorrespondent
            P K Q dQ
            (pInvariantCharacterEquivActionInvariant
              K P theta)).1.comap
            (okuyamaWajimaProperBranchQFixedPointsEquiv
              K P Q).symm)
          theta.1.1 =
        restrictionMultiplicity
          (actionFixedPointsInclusion Q K)
          (okuyamaWajimaProperBranchQCorrespondent
            P K Q dQ
            (pInvariantCharacterEquivActionInvariant
              K P theta)).1
          theta.1.1 := by
    let phi :=
      (okuyamaWajimaProperBranchQCorrespondent
        P K Q dQ
        (pInvariantCharacterEquivActionInvariant K P theta)).1
    have hconj :=
      restrictionMultiplicity_subgroupConjugationFixedPointsEquiv
        K (okuyamaWajimaProperBranchAmbientQ P Q)
        (phi.comap eAction.symm) theta.1.1
    have hcomm :
        eK.toMonoidHom.comp
            (actionFixedPointsInclusion
              (okuyamaWajimaProperBranchAmbientQ P Q) K) =
          (actionFixedPointsInclusion Q K).comp
            eAction.symm.toMonoidHom := by
      ext x
      rfl
    change
      restrictionMultiplicity
          (coprimeFixedPointsInclusion K
            (okuyamaWajimaProperBranchAmbientQ P Q))
          (phi.comap (eAction.trans eAmbient).symm)
          theta.1.1 =
        restrictionMultiplicity
          (actionFixedPointsInclusion Q K)
          phi theta.1.1
    have hchar :
        phi.comap (eAction.trans eAmbient).symm =
          (phi.comap eAction.symm).comap eAmbient.symm := by
      apply IrreducibleCharacter.ext
      funext x
      rfl
    rw [hchar]
    rw [hconj]
    have haction' :=
      restrictionMultiplicity_comap_equiv
        eK eAction.symm
        (actionFixedPointsInclusion Q K)
        (actionFixedPointsInclusion
          (okuyamaWajimaProperBranchAmbientQ P Q) K)
        hcomm phi theta.1.1
    simpa [eK] using haction'
  rw [htransport]
  exact hmultAction

omit [Fact p.Prime] [Q.Normal] in
/-- The first-stage correspondent has prime-to-`p` restriction
multiplicity in the literal ambient subgroup coordinates. -/
theorem okuyamaWajimaProperBranchAmbientQ_multiplicity_isPPrime
    (dQ : StrongActionGlaubermanCorrespondence Q K p)
    (gQ :
      GlaubermanCorrespondence K
        (okuyamaWajimaProperBranchAmbientQ P Q) p)
    (theta : PInvariantPPrimeIrreducibleCharacter K P p) :
    ¬p ∣
      restrictionMultiplicity
        (coprimeFixedPointsInclusion K
          (okuyamaWajimaProperBranchAmbientQ P Q))
        (okuyamaWajimaProperBranchAmbientQCorrespondent
          K P Q dQ theta).1
        theta.1.1 := by
  rw [okuyamaWajimaProperBranchAmbientQCorrespondent_eq
    K P Q dQ gQ theta]
  exact
    gQ.multiplicity_isPPrime
      (okuyamaWajimaProperBranchAmbientQInvariantCharacter
        K P Q theta)

/-- The ambient two-stage output is the ordinary `P`-Glauberman
correspondent.  Strong realization removes all intermediate degree
hypotheses. -/
theorem okuyamaWajimaProperBranchAmbientIteratedCorrespondent_eq
    (hP : IsPGroup p P)
    (hK : GroupTheory.IsPPrimeGroup p K)
    (dQ : StrongActionGlaubermanCorrespondence Q K p)
    (dQuot :
      StrongActionGlaubermanCorrespondence
        (P ⧸ Q) (FixedPoints.subgroup Q K) p)
    (gP : GlaubermanCorrespondence K P p)
    (theta : PInvariantPPrimeIrreducibleCharacter K P p) :
    okuyamaWajimaProperBranchAmbientIteratedCorrespondent
        K P Q dQ dQuot theta =
      gP.characterEquiv theta := by
  obtain ⟨dP, hdP⟩ :=
    gP.exists_strongActionRealization K P hP hK
  have haction :=
    okuyamaWajimaProperBranchIterated_eq_fullCorrespondent
      P K Q dQ dQuot dP
      (pInvariantCharacterEquivActionInvariant K P theta)
  have hambient :
      (glaubermanCorrespondenceOfStrongConjugationAction
        K P dP).characterEquiv theta =
        gP.characterEquiv theta := by
    rw [hdP]
  rw [← hambient]
  apply Subtype.ext
  let e :=
    subgroupConjugationFixedPointsEquiv K P
  exact
    congrArg
      (fun chi : IrreducibleCharacter
          (FixedPoints.subgroup P K) =>
        chi.comap e.symm)
      (congrArg Subtype.val haction)

/-- In particular, the two-stage output has the defining
prime-to-`p` restriction multiplicity in ambient subgroup coordinates. -/
theorem okuyamaWajimaProperBranchAmbientIterated_multiplicity_isPPrime
    (dQ : StrongActionGlaubermanCorrespondence Q K p)
    (dQuot :
      StrongActionGlaubermanCorrespondence
        (P ⧸ Q) (FixedPoints.subgroup Q K) p)
    (theta : PInvariantPPrimeIrreducibleCharacter K P p) :
    ¬p ∣
      restrictionMultiplicity
        (coprimeFixedPointsInclusion K P)
        (okuyamaWajimaProperBranchAmbientIteratedCorrespondent
          K P Q dQ dQuot theta).1
        theta.1.1 := by
  change
    ¬p ∣
      restrictionMultiplicity
        (coprimeFixedPointsInclusion K P)
        ((okuyamaWajimaProperBranchIteratedCorrespondent
          P K Q dQ dQuot
          (pInvariantCharacterEquivActionInvariant
            K P theta)).1.comap
          (subgroupConjugationFixedPointsEquiv K P).symm)
        theta.1.1
  rw [
    restrictionMultiplicity_subgroupConjugationFixedPointsEquiv
      K P]
  exact
    okuyamaWajimaProperBranchIterated_multiplicity_isPPrime
      P K Q dQ dQuot
      (pInvariantCharacterEquivActionInvariant K P theta)

/-- Minimal normalizer hypothesis needed to turn the first-stage
correspondent into the invariant kernel character of the recursive
problem. -/
def OkuyamaWajimaProperBranchNormalizerInvariant
    (theta : PInvariantPPrimeIrreducibleCharacter K P p) : Prop :=
  Subgroup.normalizer
      (okuyamaWajimaProperBranchAmbientQ P Q : Set G) ≤
    IrreducibleCharacter.inertia K theta.1.1

omit [Finite G] [Fact p.Prime] [Q.Normal] in
/-- Full ambient invariance implies the exact normalizer-invariance
condition used by the proper-branch adapter. -/
theorem okuyamaWajimaProperBranchNormalizerInvariant_of_ambientInvariant
    (theta : PInvariantPPrimeIrreducibleCharacter K P p)
    (hinvariant :
      ∀ g : G, g • theta.1.1 = theta.1.1) :
    OkuyamaWajimaProperBranchNormalizerInvariant
      K P Q theta := by
  intro g _hg
  rw [IrreducibleCharacter.mem_inertia_iff]
  exact hinvariant g

omit [Q.Normal] in
/-- Under the exact source normalizer-invariance condition, the ordinary
`Q`-Glauberman correspondent is fixed by the full normalizer of the
ambient copy of `Q`. -/
theorem okuyamaWajimaProperBranchQCorrespondent_invariant_normalizer
    (gQ :
      GlaubermanCorrespondence K
        (okuyamaWajimaProperBranchAmbientQ P Q) p)
    (theta : PInvariantPPrimeIrreducibleCharacter K P p)
    (hinvariant :
      OkuyamaWajimaProperBranchNormalizerInvariant
        K P Q theta)
    (g :
      Subgroup.normalizer
        (okuyamaWajimaProperBranchAmbientQ P Q : Set G)) :
    coprimeFixedPointsNormalizerAction K
        (okuyamaWajimaProperBranchAmbientQ P Q) g •
        (gQ.characterEquiv
          (okuyamaWajimaProperBranchAmbientQInvariantCharacter
            K P Q theta)).1 =
      (gQ.characterEquiv
        (okuyamaWajimaProperBranchAmbientQInvariantCharacter
          K P Q theta)).1 := by
  let thetaQ :=
    okuyamaWajimaProperBranchAmbientQInvariantCharacter
      K P Q theta
  have hsource :
      invariantCharacterConjByNormalizer K
          (okuyamaWajimaProperBranchAmbientQ P Q)
          g thetaQ =
        thetaQ := by
    apply Subtype.ext
    apply Subtype.ext
    rw [invariantCharacterConjByNormalizer_coe]
    exact
      (IrreducibleCharacter.mem_inertia_iff
        K theta.1.1 (g : G)).mp
        (hinvariant g.2)
  have hcovariance :=
    gQ.characterEquiv_conjByNormalizer K
      (okuyamaWajimaProperBranchAmbientQ P Q)
      g thetaQ
  rw [hsource] at hcovariance
  exact congrArg Subtype.val hcovariance.symm

omit [Q.Normal] in
/-- The first-stage action correspondent, after canonical transport to
`C_K(Q)`, has full normalizer invariance under the same minimal source
hypothesis. -/
theorem okuyamaWajimaProperBranchAmbientQCorrespondent_invariant_normalizer
    (dQ : StrongActionGlaubermanCorrespondence Q K p)
    (gQ :
      GlaubermanCorrespondence K
        (okuyamaWajimaProperBranchAmbientQ P Q) p)
    (theta : PInvariantPPrimeIrreducibleCharacter K P p)
    (hinvariant :
      OkuyamaWajimaProperBranchNormalizerInvariant
        K P Q theta)
    (g :
      Subgroup.normalizer
        (okuyamaWajimaProperBranchAmbientQ P Q : Set G)) :
    coprimeFixedPointsNormalizerAction K
        (okuyamaWajimaProperBranchAmbientQ P Q) g •
        (okuyamaWajimaProperBranchAmbientQCorrespondent
          K P Q dQ theta).1 =
      (okuyamaWajimaProperBranchAmbientQCorrespondent
        K P Q dQ theta).1 := by
  rw [okuyamaWajimaProperBranchAmbientQCorrespondent_eq
    K P Q dQ gQ theta]
  exact
    okuyamaWajimaProperBranchQCorrespondent_invariant_normalizer
      K P Q gQ theta hinvariant g

end AmbientConjugation

section CyclicQuotientSubgroup

variable (M : Type) (P : Type) (K : Type)
variable [Group M] [Group P] [Group K]
variable [MulDistribMulAction M P]
variable [MulDistribMulAction P K]
variable [Finite M] [Finite P] [Finite K]
variable {L : Subgroup M}
variable {p : ℕ} [Fact p.Prime]

/-- The subgroup constructed by the Gorenstein step can be fed directly
to the proper-branch transitivity adapter. -/
abbrev okuyamaWajimaProperBranchSelectedQ
    (d :
      GroupTheory.OkuyamaWajimaCyclicQuotientSubgroup
        M P L) :
    Subgroup P :=
  d.fixedPointPreimage

/-- The first-stage correspondent for the actual subgroup selected in
the proper branch. -/
def okuyamaWajimaSelectedQCorrespondent
    (d :
      GroupTheory.OkuyamaWajimaCyclicQuotientSubgroup
        M P L)
    (dQ :
      StrongActionGlaubermanCorrespondence
        d.fixedPointPreimage K p)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter P K p) :
    PPrimeIrreducibleCharacter
      (FixedPoints.subgroup d.fixedPointPreimage K) p :=
  okuyamaWajimaProperBranchQCorrespondent
    P K d.fixedPointPreimage dQ theta

omit [Finite M] in
/-- Source-faithful transitivity for the subgroup selected by the
Gorenstein step: the two successive correspondents equal every strong
`P`-correspondent. -/
theorem okuyamaWajimaSelectedQIteratedCorrespondent_eq
    (d :
      GroupTheory.OkuyamaWajimaCyclicQuotientSubgroup
        M P L)
    (dQ :
      StrongActionGlaubermanCorrespondence
        d.fixedPointPreimage K p)
    (dQuot :
      StrongActionGlaubermanCorrespondence
        (P ⧸ d.fixedPointPreimage)
        (FixedPoints.subgroup d.fixedPointPreimage K) p)
    (dP : StrongActionGlaubermanCorrespondence P K p)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter P K p) :
    okuyamaWajimaProperBranchIteratedCorrespondent
        P K d.fixedPointPreimage dQ dQuot theta =
      dP.characterEquiv theta :=
  okuyamaWajimaProperBranchIterated_eq_fullCorrespondent
    P K d.fixedPointPreimage dQ dQuot dP theta

end CyclicQuotientSubgroup

end McKayConjecture
