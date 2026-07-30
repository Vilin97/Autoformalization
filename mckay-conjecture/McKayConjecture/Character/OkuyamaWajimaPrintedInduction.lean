/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ExtensionEquivalenceTransport
import McKayConjecture.Character.GlaubermanTrivialAction
import McKayConjecture.Character.OkuyamaWajimaFullFixedBurnsideAdapter
import McKayConjecture.Character.OkuyamaWajimaPrintedExtension
import McKayConjecture.Character.OkuyamaWajimaProperBranchCoordinates
import McKayConjecture.GroupTheory.GorensteinCyclicImageSectionExistence

/-!
# Strong-induction assembly for the printed Okuyama--Wajima theorem

This file supplies the well-founded-recursion layer of the direct proof of
Okuyama--Wajima, Theorem 2(3).

The induction statement is the literal extension equivalence in the
ambient group:

* the invariant source character on the normal `p'`-kernel extends to the
  ambient group if and only if
* its Glauberman correspondent extends to the Sylow normalizer.

The proper branch already constructs the two smaller groups
`N_G(Q) / Q` and `H = Q M K`, proves that both have smaller order, and
composes the two recursive conclusions with Navarro prime-power ascent.
The only data needed here are therefore the two coordinate adapters which
turn the universal induction statements on those smaller groups into the
exact character-triple propositions expected by that branch.

No normality of `H` is used.  Its cardinality and both ascent indices come
from the exact set-product scope in
`OkuyamaWajimaProperBranchGroupScope`.

The file also records the unconditional Gorenstein branch dichotomy.  The
remaining source-level work is consequently localized to:

1. the full-fixed outer character-coordinate and ascent assembly around
   the already proved coprime Burnside-basis and Isaacs 13.29 theorems; and
2. the two explicit recursive coordinate adapters below.

## References

* T. Okuyama and M. Wajima, *Character correspondence and p-blocks of
  p-solvable groups*, Osaka J. Math. 17 (1980), 801--806, pp. 803--804.
-/

noncomputable section

namespace McKayConjecture

open CharacterTriple
open CliffordCorrespondence
open GroupTheory

/-! ## The unconditional Gorenstein dichotomy -/

section GorensteinDichotomy

variable {M P : Type}
variable [Group M] [Group P]
variable [MulDistribMulAction M P]
variable [Finite M] [Finite P] [Nontrivial P]
variable {p : ℕ} [Fact p.Prime]

/-- Gorenstein's hypotheses now unconditionally produce exactly the
full-fixed/proper-nontrivial dichotomy used in the printed induction. -/
theorem exists_okuyamaWajima_cyclicQuotientSubgroup_dichotomy
    (hP : IsPGroup p P)
    (hM : IsPPrimeGroup p M)
    (L : Subgroup M) [L.Normal]
    (hL : L = okuyamaWajimaActionKernel M P)
    (hML : IsMulCommutative (M ⧸ L)) :
    ∃ d : OkuyamaWajimaCyclicQuotientSubgroup M P L,
      d.fixedPoints = ⊤ ∨
        ((⊥ : Subgroup (Abelianization P)) < d.fixedPoints ∧
          d.fixedPoints < ⊤) := by
  have hGorenstein :
      GorensteinCyclicQuotientSubgroupExistenceInput
        M P p L hP hM hL hML :=
    GroupTheory.GorensteinCyclicImageSectionExistence.gorensteinCyclicQuotientSubgroupExistenceInput
      hP hM L hL hML
  obtain ⟨d⟩ :=
    exists_okuyamaWajima_cyclicQuotientSubgroup
      L hP hM hL hML hGorenstein
  exact ⟨d, d.fixedPoints_eq_top_or_proper_nontrivial⟩

end GorensteinDichotomy

/-! ## The abelian quotient in the canonical complement -/

section ComplementActionQuotient

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- The printed commutator hypothesis makes the conjugation-action
quotient of the canonical `p'`-complement commutative.

If `M` is the lifted complement and `L = C_M(P)` is the action kernel,
then a commutator in `M` lies in `K P` by the ambient hypothesis.  The
exact complement intersection `(C_K(P) P) ∩ M = C_K(P)` puts it in
`C_K(P) ≤ L`. -/
theorem okuyamaWajimaAmbientComplement_actionKernel_quotient_isMulCommutative
    (K : Subgroup G) [K.Normal]
    (P : Sylow p G)
    (hK : IsPPrimeGroup p K)
    (hKP : (K ⊔ (P : Subgroup G)).Normal)
    (hcommutativeQuotient :
      _root_.commutator G ≤ K ⊔ (P : Subgroup G)) :
    let M :=
      okuyamaWajimaProperBranchComplement K P hK hKP
    let hM :
        M ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
      okuyamaWajimaAmbientComplement_le_normalizer
        P K hK hKP
    letI : MulDistribMulAction M P :=
      OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
        M P hM
    IsMulCommutative
      (M ⧸ okuyamaWajimaActionKernel M P) := by
  let M :=
    okuyamaWajimaProperBranchComplement K P hK hKP
  let hM :
      M ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    okuyamaWajimaAmbientComplement_le_normalizer
      P K hK hKP
  letI : MulDistribMulAction M P :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      M P hM
  apply
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
  intro x hx
  rw [OkuyamaWajimaFullFixedCoordinates.selectedActionKernel_eq_centralizer_subgroupOf]
  have hxmap :
      ((x : M) : G) ∈
        (_root_.commutator M).map M.subtype :=
    Subgroup.mem_map_of_mem M.subtype hx
  rw [Subgroup.map_subtype_commutator] at hxmap
  have hxG :
      ((x : M) : G) ∈ _root_.commutator G :=
    (Subgroup.commutator_mono le_top le_top) hxmap
  have hxNormalProduct :
      ((x : M) : G) ∈
        K ⊔ (P : Subgroup G) :=
    hcommutativeQuotient hxG
  have hxNormalizer :
      ((x : M) : G) ∈
        Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    hM x.2
  have hxFixedSup :
      ((x : M) : G) ∈
        okuyamaWajimaFixedPoints K (P : Subgroup G) ⊔
          (P : Subgroup G) := by
    rw [← normalizer_inf_normalProduct_eq_fixedPoints_sup
      P K hK]
    exact ⟨hxNormalizer, hxNormalProduct⟩
  have hxIntersection :
      ((x : M) : G) ∈
        (okuyamaWajimaFixedPoints K (P : Subgroup G) ⊔
            (P : Subgroup G)) ⊓ M :=
    ⟨hxFixedSup, x.2⟩
  rw [show
      (okuyamaWajimaFixedPoints K (P : Subgroup G) ⊔
          (P : Subgroup G)) ⊓ M =
        okuyamaWajimaFixedPoints K (P : Subgroup G) by
      exact
        fixedPoints_sup_sylow_inf_ambientComplement_eq_fixedPoints
          P K hK hKP]
    at hxIntersection
  exact hxIntersection.2

/-- The canonical complement therefore has an unconditional Gorenstein
datum and the exact branch dichotomy, once the Sylow subgroup is
nontrivial. -/
theorem exists_okuyamaWajima_canonicalComplement_cyclicQuotientSubgroup_dichotomy
    (K : Subgroup G) [K.Normal]
    (P : Sylow p G)
    [Nontrivial P]
    (hK : IsPPrimeGroup p K)
    (hKP : (K ⊔ (P : Subgroup G)).Normal)
    (hcommutativeQuotient :
      _root_.commutator G ≤ K ⊔ (P : Subgroup G)) :
    let M :=
      okuyamaWajimaProperBranchComplement K P hK hKP
    let hM :
        M ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
      okuyamaWajimaAmbientComplement_le_normalizer
        P K hK hKP
    letI : MulDistribMulAction M P :=
      OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
        M P hM
    let L := okuyamaWajimaActionKernel M P
    ∃ d : OkuyamaWajimaCyclicQuotientSubgroup M P L,
      d.fixedPoints = ⊤ ∨
        ((⊥ : Subgroup (Abelianization P)) < d.fixedPoints ∧
          d.fixedPoints < ⊤) := by
  let M :=
    okuyamaWajimaProperBranchComplement K P hK hKP
  let hM :
      M ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    okuyamaWajimaAmbientComplement_le_normalizer
      P K hK hKP
  letI : MulDistribMulAction M P :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      M P hM
  let L := okuyamaWajimaActionKernel M P
  have hMPrime : IsPPrimeGroup p M :=
    okuyamaWajimaAmbientComplement_isPPrimeGroup
      K P hK hKP
  have hML : IsMulCommutative (M ⧸ L) :=
    okuyamaWajimaAmbientComplement_actionKernel_quotient_isMulCommutative
      K P hK hKP hcommutativeQuotient
  exact
    exists_okuyamaWajima_cyclicQuotientSubgroup_dichotomy
      P.isPGroup' hMPrime L rfl hML

end ComplementActionQuotient

/-! ## The exact universal induction statement -/

section InductionStatement

variable {p : ℕ} [Fact p.Prime]

/-- The direct printed extension statement for one finite ambient group.

The structural hypotheses are precisely those used on pp. 803--804:
`K` is a normal `p'`-subgroup, `P` is Sylow, the ambient group is
generated by `K` and `N_G(P)`, and the quotient by `K P` is commutative.
The conclusion uses the canonical character triples already employed by
the proper-branch recursion module. -/
def OkuyamaWajimaPrintedExtensionStatement
    (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (K : Subgroup G) [K.Normal]
      (P : Sylow p G),
    letI : MulDistribMulAction P K :=
      subgroupConjugationMulDistribMulAction K (P : Subgroup G)
    ∀ (_hK : IsPPrimeGroup p K)
      (_hproduct :
        K ⊔ Subgroup.normalizer ((P : Subgroup G) : Set G) = ⊤)
      (_hcommutativeQuotient :
        _root_.commutator G ≤ K ⊔ (P : Subgroup G))
      (theta :
        PInvariantPPrimeIrreducibleCharacter
          K (P : Subgroup G) p)
      (hinvariant :
        ∀ g : G, g • theta.1.1 = theta.1.1)
      (gP :
        GlaubermanCorrespondence K (P : Subgroup G) p),
      OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
          K P theta hinvariant gP ↔
        OkuyamaWajimaProperBranchThetaExtendsToG
          K P theta hinvariant

/-- One cardinality-induction step for the direct printed extension
statement. -/
def OkuyamaWajimaPrintedExtensionInductionStep
    (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    (∀ (H : Type) [Group H] [Finite H],
      Nat.card H < Nat.card G →
        OkuyamaWajimaPrintedExtensionStatement (p := p) H) →
      OkuyamaWajimaPrintedExtensionStatement (p := p) G

/-- Strong induction on group order from a source-faithful induction
step.  This is the well-founded recursion hidden in the prose proof on
pp. 803--804. -/
theorem okuyamaWajimaPrintedExtensionStatement_of_inductionStep
    (step :
      OkuyamaWajimaPrintedExtensionInductionStep
        p)
    (G : Type) [Group G] [Finite G] :
    OkuyamaWajimaPrintedExtensionStatement (p := p) G := by
  have all :
      ∀ n : ℕ,
        (∀ m < n,
          ∀ (H : Type) [Group H] [Finite H],
            Nat.card H = m →
              OkuyamaWajimaPrintedExtensionStatement
                (p := p) H) →
          ∀ (H : Type) [Group H] [Finite H],
            Nat.card H = n →
              OkuyamaWajimaPrintedExtensionStatement
                (p := p) H := by
    intro n ih H _ _ hcard
    apply step H
    intro Y _ _ hsmall
    exact
      ih (Nat.card Y)
        (by simpa only [hcard] using hsmall)
        Y rfl
  exact
    Nat.strong_induction_on
      (Nat.card G)
      (p := fun n =>
        ∀ (H : Type) [Group H] [Finite H],
          Nat.card H = n →
            OkuyamaWajimaPrintedExtensionStatement
              (p := p) H)
      all G rfl

end InductionStatement

/-! ## Automatic recursive calls in the proper branch -/

section ProperBranchInduction

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (K : Subgroup G) [K.Normal]
variable (P : Sylow p G)
variable (Q : Subgroup P) [Q.Normal]
variable (M : Subgroup G)

local instance printedInductionPConjugationAction :
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
variable
  (gP :
    GlaubermanCorrespondence K (P : Subgroup G) p)

/-- The two remaining coordinate maps in the proper branch.

The universal induction hypotheses already know the printed theorem on
the two smaller ambient groups.  These maps merely identify those two
specializations with the literal quotient and subgroup character triples
constructed in `OkuyamaWajimaProperBranchRecursion`.

Keeping the maps separate prevents either recursive character transport
from being hidden inside a monolithic induction premise. -/
structure OkuyamaWajimaProperBranchInductionAdapters where
  /-- Transport the theorem on `N_G(Q) / Q` to the first recursive
  extension equivalence. -/
  quotient :
    OkuyamaWajimaPrintedExtensionStatement
        (p := p)
        (okuyamaWajimaProperBranchNormalizerQuotient P Q) →
      OkuyamaWajimaProperBranchQuotientInductionHypothesis
        K P Q theta hinvariant gQ gP
  /-- Transport the theorem on `H = Q M K` to the second recursive
  extension equivalence. -/
  subgroup :
    OkuyamaWajimaPrintedExtensionStatement
        (p := p)
        (okuyamaWajimaProperBranchH K P Q M) →
      OkuyamaWajimaProperBranchSubgroupInductionHypothesis
        K P Q M theta hinvariant gQ

/-- Strong induction automatically supplies both recursive conclusions in
the proper branch.  The group scope supplies both strict inequalities and
all Navarro prime-power ascent data; in particular this theorem assumes no
normality of `H`. -/
theorem okuyamaWajimaProperBranch_extension_iff_of_smallerStatements
    (hK : IsPPrimeGroup p K)
    (scope :
      OkuyamaWajimaProperBranchGroupScope K P Q M)
    (adapters :
      OkuyamaWajimaProperBranchInductionAdapters
        K P Q M theta hinvariant gQ gP)
    (ih :
      ∀ (H : Type) [Group H] [Finite H],
        Nat.card H < Nat.card G →
          OkuyamaWajimaPrintedExtensionStatement
            (p := p) H) :
    OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
        K P theta hinvariant gP ↔
      OkuyamaWajimaProperBranchThetaExtendsToG
        K P theta hinvariant := by
  apply
    okuyamaWajimaProperBranch_extension_iff
      K P Q M theta hinvariant gQ gP hK scope
  · exact
      adapters.quotient
        (ih
          (okuyamaWajimaProperBranchNormalizerQuotient P Q)
          scope.normalizerQuotient_card_lt)
  · exact
      adapters.subgroup
        (ih
          (okuyamaWajimaProperBranchH K P Q M)
          scope.H_card_lt)

end ProperBranchInduction

/-! ## Full-fixed outer assembly -/

section FullFixedOuterAssembly

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (K : Subgroup G) [K.Normal]
variable (P : Sylow p G)

local instance fullFixedOuterPConjugationAction :
    MulDistribMulAction P K :=
  subgroupConjugationMulDistribMulAction K (P : Subgroup G)

variable
  (theta :
    PInvariantPPrimeIrreducibleCharacter
      K (P : Subgroup G) p)
  (hinvariant :
    ∀ g : G, g • theta.1.1 = theta.1.1)
  (gP :
    GlaubermanCorrespondence K (P : Subgroup G) p)

/-- The exact two-direction character-coordinate/ascent adapter around
the completed full-fixed maximal-fibre theorems.

The inner target-to-source implication is supplied by
`okuyamaWajimaFullFixed_exists_extension_automatic`.  The reverse inner
implication is supplied, without Isaacs 13.28, by
`okuyamaWajimaFullFixed_exists_target_extension_of_fixedSourceExtension_automatic`.
Thus the two fields below retain only transport to the selected subgroup
and the outer cyclic/prime-power ascent steps. -/
structure OkuyamaWajimaFullFixedOuterAssemblyInput : Prop where
  /-- Forward low-level plan: restrict a normalizer extension to the
  Gorenstein-selected target, identify its base character with the
  transported `P`-correspondent, apply
  `okuyamaWajimaFullFixed_exists_extension_automatic`, and ascend from
  `U K` to `G` through the cyclic outer quotient. -/
  source_of_target :
    OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
        K P theta hinvariant gP →
      OkuyamaWajimaProperBranchThetaExtendsToG
        K P theta hinvariant
  /-- Reverse low-level plan: restrict a source extension to `U K`,
  prove its `P`-invariance and triviality of the `P`-action on
  `(U K) / K`, identify the fixed normal correspondent with the
  transported `P`-correspondent, apply
  `okuyamaWajimaFullFixed_exists_target_extension_of_fixedSourceExtension_automatic`,
  and ascend from `U` to `N_G(P)`.  All-source invariance is automatic
  inside that theorem by Gallagher twisting. -/
  target_of_source :
    OkuyamaWajimaProperBranchThetaExtendsToG
        K P theta hinvariant →
      OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
        K P theta hinvariant gP

/-- The two outer full-fixed implications assemble into the exact printed
extension equivalence. -/
theorem okuyamaWajimaFullFixed_extension_iff_of_outerAssembly
    (h :
      OkuyamaWajimaFullFixedOuterAssemblyInput
        K P theta hinvariant gP) :
    OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
        K P theta hinvariant gP ↔
      OkuyamaWajimaProperBranchThetaExtendsToG
        K P theta hinvariant :=
  ⟨h.source_of_target, h.target_of_source⟩

end FullFixedOuterAssembly

/-! ## Canonical branch selection and automatic proper group scope -/

section CanonicalBranchSelection

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- A canonical ordinary Glauberman correspondence for the
Gorenstein-selected ambient subgroup `Q`. -/
noncomputable def
    okuyamaWajimaProperBranchSelectedGlaubermanCorrespondence
    (K : Subgroup G) [K.Normal]
    (P : Sylow p G)
    (hK : IsPPrimeGroup p K)
    (hKP : (K ⊔ (P : Subgroup G)).Normal) :
    let M :=
      okuyamaWajimaProperBranchComplement K P hK hKP
    let hM :
        M ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
      okuyamaWajimaAmbientComplement_le_normalizer
        P K hK hKP
    letI : MulDistribMulAction M P :=
      OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
        M P hM
    ∀ {L : Subgroup M}
      (d : OkuyamaWajimaCyclicQuotientSubgroup M P L),
      GlaubermanCorrespondence K
        (okuyamaWajimaProperBranchSelectedAmbientQ
          K P hK hKP d) p := by
  let M :=
    okuyamaWajimaProperBranchComplement K P hK hKP
  let hM :
      M ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    okuyamaWajimaAmbientComplement_le_normalizer
      P K hK hKP
  letI : MulDistribMulAction M P :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      M P hM
  change
    ∀ {L : Subgroup M}
      (d : OkuyamaWajimaCyclicQuotientSubgroup M P L),
      GlaubermanCorrespondence K
        (okuyamaWajimaProperBranchSelectedAmbientQ
          K P hK hKP d) p
  intro L d
  exact
    Classical.choice
      (exists_glaubermanCorrespondence_of_cyclicStrongAction
        K
        (okuyamaWajimaProperBranchSelectedAmbientQ
          K P hK hKP d)
        cyclicStrongActionGlaubermanHypothesis
        (properBranchSelectedQ_isPGroup
          K P hK hKP d)
        hK)

variable (K : Subgroup G) [K.Normal]
variable (P : Sylow p G)

local instance canonicalBranchPConjugationAction :
    MulDistribMulAction P K :=
  subgroupConjugationMulDistribMulAction K (P : Subgroup G)

variable
  (theta :
    PInvariantPPrimeIrreducibleCharacter
      K (P : Subgroup G) p)
  (hinvariant :
    ∀ g : G, g • theta.1.1 = theta.1.1)
  (gP :
    GlaubermanCorrespondence K (P : Subgroup G) p)

/-- The trivial-Sylow branch of the printed theorem is automatic.

If the Sylow subgroup has no nontrivial element, its ambient subgroup is
`⊥`, its normalizer is `⊤`, and its fixed-point subgroup on `K` is `K`.
Uniqueness identifies the supplied Glauberman correspondence with the
trivial-action correspondence.  The two extension problems then transport
to one another along the canonical subgroup equivalences. -/
theorem okuyamaWajimaPrinted_extension_iff_of_not_nontrivial_sylow
    (htrivial : ¬ Nontrivial P) :
    OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
        K P theta hinvariant gP ↔
      OkuyamaWajimaProperBranchThetaExtendsToG
        K P theta hinvariant := by
  letI : Subsingleton P :=
    not_nontrivial_iff_subsingleton.mp htrivial
  have hPbot : (P : Subgroup G) = ⊥ := by
    apply bot_unique
    intro x hx
    apply Subgroup.mem_bot.mpr
    have heq : (⟨x, hx⟩ : P) = 1 :=
      Subsingleton.elim _ _
    exact congrArg Subtype.val heq
  have hcentral :
      K ≤ Subgroup.centralizer ((P : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxbot : x ∈ (⊥ : Subgroup G) := hPbot ▸ hx
    have hxone : x = 1 := Subgroup.mem_bot.mp hxbot
    subst x
    simp
  let N :=
    Subgroup.normalizer ((P : Subgroup G) : Set G)
  have hNtop : N = ⊤ := by
    dsimp [N]
    apply Subgroup.normalizer_eq_top_iff.mpr
    rw [hPbot]
    infer_instance
  let eG : N ≃* G :=
    (MulEquiv.subgroupCongr hNtop).trans
      Subgroup.topEquiv
  let C := coprimeFixedPoints K (P : Subgroup G)
  let eK : C ≃* K :=
    coprimeFixedPointsEquivOfCentralizes
      K (P : Subgroup G) hcentral
  let hCN : C ≤ N :=
    inf_le_right.trans
      (Subgroup.centralizer_le_normalizer
        ((P : Subgroup G) : Set G))
  have hphi :
      (okuyamaWajimaProperBranchPhi
        K P theta gP).1 =
        theta.1.1.comap eK := by
    change (gP.characterEquiv theta).1 =
      theta.1.1.comap eK
    have hgP :
        gP =
          glaubermanCorrespondenceOfCentralizes
            K (P : Subgroup G) hcentral :=
      GlaubermanCorrespondence.eq _ _
    rw [hgP]
    rfl
  have hcomm :
      eG.toMonoidHom.comp
          (Subgroup.inclusion hCN) =
        K.subtype.comp eK.toMonoidHom := by
    ext x
    rfl
  have hcomm' :
      eG.symm.toMonoidHom.comp K.subtype =
        (Subgroup.inclusion hCN).comp
          eK.symm.toMonoidHom := by
    ext x
    rfl
  rw [
    okuyamaWajimaProperBranchPhi_extendsToPNormalizer_iff
      K P theta hinvariant gP]
  change
    (∃ eta : IrreducibleCharacter N,
        IrreducibleCharacter.IsExtensionAlong
          (Subgroup.inclusion hCN)
          (okuyamaWajimaProperBranchPhi
            K P theta gP).1 eta) ↔
      ∃ chi : IrreducibleCharacter G,
        IrreducibleCharacter.IsExtensionAlong
          K.subtype theta.1.1 chi
  constructor
  · rintro ⟨eta, heta⟩
    have heta' :
        IrreducibleCharacter.IsExtensionAlong
          (Subgroup.inclusion hCN)
          (theta.1.1.comap eK) eta := by
      rw [← hphi]
      exact heta
    refine ⟨eta.comap eG.symm, ?_⟩
    have h :=
      IrreducibleCharacter.IsExtensionAlong.comap_equiv
        eG.symm eK.symm hcomm' heta'
    simpa using h
  · rintro ⟨chi, hchi⟩
    refine ⟨chi.comap eG, ?_⟩
    have h :=
      IrreducibleCharacter.IsExtensionAlong.comap_equiv
        eG eK hcomm hchi
    rwa [hphi]

/-- The exact residual data after canonical complement construction and
the unconditional Gorenstein theorem.

In the full-fixed branch it retains only the coordinate/ascent map from
the automatically proved coprime Burnside-basis centralization statement
to the two outer cyclic/prime-power ascent implications.

In the proper branch it retains only the two character-coordinate maps
from the universal induction statements to the quotient and subgroup
character triples.  The subgroup `Q`, complement `M`, exact set-product
scope, strict cardinality decreases, Glauberman correspondence, and
Navarro ascent data are all canonical and are not premises. -/
def OkuyamaWajimaCanonicalBranchAssemblyInput
    (hK : IsPPrimeGroup p K)
    (hKP : (K ⊔ (P : Subgroup G)).Normal) : Prop :=
  let M :=
    okuyamaWajimaProperBranchComplement K P hK hKP
  let hM :
      M ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    okuyamaWajimaAmbientComplement_le_normalizer
      P K hK hKP
  letI : MulDistribMulAction M P :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      M P hM
  let L := okuyamaWajimaActionKernel M P
  (∀ (d : OkuyamaWajimaCyclicQuotientSubgroup M P L)
      (hfull : d.fixedPoints = ⊤),
      OkuyamaWajimaFullFixedCoordinates.FullFixedCoprimeCentralizationInput
            M P hM d P.isPGroup'
              (okuyamaWajimaAmbientComplement_isPPrimeGroup
                K P hK hKP)
              hfull →
        OkuyamaWajimaFullFixedOuterAssemblyInput
          K P theta hinvariant gP) ∧
    ∀ (d : OkuyamaWajimaCyclicQuotientSubgroup M P L)
      (_hproper : d.fixedPoints < ⊤),
      Nonempty
        (OkuyamaWajimaProperBranchInductionAdapters
          K P d.fixedPointPreimage M theta hinvariant
            (okuyamaWajimaProperBranchSelectedGlaubermanCorrespondence
              K P hK hKP d)
            gP)

/-- Source-faithful nontrivial-Sylow induction step.

The Gorenstein datum and dichotomy are chosen internally.  In the proper
case the newly derived canonical group scope is passed directly to the
existing proper-branch theorem, so `H.Normal` is neither assumed nor
constructed. -/
theorem okuyamaWajimaPrinted_extension_iff_of_canonicalBranchAssembly
    [Nontrivial P]
    (hK : IsPPrimeGroup p K)
    (hproduct :
      K ⊔ Subgroup.normalizer ((P : Subgroup G) : Set G) = ⊤)
    (hcommutativeQuotient :
      _root_.commutator G ≤ K ⊔ (P : Subgroup G))
    (assembly :
      OkuyamaWajimaCanonicalBranchAssemblyInput
        K P theta hinvariant gP hK
          (normal_sup_sylow_normal_of_sup_normalizer_eq_top
            K P hproduct))
    (ih :
      ∀ (H : Type) [Group H] [Finite H],
        Nat.card H < Nat.card G →
          OkuyamaWajimaPrintedExtensionStatement
            (p := p) H) :
    OkuyamaWajimaProperBranchPhiExtendsToPNormalizer
        K P theta hinvariant gP ↔
      OkuyamaWajimaProperBranchThetaExtendsToG
        K P theta hinvariant := by
  let hKP : (K ⊔ (P : Subgroup G)).Normal :=
    normal_sup_sylow_normal_of_sup_normalizer_eq_top
      K P hproduct
  let M :=
    okuyamaWajimaProperBranchComplement K P hK hKP
  let hM :
      M ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    okuyamaWajimaAmbientComplement_le_normalizer
      P K hK hKP
  letI : MulDistribMulAction M P :=
    OkuyamaWajimaFullFixedCoordinates.normalizerConjugationAction
      M P hM
  let L := okuyamaWajimaActionKernel M P
  change
    (∀ (d : OkuyamaWajimaCyclicQuotientSubgroup M P L)
        (hfull : d.fixedPoints = ⊤),
        OkuyamaWajimaFullFixedCoordinates.FullFixedCoprimeCentralizationInput
              M P hM d P.isPGroup'
                (okuyamaWajimaAmbientComplement_isPPrimeGroup
                  K P hK hKP)
                hfull →
          OkuyamaWajimaFullFixedOuterAssemblyInput
            K P theta hinvariant gP) ∧
      ∀ (d : OkuyamaWajimaCyclicQuotientSubgroup M P L)
        (_hproper : d.fixedPoints < ⊤),
        Nonempty
          (OkuyamaWajimaProperBranchInductionAdapters
            K P d.fixedPointPreimage M theta hinvariant
              (okuyamaWajimaProperBranchSelectedGlaubermanCorrespondence
                K P hK hKP d)
              gP)
    at assembly
  obtain ⟨d, hfull | ⟨_hnontrivial, hproper⟩⟩ :=
    exists_okuyamaWajima_canonicalComplement_cyclicQuotientSubgroup_dichotomy
      K P hK hKP hcommutativeQuotient
  · have hBurnside :
        OkuyamaWajimaFullFixedCoordinates.FullFixedCoprimeCentralizationInput
          M P hM d P.isPGroup'
            (okuyamaWajimaAmbientComplement_isPPrimeGroup
              K P hK hKP)
            hfull :=
      OkuyamaWajimaFullFixedCoordinates.fullFixedCoprimeCentralizationInput_automatic
        M P hM d P.isPGroup'
          (okuyamaWajimaAmbientComplement_isPPrimeGroup
            K P hK hKP)
          hfull
    exact
      okuyamaWajimaFullFixed_extension_iff_of_outerAssembly
        K P theta hinvariant gP
          (assembly.1 d hfull hBurnside)
  · let gQ :=
      okuyamaWajimaProperBranchSelectedGlaubermanCorrespondence
        K P hK hKP d
    let scope :
        OkuyamaWajimaProperBranchGroupScope
          K P d.fixedPointPreimage M :=
      okuyamaWajimaProperBranchGroupScopeFromComplement
        K P hK hKP d hproper
    obtain ⟨adapters⟩ := assembly.2 d hproper
    exact
      okuyamaWajimaProperBranch_extension_iff_of_smallerStatements
        K P d.fixedPointPreimage M theta hinvariant
          gQ gP hK scope adapters ih

end CanonicalBranchSelection

/-! ## Canonical induction assembly -/

section CanonicalInductionAssembly

variable {p : ℕ} [Fact p.Prime]

/-- The source-faithful residual interface for the complete printed
induction.

For a nontrivial Sylow subgroup, the provider supplies the canonical
full-fixed/proper character-coordinate assembly.  The complement,
Gorenstein subgroup, branch dichotomy, Burnside-basis step, proper group
scope, recursive cardinality decreases, Navarro ascent, and the
trivial-Sylow branch are all discharged internally.  In particular this
interface contains no arbitrary choice of `Q` or `M`. -/
def OkuyamaWajimaPrintedCanonicalAssemblyInput
    (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G]
      (K : Subgroup G) [K.Normal]
      (P : Sylow p G),
    letI : MulDistribMulAction P K :=
      subgroupConjugationMulDistribMulAction K (P : Subgroup G)
    ∀ (hK : IsPPrimeGroup p K)
      (hproduct :
        K ⊔ Subgroup.normalizer ((P : Subgroup G) : Set G) = ⊤)
      (_hcommutativeQuotient :
        _root_.commutator G ≤ K ⊔ (P : Subgroup G))
      (theta :
        PInvariantPPrimeIrreducibleCharacter
          K (P : Subgroup G) p)
      (hinvariant :
        ∀ g : G, g • theta.1.1 = theta.1.1)
      (gP :
        GlaubermanCorrespondence K (P : Subgroup G) p)
      (_hP : Nontrivial P),
      OkuyamaWajimaCanonicalBranchAssemblyInput
        K P theta hinvariant gP hK
          (normal_sup_sylow_normal_of_sup_normalizer_eq_top
            K P hproduct)

/-- A canonical residual provider gives one ordinary cardinality
induction step.  The nontrivial case uses the internally selected
Gorenstein datum; the other case is the automatic trivial-action
transport theorem above. -/
theorem okuyamaWajimaPrintedExtensionInductionStep_of_canonicalAssembly
    (assembly :
      OkuyamaWajimaPrintedCanonicalAssemblyInput p) :
    OkuyamaWajimaPrintedExtensionInductionStep p := by
  intro G _ _ ih
  intro K _ P
  letI : MulDistribMulAction P K :=
    subgroupConjugationMulDistribMulAction K (P : Subgroup G)
  intro hK hproduct hcommutativeQuotient
    theta hinvariant gP
  classical
  by_cases hP : Nontrivial P
  · letI : Nontrivial P := hP
    exact
      okuyamaWajimaPrinted_extension_iff_of_canonicalBranchAssembly
        K P theta hinvariant gP hK hproduct
          hcommutativeQuotient
          (assembly G K P hK hproduct
            hcommutativeQuotient theta hinvariant gP hP)
          ih
  · exact
      okuyamaWajimaPrinted_extension_iff_of_not_nontrivial_sylow
        K P theta hinvariant gP hP

/-- Final strong-induction theorem with canonical branch coordinates.

At this boundary, finishing the printed theorem amounts exactly to
providing the remaining character-coordinate/ascent maps in
`OkuyamaWajimaPrintedCanonicalAssemblyInput`; all group selection and
well-founded recursion are already formalized. -/
theorem okuyamaWajimaPrintedExtensionStatement_of_canonicalAssembly
    (assembly :
      OkuyamaWajimaPrintedCanonicalAssemblyInput p)
    (G : Type) [Group G] [Finite G] :
    OkuyamaWajimaPrintedExtensionStatement (p := p) G :=
  okuyamaWajimaPrintedExtensionStatement_of_inductionStep
    (okuyamaWajimaPrintedExtensionInductionStep_of_canonicalAssembly
      assembly)
    G

end CanonicalInductionAssembly

section BranchInductionStep

variable {p : ℕ} [Fact p.Prime]

/-- A branchwise induction step with only the exact remaining assembly
interfaces visible.

For each printed problem, the provider supplies either:

* the two outer full-fixed implications; or
* a proper subgroup `Q`, its normality, the exact set-product group scope,
  and the two coordinate adapters from the automatically generated
  smaller-group induction statements.

The Gorenstein theorem above guarantees that the underlying
full-fixed/proper dichotomy exists.  Constructing the ambient data in the
two alternatives is deliberately kept separate from the well-founded
recursion implemented here. -/
def OkuyamaWajimaPrintedBranchInductionStep
    (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    (∀ (H : Type) [Group H] [Finite H],
      Nat.card H < Nat.card G →
        OkuyamaWajimaPrintedExtensionStatement (p := p) H) →
    ∀ (K : Subgroup G) [K.Normal]
      (P : Sylow p G),
      letI : MulDistribMulAction P K :=
        subgroupConjugationMulDistribMulAction K (P : Subgroup G)
      ∀ (_hK : IsPPrimeGroup p K)
        (_hproduct :
          K ⊔ Subgroup.normalizer ((P : Subgroup G) : Set G) = ⊤)
        (_hcommutativeQuotient :
          _root_.commutator G ≤ K ⊔ (P : Subgroup G))
        (theta :
          PInvariantPPrimeIrreducibleCharacter
            K (P : Subgroup G) p)
        (hinvariant :
          ∀ g : G, g • theta.1.1 = theta.1.1)
        (gP :
          GlaubermanCorrespondence K (P : Subgroup G) p),
        OkuyamaWajimaFullFixedOuterAssemblyInput
            K P theta hinvariant gP ∨
          ∃ (Q : Subgroup P) (hQNormal : Q.Normal),
            letI : Q.Normal := hQNormal
            ∃ (M : Subgroup G)
              (gQ :
                GlaubermanCorrespondence K
                  (okuyamaWajimaProperBranchQ P Q) p)
              (_scope :
                OkuyamaWajimaProperBranchGroupScope
                  K P Q M),
              Nonempty
                (OkuyamaWajimaProperBranchInductionAdapters
                  K P Q M theta hinvariant gQ gP)

/-- A branchwise provider gives one ordinary cardinality-induction step.
The proper case is discharged by the already formalized Navarro chain. -/
theorem okuyamaWajimaPrintedExtensionInductionStep_of_branchStep
    (branch :
      OkuyamaWajimaPrintedBranchInductionStep p) :
    OkuyamaWajimaPrintedExtensionInductionStep p := by
  intro G _ _ ih
  intro K _ P
  letI : MulDistribMulAction P K :=
    subgroupConjugationMulDistribMulAction K (P : Subgroup G)
  intro hK hproduct hcommutativeQuotient
    theta hinvariant gP
  rcases
      branch G ih K P hK hproduct
        hcommutativeQuotient theta hinvariant gP with
    hfull | ⟨Q, hQNormal, hproper⟩
  · exact
      okuyamaWajimaFullFixed_extension_iff_of_outerAssembly
        K P theta hinvariant gP hfull
  · letI : Q.Normal := hQNormal
    obtain ⟨M, gQ, scope, ⟨adapters⟩⟩ := hproper
    exact
      okuyamaWajimaProperBranch_extension_iff_of_smallerStatements
        K P Q M theta hinvariant gQ gP hK scope adapters ih

/-- Final high-level strong-induction theorem.

Once the branch provider has constructed the full-fixed outer assembly or
the proper recursive coordinates for every printed problem, no further
well-founded or Navarro plumbing remains. -/
theorem okuyamaWajimaPrintedExtensionStatement_of_branchStep
    (branch :
      OkuyamaWajimaPrintedBranchInductionStep p)
    (G : Type) [Group G] [Finite G] :
    OkuyamaWajimaPrintedExtensionStatement (p := p) G :=
  okuyamaWajimaPrintedExtensionStatement_of_inductionStep
    (okuyamaWajimaPrintedExtensionInductionStep_of_branchStep
      branch)
    G

end BranchInductionStep

end McKayConjecture
