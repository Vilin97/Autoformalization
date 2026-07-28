/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralScalarPreservation
import McKayConjecture.InductiveMcKay.NumericalReduction

/-!
# Central-scalar-preserving normalizer induction

The ordinary normalizer induction composes local inductive-McKay
correspondences through proper intermediate subgroups.  This file performs
the same recursion on the fibre of characters affording a fixed scalar
character on a central subgroup.

At each local step, the central subgroup is regarded inside the intermediate
subgroup and its scalar character is restricted along the canonical
inclusion.  At the final step, character transport across the canonical
isomorphism between the internal and ambient Sylow normalizers preserves the
corresponding scalar fibre.
-/

noncomputable section

universe u v

namespace McKayConjecture

namespace PPrimeCentralScalarCharacter

variable {G : Type u} {H : Type v}
variable [Group G] [Group H]

/-- Pull a subgroup back along a group isomorphism. -/
def comapSubgroup
    (e : H ≃* G) (Z : Subgroup G) :
    Subgroup H :=
  Z.comap e.toMonoidHom

/-- Pull a scalar character back along a group isomorphism. -/
def comapScalar
    (e : H ≃* G) (Z : Subgroup G)
    (lambda : Z →* ℂˣ) :
    comapSubgroup e Z →* ℂˣ :=
  lambda.comp (e.toMonoidHom.subgroupComap Z)

@[simp]
theorem comapScalar_apply
    (e : H ≃* G) (Z : Subgroup G)
    (lambda : Z →* ℂˣ)
    (z : comapSubgroup e Z) :
    comapScalar e Z lambda z =
      lambda ⟨e z, z.property⟩ :=
  rfl

/-- Pullback along a group isomorphism preserves a prescribed central scalar
condition. -/
theorem comap_hasCentralScalar_iff
    (p : ℕ) (e : H ≃* G)
    (Z : Subgroup G) (lambda : Z →* ℂˣ)
    (chi : PPrimeIrreducibleCharacter G p) :
    chi.1.HasCentralScalar Z lambda ↔
      (IrreducibleCharacter.pPrimeComapEquiv p e chi).1.HasCentralScalar
        (comapSubgroup e Z) (comapScalar e Z lambda) := by
  constructor
  · intro hchi z
    exact hchi ⟨e z, z.property⟩
  · intro hchi z
    let z' : comapSubgroup e Z :=
      ⟨e.symm z, by
        change e (e.symm (z : G)) ∈ Z
        rw [e.apply_symm_apply]
        exact z.property⟩
    have hz' := hchi z'
    change
      chi.1.values (e (z' : H)) =
        ((lambda ⟨e (z' : H), z'.property⟩ :
            ℂˣ) : ℂ) *
          (chi.1.degree : ℂ) at hz'
    simpa [z'] using hz'

/-- Transport a prescribed scalar fibre along a group isomorphism. -/
def comapEquiv
    (p : ℕ) (e : H ≃* G)
    (Z : Subgroup G) (lambda : Z →* ℂˣ) :
    PPrimeCentralScalarCharacter G p Z lambda ≃
      PPrimeCentralScalarCharacter H p
        (comapSubgroup e Z) (comapScalar e Z lambda) :=
  (IrreducibleCharacter.pPrimeComapEquiv p e).subtypeEquiv
    (fun chi ↦ comap_hasCentralScalar_iff p e Z lambda chi)

@[simp]
theorem comapEquiv_apply_coe
    (p : ℕ) (e : H ≃* G)
    (Z : Subgroup G) (lambda : Z →* ℂˣ)
    (chi : PPrimeCentralScalarCharacter G p Z lambda) :
    (comapEquiv p e Z lambda chi).1 =
      IrreducibleCharacter.pPrimeComapEquiv p e chi.1 :=
  rfl

end PPrimeCentralScalarCharacter

namespace InductiveMcKay

variable {G : Type u} [Group G]
variable {p : ℕ}

/-- A subgroup `Z ≤ N`, regarded as a subgroup of `N`. -/
abbrev centralSubgroupIn
    (Z N : Subgroup G) :
    Subgroup N :=
  Z.subgroupOf N

/-- Restrict a scalar character to the canonical copy of `Z` in `N`. -/
def centralScalarIn
    (Z N : Subgroup G) (hZ : Z ≤ N)
    (lambda : Z →* ℂˣ) :
    centralSubgroupIn Z N →* ℂˣ :=
  lambda.comp
    (Subgroup.subgroupOfEquivOfLe hZ).toMonoidHom

@[simp]
theorem centralScalarIn_apply
    (Z N : Subgroup G) (hZ : Z ≤ N)
    (lambda : Z →* ℂˣ)
    (z : centralSubgroupIn Z N) :
    centralScalarIn Z N hZ lambda z =
      lambda
        (Subgroup.subgroupOfEquivOfLe hZ z) :=
  rfl

/-- A central subgroup remains central when regarded inside a subgroup that
contains it. -/
theorem centralSubgroupIn_le_center
    (Z N : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (_hZ : Z ≤ N) :
    centralSubgroupIn Z N ≤ Subgroup.center N := by
  intro z hz
  have hzCenter :
      (z : G) ∈ Subgroup.center G :=
    hZcentral hz
  rw [Subgroup.mem_center_iff]
  intro n
  apply Subtype.ext
  exact
    Subgroup.mem_center_iff.mp hzCenter (n : G)

/-- Every central subgroup lies in a Sylow normalizer. -/
theorem central_le_sylowNormalizer
    (Q : Sylow p G) (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G) :
    Z ≤ Subgroup.normalizer (Q : Set G) :=
  hZcentral.trans
    (Subgroup.center_le_normalizer (Q : Set G))

/-- The canonical copy of a central subgroup in a Sylow normalizer. -/
abbrev centralSubgroupInSylowNormalizer
    (Q : Sylow p G) (Z : Subgroup G) :
    Subgroup (SylowNormalizer Q) :=
  centralSubgroupIn Z
    (Subgroup.normalizer (Q : Set G))

/-- The corresponding scalar character on the copy of `Z` in a Sylow
normalizer. -/
def centralScalarInSylowNormalizer
    (Q : Sylow p G) (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (lambda : Z →* ℂˣ) :
    centralSubgroupInSylowNormalizer Q Z →* ℂˣ :=
  centralScalarIn Z
    (Subgroup.normalizer (Q : Set G))
    (central_le_sylowNormalizer Q Z hZcentral)
    lambda

@[simp]
theorem centralScalarInSylowNormalizer_apply
    (Q : Sylow p G) (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (lambda : Z →* ℂˣ)
    (z : centralSubgroupInSylowNormalizer Q Z) :
    centralScalarInSylowNormalizer
        Q Z hZcentral lambda z =
      lambda
        ⟨((z : SylowNormalizer Q) : G), z.property⟩ :=
  rfl

/-- The scalar fibre in the Sylow normalizer corresponding to the prescribed
ambient scalar character. -/
abbrev NormalizerCentralScalarCharacter
    (Q : Sylow p G) (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (lambda : Z →* ℂˣ) :=
  PPrimeCentralScalarCharacter
    (SylowNormalizer Q) p
    (centralSubgroupInSylowNormalizer Q Z)
    (centralScalarInSylowNormalizer
      Q Z hZcentral lambda)

/-- The canonical isomorphism from the normalizer computed in an
intermediate subgroup to the ambient Sylow normalizer. -/
abbrev scalarNormalizerMulEquiv
    (Q : Sylow p G) (N : Subgroup G)
    (hNormalizer :
      Subgroup.normalizer (Q : Set G) ≤ N) :
    SylowNormalizer
        (sylowIn Q N
          (Subgroup.le_normalizer.trans hNormalizer)) ≃*
      SylowNormalizer Q :=
  normalizerInEquivNormalizer Q N
    (Subgroup.le_normalizer.trans hNormalizer)
    hNormalizer

/-- Pulling the canonical copy of `Z` in the ambient normalizer back through
the normalizer isomorphism gives the iterated canonical copy of `Z` in the
internal normalizer. -/
theorem comap_centralSubgroupInSylowNormalizer_eq
    (Q : Sylow p G) (N : Subgroup G)
    (hNormalizer :
      Subgroup.normalizer (Q : Set G) ≤ N)
    (Z : Subgroup G) :
    PPrimeCentralScalarCharacter.comapSubgroup
        (scalarNormalizerMulEquiv Q N hNormalizer)
        (centralSubgroupInSylowNormalizer Q Z) =
      centralSubgroupInSylowNormalizer
        (sylowIn Q N
          (Subgroup.le_normalizer.trans hNormalizer))
        (centralSubgroupIn Z N) := by
  ext z
  rfl

/-- Transport the corresponding scalar fibre from the normalizer computed in
an intermediate subgroup to the ambient Sylow normalizer. -/
def normalizerCentralScalarTransport
    (Q : Sylow p G) (N : Subgroup G)
    (hNormalizer :
      Subgroup.normalizer (Q : Set G) ≤ N)
    (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (lambda : Z →* ℂˣ) :
    let hZ : Z ≤ N :=
      (central_le_sylowNormalizer Q Z hZcentral).trans
        hNormalizer
    let QN : Sylow p N :=
      sylowIn Q N
        (Subgroup.le_normalizer.trans hNormalizer)
    NormalizerCentralScalarCharacter
        QN (centralSubgroupIn Z N)
        (centralSubgroupIn_le_center
          Z N hZcentral hZ)
        (centralScalarIn Z N hZ lambda) ≃
      NormalizerCentralScalarCharacter
        Q Z hZcentral lambda := by
  dsimp only
  let e := scalarNormalizerMulEquiv Q N hNormalizer
  exact
    (PPrimeCentralScalarCharacter.comapEquiv
      p e
      (centralSubgroupInSylowNormalizer Q Z)
      (centralScalarInSylowNormalizer
        Q Z hZcentral lambda)).symm

@[simp]
theorem normalizerCentralScalarTransport_apply_coe
    (Q : Sylow p G) (N : Subgroup G)
    (hNormalizer :
      Subgroup.normalizer (Q : Set G) ≤ N)
    (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (lambda : Z →* ℂˣ)
    (chi :
      let hZ : Z ≤ N :=
        (central_le_sylowNormalizer Q Z hZcentral).trans
          hNormalizer
      let QN : Sylow p N :=
        sylowIn Q N
          (Subgroup.le_normalizer.trans hNormalizer)
      NormalizerCentralScalarCharacter
        QN (centralSubgroupIn Z N)
        (centralSubgroupIn_le_center
          Z N hZcentral hZ)
        (centralScalarIn Z N hZ lambda)) :
    (normalizerCentralScalarTransport
      Q N hNormalizer Z hZcentral lambda chi).1 =
        (IrreducibleCharacter.pPrimeComapEquiv p
          (scalarNormalizerMulEquiv Q N hNormalizer)).symm
          chi.1 :=
  rfl

/-- When the Sylow normalizer is the whole group, the identity-on-elements
isomorphism from the normalizer to the ambient group. -/
def topNormalizerMulEquiv
    (Q : Sylow p G)
    (hnormalizer :
      Subgroup.normalizer (Q : Set G) = ⊤) :
    SylowNormalizer Q ≃* G :=
  (MulEquiv.subgroupCongr hnormalizer).trans
    Subgroup.topEquiv

@[simp]
theorem topNormalizerMulEquiv_apply_coe
    (Q : Sylow p G)
    (hnormalizer :
      Subgroup.normalizer (Q : Set G) = ⊤)
    (x : SylowNormalizer Q) :
    topNormalizerMulEquiv Q hnormalizer x = (x : G) :=
  rfl

/-- Base case of scalar-preserving normalizer induction. -/
def centralScalarCorrespondenceOfNormalizerEqTop
    (Q : Sylow p G)
    (hnormalizer :
      Subgroup.normalizer (Q : Set G) = ⊤)
    (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (lambda : Z →* ℂˣ) :
    PPrimeCentralScalarCharacter G p Z lambda ≃
      NormalizerCentralScalarCharacter
        Q Z hZcentral lambda :=
  PPrimeCentralScalarCharacter.comapEquiv
    p (topNormalizerMulEquiv Q hnormalizer) Z lambda

@[simp]
theorem centralScalarCorrespondenceOfNormalizerEqTop_apply_coe
    (Q : Sylow p G)
    (hnormalizer :
      Subgroup.normalizer (Q : Set G) = ⊤)
    (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (lambda : Z →* ℂˣ)
    (chi :
      PPrimeCentralScalarCharacter G p Z lambda) :
    (centralScalarCorrespondenceOfNormalizerEqTop
      Q hnormalizer Z hZcentral lambda chi).1 =
        IrreducibleCharacter.pPrimeComapEquiv p
          (topNormalizerMulEquiv Q hnormalizer)
          chi.1 :=
  rfl

/-- The scalar-preserving form of a McKay correspondence for a fixed central
subgroup and scalar character. -/
abbrev CentralScalarNormalizerCorrespondence
    (G : Type u) [Group G] (p : ℕ)
    (Q : Sylow p G)
    (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (lambda : Z →* ℂˣ) :=
  PPrimeCentralScalarCharacter G p Z lambda ≃
    NormalizerCentralScalarCharacter
      Q Z hZcentral lambda

/-- A family of full local inductive-McKay data, one for every finite group
and Sylow subgroup in the universe. -/
abbrev LocalInductiveMcKayProvider (p : ℕ) :=
  ∀ (Y : Type u) [Group Y] [Finite Y]
    (Q : Sylow p Y),
    LocalInductiveMcKayData Q

/-- Full local inductive-McKay data recursively produces a correspondence
with the Sylow normalizer on every prescribed central-scalar fibre. -/
def centralScalarCorrespondenceOfLocal
    (localData : LocalInductiveMcKayProvider.{u} p)
    (G : Type u) [Group G] [Finite G]
    (Q : Sylow p G)
    (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (lambda : Z →* ℂˣ) :
    CentralScalarNormalizerCorrespondence
      G p Q Z hZcentral lambda := by
  have all :
      ∀ n : ℕ,
        (∀ m < n,
          ∀ (Y : Type u) [Group Y] [Finite Y],
            Nat.card Y = m →
          ∀ (R : Sylow p Y)
            (C : Subgroup Y)
            (hCcentral : C ≤ Subgroup.center Y)
            (mu : C →* ℂˣ),
            Nonempty
              (CentralScalarNormalizerCorrespondence
                Y p R C hCcentral mu)) →
        ∀ (Y : Type u) [Group Y] [Finite Y],
          Nat.card Y = n →
        ∀ (R : Sylow p Y)
          (C : Subgroup Y)
          (hCcentral : C ≤ Subgroup.center Y)
          (mu : C →* ℂˣ),
          Nonempty
            (CentralScalarNormalizerCorrespondence
              Y p R C hCcentral mu) := by
    intro n ih Y _ _ hcard R C hCcentral mu
    let datum := localData Y R
    by_cases hnormalizer :
        Subgroup.normalizer (R : Set Y) = ⊤
    · exact
        ⟨centralScalarCorrespondenceOfNormalizerEqTop
          R hnormalizer C hCcentral mu⟩
    · have hproper : datum.intermediate < ⊤ :=
        datum.proper_of_normalizer_ne_top hnormalizer
      have hsmall :
          Nat.card datum.intermediate < n := by
        rw [← hcard]
        exact natCard_lt_of_lt_top hproper
      let hRle :
          (R : Subgroup Y) ≤ datum.intermediate :=
        Subgroup.le_normalizer.trans
          datum.normalizer_le
      let R' : Sylow p datum.intermediate :=
        sylowIn R datum.intermediate hRle
      let hCle : C ≤ datum.intermediate :=
        (central_le_sylowNormalizer
          R C hCcentral).trans datum.normalizer_le
      let C' : Subgroup datum.intermediate :=
        centralSubgroupIn C datum.intermediate
      let hC'central :
          C' ≤ Subgroup.center datum.intermediate :=
        centralSubgroupIn_le_center
          C datum.intermediate hCcentral hCle
      let mu' : C' →* ℂˣ :=
        centralScalarIn C datum.intermediate hCle mu
      obtain ⟨inductionCorrespondence⟩ :=
        ih (Nat.card datum.intermediate) hsmall
          datum.intermediate rfl
          R' C' hC'central mu'
      let localCorrespondence :
          PPrimeCentralScalarCharacter Y p C mu ≃
            PPrimeCentralScalarCharacter
              datum.intermediate p C' mu' :=
        datum.centralScalarCorrespondence
          C hCcentral hCle mu
      let normalizerTransport :
          NormalizerCentralScalarCharacter
              R' C' hC'central mu' ≃
            NormalizerCentralScalarCharacter
              R C hCcentral mu :=
        normalizerCentralScalarTransport
          R datum.intermediate datum.normalizer_le
          C hCcentral mu
      exact
        ⟨localCorrespondence.trans
          (inductionCorrespondence.trans
            normalizerTransport)⟩
  exact
    Classical.choice
      (Nat.strong_induction_on (Nat.card G)
        (p := fun n =>
          ∀ (Y : Type u) [Group Y] [Finite Y],
            Nat.card Y = n →
          ∀ (R : Sylow p Y)
            (C : Subgroup Y)
            (hCcentral : C ≤ Subgroup.center Y)
            (mu : C →* ℂˣ),
            Nonempty
              (CentralScalarNormalizerCorrespondence
                Y p R C hCcentral mu))
        all G rfl Q Z hZcentral lambda)

/-- The output of scalar-preserving normalizer induction, viewed as the
underlying `p'`-degree character in the Sylow normalizer. -/
def centralScalarCorrespondenceOfLocal_applyCharacter
    (localData : LocalInductiveMcKayProvider.{u} p)
    (G : Type u) [Group G] [Finite G]
    (Q : Sylow p G)
    (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (lambda : Z →* ℂˣ)
    (chi : PPrimeCentralScalarCharacter G p Z lambda) :
    PPrimeIrreducibleCharacter (SylowNormalizer Q) p :=
  (centralScalarCorrespondenceOfLocal
    localData G Q Z hZcentral lambda chi).1

@[simp]
theorem centralScalarCorrespondenceOfLocal_apply_coe
    (localData : LocalInductiveMcKayProvider.{u} p)
    (G : Type u) [Group G] [Finite G]
    (Q : Sylow p G)
    (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (lambda : Z →* ℂˣ)
    (chi : PPrimeCentralScalarCharacter G p Z lambda) :
    (centralScalarCorrespondenceOfLocal
      localData G Q Z hZcentral lambda chi).1 =
        centralScalarCorrespondenceOfLocal_applyCharacter
          localData G Q Z hZcentral lambda chi :=
  rfl

/-- The recursively constructed target character has the prescribed scalar
action on the canonical copy of `Z` in the Sylow normalizer. -/
theorem centralScalarCorrespondenceOfLocal_hasCentralScalar
    (localData : LocalInductiveMcKayProvider.{u} p)
    (G : Type u) [Group G] [Finite G]
    (Q : Sylow p G)
    (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (lambda : Z →* ℂˣ)
    (chi : PPrimeCentralScalarCharacter G p Z lambda) :
    (centralScalarCorrespondenceOfLocal_applyCharacter
      localData G Q Z hZcentral lambda chi).1.HasCentralScalar
        (centralSubgroupInSylowNormalizer Q Z)
        (centralScalarInSylowNormalizer
          Q Z hZcentral lambda) :=
  (centralScalarCorrespondenceOfLocal
    localData G Q Z hZcentral lambda chi).property

namespace InductiveMcKayCondition

/-- Choose a full local datum from the inductive McKay condition at every
finite group and Sylow subgroup. -/
def fullLocalData
    (h : InductiveMcKayCondition.{u} p) :
    LocalInductiveMcKayProvider.{u} p :=
  fun Y _ _ Q ↦ Classical.choice (h Y Q)

/-- The full inductive McKay condition yields the scalar-preserving
normalizer correspondence for every finite group. -/
def centralScalarCorrespondence
    (h : InductiveMcKayCondition.{u} p)
    (G : Type u) [Group G] [Finite G]
    (Q : Sylow p G)
    (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (lambda : Z →* ℂˣ) :
    CentralScalarNormalizerCorrespondence
      G p Q Z hZcentral lambda :=
  centralScalarCorrespondenceOfLocal
    h.fullLocalData G Q Z hZcentral lambda

@[simp]
theorem centralScalarCorrespondence_apply_coe
    (h : InductiveMcKayCondition.{u} p)
    (G : Type u) [Group G] [Finite G]
    (Q : Sylow p G)
    (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (lambda : Z →* ℂˣ)
    (chi : PPrimeCentralScalarCharacter G p Z lambda) :
    (h.centralScalarCorrespondence
      G Q Z hZcentral lambda chi).1 =
        centralScalarCorrespondenceOfLocal_applyCharacter
          h.fullLocalData G Q Z hZcentral lambda chi :=
  rfl

end InductiveMcKayCondition

end InductiveMcKay
end McKayConjecture
