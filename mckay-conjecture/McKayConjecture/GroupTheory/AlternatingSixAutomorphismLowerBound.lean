/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixAutomorphismCardinality
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverConjugacyClasses
import McKayConjecture.GroupTheory.AlternatingSixSchurOuterAutomorphismChecks
import McKayConjecture.GroupTheory.InnerAutomorphismSubgroup
import McKayConjecture.GroupTheory.InnerAutomorphismKernel

/-!
# The automorphism group of `A₆`

The two audited automorphisms of the computable sixfold Schur cover
transport to the canonical universal cover and hence descend uniquely to
`A₆`.  A single checked conjugacy class separates the four outer
representatives

`1, α₁, α₂, α₁ * α₂`.

Multiplying these representatives by the `360` inner automorphisms gives an
explicit injection

`A₆ × Fin 4 ↪ Aut(6.A₆) ≃ Aut(A₆)`.

Together with the generator-image upper bound, this proves that
`|Aut(A₆)| = 1440`.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-! ### Four checked outer representatives -/

/-- The four Schur-coordinate representatives used for the outer cosets. -/
def alternatingSixSchurOuterRepresentative :
    Fin 4 → MulAut AlternatingSixSchurCoordinates :=
  ![
    1,
    alternatingSixSchurAlphaOneAutomorphism,
    alternatingSixSchurAlphaTwoAutomorphism,
    alternatingSixSchurAlphaOneAutomorphism *
      alternatingSixSchurAlphaTwoAutomorphism
  ]

/-- Transport the four checked representatives to the canonical universal
cover. -/
def alternatingSixUniversalCoverOuterRepresentative
    (i : Fin 4) :
    MulAut AlternatingSixUniversalCover :=
  MulAut.congr
    alternatingSixSchurCoordinatesEquivUniversalCover
    (alternatingSixSchurOuterRepresentative i)

/-- Descend each checked universal-cover representative to `A₆`. -/
def alternatingSixOuterRepresentative
    (i : Fin 4) :
    MulAut AlternatingSix :=
  alternatingSixUniversalCoverAutomorphismMulEquiv
    (alternatingSixUniversalCoverOuterRepresentative i)

/-- The first audited cover automorphism, descended to `A₆`. -/
def alternatingSixAlphaOneAutomorphism :
    MulAut AlternatingSix :=
  alternatingSixOuterRepresentative 1

/-- The second audited cover automorphism, descended to `A₆`. -/
def alternatingSixAlphaTwoAutomorphism :
    MulAut AlternatingSix :=
  alternatingSixOuterRepresentative 2

/-- Descent is characterized by commuting with the universal-cover
projection. -/
theorem alternatingSixOuterRepresentative_projection
    (i : Fin 4) (u : AlternatingSixUniversalCover) :
    alternatingSixOuterRepresentative i
        (alternatingSixUniversalCentralExtension.toCentralExtension.projection u) =
      alternatingSixUniversalCentralExtension.toCentralExtension.projection
        (alternatingSixUniversalCoverOuterRepresentative i u) := by
  change
    (alternatingSixUniversalCentralExtension.toCentralExtension
        |>.inducedTargetAutomorphism
          (inferInstance : IsSimpleGroup AlternatingSix)
          alternatingSix_not_isMulCommutative
          (alternatingSixUniversalCoverOuterRepresentative i))
        (alternatingSixUniversalCentralExtension.toCentralExtension.projection u) =
      alternatingSixUniversalCentralExtension.toCentralExtension.projection
        (alternatingSixUniversalCoverOuterRepresentative i u)
  exact
    alternatingSixUniversalCentralExtension.toCentralExtension
      |>.inducedTargetAutomorphism_projection
        (inferInstance : IsSimpleGroup AlternatingSix)
        alternatingSix_not_isMulCommutative
        (alternatingSixUniversalCoverOuterRepresentative i) u

/-- The checked class indices reached from class `10` by the four outer
representatives. -/
def alternatingSixOuterRepresentativeClassWitness :
    Fin 4 → Fin 31 :=
  ![10, 11, 14, 13]

/-- The four class witnesses are pairwise distinct. -/
theorem alternatingSixOuterRepresentativeClassWitness_injective :
    Function.Injective
      alternatingSixOuterRepresentativeClassWitness := by
  decide

/-- The checked coordinate calculation behind the four-coset separation. -/
theorem alternatingSixSchurOuterRepresentative_classIndex_ten
    (i : Fin 4) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurOuterRepresentative i
          (alternatingSixSchurClassRepresentative 10)) =
      alternatingSixOuterRepresentativeClassWitness i := by
  fin_cases i <;> rfl

/-- The checked class enumeration transported directly from Schur
coordinates to the canonical universal cover. -/
def alternatingSixUniversalCoverClassIndexEquiv :
    Fin 31 ≃ ConjClasses AlternatingSixUniversalCover :=
  alternatingSixSchurCoordinateConjugacyClassEquiv.trans
    (conjugacyClassesEquivOfMulEquiv
      alternatingSixSchurCoordinatesEquivUniversalCover)

/-- A checked class index computes the conjugacy class of the image of a
representative under any coordinate automorphism. -/
theorem alternatingSixSchurAutomorphism_classIndex
    (α : MulAut AlternatingSixSchurCoordinates)
    (i : Fin 31) :
    ConjClasses.map α.toMonoidHom
        (alternatingSixSchurCoordinateConjugacyClassEquiv i) =
      alternatingSixSchurCoordinateConjugacyClassEquiv
        (alternatingSixSchurClassIndex
          (α (alternatingSixSchurClassRepresentative i))) := by
  change
    ConjClasses.mk
        (α (alternatingSixSchurClassRepresentative i)) =
      ConjClasses.mk
        (alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex
            (α (alternatingSixSchurClassRepresentative i))))
  symm
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  exact
    isConj_iff.mpr
      ⟨alternatingSixSchurClassConjugator
          (α (alternatingSixSchurClassRepresentative i)),
        alternatingSixSchurClassConjugator_spec
          (α (alternatingSixSchurClassRepresentative i))⟩

/-- Transporting conjugacy classes through a group equivalence intertwines
an automorphism with its conjugate automorphism on the target. -/
theorem conjugacyClassesEquivOfMulEquiv_map_congr
    {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (α : MulAut G)
    (c : ConjClasses G) :
    conjugacyClassesEquivOfMulEquiv e
        (ConjClasses.map α.toMonoidHom c) =
      ConjClasses.map (MulAut.congr e α).toMonoidHom
        (conjugacyClassesEquivOfMulEquiv e c) := by
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
  change
    ConjClasses.mk (e (α x)) =
      ConjClasses.mk ((MulAut.congr e α) (e x))
  congr 1
  simp [MulAut.congr]

/-- The class action of a transported Schur-coordinate automorphism is
read off by applying it to the checked representative. -/
theorem alternatingSixUniversalCoverAutomorphismOfSchur_classIndex
    (α : MulAut AlternatingSixSchurCoordinates)
    (i : Fin 31) :
    ConjClasses.map
        (MulAut.congr
          alternatingSixSchurCoordinatesEquivUniversalCover
          α).toMonoidHom
        (alternatingSixUniversalCoverClassIndexEquiv i) =
      alternatingSixUniversalCoverClassIndexEquiv
        (alternatingSixSchurClassIndex
          (α (alternatingSixSchurClassRepresentative i))) := by
  rw [alternatingSixUniversalCoverClassIndexEquiv,
    Equiv.trans_apply, Equiv.trans_apply]
  rw [← conjugacyClassesEquivOfMulEquiv_map_congr]
  exact congrArg
    (conjugacyClassesEquivOfMulEquiv
      alternatingSixSchurCoordinatesEquivUniversalCover)
    (alternatingSixSchurAutomorphism_classIndex α i)

/-- On checked class `10`, the four transported representatives have the
four pairwise-distinct advertised images. -/
theorem alternatingSixUniversalCoverOuterRepresentative_class_ten
    (i : Fin 4) :
    ConjClasses.map
        (alternatingSixUniversalCoverOuterRepresentative i).toMonoidHom
        (alternatingSixUniversalCoverClassIndexEquiv 10) =
      alternatingSixUniversalCoverClassIndexEquiv
        (alternatingSixOuterRepresentativeClassWitness i) := by
  rw [alternatingSixUniversalCoverOuterRepresentative,
    alternatingSixUniversalCoverAutomorphismOfSchur_classIndex,
    alternatingSixSchurOuterRepresentative_classIndex_ten]

/-! ### The inner part -/

/-- Inner automorphisms of the universal cover, parametrized by its central
quotient. -/
def alternatingSixUniversalCoverQuotientCenterConj :
    (AlternatingSixUniversalCover ⧸
        Subgroup.center AlternatingSixUniversalCover) →*
      MulAut AlternatingSixUniversalCover :=
  QuotientGroup.lift
    (Subgroup.center AlternatingSixUniversalCover)
    MulAut.conj
    (mulAutConj_ker_eq_center (G := AlternatingSixUniversalCover)).ge

/-- The central quotient acts faithfully by inner automorphisms. -/
theorem alternatingSixUniversalCoverQuotientCenterConj_injective :
    Function.Injective
      alternatingSixUniversalCoverQuotientCenterConj := by
  unfold alternatingSixUniversalCoverQuotientCenterConj
  rw [QuotientGroup.injective_lift_iff]
  exact
    (mulAutConj_ker_eq_center
      (G := AlternatingSixUniversalCover)).symm

/-- Parametrize the inner automorphisms of the universal cover by `A₆`. -/
def alternatingSixUniversalCoverInnerAutomorphism :
    AlternatingSix → MulAut AlternatingSixUniversalCover :=
  fun g =>
    alternatingSixUniversalCoverQuotientCenterConj
      (alternatingSixUniversalCoverQuotientCenterEquiv.symm g)

/-- The `A₆` parametrization of inner automorphisms is injective. -/
theorem alternatingSixUniversalCoverInnerAutomorphism_injective :
    Function.Injective
      alternatingSixUniversalCoverInnerAutomorphism :=
  alternatingSixUniversalCoverQuotientCenterConj_injective.comp
    alternatingSixUniversalCoverQuotientCenterEquiv.symm.injective

/-- Inner automorphisms act trivially on conjugacy classes, even after an
arbitrary automorphism is applied. -/
theorem conjClasses_map_inner_mul
    {G : Type*} [Group G]
    (g : G) (α : MulAut G) (c : ConjClasses G) :
    ConjClasses.map
        (MulAut.conj g * α).toMonoidHom c =
      ConjClasses.map α.toMonoidHom c := by
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
  change
    ConjClasses.mk (g * α x * g⁻¹) =
      ConjClasses.mk (α x)
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  exact isConj_iff.mpr ⟨g⁻¹, by simp [mul_assoc]⟩

/-! ### The `1440`-element family -/

/-- The four outer representatives multiplied by all `360` inner
automorphisms of the universal cover. -/
def alternatingSixUniversalCoverAutomorphismFamily :
    AlternatingSix × Fin 4 →
      MulAut AlternatingSixUniversalCover :=
  fun pair =>
    alternatingSixUniversalCoverInnerAutomorphism pair.1 *
      alternatingSixUniversalCoverOuterRepresentative pair.2

/-- The class-`10` witness of a family member depends only on, and detects,
its outer index. -/
theorem alternatingSixUniversalCoverAutomorphismFamily_class_ten
    (g : AlternatingSix) (i : Fin 4) :
    ConjClasses.map
        (alternatingSixUniversalCoverAutomorphismFamily (g, i)).toMonoidHom
        (alternatingSixUniversalCoverClassIndexEquiv 10) =
      alternatingSixUniversalCoverClassIndexEquiv
        (alternatingSixOuterRepresentativeClassWitness i) := by
  rw [alternatingSixUniversalCoverAutomorphismFamily]
  change
    ConjClasses.map
        (alternatingSixUniversalCoverInnerAutomorphism g *
          alternatingSixUniversalCoverOuterRepresentative i).toMonoidHom
        (alternatingSixUniversalCoverClassIndexEquiv 10) =
      _
  obtain ⟨q, hq⟩ :=
    QuotientGroup.mk'_surjective
      (Subgroup.center AlternatingSixUniversalCover)
      (alternatingSixUniversalCoverQuotientCenterEquiv.symm g)
  have hinner :
      alternatingSixUniversalCoverInnerAutomorphism g =
        MulAut.conj q := by
    rw [alternatingSixUniversalCoverInnerAutomorphism, ← hq]
    rfl
  rw [hinner,
    conjClasses_map_inner_mul,
    alternatingSixUniversalCoverOuterRepresentative_class_ten]

/-- The inner-times-outer family on the universal cover is injective. -/
theorem alternatingSixUniversalCoverAutomorphismFamily_injective :
    Function.Injective
      alternatingSixUniversalCoverAutomorphismFamily := by
  rintro ⟨g, i⟩ ⟨h, j⟩ hij
  have hclass :=
    congrArg
      (fun α : MulAut AlternatingSixUniversalCover =>
        ConjClasses.map α.toMonoidHom
          (alternatingSixUniversalCoverClassIndexEquiv 10))
      hij
  rw [
    alternatingSixUniversalCoverAutomorphismFamily_class_ten,
    alternatingSixUniversalCoverAutomorphismFamily_class_ten
  ] at hclass
  have hout :
      i = j :=
    alternatingSixOuterRepresentativeClassWitness_injective
      (alternatingSixUniversalCoverClassIndexEquiv.injective hclass)
  subst j
  have hinner :
      alternatingSixUniversalCoverInnerAutomorphism g =
        alternatingSixUniversalCoverInnerAutomorphism h :=
    mul_right_cancel hij
  have hin :
      g = h :=
    alternatingSixUniversalCoverInnerAutomorphism_injective hinner
  subst h
  rfl

/-- Descend the explicit cover family to automorphisms of `A₆`. -/
def alternatingSixAutomorphismFamily :
    AlternatingSix × Fin 4 → MulAut AlternatingSix :=
  fun pair =>
    alternatingSixUniversalCoverAutomorphismMulEquiv
      (alternatingSixUniversalCoverAutomorphismFamily pair)

/-- The descended `1440`-element family of automorphisms of `A₆` is
injective. -/
theorem alternatingSixAutomorphismFamily_injective :
    Function.Injective alternatingSixAutomorphismFamily :=
  alternatingSixUniversalCoverAutomorphismMulEquiv.injective.comp
    alternatingSixUniversalCoverAutomorphismFamily_injective

/-- The audited cover automorphisms give the lower bound
`1440 ≤ |Aut(A₆)|`. -/
theorem natCard_mulAut_alternatingSix_ge_1440 :
    1440 ≤ Nat.card (MulAut AlternatingSix) := by
  have hcard :=
    Nat.card_le_card_of_injective
      alternatingSixAutomorphismFamily
      alternatingSixAutomorphismFamily_injective
  calc
    1440 =
        Nat.card (AlternatingSix × Fin 4) := by
      rw [Nat.card_prod, natCard_alternatingSix, Nat.card_fin]
    _ ≤ Nat.card (MulAut AlternatingSix) := hcard

/-- The automorphism group of `A₆` has order exactly `1440`. -/
@[simp]
theorem natCard_mulAut_alternatingSix :
    Nat.card (MulAut AlternatingSix) = 1440 :=
  le_antisymm
    natCard_mulAut_alternatingSix_le_1440
    natCard_mulAut_alternatingSix_ge_1440

/-- The automorphism group of the canonical universal cover likewise has
order exactly `1440`. -/
@[simp]
theorem natCard_mulAut_alternatingSixUniversalCover :
    Nat.card (MulAut AlternatingSixUniversalCover) = 1440 := by
  rw [
    Nat.card_congr
      alternatingSixUniversalCoverAutomorphismMulEquiv.toEquiv,
    natCard_mulAut_alternatingSix
  ]

/-- The explicit inner-times-four-outers family exhausts all
automorphisms of the universal cover. -/
theorem alternatingSixUniversalCoverAutomorphismFamily_surjective :
    Function.Surjective
      alternatingSixUniversalCoverAutomorphismFamily :=
  (alternatingSixUniversalCoverAutomorphismFamily_injective
    |>.bijective_of_nat_card_le
      (by
        rw [
          natCard_mulAut_alternatingSixUniversalCover,
          Nat.card_prod,
          natCard_alternatingSix,
          Nat.card_fin
        ]))
    |>.2

/-- Every member of the four-element outer list belongs to the subgroup
generated by the two audited outer representatives. -/
theorem alternatingSixUniversalCoverOuterRepresentative_mem_closure
    (i : Fin 4) :
    alternatingSixUniversalCoverOuterRepresentative i ∈
      Subgroup.closure
        {alternatingSixUniversalCoverOuterRepresentative 1,
          alternatingSixUniversalCoverOuterRepresentative 2} := by
  fin_cases i
  · have hzero :
        alternatingSixUniversalCoverOuterRepresentative 0 = 1 := by
      simpa [
        alternatingSixUniversalCoverOuterRepresentative,
        alternatingSixSchurOuterRepresentative
      ] using
        map_one
          (MulAut.congr
            alternatingSixSchurCoordinatesEquivUniversalCover)
    change alternatingSixUniversalCoverOuterRepresentative 0 ∈ _
    rw [hzero]
    exact Subgroup.one_mem _
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · have hthree :
        alternatingSixUniversalCoverOuterRepresentative 3 =
          alternatingSixUniversalCoverOuterRepresentative 1 *
            alternatingSixUniversalCoverOuterRepresentative 2 := by
      simpa [
        alternatingSixUniversalCoverOuterRepresentative,
        alternatingSixSchurOuterRepresentative
      ] using
        map_mul
          (MulAut.congr
            alternatingSixSchurCoordinatesEquivUniversalCover)
          alternatingSixSchurAlphaOneAutomorphism
          alternatingSixSchurAlphaTwoAutomorphism
    change alternatingSixUniversalCoverOuterRepresentative 3 ∈ _
    rw [hthree]
    exact
      (Subgroup.closure
        {alternatingSixUniversalCoverOuterRepresentative 1,
          alternatingSixUniversalCoverOuterRepresentative 2}).mul_mem
        (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))

/-- Every inner member of the explicit family lies in the named inner
automorphism subgroup. -/
theorem alternatingSixUniversalCoverInnerAutomorphism_mem
    (g : AlternatingSix) :
    alternatingSixUniversalCoverInnerAutomorphism g ∈
      innerAutomorphismSubgroup AlternatingSixUniversalCover := by
  obtain ⟨q, hq⟩ :=
    QuotientGroup.mk'_surjective
      (Subgroup.center AlternatingSixUniversalCover)
      (alternatingSixUniversalCoverQuotientCenterEquiv.symm g)
  refine ⟨q, ?_⟩
  rw [alternatingSixUniversalCoverInnerAutomorphism, ← hq]
  rfl

/-- Inner automorphisms together with the two audited outer
representatives generate the full automorphism group of the canonical
universal cover. -/
theorem
    alternatingSixUniversalCover_inner_sup_outer_closure_eq_top :
    innerAutomorphismSubgroup AlternatingSixUniversalCover ⊔
        Subgroup.closure
          {alternatingSixUniversalCoverOuterRepresentative 1,
            alternatingSixUniversalCoverOuterRepresentative 2} =
      ⊤ := by
  apply top_unique
  intro α _
  obtain ⟨⟨g, i⟩, rfl⟩ :=
    alternatingSixUniversalCoverAutomorphismFamily_surjective α
  exact
    Subgroup.mul_mem_sup
      (alternatingSixUniversalCoverInnerAutomorphism_mem g)
      (alternatingSixUniversalCoverOuterRepresentative_mem_closure i)

end GroupTheory
end McKayConjecture
