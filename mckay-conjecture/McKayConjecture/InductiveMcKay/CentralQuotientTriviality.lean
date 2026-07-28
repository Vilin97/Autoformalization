/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralKernelTriviality
import McKayConjecture.InductiveMcKay.Condition

/-!
# Central-kernel triviality for local inductive-McKay data

The central character-triple clause identifies representation-level
triviality on a central subgroup of the ambient group with triviality of
the corresponding local character on its copy in the intermediate
subgroup.  Consequently, the stored `p'`-character correspondence
restricts to an equivalence on characters descending through the central
quotient.
-/

noncomputable section

open CategoryTheory

universe u v

namespace McKayConjecture

namespace IrreducibleCharacter

variable {G : Type u} {H : Type v}
variable [Group G] [Group H] [Finite H]

/-- Pullback along a group equivalence preserves representation-level
triviality on the pulled-back subgroup. -/
theorem comap_trivialOn_comap_iff
    (e : H ≃* G) (χ : IrreducibleCharacter G)
    (Z : Subgroup G) :
    (χ.comap e).TrivialOn
        (Z.comap e.toMonoidHom) ↔
      χ.TrivialOn Z := by
  let V : FDRep ℂ H :=
    FDRep.of (χ.realization.ρ.comp e.toMonoidHom)
  letI : Simple V := by
    let E : FDRep ℂ G ≌ FDRep ℂ H :=
      Action.resEquiv (FGModuleCat ℂ) e
    change Simple (E.functor.obj χ.realization)
    exact CategoryTheory.simple_obj E.functor χ.realization
  have hcharacter :
      V.character = (χ.comap e).values := by
    funext h
    change
      χ.realization.character (e h) =
        χ.values (e h)
    exact congrFun χ.realization_character (e h)
  rw [trivialOn_iff_of_character_eq
    (Z.comap e.toMonoidHom) (χ.comap e) V hcharacter]
  constructor
  · intro h z
    let zH : Z.comap e.toMonoidHom :=
      ⟨e.symm z.1, by
        change e (e.symm z.1) ∈ Z
        rw [e.apply_symm_apply]
        exact z.2⟩
    have hz := h zH
    change
      χ.realization.ρ (e (e.symm z.1)) =
        LinearMap.id at hz
    simpa using hz
  · intro h z
    let zG : Z :=
      ⟨e z.1, z.2⟩
    change
      χ.realization.ρ (e z.1) =
        LinearMap.id
    exact h zG

end IrreducibleCharacter

namespace InductiveMcKay

open McKayConjecture.CharacterTriple

variable {G : Type u} [Group G] [Finite G] {p : ℕ}

namespace LocalInductiveMcKayData

variable {P : Sylow p G}

/-- The copy of an ambient subgroup inside the intermediate subgroup. -/
def subgroupInIntermediate
    (d : LocalInductiveMcKayData P) (Z : Subgroup G) :
    Subgroup d.intermediate :=
  Z.comap d.intermediate.subtype

/-- The copy of `Z` inside the normal subgroup of the ambient semidirect
character triple. -/
def ambientTripleSubgroup
    (χ : PPrimeIrreducibleCharacter G p)
    (Z : Subgroup G) :
    Subgroup
      (EquivariantLocalCorrespondence.ambientTriple
        (P := P) χ).normalSubgroup :=
  Z.comap
    (semidirectNormalEquiv
      (PPrimeCharacterStabilizer.ambientAction
        (P := P) (χ := χ))).toMonoidHom

/-- The copy of `Z ∩ d.intermediate` inside the normal subgroup of the
intermediate semidirect character triple. -/
def intermediateTripleSubgroup
    (d : LocalInductiveMcKayData P)
    (χ : PPrimeIrreducibleCharacter G p)
    (Z : Subgroup G) :
    Subgroup
      (d.toEquivariant.intermediateTriple χ).normalSubgroup :=
  (subgroupInIntermediate d Z).comap
    (semidirectNormalEquiv
      (d.toEquivariant.stabilizerIntermediateAction χ)).toMonoidHom

/-- The canonical inclusion of the intermediate normal subgroup into
the ambient normal subgroup, expressed through the two canonical
semidirect normal-subgroup equivalences. -/
def intermediateNormalEmbedding
    (d : LocalInductiveMcKayData P)
    (χ : PPrimeIrreducibleCharacter G p) :
    (d.toEquivariant.intermediateTriple χ).normalSubgroup →*
      (EquivariantLocalCorrespondence.ambientTriple
        (P := P) χ).normalSubgroup :=
  (semidirectNormalEquiv
      (PPrimeCharacterStabilizer.ambientAction
        (P := P) (χ := χ))).symm.toMonoidHom.comp
    (d.intermediate.subtype.comp
      (semidirectNormalEquiv
        (d.toEquivariant.stabilizerIntermediateAction χ)).toMonoidHom)

@[simp]
theorem intermediateNormalEmbedding_left
    (d : LocalInductiveMcKayData P)
    (χ : PPrimeIrreducibleCharacter G p)
    (z : (d.toEquivariant.intermediateTriple χ).normalSubgroup) :
    ((intermediateNormalEmbedding d χ z :
        (EquivariantLocalCorrespondence.ambientTriple
          (P := P) χ).normalSubgroup) :
      G ⋊[PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer P χ).left =
      ((semidirectNormalEquiv
        (d.toEquivariant.stabilizerIntermediateAction χ) z :
          d.intermediate) : G) :=
  rfl

@[simp]
theorem intermediateNormalEmbedding_symm_apply
    (d : LocalInductiveMcKayData P)
    (χ : PPrimeIrreducibleCharacter G p)
    (z : d.intermediate) :
    intermediateNormalEmbedding d χ
        ((semidirectNormalEquiv
          (d.toEquivariant.stabilizerIntermediateAction χ)).symm z) =
      (semidirectNormalEquiv
        (PPrimeCharacterStabilizer.ambientAction
          (P := P) (χ := χ))).symm (z : G) :=
  rfl

/-- When `Z` lies in the intermediate subgroup, its two copies in the
normal subgroups of the semidirect character triples are canonically
equivalent. -/
def intermediateTripleSubgroupEquivAmbient
    (d : LocalInductiveMcKayData P)
    (χ : PPrimeIrreducibleCharacter G p)
    (Z : Subgroup G)
    (hZ : Z ≤ d.intermediate) :
    intermediateTripleSubgroup d χ Z ≃*
      ambientTripleSubgroup (P := P) χ Z where
  toFun z :=
    ⟨intermediateNormalEmbedding d χ z.1, by
      have hz := z.2
      change
        (((semidirectNormalEquiv
          (d.toEquivariant.stabilizerIntermediateAction χ))
            z.1 : d.intermediate) : G) ∈ Z at hz
      change
        ((intermediateNormalEmbedding d χ z.1 :
            (EquivariantLocalCorrespondence.ambientTriple
              (P := P) χ).normalSubgroup) :
          G ⋊[PPrimeCharacterStabilizer.ambientAction]
            PPrimeCharacterStabilizer P χ).left ∈ Z
      rw [intermediateNormalEmbedding_left]
      exact hz⟩
  invFun z :=
    ⟨(semidirectNormalEquiv
        (d.toEquivariant.stabilizerIntermediateAction χ)).symm
        ⟨semidirectNormalEquiv
            (PPrimeCharacterStabilizer.ambientAction
              (P := P) (χ := χ)) z.1,
          hZ (by
            have hz := z.2
            change
              semidirectNormalEquiv
                (PPrimeCharacterStabilizer.ambientAction
                  (P := P) (χ := χ)) z.1 ∈ Z at hz
            exact hz)⟩, by
      have hz := z.2
      change
        semidirectNormalEquiv
          (PPrimeCharacterStabilizer.ambientAction
            (P := P) (χ := χ)) z.1 ∈ Z at hz
      change
        (((semidirectNormalEquiv
          (d.toEquivariant.stabilizerIntermediateAction χ))
            ((semidirectNormalEquiv
              (d.toEquivariant.stabilizerIntermediateAction χ)).symm
                ⟨semidirectNormalEquiv
                    (PPrimeCharacterStabilizer.ambientAction
                      (P := P) (χ := χ)) z.1,
                  hZ hz⟩) : d.intermediate) : G) ∈ Z
      simpa using hz⟩
  left_inv z := by
    apply Subtype.ext
    apply (semidirectNormalEquiv
      (d.toEquivariant.stabilizerIntermediateAction χ)).injective
    apply Subtype.ext
    exact intermediateNormalEmbedding_left d χ z.1
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · have hzright :
          (z.1 :
            G ⋊[PPrimeCharacterStabilizer.ambientAction]
              PPrimeCharacterStabilizer P χ).right = 1 := by
        rw [← SemidirectProduct.rightHom_eq_right,
          ← MonoidHom.mem_ker,
          ← SemidirectProduct.range_inl_eq_ker_rightHom]
        exact z.1.2
      exact hzright.symm
  map_mul' z w := by
    apply Subtype.ext
    exact (intermediateNormalEmbedding d χ).map_mul z.1 w.1

/-- The ambient copy of a central subgroup is central in the normal
subgroup of the ambient semidirect character triple. -/
theorem ambientTripleSubgroup_le_center
    (χ : PPrimeIrreducibleCharacter G p)
    (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G) :
    ambientTripleSubgroup (P := P) χ Z ≤
      Subgroup.center
        (EquivariantLocalCorrespondence.ambientTriple
          (P := P) χ).normalSubgroup := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro x
  let e :=
    semidirectNormalEquiv
      (PPrimeCharacterStabilizer.ambientAction
        (P := P) (χ := χ))
  have hz' : e z ∈ Z := hz
  apply e.injective
  calc
    e (x * z) = e x * e z := map_mul e x z
    _ = e z * e x :=
      (Subgroup.mem_center_iff.mp
        (hZcentral hz')) (e x)
    _ = e (z * x) := (map_mul e z x).symm

/-- On the normal subgroup of the intermediate semidirect product, the
canonical semidirect embedding is exactly the canonical normal-subgroup
embedding. -/
theorem semidirectEmbedding_apply_normalSubgroup
    (d : LocalInductiveMcKayData P)
    (χ : PPrimeIrreducibleCharacter G p)
    (z : (d.toEquivariant.intermediateTriple χ).normalSubgroup) :
    d.toEquivariant.semidirectEmbedding χ
        (z.1 :
          d.intermediate ⋊[
            d.toEquivariant.stabilizerIntermediateAction χ]
            PPrimeCharacterStabilizer P χ) =
      (intermediateNormalEmbedding d χ z :
        (EquivariantLocalCorrespondence.ambientTriple
          (P := P) χ).normalSubgroup) := by
  apply SemidirectProduct.ext
  · rfl
  · have hzright :
        (z.1 :
          d.intermediate ⋊[
            d.toEquivariant.stabilizerIntermediateAction χ]
            PPrimeCharacterStabilizer P χ).right = 1 := by
      rw [← SemidirectProduct.rightHom_eq_right,
        ← MonoidHom.mem_ker,
        ← SemidirectProduct.range_inl_eq_ker_rightHom]
      exact z.2
    exact hzright

/-- Explicit matched-subgroup form of
`semidirectEmbedding_apply_normalSubgroup`. -/
theorem semidirectEmbedding_apply_intermediateTripleSubgroup
    (d : LocalInductiveMcKayData P)
    (χ : PPrimeIrreducibleCharacter G p)
    (Z : Subgroup G)
    (hZ : Z ≤ d.intermediate)
    (z : intermediateTripleSubgroup d χ Z) :
    d.toEquivariant.semidirectEmbedding χ
        ((z.1 :
            (d.toEquivariant.intermediateTriple χ).normalSubgroup).1 :
          d.intermediate ⋊[
            d.toEquivariant.stabilizerIntermediateAction χ]
            PPrimeCharacterStabilizer P χ) =
      (((intermediateTripleSubgroupEquivAmbient
          d χ Z hZ z).1 :
          (EquivariantLocalCorrespondence.ambientTriple
            (P := P) χ).normalSubgroup) :
        G ⋊[PPrimeCharacterStabilizer.ambientAction]
          PPrimeCharacterStabilizer P χ) :=
  semidirectEmbedding_apply_normalSubgroup d χ z.1

/-- Matched central character values satisfy the exact cross-multiplied
identity supplied by the central character-triple witness. -/
theorem correspondence_central_cross
    (d : LocalInductiveMcKayData P)
    (χ : PPrimeIrreducibleCharacter G p)
    (z : G)
    (hzcentral : z ∈ Subgroup.center G)
    (hzintermediate : z ∈ d.intermediate) :
    χ.1.values z *
        ((d.correspondence χ).1.degree : ℂ) =
      (d.correspondence χ).1.values
          ⟨z, hzintermediate⟩ *
        (χ.1.degree : ℂ) := by
  obtain
    ⟨V, W, hVadd, hVmodule, hVfinite, hVnontrivial,
      hWadd, hWmodule, hWfinite, hWnontrivial, C, hC⟩ :=
    d.triple_compatible χ
  letI : AddCommGroup V := hVadd
  letI : Module ℂ V := hVmodule
  letI : Module.Finite ℂ V := hVfinite
  letI : Nontrivial V := hVnontrivial
  letI : AddCommGroup W := hWadd
  letI : Module ℂ W := hWmodule
  letI : Module.Finite ℂ W := hWfinite
  letI : Nontrivial W := hWnontrivial
  let zN : d.intermediate := ⟨z, hzintermediate⟩
  let x :
      (EquivariantLocalCorrespondence.ambientTriple
        (P := P) χ).normalSubgroup :=
    (semidirectNormalEquiv
      (PPrimeCharacterStabilizer.ambientAction
        (P := P) (χ := χ))).symm z
  let y :
      (d.toEquivariant.intermediateTriple χ).normalSubgroup :=
    (semidirectNormalEquiv
      (d.toEquivariant.stabilizerIntermediateAction χ)).symm zN
  have hxy :
      C.embedding
          (y.1 :
            d.intermediate ⋊[
              d.toEquivariant.stabilizerIntermediateAction χ]
              PPrimeCharacterStabilizer P χ) =
        (x.1 :
          G ⋊[PPrimeCharacterStabilizer.ambientAction]
            PPrimeCharacterStabilizer P χ) := by
    rw [hC]
    calc
      d.toEquivariant.semidirectEmbedding χ y.1 =
          intermediateNormalEmbedding d χ y :=
        semidirectEmbedding_apply_normalSubgroup d χ y
      _ = x := by
        simp only [y, zN,
          intermediateNormalEmbedding_symm_apply]
        rfl
  have hx :
      x ∈ Subgroup.center
        (EquivariantLocalCorrespondence.ambientTriple
          (P := P) χ).normalSubgroup := by
    apply
      ambientTripleSubgroup_le_center
        (P := P) χ (Subgroup.center G) le_rfl
    change
      semidirectNormalEquiv
        (PPrimeCharacterStabilizer.ambientAction
          (P := P) (χ := χ)) x ∈
        Subgroup.center G
    simpa only [x, MulEquiv.apply_symm_apply]
      using hzcentral
  have hcross :=
    C.normalCharacter_matchedCentral_cross x y hxy hx
  change
    χ.1.values
          ((x.1 :
            G ⋊[PPrimeCharacterStabilizer.ambientAction]
              PPrimeCharacterStabilizer P χ).left) *
        ((d.correspondence χ).1.degree : ℂ) =
      (d.correspondence χ).1.values
          ((y.1 :
            d.intermediate ⋊[
              d.toEquivariant.stabilizerIntermediateAction χ]
              PPrimeCharacterStabilizer P χ).left) *
        (χ.1.degree : ℂ) at hcross
  have hxleft :
      (x.1 :
        G ⋊[PPrimeCharacterStabilizer.ambientAction]
          PPrimeCharacterStabilizer P χ).left = z :=
    rfl
  have hyleft :
      (y.1 :
        d.intermediate ⋊[
          d.toEquivariant.stabilizerIntermediateAction χ]
          PPrimeCharacterStabilizer P χ).left = zN :=
    rfl
  rw [hxleft, hyleft] at hcross
  exact hcross

/-- The local inductive-McKay correspondence preserves
representation-level triviality on an ambient central subgroup contained
in the intermediate subgroup. -/
theorem correspondence_trivialOn_iff
    (d : LocalInductiveMcKayData P)
    (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (hZ : Z ≤ d.intermediate)
    (χ : PPrimeIrreducibleCharacter G p) :
    χ.1.TrivialOn Z ↔
      (d.correspondence χ).1.TrivialOn
        (subgroupInIntermediate d Z) := by
  obtain
    ⟨V, W, hVadd, hVmodule, hVfinite, hVnontrivial,
      hWadd, hWmodule, hWfinite, hWnontrivial, C, hC⟩ :=
    d.triple_compatible χ
  letI : AddCommGroup V := hVadd
  letI : Module ℂ V := hVmodule
  letI : Module.Finite ℂ V := hVfinite
  letI : Nontrivial V := hVnontrivial
  letI : AddCommGroup W := hWadd
  letI : Module ℂ W := hWmodule
  letI : Module.Finite ℂ W := hWfinite
  letI : Nontrivial W := hWnontrivial
  let ZT := ambientTripleSubgroup (P := P) χ Z
  let ZU := intermediateTripleSubgroup d χ Z
  let eZ := intermediateTripleSubgroupEquivAmbient
    d χ Z hZ
  have hcomm :
      ∀ z : ZU,
        C.embedding
            ((z.1 :
                (d.toEquivariant.intermediateTriple χ).normalSubgroup).1 :
              d.intermediate ⋊[
                d.toEquivariant.stabilizerIntermediateAction χ]
                PPrimeCharacterStabilizer P χ) =
          ((eZ z : ZT).1 :
            (EquivariantLocalCorrespondence.ambientTriple
              (P := P) χ).normalSubgroup) := by
    intro z
    rw [hC]
    exact
      semidirectEmbedding_apply_intermediateTripleSubgroup
        d χ Z hZ z
  have hmatched :
      (EquivariantLocalCorrespondence.ambientTriple
          (P := P) χ).character.TrivialOn ZT ↔
        (d.toEquivariant.intermediateTriple χ).character.TrivialOn ZU :=
    C.normalCharacter_trivialOn_iff
      ZT ZU
      (ambientTripleSubgroup_le_center
        (P := P) χ Z hZcentral)
      eZ hcomm
  have hambient :
      (EquivariantLocalCorrespondence.ambientTriple
          (P := P) χ).character.TrivialOn ZT ↔
        χ.1.TrivialOn Z :=
    IrreducibleCharacter.comap_trivialOn_comap_iff
      (semidirectNormalEquiv
        (PPrimeCharacterStabilizer.ambientAction
          (P := P) (χ := χ)))
      χ.1 Z
  have hlocal :
      (d.toEquivariant.intermediateTriple χ).character.TrivialOn ZU ↔
        (d.correspondence χ).1.TrivialOn
          (subgroupInIntermediate d Z) :=
    IrreducibleCharacter.comap_trivialOn_comap_iff
      (semidirectNormalEquiv
        (d.toEquivariant.stabilizerIntermediateAction χ))
      (d.correspondence χ).1
      (subgroupInIntermediate d Z)
  exact hambient.symm.trans (hmatched.trans hlocal)

/-- The stored `p'`-character correspondence restricts exactly to the
characters trivial on the matched copies of a central subgroup. -/
def correspondenceTrivialOnEquiv
    (d : LocalInductiveMcKayData P)
    (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (hZ : Z ≤ d.intermediate) :
    {χ : PPrimeIrreducibleCharacter G p //
      χ.1.TrivialOn Z} ≃
      {ψ : PPrimeIrreducibleCharacter d.intermediate p //
        ψ.1.TrivialOn (subgroupInIntermediate d Z)} where
  toFun χ :=
    ⟨d.correspondence χ.1,
      (correspondence_trivialOn_iff
        d Z hZcentral hZ χ.1).mp χ.2⟩
  invFun ψ :=
    ⟨d.correspondence.symm ψ.1, by
      apply
        (correspondence_trivialOn_iff
          d Z hZcentral hZ
            (d.correspondence.symm ψ.1)).mpr
      simpa using ψ.2⟩
  left_inv χ := by
    apply Subtype.ext
    exact d.correspondence.symm_apply_apply χ.1
  right_inv ψ := by
    apply Subtype.ext
    exact d.correspondence.apply_symm_apply ψ.1

end LocalInductiveMcKayData
end InductiveMcKay
end McKayConjecture
