/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedExistence
import McKayConjecture.CharacterTriple.Transport
import McKayConjecture.InductiveMcKay.Condition

/-!
# The trivial local case of the inductive McKay condition

When a Sylow subgroup has full normalizer, the full group is the local
subgroup and transport along `Subgroup.topEquiv` gives the identity
correspondence.  The two semidirect character triples are then isomorphic
by the canonical semidirect embedding.  Relabelling a reflexive central
isomorphism witness along this isomorphism supplies the complete
character-triple compatibility required by `LocalInductiveMcKayData`.
-/

noncomputable section

open scoped IsMulCommutative

universe u

namespace McKayConjecture.InductiveMcKay

open McKayConjecture.CharacterTriple

variable {G : Type u} [Group G] [Finite G] {p : ℕ}

private theorem characterTriple_ext
    {A : Type u} [Finite A] [Group A]
    {T U : CharacterTriple A}
    (hN : T.normalSubgroup = U.normalSubgroup)
    (hχ : HEq T.character U.character) :
    T = U := by
  cases T
  cases U
  cases hN
  cases eq_of_heq hχ
  rfl

private theorem comap_subgroupCongr_heq
    {A : Type u} [Group A]
    {H K : Subgroup A} (h : H = K)
    (χ : IrreducibleCharacter K) :
    HEq (χ.comap (MulEquiv.subgroupCongr h)) χ := by
  cases h
  apply heq_of_eq
  exact IrreducibleCharacter.comap_refl χ

private theorem characterTriple_ext_comap
    {A : Type u} [Finite A] [Group A]
    {T U : CharacterTriple A}
    (hN : T.normalSubgroup = U.normalSubgroup)
    (hχ :
      T.character =
        U.character.comap
          (MulEquiv.subgroupCongr hN)) :
    T = U := by
  apply characterTriple_ext hN
  exact (heq_of_eq hχ).trans
    (comap_subgroupCongr_heq hN U.character)

private theorem characterTriple_comap_refl
    {A : Type u} [Finite A] [Group A]
    (T : CharacterTriple A) :
    T.comap (MulEquiv.refl A) = T := by
  have hN :
      (T.comap (MulEquiv.refl A)).normalSubgroup =
        T.normalSubgroup := by
    ext a
    rfl
  apply characterTriple_ext_comap hN
  apply IrreducibleCharacter.ext
  funext x
  rfl

namespace EquivariantLocalCorrespondence

/-- The identity equivariant local correspondence through the full group.

The intermediate group is the top subgroup.  Its character correspondence
is pullback along `Subgroup.topEquiv`, and hence is the identity after
forgetting the harmless subtype wrapper. -/
def of_normalizer_eq_top
    (P : Sylow p G)
    (hP : Subgroup.normalizer (P : Set G) = ⊤) :
    EquivariantLocalCorrespondence P where
  toLocalCorrespondence :=
    { intermediate := ⊤
      normalizer_le := hP.le
      proper_of_normalizer_ne_top := fun h ↦ (h hP).elim
      correspondence :=
        PPrimeCorrespondence.ofMulEquiv p Subgroup.topEquiv }
  intermediate_invariant := by
    intro a
    exact Subgroup.map_top_of_surjective
      (a.1 : G →* G) a.1.surjective
  map_smul' := by
    intro a χ
    apply Subtype.ext
    apply IrreducibleCharacter.ext
    funext x
    rfl

variable {P : Sylow p G}

omit [Finite G] in
/-- In the full-normalizer case, the canonical semidirect embedding is
surjective as well as injective. -/
theorem semidirectEmbedding_surjective_of_normalizer_eq_top
    (hP : Subgroup.normalizer (P : Set G) = ⊤)
    (χ : PPrimeIrreducibleCharacter G p) :
    Function.Surjective
      ((of_normalizer_eq_top P hP).semidirectEmbedding χ) := by
  intro z
  let h :
      (of_normalizer_eq_top P hP).intermediate ⋊[(of_normalizer_eq_top
        P hP).stabilizerIntermediateAction χ]
        PPrimeCharacterStabilizer P χ :=
    ⟨⟨z.left, Subgroup.mem_top z.left⟩, z.right⟩
  exact ⟨h, by
    apply SemidirectProduct.ext
    · rfl
    · rfl⟩

/-- The canonical semidirect embedding in the full-normalizer case,
regarded as a group equivalence. -/
def semidirectEquivOfNormalizerEqTop
    (hP : Subgroup.normalizer (P : Set G) = ⊤)
    (χ : PPrimeIrreducibleCharacter G p) :
    ((of_normalizer_eq_top P hP).intermediate ⋊[(of_normalizer_eq_top
      P hP).stabilizerIntermediateAction χ]
      PPrimeCharacterStabilizer P χ) ≃*
      (G ⋊[PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer P χ) :=
  MulEquiv.ofBijective
    ((of_normalizer_eq_top P hP).semidirectEmbedding χ)
    ⟨(of_normalizer_eq_top P hP).semidirectEmbedding_injective χ,
      semidirectEmbedding_surjective_of_normalizer_eq_top hP χ⟩

omit [Finite G] in
@[simp]
theorem semidirectEquivOfNormalizerEqTop_apply
    (hP : Subgroup.normalizer (P : Set G) = ⊤)
    (χ : PPrimeIrreducibleCharacter G p)
    (z :
      (of_normalizer_eq_top P hP).intermediate ⋊[(of_normalizer_eq_top
        P hP).stabilizerIntermediateAction χ]
        PPrimeCharacterStabilizer P χ) :
    semidirectEquivOfNormalizerEqTop hP χ z =
      (of_normalizer_eq_top P hP).semidirectEmbedding χ z :=
  rfl

/-- Pulling the ambient semidirect character triple back along the
canonical full-local equivalence gives the local semidirect triple. -/
theorem ambientTriple_comap_semidirectEquivOfNormalizerEqTop
    (hP : Subgroup.normalizer (P : Set G) = ⊤)
    (χ : PPrimeIrreducibleCharacter G p) :
    (ambientTriple (P := P) χ).comap
        (semidirectEquivOfNormalizerEqTop hP χ) =
      (of_normalizer_eq_top P hP).intermediateTriple χ := by
  let d := of_normalizer_eq_top P hP
  let e := semidirectEquivOfNormalizerEqTop hP χ
  have hN :
      ((ambientTriple (P := P) χ).comap e).normalSubgroup =
        (d.intermediateTriple χ).normalSubgroup := by
    change
      (MonoidHom.range
        (SemidirectProduct.inl :
          G →*
            (G ⋊[PPrimeCharacterStabilizer.ambientAction]
              PPrimeCharacterStabilizer P χ))).comap
          e.toMonoidHom =
        MonoidHom.range
          (SemidirectProduct.inl :
            d.intermediate →*
              (d.intermediate ⋊[
                d.stabilizerIntermediateAction χ]
                PPrimeCharacterStabilizer P χ))
    rw [SemidirectProduct.range_inl_eq_ker_rightHom,
      SemidirectProduct.range_inl_eq_ker_rightHom]
    ext z
    change (e z).right = 1 ↔ z.right = 1
    rfl
  apply characterTriple_ext_comap hN
  apply IrreducibleCharacter.ext
  funext z
  rfl

/-- The identity equivariant correspondence satisfies the complete
character-triple clause.  The witness is a relabelled reflexive witness,
and its embedding is exactly the canonical semidirect embedding. -/
theorem tripleCompatible_of_normalizer_eq_top
    (hP : Subgroup.normalizer (P : Set G) = ⊤)
    (χ : PPrimeIrreducibleCharacter G p) :
    (of_normalizer_eq_top P hP).TripleCompatible χ := by
  let d := of_normalizer_eq_top P hP
  let T := ambientTriple (P := P) χ
  let e := semidirectEquivOfNormalizerEqTop hP χ
  let R :=
    AssociatedExistence.associated
      (PPrimeCharacterStabilizer.ambientAction
        (P := P) (χ := χ)) χ.1
        (PPrimeCharacterStabilizer.character_invariant
          (P := P) (χ := χ))
  let C₀ := CentralIsomorphismWitness.refl R
  refine ⟨χ.1.realization, χ.1.realization,
    inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  have hleft :
      T.comap
          (MulEquiv.refl
            (G ⋊[PPrimeCharacterStabilizer.ambientAction]
              PPrimeCharacterStabilizer P χ)) =
        T :=
    characterTriple_comap_refl T
  have hright :
      T.comap e = d.intermediateTriple χ :=
    ambientTriple_comap_semidirectEquivOfNormalizerEqTop hP χ
  change
    ∃ C : CentralIsomorphismWitness T
        (d.intermediateTriple χ)
        χ.1.realization χ.1.realization,
      C.embedding = d.semidirectEmbedding χ
  rw [← hleft, ← hright]
  refine ⟨C₀.comap
    (MulEquiv.refl
      (G ⋊[PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer P χ)) e, ?_⟩
  apply MonoidHom.ext
  intro z
  rfl

end EquivariantLocalCorrespondence

namespace LocalInductiveMcKayData

/-- Full local inductive-McKay data in the base case where the Sylow
normalizer is the whole group. -/
def of_normalizer_eq_top
    (P : Sylow p G)
    (hP : Subgroup.normalizer (P : Set G) = ⊤) :
    LocalInductiveMcKayData P where
  toEquivariantLocalCorrespondence :=
    EquivariantLocalCorrespondence.of_normalizer_eq_top P hP
  triple_compatible :=
    EquivariantLocalCorrespondence.tripleCompatible_of_normalizer_eq_top hP

/-- A normal Sylow subgroup has the full local inductive-McKay datum. -/
def of_normal_sylow
    (P : Sylow p G) [(P : Subgroup G).Normal] :
    LocalInductiveMcKayData P :=
  of_normalizer_eq_top P
    (Subgroup.normalizer_eq_top (H := (P : Subgroup G)))

/-- Full local data for a group whose multiplication is commutative. -/
def of_isMulCommutative
    (hG : IsMulCommutative G)
    (P : Sylow p G) :
    LocalInductiveMcKayData P := by
  letI : IsMulCommutative G := hG
  exact of_normal_sylow P

/-- Full local data for a commutative group. -/
def of_commGroup
    {G : Type u} [CommGroup G] [Finite G]
    (P : Sylow p G) :
    LocalInductiveMcKayData P :=
  of_isMulCommutative inferInstance P

end LocalInductiveMcKayData

end McKayConjecture.InductiveMcKay
