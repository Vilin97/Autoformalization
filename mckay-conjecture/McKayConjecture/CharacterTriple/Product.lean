/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DirectProductCorrespondence
import McKayConjecture.Character.Transport
import McKayConjecture.CharacterTriple.CentralCorrespondence
import McKayConjecture.CharacterTriple.CentralIsomorphism
import McKayConjecture.CharacterTriple.ProjectiveRestriction
import McKayConjecture.CharacterTriple.ProjectiveTensor

/-!
# Products of character triples

This file constructs the direct product of two character triples.  The normal
subgroup is the product subgroup, and its character is the external tensor
product, transported across `Subgroup.prodEquiv`.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w x

namespace McKayConjecture
namespace CharacterTriple

variable {A : Type u} {B : Type v}
  [Group A] [Group B]

section CharacterTripleProduct

variable [Finite A] [Finite B]

/-- The direct product of two character triples. -/
def prod (T : CharacterTriple A) (U : CharacterTriple B) :
    CharacterTriple (A × B) where
  normalSubgroup := T.normalSubgroup.prod U.normalSubgroup
  isNormal := inferInstance
  character :=
    (T.character.externalTensor U.character).comap
      (Subgroup.prodEquiv T.normalSubgroup U.normalSubgroup)
  isInvariant := by
    intro a z
    rw [IrreducibleCharacter.comap_values,
      IrreducibleCharacter.externalTensor_values,
      IrreducibleCharacter.comap_values,
      IrreducibleCharacter.externalTensor_values]
    exact congrArg₂ (· * ·)
      (T.isInvariant a.1 ⟨z.1.1, (Subgroup.mem_prod.mp z.2).1⟩)
      (U.isInvariant a.2 ⟨z.1.2, (Subgroup.mem_prod.mp z.2).2⟩)

@[simp]
theorem prod_normalSubgroup (T : CharacterTriple A) (U : CharacterTriple B) :
    (T.prod U).normalSubgroup = T.normalSubgroup.prod U.normalSubgroup :=
  rfl

@[simp]
theorem prod_character_values (T : CharacterTriple A) (U : CharacterTriple B)
    (z : T.normalSubgroup.prod U.normalSubgroup) :
    (T.prod U).character.values z =
      T.character.values
          ⟨z.1.1, (Subgroup.mem_prod.mp z.2).1⟩ *
        U.character.values
          ⟨z.1.2, (Subgroup.mem_prod.mp z.2).2⟩ := by
  change
    ((T.character.externalTensor U.character).comap
        (Subgroup.prodEquiv T.normalSubgroup U.normalSubgroup)).values z = _
  rw [IrreducibleCharacter.comap_values,
    IrreducibleCharacter.externalTensor_values]
  congr 1

@[simp]
theorem prod_character_degree (T : CharacterTriple A) (U : CharacterTriple B) :
    (T.prod U).character.degree =
      T.character.degree * U.character.degree := by
  simp [prod]

end CharacterTripleProduct

namespace ProjectiveRepresentation

variable {K : Type w} [Field K]
  {V : Type x} [AddCommGroup V] [Module K V]
  {W : Type*} [AddCommGroup W] [Module K W]

/-- The external tensor product of projective representations.  Its factor
set is the pointwise product of the two factor sets. -/
def externalTensor (P : ProjectiveRepresentation K A V)
    (Q : ProjectiveRepresentation K B W) :
    ProjectiveRepresentation K (A × B) (V ⊗[K] W) :=
  (P.comap (MonoidHom.fst A B)).tensor
    (Q.comap (MonoidHom.snd A B))

@[simp]
theorem externalTensor_operator
    (P : ProjectiveRepresentation K A V)
    (Q : ProjectiveRepresentation K B W) (a : A) (b : B) :
    (P.externalTensor Q).operator (a, b) =
      TensorProduct.congr (P.operator a) (Q.operator b) :=
  rfl

@[simp]
theorem externalTensor_factor
    (P : ProjectiveRepresentation K A V)
    (Q : ProjectiveRepresentation K B W)
    (a a' : A) (b b' : B) :
    (P.externalTensor Q).factor (a, b) (a', b') =
      P.factor a a' * Q.factor b b' :=
  rfl

theorem HasInverseFactorSet.externalTensor
    {P : ProjectiveRepresentation K A V}
    {Q : ProjectiveRepresentation K B W}
    {X Y : Type*}
    [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y]
    {P' : ProjectiveRepresentation K A X}
    {Q' : ProjectiveRepresentation K B Y}
    (hP : P.HasInverseFactorSet P')
    (hQ : Q.HasInverseFactorSet Q') :
    (P.externalTensor Q).HasInverseFactorSet
      (P'.externalTensor Q') := by
  intro g h
  change
    P'.factor g.1 h.1 * Q'.factor g.2 h.2 =
      (P.factor g.1 h.1 * Q.factor g.2 h.2)⁻¹
  rw [hP, hQ, mul_inv]

section Trace

variable [Module.Finite K V] [Module.Finite K W]

@[simp]
theorem externalTensor_traceFunction
    (P : ProjectiveRepresentation K A V)
    (Q : ProjectiveRepresentation K B W) (a : A) (b : B) :
    (P.externalTensor Q).traceFunction (a, b) =
      P.traceFunction a * Q.traceFunction b := by
  change
    ((P.comap (MonoidHom.fst A B)).tensor
      (Q.comap (MonoidHom.snd A B))).traceFunction (a, b) =
        P.traceFunction a * Q.traceFunction b
  rw [congrFun
    (ProjectiveRepresentation.traceFunction_tensor
      (P.comap (MonoidHom.fst A B))
      (Q.comap (MonoidHom.snd A B))) (a, b)]
  rfl

end Trace

/-- The external tensor product of two honest linear actions. -/
def externalTensorLinearAction
    (ρ : A →* (V ≃ₗ[K] V)) (σ : B →* (W ≃ₗ[K] W)) :
    A × B →* ((V ⊗[K] W) ≃ₗ[K] (V ⊗[K] W)) :=
  ((ofLinearAction ρ).comap (MonoidHom.fst A B)).tensorLinearAction
    ((ofLinearAction σ).comap (MonoidHom.snd A B)) (by
      intro g h
      change (1 : Kˣ) * 1 = 1
      simp)

@[simp]
theorem externalTensorLinearAction_apply
    (ρ : A →* (V ≃ₗ[K] V)) (σ : B →* (W ≃ₗ[K] W))
    (a : A) (b : B) :
    externalTensorLinearAction ρ σ (a, b) =
      TensorProduct.congr (ρ a) (σ b) :=
  rfl

end ProjectiveRepresentation

namespace Subgroup

variable {C : Type w} {D : Type x} [Group C] [Group D]

/-- Intersections of product subgroups are computed coordinatewise. -/
theorem prod_inf_prod (H₁ H₂ : Subgroup A) (K₁ K₂ : Subgroup B) :
    H₁.prod K₁ ⊓ H₂.prod K₂ =
      (H₁ ⊓ H₂).prod (K₁ ⊓ K₂) := by
  ext z
  change
    ((z.1 ∈ H₁ ∧ z.2 ∈ K₁) ∧ (z.1 ∈ H₂ ∧ z.2 ∈ K₂)) ↔
      ((z.1 ∈ H₁ ∧ z.1 ∈ H₂) ∧ (z.2 ∈ K₁ ∧ z.2 ∈ K₂))
  tauto

/-- Mapping a product subgroup along a product homomorphism is coordinatewise. -/
theorem prod_map_prodMap (H : Subgroup A) (K : Subgroup B)
    (f : A →* C) (g : B →* D) :
    (H.prod K).map (f.prodMap g) =
      (H.map f).prod (K.map g) := by
  ext z
  constructor
  · rintro ⟨y, hy, hyz⟩
    exact
      ⟨⟨y.1, hy.1, congrArg Prod.fst hyz⟩,
        ⟨y.2, hy.2, congrArg Prod.snd hyz⟩⟩
  · rintro ⟨⟨a, ha, hfa⟩, ⟨b, hb, hgb⟩⟩
    refine ⟨(a, b), ⟨ha, hb⟩, ?_⟩
    exact Prod.ext hfa hgb

/-- The centralizer of a product subgroup is the product of centralizers. -/
theorem centralizer_prod (H : Subgroup A) (K : Subgroup B) :
    Subgroup.centralizer (H.prod K : Set (A × B)) =
      (Subgroup.centralizer (H : Set A)).prod
        (Subgroup.centralizer (K : Set B)) := by
  ext z
  constructor
  · intro hz
    rw [Subgroup.mem_centralizer_iff] at hz
    constructor
    · change ∀ a : A, a ∈ H → a * z.1 = z.1 * a
      intro a ha
      have h := hz (a, 1) ⟨ha, one_mem K⟩
      exact congrArg Prod.fst h
    · change ∀ b : B, b ∈ K → b * z.2 = z.2 * b
      intro b hb
      have h := hz (1, b) ⟨one_mem H, hb⟩
      exact congrArg Prod.snd h
  · rintro ⟨hzA, hzB⟩
    change (∀ a : A, a ∈ H → a * z.1 = z.1 * a) at hzA
    change (∀ b : B, b ∈ K → b * z.2 = z.2 * b) at hzB
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Prod.ext (hzA y.1 hy.1) (hzB y.2 hy.2)

end Subgroup

namespace TensorProduct

variable {K : Type w} [Field K]
  {V : Type} [AddCommGroup V] [Module K V]
  {W : Type} [AddCommGroup W] [Module K W]

/-- The tensor product of two scalar linear equivalences is scalar, with
scalar equal to the product. -/
theorem congr_scalarLinearEquiv (c d : Kˣ) :
    TensorProduct.congr
        (scalarLinearEquiv K V c) (scalarLinearEquiv K W d) =
      scalarLinearEquiv K (V ⊗[K] W) (c * d) := by
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.ext'
  intro v w
  change
    ((c : K) • v) ⊗ₜ[K] ((d : K) • w) =
      (((c * d : Kˣ) : K) • (v ⊗ₜ[K] w))
  simpa only [Units.val_mul] using
    (TensorProduct.smul_tmul_smul (c : K) (d : K) v w)

end TensorProduct

namespace AssociatedProjectiveRepresentation

variable [Finite A] [Finite B]
variable {V : Type} [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
  {W : Type} [AddCommGroup W] [Module ℂ W]
  [Module.Finite ℂ W] [Nontrivial W]
  {T : CharacterTriple A} {U : CharacterTriple B}
  {P : ProjectiveRepresentation ℂ A V}
  {Q : ProjectiveRepresentation ℂ B W}

/-- The external tensor restriction action on the product normal subgroup. -/
def prodRestriction
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q) :
    (T.prod U).normalSubgroup →*
      ((V ⊗[ℂ] W) ≃ₗ[ℂ] (V ⊗[ℂ] W)) :=
  (ProjectiveRepresentation.externalTensorLinearAction
      R.restriction S.restriction).comp
    (Subgroup.prodEquiv T.normalSubgroup U.normalSubgroup).toMonoidHom

@[simp]
theorem prodRestriction_apply
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (z : (T.prod U).normalSubgroup) :
    R.prodRestriction S z =
      TensorProduct.congr
        (R.restriction
          ⟨z.1.1, (Subgroup.mem_prod.mp z.2).1⟩)
        (S.restriction
          ⟨z.1.2, (Subgroup.mem_prod.mp z.2).2⟩) := by
  rfl

variable [Nontrivial (V ⊗[ℂ] W)]

/-- External tensor products preserve association with character triples. -/
def prod
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q) :
    AssociatedProjectiveRepresentation
      (T.prod U) (V ⊗[ℂ] W) (P.externalTensor Q) where
  restriction := R.prodRestriction S
  restriction_apply := by
    intro z
    rw [prodRestriction_apply, ProjectiveRepresentation.externalTensor_operator]
    congr 1
    · exact R.restriction_apply
        ⟨z.1.1, (Subgroup.mem_prod.mp z.2).1⟩
    · exact S.restriction_apply
        ⟨z.1.2, (Subgroup.mem_prod.mp z.2).2⟩
  restriction_simple := by
    let E : FDRep ℂ (T.normalSubgroup × U.normalSubgroup) ≌
        FDRep ℂ (T.normalSubgroup.prod U.normalSubgroup) :=
      Action.resEquiv (FGModuleCat ℂ)
        (Subgroup.prodEquiv T.normalSubgroup U.normalSubgroup)
    letI :
        Simple (FDRep.externalTensor R.fdRestriction S.fdRestriction) :=
      FDRep.externalTensor_simple R.fdRestriction S.fdRestriction
    change
      Simple
        (E.functor.obj
          (FDRep.externalTensor R.fdRestriction S.fdRestriction))
    exact CategoryTheory.simple_obj E.functor _
  restriction_character := by
    funext z
    change
      (FDRep.externalTensor R.fdRestriction S.fdRestriction).character
          ((Subgroup.prodEquiv T.normalSubgroup U.normalSubgroup) z) =
        (T.character.externalTensor U.character).values
          ((Subgroup.prodEquiv T.normalSubgroup U.normalSubgroup) z)
    rw [FDRep.externalTensor_character,
      IrreducibleCharacter.externalTensor_values,
      R.fdRestriction_character, S.fdRestriction_character]
  normal_mul := by
    intro z a
    rw [ProjectiveRepresentation.externalTensor_operator,
      ProjectiveRepresentation.externalTensor_operator,
      ProjectiveRepresentation.externalTensor_operator,
      ← TensorProduct.congr_mul]
    change
      TensorProduct.congr
          (P.operator (z.1.1 * a.1))
          (Q.operator (z.1.2 * a.2)) =
        TensorProduct.congr
          (P.operator z.1.1 * P.operator a.1)
          (Q.operator z.1.2 * Q.operator a.2)
    rw [R.normal_mul
      ⟨z.1.1, (Subgroup.mem_prod.mp z.2).1⟩ a.1,
      S.normal_mul
      ⟨z.1.2, (Subgroup.mem_prod.mp z.2).2⟩ a.2]
  mul_normal := by
    intro a z
    rw [ProjectiveRepresentation.externalTensor_operator,
      ProjectiveRepresentation.externalTensor_operator,
      ProjectiveRepresentation.externalTensor_operator,
      ← TensorProduct.congr_mul]
    change
      TensorProduct.congr
          (P.operator (a.1 * z.1.1))
          (Q.operator (a.2 * z.1.2)) =
        TensorProduct.congr
          (P.operator a.1 * P.operator z.1.1)
          (Q.operator a.2 * Q.operator z.1.2)
    rw [R.mul_normal a.1
      ⟨z.1.1, (Subgroup.mem_prod.mp z.2).1⟩,
      S.mul_normal a.2
      ⟨z.1.2, (Subgroup.mem_prod.mp z.2).2⟩]

end AssociatedProjectiveRepresentation

namespace CentralIsomorphismWitness

variable {A₁ : Type u} {B₁ : Type v} {A₂ : Type w} {B₂ : Type x}
  [Finite A₁] [Group A₁] [Finite B₁] [Group B₁]
  [Finite A₂] [Group A₂] [Finite B₂] [Group B₂]
  {T₁ : CharacterTriple A₁} {U₁ : CharacterTriple B₁}
  {T₂ : CharacterTriple A₂} {U₂ : CharacterTriple B₂}
  {V₁ W₁ V₂ W₂ : Type}
  [AddCommGroup V₁] [Module ℂ V₁] [Module.Finite ℂ V₁] [Nontrivial V₁]
  [AddCommGroup W₁] [Module ℂ W₁] [Module.Finite ℂ W₁] [Nontrivial W₁]
  [AddCommGroup V₂] [Module ℂ V₂] [Module.Finite ℂ V₂] [Nontrivial V₂]
  [AddCommGroup W₂] [Module ℂ W₂] [Module.Finite ℂ W₂] [Nontrivial W₂]
  [Nontrivial (V₁ ⊗[ℂ] V₂)] [Nontrivial (W₁ ⊗[ℂ] W₂)]

/-- Central isomorphism witnesses are closed under direct products. -/
def prod
    (C : CentralIsomorphismWitness T₁ U₁ V₁ W₁)
    (D : CentralIsomorphismWitness T₂ U₂ V₂ W₂) :
    CentralIsomorphismWitness
      (T₁.prod T₂) (U₁.prod U₂)
      (V₁ ⊗[ℂ] V₂) (W₁ ⊗[ℂ] W₂) where
  leftProjective :=
    C.leftProjective.externalTensor D.leftProjective
  leftAssociated :=
    C.leftAssociated.prod D.leftAssociated
  rightProjective :=
    C.rightProjective.externalTensor D.rightProjective
  rightAssociated :=
    C.rightAssociated.prod D.rightAssociated
  embedding := C.embedding.prodMap D.embedding
  embedding_injective := by
    exact Function.Injective.prodMap
      C.embedding_injective D.embedding_injective
  centralizer_le := by
    change
      Subgroup.centralizer
          (T₁.normalSubgroup.prod T₂.normalSubgroup :
            Set (A₁ × A₂)) ≤
        MonoidHom.range (C.embedding.prodMap D.embedding)
    rw [Subgroup.centralizer_prod, MonoidHom.range_prodMap]
    exact Subgroup.prod_mono C.centralizer_le D.centralizer_le
  ambient_eq_product := by
    intro a
    obtain ⟨x₁, h₁, hh₁⟩ := C.ambient_eq_product a.1
    obtain ⟨x₂, h₂, hh₂⟩ := D.ambient_eq_product a.2
    refine
      ⟨⟨(x₁, x₂), ⟨x₁.property, x₂.property⟩⟩,
        (h₁, h₂), ?_⟩
    exact Prod.ext hh₁ hh₂
  intersection_eq := by
    change
      T₁.normalSubgroup.prod T₂.normalSubgroup ⊓
          MonoidHom.range (C.embedding.prodMap D.embedding) =
        (U₁.normalSubgroup.prod U₂.normalSubgroup).map
          (C.embedding.prodMap D.embedding)
    rw [MonoidHom.range_prodMap,
      Subgroup.prod_inf_prod,
      C.intersection_eq, D.intersection_eq,
      Subgroup.prod_map_prodMap]
  factor_agreement := by
    intro h k
    change
      C.leftProjective.factor (C.embedding h.1) (C.embedding k.1) *
          D.leftProjective.factor (D.embedding h.2) (D.embedding k.2) =
        C.rightProjective.factor h.1 k.1 *
          D.rightProjective.factor h.2 k.2
    rw [C.factor_agreement, D.factor_agreement]
  scalar_agreement := by
    intro h hh
    change
      (C.embedding h.1, D.embedding h.2) ∈
        Subgroup.centralizer
          (T₁.normalSubgroup.prod T₂.normalSubgroup :
            Set (A₁ × A₂)) at hh
    rw [Subgroup.centralizer_prod] at hh
    obtain ⟨c, hcL, hcR⟩ :=
      C.scalar_agreement h.1 hh.1
    obtain ⟨d, hdL, hdR⟩ :=
      D.scalar_agreement h.2 hh.2
    refine ⟨c * d, ?_, ?_⟩
    · change
        TensorProduct.congr
            (C.leftProjective.operator (C.embedding h.1))
            (D.leftProjective.operator (D.embedding h.2)) =
          scalarLinearEquiv ℂ (V₁ ⊗[ℂ] V₂) (c * d)
      rw [hcL, hdL, TensorProduct.congr_scalarLinearEquiv]
    · change
        TensorProduct.congr
            (C.rightProjective.operator h.1)
            (D.rightProjective.operator h.2) =
          scalarLinearEquiv ℂ (W₁ ⊗[ℂ] W₂) (c * d)
      rw [hcR, hdR, TensorProduct.congr_scalarLinearEquiv]

section CorrespondenceCompatibility

variable {Z₁ Z₂ : Type}
  [AddCommGroup Z₁] [Module ℂ Z₁]
  [AddCommGroup Z₂] [Module ℂ Z₂]

/-- The external product of inverse factor-set representations cancels the
left projective lift of the product witness. -/
theorem prod_left_hasInverseFactorSet
    (C : CentralIsomorphismWitness T₁ U₁ V₁ W₁)
    (D : CentralIsomorphismWitness T₂ U₂ V₂ W₂)
    (Q : ProjectiveRepresentation ℂ A₁ Z₁)
    (R : ProjectiveRepresentation ℂ A₂ Z₂)
    (hQ : C.leftProjective.HasInverseFactorSet Q)
    (hR : D.leftProjective.HasInverseFactorSet R) :
    (C.prod D).leftProjective.HasInverseFactorSet
      (Q.externalTensor R) := by
  change
    (C.leftProjective.externalTensor D.leftProjective).HasInverseFactorSet
      (Q.externalTensor R)
  exact hQ.externalTensor hR

variable [Module.Finite ℂ Z₁] [Module.Finite ℂ Z₂]

/-- On the left, the character-producing cancelled tensor construction for
a product witness is the pointwise product of the two factor constructions.
This is the character formula underlying compatibility of the central
character correspondence with external tensor products. -/
theorem prod_leftTensorRepresentation_character
    (C : CentralIsomorphismWitness T₁ U₁ V₁ W₁)
    (D : CentralIsomorphismWitness T₂ U₂ V₂ W₂)
    (Q : ProjectiveRepresentation ℂ A₁ Z₁)
    (R : ProjectiveRepresentation ℂ A₂ Z₂)
    (hQ : C.leftProjective.HasInverseFactorSet Q)
    (hR : D.leftProjective.HasInverseFactorSet R)
    (a : A₁) (b : A₂) :
    ((C.prod D).leftTensorRepresentation
        (Q.externalTensor R)
        (prod_left_hasInverseFactorSet C D Q R hQ hR)).character (a, b) =
      (C.leftTensorRepresentation Q hQ).character a *
        (D.leftTensorRepresentation R hR).character b := by
  rw [(C.prod D).leftTensorRepresentation_character,
    C.leftTensorRepresentation_character,
    D.leftTensorRepresentation_character]
  simp only [Pi.mul_apply]
  dsimp only [CentralIsomorphismWitness.prod]
  rw [ProjectiveRepresentation.externalTensor_traceFunction,
    ProjectiveRepresentation.externalTensor_traceFunction]
  ring

/-- The corresponding right-hand cancelled tensor character also commutes
with products.  Thus product witnesses preserve the exact character formula
used by the forward central-character correspondence. -/
theorem prod_rightTensorRepresentation_character
    (C : CentralIsomorphismWitness T₁ U₁ V₁ W₁)
    (D : CentralIsomorphismWitness T₂ U₂ V₂ W₂)
    (Q : ProjectiveRepresentation ℂ A₁ Z₁)
    (R : ProjectiveRepresentation ℂ A₂ Z₂)
    (hQ : C.leftProjective.HasInverseFactorSet Q)
    (hR : D.leftProjective.HasInverseFactorSet R)
    (a : B₁) (b : B₂) :
    ((C.prod D).rightTensorRepresentation
        (Q.externalTensor R)
        (prod_left_hasInverseFactorSet C D Q R hQ hR)).character (a, b) =
      (C.rightTensorRepresentation Q hQ).character a *
        (D.rightTensorRepresentation R hR).character b := by
  rw [(C.prod D).rightTensorRepresentation_character,
    C.rightTensorRepresentation_character,
    D.rightTensorRepresentation_character]
  simp only [Pi.mul_apply, Function.comp_apply]
  dsimp only [CentralIsomorphismWitness.prod]
  rw [ProjectiveRepresentation.externalTensor_traceFunction,
    ProjectiveRepresentation.externalTensor_traceFunction]
  simp only [MonoidHom.coe_prodMap, Prod.map_apply]
  ring

end CorrespondenceCompatibility

end CentralIsomorphismWitness

end CharacterTriple
end McKayConjecture
