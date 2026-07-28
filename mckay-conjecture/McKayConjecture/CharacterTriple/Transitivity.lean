/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralIsomorphism

/-!
# Composition of central isomorphisms

The subgroup part of a central-isomorphism witness composes directly.  The
projective part requires one genuine coherence condition: the two witnesses
may have chosen unrelated associated projective representations of their
common middle character triple.  To retain the *exact* factor-set and scalar
equalities in `CentralIsomorphismWitness`, those middle lifts must agree on
the subgroup used by the second witness.

`MiddleCompatibility` records precisely that local coherence, and `compose`
constructs the composite witness without weakening any condition.
-/

noncomputable section

universe u v w

namespace McKayConjecture
namespace CharacterTriple
namespace FactorMatchedIsomorphismWitness

section SubgroupGeometry

local notation "CentralIsomorphismWitness" =>
  FactorMatchedIsomorphismWitness

variable {A : Type u} {B : Type v} [Finite A] [Finite B] [Group A] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {V W : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]

/-- The embedding sends the right normal subgroup into the left one. -/
theorem embedding_rightNormal_mem_leftNormal
    (C : CentralIsomorphismWitness T U V W)
    (m : U.normalSubgroup) :
    C.embedding m ∈ T.normalSubgroup :=
  C.map_rightNormal_le_leftNormal ⟨m, m.property, rfl⟩

/-- The exact intersection condition also reflects membership: if an element
of the right ambient group maps into the left normal subgroup, it already lies
in the right normal subgroup. -/
theorem mem_rightNormal_of_embedding_mem_leftNormal
    (C : CentralIsomorphismWitness T U V W)
    {b : B} (hb : C.embedding b ∈ T.normalSubgroup) :
    b ∈ U.normalSubgroup := by
  have hbInf :
      C.embedding b ∈ T.normalSubgroup ⊓ MonoidHom.range C.embedding :=
    ⟨hb, ⟨b, rfl⟩⟩
  rw [C.intersection_eq] at hbInf
  obtain ⟨m, hm, hmEq⟩ := hbInf
  have hmb : m = b := C.embedding_injective hmEq
  simpa [hmb] using hm

/-- A preimage of an element centralizing the left normal subgroup
centralizes the right normal subgroup. -/
theorem mem_rightCentralizer_of_embedding_mem_leftCentralizer
    (C : CentralIsomorphismWitness T U V W)
    {b : B}
    (hb : C.embedding b ∈
      Subgroup.centralizer (T.normalSubgroup : Set A)) :
    b ∈ Subgroup.centralizer (U.normalSubgroup : Set B) := by
  rw [Subgroup.mem_centralizer_iff] at hb ⊢
  intro m hm
  apply C.embedding_injective
  rw [map_mul, map_mul]
  exact hb (C.embedding m)
    (C.embedding_rightNormal_mem_leftNormal ⟨m, hm⟩)

end SubgroupGeometry

end FactorMatchedIsomorphismWitness

namespace CentralIsomorphismWitness

section SubgroupGeometry

variable {A : Type u} {B : Type v} [Finite A] [Finite B] [Group A] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {V W : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]

/-- Compatibility wrapper for the stronger central witness. -/
theorem embedding_rightNormal_mem_leftNormal
    (C : CentralIsomorphismWitness T U V W)
    (m : U.normalSubgroup) :
    C.embedding m ∈ T.normalSubgroup :=
  C.toFactorMatchedIsomorphismWitness
    |>.embedding_rightNormal_mem_leftNormal m

/-- Compatibility wrapper for the stronger central witness. -/
theorem mem_rightNormal_of_embedding_mem_leftNormal
    (C : CentralIsomorphismWitness T U V W)
    {b : B} (hb : C.embedding b ∈ T.normalSubgroup) :
    b ∈ U.normalSubgroup :=
  C.toFactorMatchedIsomorphismWitness
    |>.mem_rightNormal_of_embedding_mem_leftNormal hb

/-- Compatibility wrapper for the stronger central witness. -/
theorem mem_rightCentralizer_of_embedding_mem_leftCentralizer
    (C : CentralIsomorphismWitness T U V W)
    {b : B}
    (hb : C.embedding b ∈
      Subgroup.centralizer (T.normalSubgroup : Set A)) :
    b ∈ Subgroup.centralizer (U.normalSubgroup : Set B) :=
  C.toFactorMatchedIsomorphismWitness
    |>.mem_rightCentralizer_of_embedding_mem_leftCentralizer hb

end SubgroupGeometry

section Compatibility

variable {A : Type u} {B : Type v} {D : Type w}
  [Finite A] [Finite B] [Finite D] [Group A] [Group B] [Group D]
variable {T : CharacterTriple A} {U : CharacterTriple B}
  {Z : CharacterTriple D}
variable {V W W' Y : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]
  [AddCommGroup W'] [Module ℂ W'] [Module.Finite ℂ W'] [Nontrivial W']
  [AddCommGroup Y] [Module ℂ Y] [Module.Finite ℂ Y] [Nontrivial Y]

/-- Coherence of the two chosen projective lifts of the middle character
triple, restricted to the subgroup used by the second witness.

These are exactly the equalities needed to compose the outer factor sets and
central scalar data.  No identification of the two representation spaces is
required.
-/
structure MiddleCompatibility
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U Z W' Y) : Prop where
  /-- The two middle factor sets agree on the second embedded subgroup. -/
  factor_agreement : ∀ d e : D,
    C₁.rightProjective.factor (C₂.embedding d) (C₂.embedding e) =
      C₂.leftProjective.factor (C₂.embedding d) (C₂.embedding e)
  /-- The two middle lifts use the same scalar precisely on elements whose
  image must satisfy the scalar condition in the composite witness. -/
  scalar_agreement : ∀ (d : D),
    C₁.embedding (C₂.embedding d) ∈
      Subgroup.centralizer (T.normalSubgroup : Set A) →
      ∃ c : ℂˣ,
        C₁.rightProjective.operator (C₂.embedding d) =
          scalarLinearEquiv ℂ W c ∧
        C₂.leftProjective.operator (C₂.embedding d) =
          scalarLinearEquiv ℂ W' c

/-- The subgroup embedding of the composite witness. -/
def compositeEmbedding
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U Z W' Y) : D →* A :=
  C₁.embedding.comp C₂.embedding

@[simp]
theorem compositeEmbedding_apply
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U Z W' Y) (d : D) :
    C₁.compositeEmbedding C₂ d = C₁.embedding (C₂.embedding d) :=
  rfl

/-- Compose two central-isomorphism witnesses whose chosen middle projective
lifts are compatible. -/
def compose
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U Z W' Y)
    (hmid : MiddleCompatibility C₁ C₂) :
    CentralIsomorphismWitness T Z V Y where
  leftProjective := C₁.leftProjective
  leftAssociated := C₁.leftAssociated
  rightProjective := C₂.rightProjective
  rightAssociated := C₂.rightAssociated
  embedding := C₁.compositeEmbedding C₂
  embedding_injective :=
    C₁.embedding_injective.comp C₂.embedding_injective
  centralizer_le := by
    intro a ha
    obtain ⟨b, hb⟩ := C₁.centralizer_le ha
    have hbCentralizer : C₁.embedding b ∈
        Subgroup.centralizer (T.normalSubgroup : Set A) := by
      simpa only [hb] using ha
    have hbMiddle :=
      C₁.mem_rightCentralizer_of_embedding_mem_leftCentralizer hbCentralizer
    obtain ⟨d, hd⟩ := C₂.centralizer_le hbMiddle
    refine ⟨d, ?_⟩
    change C₁.embedding (C₂.embedding d) = a
    rw [hd, hb]
  ambient_eq_product := by
    intro a
    obtain ⟨x, b, hxb⟩ := C₁.ambient_eq_product a
    obtain ⟨m, d, hmd⟩ := C₂.ambient_eq_product b
    have hmX : C₁.embedding m ∈ T.normalSubgroup :=
      C₁.embedding_rightNormal_mem_leftNormal m
    refine
      ⟨⟨(x : A) * C₁.embedding m,
          T.normalSubgroup.mul_mem x.property hmX⟩, d, ?_⟩
    change ((x : A) * C₁.embedding m) *
      C₁.embedding (C₂.embedding d) = a
    calc
      ((x : A) * C₁.embedding m) *
          C₁.embedding (C₂.embedding d) =
        (x : A) * C₁.embedding ((m : B) * C₂.embedding d) := by
          rw [mul_assoc, map_mul]
      _ = (x : A) * C₁.embedding b := by rw [hmd]
      _ = a := hxb
  intersection_eq := by
    ext a
    constructor
    · rintro ⟨haX, ⟨d, hd⟩⟩
      have hdX : C₁.embedding (C₂.embedding d) ∈ T.normalSubgroup := by
        change C₁.embedding (C₂.embedding d) = a at hd
        rw [hd]
        exact haX
      have hdM : C₂.embedding d ∈ U.normalSubgroup :=
        C₁.mem_rightNormal_of_embedding_mem_leftNormal hdX
      have hdN : d ∈ Z.normalSubgroup :=
        C₂.mem_rightNormal_of_embedding_mem_leftNormal hdM
      exact ⟨d, hdN, hd⟩
    · rintro ⟨d, hdN, hd⟩
      have hdM : C₂.embedding d ∈ U.normalSubgroup :=
        C₂.embedding_rightNormal_mem_leftNormal ⟨d, hdN⟩
      have hdX : C₁.embedding (C₂.embedding d) ∈ T.normalSubgroup :=
        C₁.embedding_rightNormal_mem_leftNormal ⟨C₂.embedding d, hdM⟩
      refine ⟨?_, ⟨d, hd⟩⟩
      rw [← hd]
      exact hdX
  factor_agreement := by
    intro d e
    calc
      C₁.leftProjective.factor
          (C₁.embedding (C₂.embedding d))
          (C₁.embedding (C₂.embedding e)) =
        C₁.rightProjective.factor
          (C₂.embedding d) (C₂.embedding e) :=
            C₁.factor_agreement (C₂.embedding d) (C₂.embedding e)
      _ = C₂.leftProjective.factor
          (C₂.embedding d) (C₂.embedding e) :=
            hmid.factor_agreement d e
      _ = C₂.rightProjective.factor d e :=
            C₂.factor_agreement d e
  scalar_agreement := by
    intro d hd
    change C₁.embedding (C₂.embedding d) ∈
      Subgroup.centralizer (T.normalSubgroup : Set A) at hd
    have hdMiddle :
        C₂.embedding d ∈
          Subgroup.centralizer (U.normalSubgroup : Set B) :=
      C₁.mem_rightCentralizer_of_embedding_mem_leftCentralizer hd
    obtain ⟨c₁, hleft, hmiddle₁⟩ :=
      C₁.scalar_agreement (C₂.embedding d) hd
    obtain ⟨c₂, hmiddle₂, hright⟩ :=
      C₂.scalar_agreement d hdMiddle
    obtain ⟨c, hmiddleRight, hmiddleLeft⟩ :=
      hmid.scalar_agreement d hd
    have hc₁ : c₁ = c :=
      scalarLinearEquiv_injective ℂ W
        (hmiddle₁.symm.trans hmiddleRight)
    have hc₂ : c₂ = c :=
      scalarLinearEquiv_injective ℂ W'
        (hmiddle₂.symm.trans hmiddleLeft)
    refine ⟨c, ?_, ?_⟩
    · change C₁.leftProjective.operator
          (C₁.embedding (C₂.embedding d)) =
        scalarLinearEquiv ℂ V c
      simpa only [hc₁] using hleft
    · simpa only [hc₂] using hright

/-- Compatible composable witnesses yield the corresponding existence
statement for the outer character triples. -/
theorem centrallyIsomorphicVia_trans_of_compatible
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U Z W' Y)
    (hmid : MiddleCompatibility C₁ C₂) :
    CentrallyIsomorphicVia T Z V Y :=
  ⟨C₁.compose C₂ hmid⟩

/-- The middle coherence is necessary for a direct composite retaining the
outer projective representations and the composite subgroup embedding.

Thus raw witnesses cannot in general be composed by simply forgetting their
two potentially unrelated choices of middle projective lift.
-/
theorem middleCompatibility_of_direct_composite
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U Z W' Y)
    (C₃ : CentralIsomorphismWitness T Z V Y)
    (hleft : C₃.leftProjective = C₁.leftProjective)
    (hright : C₃.rightProjective = C₂.rightProjective)
    (hembedding : C₃.embedding = C₁.compositeEmbedding C₂) :
    MiddleCompatibility C₁ C₂ := by
  constructor
  · intro d e
    have houter := C₃.factor_agreement d e
    rw [hleft, hright, hembedding] at houter
    change C₁.leftProjective.factor
        (C₁.embedding (C₂.embedding d))
        (C₁.embedding (C₂.embedding e)) =
      C₂.rightProjective.factor d e at houter
    calc
      C₁.rightProjective.factor
          (C₂.embedding d) (C₂.embedding e) =
        C₁.leftProjective.factor
          (C₁.embedding (C₂.embedding d))
          (C₁.embedding (C₂.embedding e)) :=
            (C₁.factor_agreement (C₂.embedding d) (C₂.embedding e)).symm
      _ = C₂.rightProjective.factor d e := houter
      _ = C₂.leftProjective.factor
          (C₂.embedding d) (C₂.embedding e) :=
            (C₂.factor_agreement d e).symm
  · intro d hd
    have hdMiddle :
        C₂.embedding d ∈
          Subgroup.centralizer (U.normalSubgroup : Set B) :=
      C₁.mem_rightCentralizer_of_embedding_mem_leftCentralizer hd
    obtain ⟨c₁, houter₁, hmiddleRight⟩ :=
      C₁.scalar_agreement (C₂.embedding d) hd
    obtain ⟨c₂, hmiddleLeft, houter₂⟩ :=
      C₂.scalar_agreement d hdMiddle
    have hdComposite : C₃.embedding d ∈
        Subgroup.centralizer (T.normalSubgroup : Set A) := by
      rw [hembedding]
      exact hd
    obtain ⟨c₃, houter₃, hright₃⟩ :=
      C₃.scalar_agreement d hdComposite
    have houter₃' :
        C₁.leftProjective.operator
            (C₁.embedding (C₂.embedding d)) =
          scalarLinearEquiv ℂ V c₃ := by
      rw [hleft, hembedding] at houter₃
      change C₁.leftProjective.operator
          (C₁.embedding (C₂.embedding d)) =
        scalarLinearEquiv ℂ V c₃ at houter₃
      exact houter₃
    have hright₃' :
        C₂.rightProjective.operator d =
          scalarLinearEquiv ℂ Y c₃ := by
      rw [hright] at hright₃
      exact hright₃
    have hc₁ : c₁ = c₃ :=
      scalarLinearEquiv_injective ℂ V
        (houter₁.symm.trans houter₃')
    have hc₂ : c₂ = c₃ :=
      scalarLinearEquiv_injective ℂ Y
        (houter₂.symm.trans hright₃')
    refine ⟨c₃, ?_, ?_⟩
    · simpa only [hc₁] using hmiddleRight
    · simpa only [hc₂] using hmiddleLeft

end Compatibility

section SameMiddleLift

variable {A : Type u} {B : Type v} {D : Type w}
  [Finite A] [Finite B] [Finite D] [Group A] [Group B] [Group D]
variable {T : CharacterTriple A} {U : CharacterTriple B}
  {Z : CharacterTriple D}
variable {V W Y : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]
  [AddCommGroup Y] [Module ℂ Y] [Module.Finite ℂ Y] [Nontrivial Y]

/-- Literal equality of the two chosen middle projective representations is a
sufficient source of middle compatibility. -/
theorem MiddleCompatibility.of_projective_eq
    {C₁ : CentralIsomorphismWitness T U V W}
    {C₂ : CentralIsomorphismWitness U Z W Y}
    (hP : C₁.rightProjective = C₂.leftProjective) :
    MiddleCompatibility C₁ C₂ where
  factor_agreement := by
    intro d e
    rw [hP]
  scalar_agreement := by
    intro d hd
    have hdMiddle :
        C₂.embedding d ∈
          Subgroup.centralizer (U.normalSubgroup : Set B) :=
      C₁.mem_rightCentralizer_of_embedding_mem_leftCentralizer hd
    obtain ⟨c, hc⟩ :=
      C₁.rightAssociated.operator_centralizer_isScalar
        (C₂.embedding d) hdMiddle
    refine ⟨c, hc, ?_⟩
    rw [← hP]
    exact hc

/-- Compose witnesses which use literally the same projective representation
for their common middle character triple. -/
def compose_of_projective_eq
    (C₁ : CentralIsomorphismWitness T U V W)
    (C₂ : CentralIsomorphismWitness U Z W Y)
    (hP : C₁.rightProjective = C₂.leftProjective) :
    CentralIsomorphismWitness T Z V Y :=
  C₁.compose C₂ (MiddleCompatibility.of_projective_eq hP)

end SameMiddleLift

end CentralIsomorphismWitness
end CharacterTriple
end McKayConjecture
