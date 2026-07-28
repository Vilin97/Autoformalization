/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.Condition

/-!
# Structural conditions for the inductive-McKay semidirect products

For the canonical inclusion

`N ⋊ Γ_χ ↪ G ⋊ Γ_χ`,

the three group-theoretic clauses in a central character-triple
isomorphism are automatic from `N_G(P) ≤ N`.  This file proves the most
delicate clause: the centralizer of the canonical copy of `G` lies in
the image of the local semidirect product.
-/

noncomputable section

universe u

namespace McKayConjecture.InductiveMcKay

open McKayConjecture.CharacterTriple

variable {G : Type u} [Group G] {p : ℕ}

namespace EquivariantLocalCorrespondence

variable {P : Sylow p G}

private theorem automorphism_mem_iff
    (a : SylowAutStabilizer P) (g : G) :
    a.1 g ∈ (P : Subgroup G) ↔ g ∈ (P : Subgroup G) := by
  constructor
  · intro hg
    have hginv :
        a.1.symm (a.1 g) ∈
          (P : Subgroup G).map (a⁻¹).1 := by
      exact Subgroup.mem_map.mpr ⟨a.1 g, hg, by simp⟩
    have hmap := SylowAutStabilizer.map_sylow_eq (a⁻¹)
    rw [hmap] at hginv
    simpa using hginv
  · intro hg
    have hga :
        a.1 g ∈ (P : Subgroup G).map (a.1 : G →* G) :=
      Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
    rw [SylowAutStabilizer.map_sylow_eq a] at hga
    exact hga

/-- If an element `(g,a)` of `G ⋊ Γ_χ` centralizes the canonical copy of
`G`, then `g` normalizes `P`.

Indeed centrality gives `a(x) = g⁻¹xg`; since `a` stabilizes `P`, inner
conjugation by `g` stabilizes `P` as well.
-/
theorem left_mem_normalizer_of_mem_centralizer
    [Finite G]
    (χ : PPrimeIrreducibleCharacter G p)
    (z :
      G ⋊[PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer P χ)
    (hz :
      z ∈ Subgroup.centralizer
        ((ambientTriple (P := P) χ).normalSubgroup :
          Set
            (G ⋊[PPrimeCharacterStabilizer.ambientAction]
              PPrimeCharacterStabilizer P χ))) :
    z.left ∈ Subgroup.normalizer (P : Subgroup G) := by
  rw [Subgroup.mem_normalizer_iff'']
  intro g
  let a : SylowAutStabilizer P := z.right.1
  have hcomm :=
    (Subgroup.mem_centralizer_iff.mp hz)
      (SemidirectProduct.inl g)
      (show SemidirectProduct.inl g ∈
          (ambientTriple (P := P) χ).normalSubgroup from
        ⟨g, rfl⟩)
  have hleft := congrArg SemidirectProduct.left hcomm
  have hleft' :
      g * z.left = z.left * a.1 g := by
    simpa using hleft
  have ha_eq :
      a.1 g = z.left⁻¹ * g * z.left := by
    calc
      a.1 g = z.left⁻¹ * (z.left * a.1 g) := by simp
      _ = z.left⁻¹ * (g * z.left) := by
        rw [hleft']
      _ = z.left⁻¹ * g * z.left := by
        rw [mul_assoc]
  rw [← ha_eq]
  exact (automorphism_mem_iff a g).symm

/-- The centralizer clause `C_A(G) ≤ N ⋊ Γ_χ` for the canonical
semidirect embedding. -/
theorem centralizer_le_semidirectEmbedding_range
    [Finite G]
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p) :
    Subgroup.centralizer
        ((ambientTriple (P := P) χ).normalSubgroup :
          Set
            (G ⋊[PPrimeCharacterStabilizer.ambientAction]
              PPrimeCharacterStabilizer P χ)) ≤
      MonoidHom.range (d.semidirectEmbedding χ) := by
  intro z hz
  have hz_normalizer :
      z.left ∈ Subgroup.normalizer (P : Subgroup G) :=
    left_mem_normalizer_of_mem_centralizer χ z hz
  have hz_intermediate : z.left ∈ d.intermediate :=
    d.normalizer_le hz_normalizer
  let n : d.intermediate := ⟨z.left, hz_intermediate⟩
  let h :
      d.intermediate ⋊[d.stabilizerIntermediateAction χ]
        PPrimeCharacterStabilizer P χ :=
    ⟨n, z.right⟩
  exact ⟨h, by
    apply SemidirectProduct.ext
    · rfl
    · rfl⟩

/-- Every element of the ambient semidirect product is a product of an
element in the canonical copy of `G` and an element in the embedded local
semidirect product. -/
theorem ambient_eq_normal_mul_semidirectEmbedding
    [Finite G]
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p)
    (a :
      G ⋊[PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer P χ) :
    ∃ x : (ambientTriple (P := P) χ).normalSubgroup,
      ∃ h :
        d.intermediate ⋊[d.stabilizerIntermediateAction χ]
          PPrimeCharacterStabilizer P χ,
        (x :
          G ⋊[PPrimeCharacterStabilizer.ambientAction]
            PPrimeCharacterStabilizer P χ) *
            d.semidirectEmbedding χ h = a := by
  let x : (ambientTriple (P := P) χ).normalSubgroup :=
    ⟨SemidirectProduct.inl a.left, ⟨a.left, rfl⟩⟩
  let h :
      d.intermediate ⋊[d.stabilizerIntermediateAction χ]
        PPrimeCharacterStabilizer P χ :=
    ⟨1, a.right⟩
  exact ⟨x, h, by
    apply SemidirectProduct.ext
    · simp [x, h]
    · simp [x, h]⟩

/-- The canonical intersection identity
`G ∩ (N ⋊ Γ_χ) = N` inside `G ⋊ Γ_χ`. -/
theorem normal_inf_embedding_range
    [Finite G]
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p) :
    (ambientTriple (P := P) χ).normalSubgroup ⊓
        MonoidHom.range (d.semidirectEmbedding χ) =
      (d.intermediateTriple χ).normalSubgroup.map
        (d.semidirectEmbedding χ) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨h, hh⟩ := hz.2
    have hzright : z.right = 1 := by
      obtain ⟨g, hg⟩ := hz.1
      rw [← hg]
      rfl
    have hright : h.right = 1 := by
      rw [← d.semidirectEmbedding_right χ h, hh]
      exact hzright
    refine ⟨h, ?_, hh⟩
    exact ⟨h.left, by
      apply SemidirectProduct.ext
      · rfl
      · exact hright.symm⟩
  · intro z hz
    obtain ⟨h, hh, rfl⟩ := hz
    constructor
    · obtain ⟨n, hn⟩ := hh
      refine ⟨(n : G), ?_⟩
      rw [← hn]
      apply SemidirectProduct.ext
      · rfl
      · rfl
    · exact ⟨h, rfl⟩

/-- The genuinely representation-theoretic part of central
character-triple compatibility.

The ambient-product, intersection, embedding-injectivity, and centralizer
clauses have been removed: the preceding theorems show that they follow
automatically from the local subgroup conditions. -/
structure ProjectiveCompatibilityWitness
    [Finite G]
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p)
    (V W : Type)
    [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
    [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W] where
  /-- Associated projective representation on the ambient semidirect
  product. -/
  leftProjective :
    ProjectiveRepresentation ℂ
      (G ⋊[PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer P χ) V
  /-- It is associated with `(G ⋊ Γ_χ,G,χ)`. -/
  leftAssociated :
    AssociatedProjectiveRepresentation
      (ambientTriple (P := P) χ) V leftProjective
  /-- Associated projective representation on the local semidirect
  product. -/
  rightProjective :
    ProjectiveRepresentation ℂ
      (d.intermediate ⋊[d.stabilizerIntermediateAction χ]
        PPrimeCharacterStabilizer P χ) W
  /-- It is associated with `(N ⋊ Γ_χ,N,Ω(χ))`. -/
  rightAssociated :
    AssociatedProjectiveRepresentation
      (d.intermediateTriple χ) W rightProjective
  /-- Equality of factor sets along the canonical embedding. -/
  factorAgreement :
    ∀ h k :
      d.intermediate ⋊[d.stabilizerIntermediateAction χ]
        PPrimeCharacterStabilizer P χ,
      leftProjective.factor
          (d.semidirectEmbedding χ h)
          (d.semidirectEmbedding χ k) =
        rightProjective.factor h k
  /-- Equality of scalar matrices on the ambient centralizer. -/
  scalarAgreement :
    ∀ h :
      d.intermediate ⋊[d.stabilizerIntermediateAction χ]
        PPrimeCharacterStabilizer P χ,
      d.semidirectEmbedding χ h ∈
          Subgroup.centralizer
            ((ambientTriple (P := P) χ).normalSubgroup :
              Set
                (G ⋊[PPrimeCharacterStabilizer.ambientAction]
                  PPrimeCharacterStabilizer P χ)) →
        ∃ c : ℂˣ,
          leftProjective.operator (d.semidirectEmbedding χ h) =
              scalarLinearEquiv ℂ V c ∧
            rightProjective.operator h =
              scalarLinearEquiv ℂ W c

namespace ProjectiveCompatibilityWitness

variable [Finite G]
variable
  {d : EquivariantLocalCorrespondence P}
  {χ : PPrimeIrreducibleCharacter G p}
  {V W : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]

/-- Add the automatic group-theoretic fields to obtain the exact central
isomorphism witness. -/
def toCentralIsomorphismWitness
    (C : ProjectiveCompatibilityWitness d χ V W) :
    CentralIsomorphismWitness
      (ambientTriple (P := P) χ) (d.intermediateTriple χ) V W where
  leftProjective := C.leftProjective
  leftAssociated := C.leftAssociated
  rightProjective := C.rightProjective
  rightAssociated := C.rightAssociated
  embedding := d.semidirectEmbedding χ
  embedding_injective := d.semidirectEmbedding_injective χ
  centralizer_le := d.centralizer_le_semidirectEmbedding_range χ
  ambient_eq_product :=
    d.ambient_eq_normal_mul_semidirectEmbedding χ
  intersection_eq :=
    d.normal_inf_embedding_range χ
  factor_agreement := C.factorAgreement
  scalar_agreement := C.scalarAgreement

/-- Projective compatibility proves the full compatibility predicate in
the inductive McKay condition. -/
theorem tripleCompatible
    (C : ProjectiveCompatibilityWitness d χ V W) :
    d.TripleCompatible χ := by
  refine ⟨V, W, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, C.toCentralIsomorphismWitness, rfl⟩

end ProjectiveCompatibilityWitness

/-- Existential form of the reduced projective-compatibility data. -/
def ProjectivelyCompatible
    [Finite G]
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p) : Prop :=
  ∃ (V W : Type)
    (_ : AddCommGroup V) (_ : Module ℂ V)
    (_ : Module.Finite ℂ V) (_ : Nontrivial V)
    (_ : AddCommGroup W) (_ : Module ℂ W)
    (_ : Module.Finite ℂ W) (_ : Nontrivial W),
    Nonempty (ProjectiveCompatibilityWitness d χ V W)

/-- The reduced projective predicate is exactly equivalent to the complete
central character-triple predicate. -/
theorem projectivelyCompatible_iff_tripleCompatible
    [Finite G]
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p) :
    d.ProjectivelyCompatible χ ↔ d.TripleCompatible χ := by
  constructor
  · rintro ⟨V, W, _, _, _, _, _, _, _, _, ⟨C⟩⟩
    exact C.tripleCompatible
  · rintro ⟨V, W, _, _, _, _, _, _, _, _, C, hC⟩
    refine ⟨V, W, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, ?_⟩
    refine ⟨{
      leftProjective := C.leftProjective
      leftAssociated := C.leftAssociated
      rightProjective := C.rightProjective
      rightAssociated := C.rightAssociated
      factorAgreement := by
        intro h k
        rw [← hC]
        exact C.factor_agreement h k
      scalarAgreement := by
        intro h hh
        rw [← hC] at hh ⊢
        exact C.scalar_agreement h hh
    }⟩

end EquivariantLocalCorrespondence
end McKayConjecture.InductiveMcKay
