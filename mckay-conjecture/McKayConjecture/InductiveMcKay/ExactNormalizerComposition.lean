/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.ExactNormalizerRecursiveStep

/-!
# Composing local and exact-normalizer character triples

The equivariant character correspondence in a normalizer-induction step is
constructed unconditionally in `ExactNormalizerRecursiveStep`.  To compose
the character-triple witnesses, the inner exact-normalizer witness must be
viewed with the outer character stabilizer and transported across the
canonical isomorphism

`N_N(P) ≃ N_G(P)`.

`RestrictedExactNormalizerCompatibility` is the precise remaining interface:
it asks only for that restricted-and-transported witness, with its literal
canonical embedding.  In particular, it does not ask for another character
equivalence, factor-set equality, scalar agreement, or coherence between the
two projective realizations of the intermediate triple.  The latter coherence
is supplied automatically by `composeAutomaticStrict`.

The generic homomorphism pullback constructor in
`CharacterTriple.CentralIsomorphismHomPullback` is intended to discharge this
interface from a concrete semidirect-product square.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple

variable {G : Type u} [Group G] [Finite G] {p : ℕ}
variable {P : Sylow p G}

namespace EquivariantLocalCorrespondence

/-- Inclusion of the ambient Sylow normalizer into an intermediate subgroup
which contains it. -/
def exactNormalizerToIntermediateHom
    (d : EquivariantLocalCorrespondence P) :
    SylowNormalizer P →* d.intermediate :=
  (Subgroup.normalizer (P : Set G)).subtype.codRestrict
    d.intermediate (fun x ↦ d.normalizer_le x.property)

@[simp]
theorem exactNormalizerToIntermediateHom_apply_coe
    (d : EquivariantLocalCorrespondence P)
    (x : SylowNormalizer P) :
    ((d.exactNormalizerToIntermediateHom x :
        d.intermediate) : G) = x.1 :=
  rfl

/-- The canonical inclusion
`N_G(P) ⋊ Γ_χ ↪ N ⋊ Γ_χ` used in the second half of a recursive
normalizer-induction step. -/
def exactNormalizerToIntermediateSemidirectEmbedding
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p) :
    (SylowNormalizer P ⋊[
        PPrimeCharacterStabilizer.normalizerAction]
      PPrimeCharacterStabilizer P χ) →*
      (d.intermediate ⋊[d.stabilizerIntermediateAction χ]
        PPrimeCharacterStabilizer P χ) :=
  SemidirectProduct.map d.exactNormalizerToIntermediateHom
    (MonoidHom.id (PPrimeCharacterStabilizer P χ)) (by
      intro a
      ext x
      rfl)

@[simp]
theorem exactNormalizerToIntermediateSemidirectEmbedding_left
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p)
    (x : SylowNormalizer P ⋊[
        PPrimeCharacterStabilizer.normalizerAction]
      PPrimeCharacterStabilizer P χ) :
    (d.exactNormalizerToIntermediateSemidirectEmbedding χ x).left =
      d.exactNormalizerToIntermediateHom x.left :=
  rfl

@[simp]
theorem exactNormalizerToIntermediateSemidirectEmbedding_right
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p)
    (x : SylowNormalizer P ⋊[
        PPrimeCharacterStabilizer.normalizerAction]
      PPrimeCharacterStabilizer P χ) :
    (d.exactNormalizerToIntermediateSemidirectEmbedding χ x).right =
      x.right :=
  rfl

theorem exactNormalizerToIntermediateSemidirectEmbedding_injective
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p) :
    Function.Injective
      (d.exactNormalizerToIntermediateSemidirectEmbedding χ) := by
  intro x y hxy
  apply SemidirectProduct.ext
  · have hleft := congrArg (fun z ↦ z.left) hxy
    apply Subtype.ext
    exact congrArg (fun z : d.intermediate ↦ (z : G)) hleft
  · exact congrArg (fun z ↦ z.right) hxy

/-- The two canonical inclusions in a recursive step compose to the
canonical inclusion of the exact normalizer into the ambient group. -/
theorem semidirectEmbedding_comp_exactNormalizerEmbedding
    (d : EquivariantLocalCorrespondence P)
    (e : EquivariantMcKayEquiv P)
    (χ : PPrimeIrreducibleCharacter G p) :
    (d.semidirectEmbedding χ).comp
        (d.exactNormalizerToIntermediateSemidirectEmbedding χ) =
      e.normalizerSemidirectEmbedding χ := by
  apply MonoidHom.ext
  intro x
  apply SemidirectProduct.ext
  · rfl
  · rfl

end EquivariantLocalCorrespondence

namespace ExactNormalizerRecursiveStep

variable
  (d : EquivariantLocalCorrespondence P)
  (e : ExactNormalizerInductiveMcKayData d.intermediateSylow)

/-- The exact semidirect-action pullback needed to retain character-triple
compatibility during one normalizer-induction step.

The endpoint character and correspondence are fixed by `d` and `e`; the only
new datum is a witness for the already determined pair of triples with the
canonical inclusion. -/
def RestrictedExactNormalizerCompatibility : Prop :=
  ∀ χ : PPrimeIrreducibleCharacter G p,
    ∃ (V W : Type)
      (_ : AddCommGroup V) (_ : Module ℂ V)
      (_ : Module.Finite ℂ V) (_ : Nontrivial V)
      (_ : AddCommGroup W) (_ : Module ℂ W)
      (_ : Module.Finite ℂ W) (_ : Nontrivial W),
      ∃ C : CentralIsomorphismWitness
        (d.intermediateTriple χ)
        ((equivariantEquiv d e).normalizerTriple χ) V W,
        C.embedding =
          d.exactNormalizerToIntermediateSemidirectEmbedding χ

end ExactNormalizerRecursiveStep

namespace LocalInductiveMcKayData

/-- A local inductive-McKay datum and exact-normalizer data inside its
intermediate subgroup compose to exact-normalizer data, once the inner
witness has been pulled back to the outer stabilizer.

No compatibility hypothesis between the two chosen projective
representations of the middle triple is required. -/
def composeExactNormalizer
    (d : LocalInductiveMcKayData P)
    (e : ExactNormalizerInductiveMcKayData
      d.toEquivariant.intermediateSylow)
    (h :
      ExactNormalizerRecursiveStep.RestrictedExactNormalizerCompatibility
        d.toEquivariant e) :
    ExactNormalizerInductiveMcKayData P where
  toEquivariantMcKayEquiv :=
    ExactNormalizerRecursiveStep.equivariantEquiv d.toEquivariant e
  triple_compatible := by
    intro χ
    obtain
      ⟨V₁, W₁, addV₁, moduleV₁, finiteV₁, nontrivialV₁,
        addW₁, moduleW₁, finiteW₁, nontrivialW₁, C₁, hC₁⟩ :=
      d.triple_compatible χ
    obtain
      ⟨V₂, W₂, addV₂, moduleV₂, finiteV₂, nontrivialV₂,
        addW₂, moduleW₂, finiteW₂, nontrivialW₂, C₂, hC₂⟩ :=
      h χ
    change
      CentralIsomorphismWitness
        (d.intermediateTriple χ)
        ((ExactNormalizerRecursiveStep.equivariantEquiv
          d.toEquivariant e).normalizerTriple χ) V₂ W₂
      at C₂
    letI : AddCommGroup V₁ := addV₁
    letI : Module ℂ V₁ := moduleV₁
    letI : Module.Finite ℂ V₁ := finiteV₁
    letI : Nontrivial V₁ := nontrivialV₁
    letI : AddCommGroup W₁ := addW₁
    letI : Module ℂ W₁ := moduleW₁
    letI : Module.Finite ℂ W₁ := finiteW₁
    letI : Nontrivial W₁ := nontrivialW₁
    letI : AddCommGroup V₂ := addV₂
    letI : Module ℂ V₂ := moduleV₂
    letI : Module.Finite ℂ V₂ := finiteV₂
    letI : Nontrivial V₂ := nontrivialV₂
    letI : AddCommGroup W₂ := addW₂
    letI : Module ℂ W₂ := moduleW₂
    letI : Module.Finite ℂ W₂ := finiteW₂
    letI : Nontrivial W₂ := nontrivialW₂
    refine
      ⟨V₁, W₂, inferInstance, inferInstance, inferInstance,
        inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, C₁.composeAutomaticStrict C₂, ?_⟩
    rw [CentralIsomorphismWitness.composeAutomaticStrict_embedding,
      hC₁, hC₂]
    exact
      d.toEquivariant.semidirectEmbedding_comp_exactNormalizerEmbedding
        (ExactNormalizerRecursiveStep.equivariantEquiv
          d.toEquivariant e) χ

end LocalInductiveMcKayData

end InductiveMcKay
end McKayConjecture
