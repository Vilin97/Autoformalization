/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CompleteCentralIsomorphismAutomaticTransitivity
import McKayConjecture.InductiveMcKay.Condition

/-!
# The exact-normalizer form of the inductive McKay datum

The local inductive McKay condition relates a group to an intermediate
subgroup.  Iterating that condition eventually produces the exact Sylow
normalizer.  This file records the strengthened output needed to retain the
character-triple part of the condition during that iteration.

For `Γ = Aut(G)_P` and `χ ∈ Irr_{p'}(G)`, the target triple is

`(N_G(P) ⋊ Γ_χ, N_G(P), Ω(χ))`.

The action and the embedding are the literal restrictions of the ambient
ones.  Thus the datum below contains no unspecified relabelling of the final
normalizer.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple

variable {G : Type u} [Group G] {p : ℕ}

namespace PPrimeCharacterStabilizer

variable {P : Sylow p G} {χ : PPrimeIrreducibleCharacter G p}

/-- The action of the ambient character stabilizer on the exact Sylow
normalizer. -/
def normalizerAction :
    PPrimeCharacterStabilizer P χ →* MulAut (SylowNormalizer P) :=
  (SylowAutStabilizer.normalizerRestrictionHom P).comp
    (PPrimeCharacterStabilizer P χ).subtype

@[simp]
theorem normalizerAction_apply_coe
    (a : PPrimeCharacterStabilizer P χ)
    (x : SylowNormalizer P) :
    (((normalizerAction (P := P) (χ := χ) a x :
        SylowNormalizer P) : G)) =
      a.1.1 x.1 :=
  rfl

end PPrimeCharacterStabilizer

namespace EquivariantMcKayEquiv

variable {P : Sylow p G}

/-- Equivariance makes the exact-normalizer character paired with `χ`
invariant under the stabilizer `Γ_χ`. -/
theorem normalizerCharacter_invariant
    (e : EquivariantMcKayEquiv P)
    (χ : PPrimeIrreducibleCharacter G p) :
    CharacterTriple.IsInvariant
      (PPrimeCharacterStabilizer.normalizerAction
        (P := P) (χ := χ))
      (e χ).1 := by
  intro a x
  have hsource : a.1 • χ = χ :=
    MulAction.mem_stabilizer_iff.mp a.2
  have htarget : a.1 • e χ = e χ := by
    rw [← e.map_smul a.1 χ, hsource]
  have htarget' :
      (SylowAutStabilizer.normalizerRestrictionHom P a.1) •
          (e χ).1 =
        (e χ).1 :=
    congrArg Subtype.val htarget
  let r : MulAut (SylowNormalizer P) :=
    SylowAutStabilizer.normalizerRestrictionHom P a.1
  have hvalue :=
    congrArg (fun θ : IrreducibleCharacter (SylowNormalizer P) ↦
      θ.values (r x)) htarget'
  have hvalue' :
      (e χ).1.values (r.symm (r x)) =
        (e χ).1.values (r x) := by
    simpa only [IrreducibleCharacter.smul_values] using hvalue
  rw [r.symm_apply_apply] at hvalue'
  exact hvalue'.symm

/-- The exact-normalizer triple paired with the ambient triple of `χ`. -/
abbrev normalizerTriple
    [Finite G]
    (e : EquivariantMcKayEquiv P)
    (χ : PPrimeIrreducibleCharacter G p) :
    CharacterTriple
      (SylowNormalizer P ⋊[
          PPrimeCharacterStabilizer.normalizerAction]
        PPrimeCharacterStabilizer P χ) :=
  CharacterTriple.ofSemidirect
    (PPrimeCharacterStabilizer.normalizerAction
      (P := P) (χ := χ))
    (e χ).1 (e.normalizerCharacter_invariant χ)

/-- The canonical inclusion of the exact-normalizer semidirect product into
the ambient semidirect product. -/
def normalizerSemidirectEmbedding
    (e : EquivariantMcKayEquiv P)
    (χ : PPrimeIrreducibleCharacter G p) :
    (SylowNormalizer P ⋊[
        PPrimeCharacterStabilizer.normalizerAction]
      PPrimeCharacterStabilizer P χ) →*
      (G ⋊[PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer P χ) :=
  SemidirectProduct.map
    (Subgroup.normalizer (P : Set G)).subtype
    (MonoidHom.id (PPrimeCharacterStabilizer P χ)) (by
      intro a
      ext x
      rfl)

@[simp]
theorem normalizerSemidirectEmbedding_left
    (e : EquivariantMcKayEquiv P)
    (χ : PPrimeIrreducibleCharacter G p)
    (x : SylowNormalizer P ⋊[
        PPrimeCharacterStabilizer.normalizerAction]
      PPrimeCharacterStabilizer P χ) :
    (e.normalizerSemidirectEmbedding χ x).left = x.left :=
  rfl

@[simp]
theorem normalizerSemidirectEmbedding_right
    (e : EquivariantMcKayEquiv P)
    (χ : PPrimeIrreducibleCharacter G p)
    (x : SylowNormalizer P ⋊[
        PPrimeCharacterStabilizer.normalizerAction]
      PPrimeCharacterStabilizer P χ) :
    (e.normalizerSemidirectEmbedding χ x).right = x.right :=
  rfl

theorem normalizerSemidirectEmbedding_injective
    (e : EquivariantMcKayEquiv P)
    (χ : PPrimeIrreducibleCharacter G p) :
    Function.Injective (e.normalizerSemidirectEmbedding χ) := by
  intro x y hxy
  apply SemidirectProduct.ext
  · apply Subtype.ext
    simpa only [normalizerSemidirectEmbedding_left] using
      congrArg (fun z ↦ z.left) hxy
  · simpa only [normalizerSemidirectEmbedding_right] using
      congrArg (fun z ↦ z.right) hxy

/-- Full central character-triple compatibility with the exact Sylow
normalizer for one `p'`-degree character. -/
def ExactTripleCompatible
    [Finite G]
    (e : EquivariantMcKayEquiv P)
    (χ : PPrimeIrreducibleCharacter G p) : Prop :=
  ∃ (V W : Type)
    (_ : AddCommGroup V) (_ : Module ℂ V)
    (_ : Module.Finite ℂ V) (_ : Nontrivial V)
    (_ : AddCommGroup W) (_ : Module ℂ W)
    (_ : Module.Finite ℂ W) (_ : Nontrivial W),
    ∃ C : CentralIsomorphismWitness
      (EquivariantLocalCorrespondence.ambientTriple χ)
      (e.normalizerTriple χ) V W,
      C.embedding = e.normalizerSemidirectEmbedding χ

end EquivariantMcKayEquiv

/-- A fully equivariant McKay correspondence to the exact Sylow normalizer,
together with the central character-triple relation for every paired
character. -/
structure ExactNormalizerInductiveMcKayData
    [Finite G] (P : Sylow p G)
    extends EquivariantMcKayEquiv P where
  /-- Character-triple compatibility with the literal exact normalizer. -/
  triple_compatible :
    ∀ χ : PPrimeIrreducibleCharacter G p,
      toEquivariantMcKayEquiv.ExactTripleCompatible χ

namespace ExactNormalizerInductiveMcKayData

variable [Finite G] {P : Sylow p G}

/-- Forget the character-triple witnesses. -/
def toEquivariant
    (d : ExactNormalizerInductiveMcKayData P) :
    EquivariantMcKayEquiv P :=
  d.toEquivariantMcKayEquiv

/-- Forget equivariance and character triples. -/
def toMcKayCorrespondence
    (d : ExactNormalizerInductiveMcKayData P) :
    McKayCorrespondence G p P :=
  d.toEquivariantMcKayEquiv.toEquiv

end ExactNormalizerInductiveMcKayData

/-! ## Bundled witnesses in the concrete universe

The Clifford and extension-transport APIs bundle their auxiliary
representation spaces in `CompleteCentralIsomorphismWitness`.  Its ambient
groups currently live in `Type`, whereas the recursive exact-normalizer
datum is universe-polymorphic.  The following accessors bridge the two APIs
for the concrete finite groups used in Proposition 4.5 without imposing a
universe restriction on the datum itself.
-/

namespace EquivariantMcKayEquiv

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G}

/-- An exact-normalizer compatibility proposition supplies a bundled
witness whose embedding is still the canonical one. -/
theorem exists_completeExactTripleWitness
    (e : EquivariantMcKayEquiv P)
    (χ : PPrimeIrreducibleCharacter G p)
    (h : e.ExactTripleCompatible χ) :
    ∃ C :
        CompleteCentralIsomorphismWitness
          (EquivariantLocalCorrespondence.ambientTriple (P := P) χ)
          (e.normalizerTriple χ),
      C.embedding = e.normalizerSemidirectEmbedding χ := by
  obtain
    ⟨V, W, addV, moduleV, finiteV, nontrivialV,
      addW, moduleW, finiteW, nontrivialW, C, hC⟩ := h
  refine
    ⟨{ leftSpace := V
       rightSpace := W
       leftAddCommGroup := addV
       leftModule := moduleV
       leftModuleFinite := finiteV
       leftNontrivial := nontrivialV
       rightAddCommGroup := addW
       rightModule := moduleW
       rightModuleFinite := finiteW
       rightNontrivial := nontrivialW
       witness := C },
     ?_⟩
  exact hC

/-- Bundle an exact-normalizer compatibility witness, including its two
chosen representation spaces. -/
def completeExactTripleWitness
    (e : EquivariantMcKayEquiv P)
    (χ : PPrimeIrreducibleCharacter G p)
    (h : e.ExactTripleCompatible χ) :
    CompleteCentralIsomorphismWitness
      (EquivariantLocalCorrespondence.ambientTriple (P := P) χ)
      (e.normalizerTriple χ) :=
  Classical.choose (e.exists_completeExactTripleWitness χ h)

/-- The bundled witness retains the literal exact-normalizer embedding. -/
theorem completeExactTripleWitness_embedding
    (e : EquivariantMcKayEquiv P)
    (χ : PPrimeIrreducibleCharacter G p)
    (h : e.ExactTripleCompatible χ) :
    (e.completeExactTripleWitness χ h).embedding =
      e.normalizerSemidirectEmbedding χ := by
  exact
    Classical.choose_spec
      (e.exists_completeExactTripleWitness χ h)

end EquivariantMcKayEquiv

namespace ExactNormalizerInductiveMcKayData

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G}

/-- The complete central witness carried by exact-normalizer data at one
prime-to-`p` character. -/
def completeTripleWitness
    (d : ExactNormalizerInductiveMcKayData P)
    (χ : PPrimeIrreducibleCharacter G p) :
    CompleteCentralIsomorphismWitness
      (EquivariantLocalCorrespondence.ambientTriple (P := P) χ)
      (d.toEquivariant.normalizerTriple χ) :=
  d.toEquivariant.completeExactTripleWitness χ
    (d.triple_compatible χ)

@[simp]
theorem completeTripleWitness_embedding
    (d : ExactNormalizerInductiveMcKayData P)
    (χ : PPrimeIrreducibleCharacter G p) :
    (d.completeTripleWitness χ).embedding =
      d.toEquivariant.normalizerSemidirectEmbedding χ :=
  d.toEquivariant.completeExactTripleWitness_embedding χ
    (d.triple_compatible χ)

end ExactNormalizerInductiveMcKayData

end InductiveMcKay
end McKayConjecture
