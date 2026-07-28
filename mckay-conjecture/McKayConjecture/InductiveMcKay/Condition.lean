/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.SemidirectProduct
import McKayConjecture.Character.Inertia
import McKayConjecture.CharacterTriple.Semidirect
import McKayConjecture.InductiveMcKay.EquivariantLocal

/-!
# The inductive McKay condition

This file packages the full local condition used by the reduction theorem.
For `Γ = Aut(G)_P`, an equivariant local correspondence `Ω` must satisfy,
for every `χ ∈ Irr_{p'}(G)`, the central character-triple relation

`(G ⋊ Γ_χ, G, χ) ≥c (N ⋊ Γ_χ, N, Ω(χ))`.

Unlike the numerical and equivariant-numerical interfaces, the definition
below records the actual semidirect products, the stabilizer action, the
canonical embedding of the right semidirect product, and the complete
projective-representation witness.
-/

noncomputable section

universe u

namespace McKayConjecture.InductiveMcKay

open McKayConjecture.CharacterTriple

variable {G : Type u} [Group G] {p : ℕ}

/-- The stabilizer `Γ_χ` of a `p'`-degree character inside `Γ = Aut(G)_P`. -/
abbrev PPrimeCharacterStabilizer (P : Sylow p G)
    (χ : PPrimeIrreducibleCharacter G p) :
    Subgroup (SylowAutStabilizer P) :=
  MulAction.stabilizer (SylowAutStabilizer P) χ

namespace PPrimeCharacterStabilizer

variable {P : Sylow p G} {χ : PPrimeIrreducibleCharacter G p}

@[simp]
theorem mem_iff (a : SylowAutStabilizer P) :
    a ∈ PPrimeCharacterStabilizer P χ ↔ a • χ = χ :=
  MulAction.mem_stabilizer_iff

/-- The action of `Γ_χ` on the ambient group `G`. -/
def ambientAction :
    PPrimeCharacterStabilizer P χ →* MulAut G :=
  (SylowAutStabilizer P).subtype.comp
    (PPrimeCharacterStabilizer P χ).subtype

@[simp]
theorem ambientAction_apply
    (a : PPrimeCharacterStabilizer P χ) (g : G) :
    ambientAction a g = a.1.1 g :=
  rfl

/-- By definition of the stabilizer, `χ` is invariant under its action on
`G`; this is the input needed for the left semidirect character triple. -/
theorem character_invariant :
    CharacterTriple.IsInvariant
      (ambientAction (P := P) (χ := χ)) χ.1 := by
  intro a g
  have hfix : a.1 • χ = χ :=
    (MulAction.mem_stabilizer_iff.mp a.2)
  have hfix' : a.1.1 • χ.1 = χ.1 := by
    exact congrArg Subtype.val hfix
  have hvalue :=
    congrArg (fun θ : IrreducibleCharacter G ↦
      θ.values (ambientAction (P := P) (χ := χ) a g)) hfix'
  simpa only [IrreducibleCharacter.smul_values,
    ambientAction_apply, MulEquiv.symm_apply_apply] using hvalue.symm

end PPrimeCharacterStabilizer

namespace EquivariantLocalCorrespondence

variable {P : Sylow p G}

/-- The local character paired with `χ`. -/
abbrev localCharacter (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p) :
    PPrimeIrreducibleCharacter d.intermediate p :=
  d.correspondence χ

/-- Restrict the action of `Γ_χ` to the invariant intermediate subgroup
chosen by the local datum. -/
def stabilizerIntermediateAction
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p) :
    PPrimeCharacterStabilizer P χ →* MulAut d.intermediate :=
  (SylowAutStabilizer.intermediateRestrictionHom
      P d.intermediate d.intermediate_invariant).comp
    (PPrimeCharacterStabilizer P χ).subtype

@[simp]
theorem stabilizerIntermediateAction_apply_coe
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p)
    (a : PPrimeCharacterStabilizer P χ) (n : d.intermediate) :
    ((stabilizerIntermediateAction d χ a n : d.intermediate) : G) =
      a.1.1 n.1 :=
  rfl

/-- Equivariance of `Ω` makes `Ω(χ)` invariant under `Γ_χ`. -/
theorem localCharacter_invariant
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p) :
    CharacterTriple.IsInvariant
      (stabilizerIntermediateAction d χ) (d.localCharacter χ).1 := by
  letI := d.intermediateCharacterMulAction
  intro a n
  have hsource : a.1 • χ = χ :=
    MulAction.mem_stabilizer_iff.mp a.2
  have htarget :
      a.1 • d.localCharacter χ = d.localCharacter χ := by
    rw [← d.map_smul a.1 χ, hsource]
  have htarget' :
      (SylowAutStabilizer.intermediateRestrictionHom
          P d.intermediate d.intermediate_invariant a.1) •
          (d.localCharacter χ).1 =
        (d.localCharacter χ).1 :=
    congrArg Subtype.val htarget
  let r : MulAut d.intermediate :=
    SylowAutStabilizer.intermediateRestrictionHom
      P d.intermediate d.intermediate_invariant a.1
  have hvalue :=
    congrArg (fun θ : IrreducibleCharacter d.intermediate ↦
      θ.values (r n)) htarget'
  have hvalue' :
      (d.localCharacter χ).1.values (r.symm (r n)) =
        (d.localCharacter χ).1.values (r n) := by
    simpa only [IrreducibleCharacter.smul_values] using hvalue
  rw [r.symm_apply_apply] at hvalue'
  change
    (d.localCharacter χ).1.values (r n) =
      (d.localCharacter χ).1.values n
  exact hvalue'.symm

/-- The left character triple `(G ⋊ Γ_χ, G, χ)`. -/
abbrev ambientTriple
    [Finite G] (χ : PPrimeIrreducibleCharacter G p) :
    CharacterTriple
      (G ⋊[PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer P χ) :=
  CharacterTriple.ofSemidirect
    PPrimeCharacterStabilizer.ambientAction χ.1
      PPrimeCharacterStabilizer.character_invariant

/-- The right character triple `(N ⋊ Γ_χ, N, Ω(χ))`. -/
abbrev intermediateTriple
    [Finite G]
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p) :
    CharacterTriple
      (d.intermediate ⋊[stabilizerIntermediateAction d χ]
        PPrimeCharacterStabilizer P χ) :=
  CharacterTriple.ofSemidirect
    (stabilizerIntermediateAction d χ) (d.localCharacter χ).1
      (d.localCharacter_invariant χ)

/-- The canonical embedding
`N ⋊ Γ_χ ↪ G ⋊ Γ_χ` occurring in the inductive McKay condition. -/
def semidirectEmbedding
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p) :
    (d.intermediate ⋊[stabilizerIntermediateAction d χ]
      PPrimeCharacterStabilizer P χ) →*
      (G ⋊[PPrimeCharacterStabilizer.ambientAction]
        PPrimeCharacterStabilizer P χ) :=
  SemidirectProduct.map d.intermediate.subtype
    (MonoidHom.id (PPrimeCharacterStabilizer P χ)) (by
      intro a
      ext n
      rfl)

@[simp]
theorem semidirectEmbedding_left
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p)
    (a : d.intermediate ⋊[stabilizerIntermediateAction d χ]
      PPrimeCharacterStabilizer P χ) :
    (semidirectEmbedding d χ a).left = a.left :=
  rfl

@[simp]
theorem semidirectEmbedding_right
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p)
    (a : d.intermediate ⋊[stabilizerIntermediateAction d χ]
      PPrimeCharacterStabilizer P χ) :
    (semidirectEmbedding d χ a).right = a.right :=
  rfl

theorem semidirectEmbedding_injective
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p) :
    Function.Injective (semidirectEmbedding d χ) := by
  intro a b hab
  apply SemidirectProduct.ext
  · apply Subtype.ext
    simpa only [semidirectEmbedding_left] using
      congrArg (fun z ↦ z.left) hab
  · simpa only [semidirectEmbedding_right] using
      congrArg (fun z ↦ z.right) hab

/-- Full character-triple compatibility for one paired character.

The finite-dimensional spaces are existentially quantified.  The final
equality ensures that the abstract embedding stored by the central
isomorphism witness is exactly the canonical inclusion
`N ⋊ Γ_χ ↪ G ⋊ Γ_χ`.
-/
def TripleCompatible
    [Finite G]
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter G p) : Prop :=
  ∃ (V W : Type)
    (_ : AddCommGroup V) (_ : Module ℂ V)
    (_ : Module.Finite ℂ V) (_ : Nontrivial V)
    (_ : AddCommGroup W) (_ : Module ℂ W)
    (_ : Module.Finite ℂ W) (_ : Nontrivial W),
    ∃ C : CharacterTriple.CentralIsomorphismWitness
      (ambientTriple χ) (d.intermediateTriple χ) V W,
      C.embedding = semidirectEmbedding d χ

end EquivariantLocalCorrespondence

/-- A full local datum for the inductive McKay condition: the equivariant
local correspondence together with central character-triple compatibility
for every character in its domain. -/
structure LocalInductiveMcKayData [Finite G] (P : Sylow p G)
    extends EquivariantLocalCorrespondence P where
  /-- Part (b) of the inductive McKay condition. -/
  triple_compatible :
    ∀ χ : PPrimeIrreducibleCharacter G p,
      toEquivariantLocalCorrespondence.TripleCompatible χ

namespace LocalInductiveMcKayData

variable [Finite G] {P : Sylow p G}

/-- Forget the character-triple witnesses. -/
def toEquivariant
    (d : LocalInductiveMcKayData P) :
    EquivariantLocalCorrespondence P :=
  d.toEquivariantLocalCorrespondence

/-- Forget all but the numerical local datum. -/
def toLocal
    (d : LocalInductiveMcKayData P) :
    LocalCorrespondence P :=
  d.toEquivariantLocalCorrespondence.toLocalCorrespondence

end LocalInductiveMcKayData

/-- The inductive McKay condition at `p`, uniformly for every finite group
in the universe. -/
def InductiveMcKayCondition (p : ℕ) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (P : Sylow p G),
    Nonempty (LocalInductiveMcKayData P)

namespace InductiveMcKayCondition

/-- The full condition implies its equivariant numerical part. -/
theorem toEquivariantNumerical
    (h : InductiveMcKayCondition.{u} p) :
    EquivariantNumericalInductiveMcKay.{u} p := by
  intro G _ _ P
  obtain ⟨d⟩ := h G P
  exact ⟨d.toEquivariant⟩

/-- The full condition implies the numerical condition used by normalizer
induction. -/
theorem toNumerical
    (h : InductiveMcKayCondition.{u} p) :
    NumericalInductiveMcKay.{u} p :=
  h.toEquivariantNumerical.toNumerical

/-- The formalized elementary reduction: the full inductive McKay condition
produces an explicit McKay correspondence. -/
def correspondence
    (h : InductiveMcKayCondition.{u} p)
    (G : Type u) [Group G] [Finite G] (P : Sylow p G) :
    McKayCorrespondence G p P :=
  h.toNumerical.correspondence G P

/-- Consequently, the inductive McKay condition implies the cardinal
statement of the McKay conjecture. -/
theorem statement [Fact p.Prime]
    (h : InductiveMcKayCondition.{u} p)
    (G : Type u) [Group G] [Finite G] (P : Sylow p G) :
    Statement G p P :=
  h.toNumerical.statement G P

end InductiveMcKayCondition

end McKayConjecture.InductiveMcKay
