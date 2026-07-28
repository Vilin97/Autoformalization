/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralProduct
import McKayConjecture.CharacterTriple.ProjectiveQuotientDescent
import McKayConjecture.InductiveMcKay.CentralTripleCliffordAssembly
import McKayConjecture.InductiveMcKay.Condition
import McKayConjecture.InductiveMcKay.LayerComponentCorrespondence

/-!
# Central-triple data supplied by the layer components

This file isolates the exact central-triple information supplied by the
componentwise inductive McKay condition.

The bundled complete witnesses are closed under products, arbitrary
relabelling, and transport from internal central-product images to their
canonical quotient presentations.  For a character of the layer, the local
inductive McKay datum therefore gives a canonical complete witness at every
component coordinate.

There are two genuinely additional steps between these coordinate witnesses
and a witness for a layer inertia triple:

* coordinate stabilizers must be assembled while the ambient normalizer
  permutes the components; and
* the resulting chosen projective representations must be shown to descend
  through the kernel of component multiplication.

The ordinary-character kernel compatibility used by the layer character
correspondence does not imply the latter projective compatibility.  The
`CompleteCentralProductImageWitness` structure below records the strongest
currently supported quotient boundary: once a complete witness has been
constructed on the two *internal images*, transport to the canonical quotient
presentations is automatic.
-/

noncomputable section

open scoped TensorProduct

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple
open GroupTheory

variable {A B V W : Type}
  [Group A] [Finite A] [Group B] [Finite B]
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]
  {T : CharacterTriple A} {U : CharacterTriple B}

/-- Exact projective-lift hypotheses needed to descend the two chosen
projective representations in a central-isomorphism witness through specified
normal kernels.  This is stronger than scalar compatibility of the ordinary
characters: both chosen operators must be the identity on the kernel, and
both factor sets must be one whenever either input lies in the kernel. -/
structure CentralWitnessProjectiveQuotientCompatibility
    (C : CentralIsomorphismWitness T U V W)
    (N : Subgroup A) (M : Subgroup B) : Prop where
  /-- Exact quotient compatibility on the ambient side. -/
  left :
    C.leftProjective.IsQuotientCompatible N
  /-- Exact quotient compatibility on the local side. -/
  right :
    C.rightProjective.IsQuotientCompatible M

namespace CompleteCentralIsomorphismWitness

variable {A : Type} {B : Type}
  [Group A] [Finite A] [Group B] [Finite B]
  {T : CharacterTriple A} {U : CharacterTriple B}

/-- Relabel both ambient groups of a bundled complete central-isomorphism
witness. -/
def comap
    (C : CompleteCentralIsomorphismWitness T U)
    {A' : Type} {B' : Type}
    [Group A'] [Finite A'] [Group B'] [Finite B']
    (eA : A' ≃* A) (eB : B' ≃* B) :
    CompleteCentralIsomorphismWitness (T.comap eA) (U.comap eB) := by
  letI := C.leftAddCommGroup
  letI := C.leftModule
  letI := C.leftModuleFinite
  letI := C.leftNontrivial
  letI := C.rightAddCommGroup
  letI := C.rightModule
  letI := C.rightModuleFinite
  letI := C.rightNontrivial
  exact
    { leftSpace := C.leftSpace
      rightSpace := C.rightSpace
      witness := C.witness.comap eA eB }

/-- Exact quotient compatibility of both projective lifts hidden inside a
bundled complete witness. -/
def HasProjectiveQuotientCompatibility
    (C : CompleteCentralIsomorphismWitness T U)
    (N : Subgroup A) (M : Subgroup B) : Prop := by
  letI := C.leftAddCommGroup
  letI := C.leftModule
  letI := C.leftModuleFinite
  letI := C.leftNontrivial
  letI := C.rightAddCommGroup
  letI := C.rightModule
  letI := C.rightModuleFinite
  letI := C.rightNontrivial
  exact CentralWitnessProjectiveQuotientCompatibility C.witness N M

variable {A₁ : Type} {B₁ : Type} {A₂ : Type} {B₂ : Type}
  [Group A₁] [Finite A₁] [Group B₁] [Finite B₁]
  [Group A₂] [Finite A₂] [Group B₂] [Finite B₂]
  {T₁ : CharacterTriple A₁} {U₁ : CharacterTriple B₁}
  {T₂ : CharacterTriple A₂} {U₂ : CharacterTriple B₂}

/-- Tensor two bundled complete central-isomorphism witnesses.  In particular,
all finite-dimensional representation-space data remain bundled in the
result. -/
def prod
    (C : CompleteCentralIsomorphismWitness T₁ U₁)
    (D : CompleteCentralIsomorphismWitness T₂ U₂) :
    CompleteCentralIsomorphismWitness (T₁.prod T₂) (U₁.prod U₂) := by
  letI := C.leftAddCommGroup
  letI := C.leftModule
  letI := C.leftModuleFinite
  letI := C.leftNontrivial
  letI := C.rightAddCommGroup
  letI := C.rightModule
  letI := C.rightModuleFinite
  letI := C.rightNontrivial
  letI := D.leftAddCommGroup
  letI := D.leftModule
  letI := D.leftModuleFinite
  letI := D.leftNontrivial
  letI := D.rightAddCommGroup
  letI := D.rightModule
  letI := D.rightModuleFinite
  letI := D.rightNontrivial
  have hleft :
      0 < Module.finrank ℂ (C.leftSpace ⊗[ℂ] D.leftSpace) := by
    rw [Module.finrank_tensorProduct]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos
  have hright :
      0 < Module.finrank ℂ (C.rightSpace ⊗[ℂ] D.rightSpace) := by
    rw [Module.finrank_tensorProduct]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos
  letI : Nontrivial (C.leftSpace ⊗[ℂ] D.leftSpace) :=
    Module.nontrivial_of_finrank_pos hleft
  letI : Nontrivial (C.rightSpace ⊗[ℂ] D.rightSpace) :=
    Module.nontrivial_of_finrank_pos hright
  exact
    { leftSpace := C.leftSpace ⊗[ℂ] D.leftSpace
      rightSpace := C.rightSpace ⊗[ℂ] D.rightSpace
      witness := C.witness.prod D.witness }

/-- Form a product of complete witnesses and independently relabel its two
ambient product groups. -/
def prodComap
    (C : CompleteCentralIsomorphismWitness T₁ U₁)
    (D : CompleteCentralIsomorphismWitness T₂ U₂)
    {A' B' : Type} [Group A'] [Finite A'] [Group B'] [Finite B']
    (eA : A' ≃* A₁ × A₂) (eB : B' ≃* B₁ × B₂) :
    CompleteCentralIsomorphismWitness
      ((T₁.prod T₂).comap eA) ((U₁.prod U₂).comap eB) :=
  (C.prod D).comap eA eB

variable {G : Type} {H : Type}
  [Group G] [Finite G] [Group H] [Finite H]

/-- Transport a bundled witness on two internal central-product images to the
canonical quotient presentations of those images. -/
def centralProductQuotientComap
    (P : InternalCentralProduct G) (Q : InternalCentralProduct H)
    {S : CharacterTriple P.subgroup}
    {V : CharacterTriple Q.subgroup}
    (C : CompleteCentralIsomorphismWitness S V) :
    CompleteCentralIsomorphismWitness
      (S.comap P.quotientEquiv) (V.comap Q.quotientEquiv) :=
  C.comap P.quotientEquiv Q.quotientEquiv

end CompleteCentralIsomorphismWitness

/-- A complete local central-triple witness together with the assertion that
its abstract embedding is the canonical semidirect-product inclusion. -/
structure CompleteLocalTripleWitness
    {K : Type} [Group K] [Finite K] {p : ℕ}
    {P : Sylow p K}
    (d : EquivariantLocalCorrespondence P)
    (χ : PPrimeIrreducibleCharacter K p) where
  /-- Representation space on the ambient side. -/
  leftSpace : Type
  /-- Representation space on the intermediate side. -/
  rightSpace : Type
  [leftAddCommGroup : AddCommGroup leftSpace]
  [leftModule : Module ℂ leftSpace]
  [leftModuleFinite : Module.Finite ℂ leftSpace]
  [leftNontrivial : Nontrivial leftSpace]
  [rightAddCommGroup : AddCommGroup rightSpace]
  [rightModule : Module ℂ rightSpace]
  [rightModuleFinite : Module.Finite ℂ rightSpace]
  [rightNontrivial : Nontrivial rightSpace]
  /-- The central-isomorphism witness on the chosen spaces. -/
  witness :
    CentralIsomorphismWitness
      (EquivariantLocalCorrespondence.ambientTriple χ)
      (d.intermediateTriple χ) leftSpace rightSpace
  /-- Identification of its embedding with the canonical local inclusion. -/
  embedding_eq :
    witness.embedding = d.semidirectEmbedding χ

namespace CompleteLocalTripleWitness

variable {K : Type} [Group K] [Finite K] {p : ℕ}
  {P : Sylow p K} {d : EquivariantLocalCorrespondence P}
  {χ : PPrimeIrreducibleCharacter K p}

/-- Forget the identification of the embedding, retaining a fully bundled
central-isomorphism witness. -/
def complete (C : CompleteLocalTripleWitness d χ) :
    CompleteCentralIsomorphismWitness
      (EquivariantLocalCorrespondence.ambientTriple (P := P) χ)
      (d.intermediateTriple χ) := by
  letI := C.leftAddCommGroup
  letI := C.leftModule
  letI := C.leftModuleFinite
  letI := C.leftNontrivial
  letI := C.rightAddCommGroup
  letI := C.rightModule
  letI := C.rightModuleFinite
  letI := C.rightNontrivial
  exact
    { leftSpace := C.leftSpace
      rightSpace := C.rightSpace
      witness := C.witness }

/-- Predicate form of the canonical-embedding assertion.  This accessor
installs the representation-space instances bundled in `C`. -/
def HasCanonicalEmbedding (C : CompleteLocalTripleWitness d χ) : Prop := by
  letI := C.leftAddCommGroup
  letI := C.leftModule
  letI := C.leftModuleFinite
  letI := C.leftNontrivial
  letI := C.rightAddCommGroup
  letI := C.rightModule
  letI := C.rightModuleFinite
  letI := C.rightNontrivial
  exact C.witness.embedding = d.semidirectEmbedding χ

theorem hasCanonicalEmbedding
    (C : CompleteLocalTripleWitness d χ) :
    C.HasCanonicalEmbedding := by
  unfold HasCanonicalEmbedding
  exact C.embedding_eq

end CompleteLocalTripleWitness

namespace LocalInductiveMcKayData

variable {K : Type} [Group K] [Finite K] {p : ℕ}
  {P : Sylow p K}

/-- Extract the fully bundled canonical local witness from part (b) of the
inductive McKay datum. -/
def completeTripleWitness
    (d : LocalInductiveMcKayData P)
    (χ : PPrimeIrreducibleCharacter K p) :
    CompleteLocalTripleWitness d.toEquivariant χ :=
  Classical.choice (by
    rcases d.triple_compatible χ with
      ⟨V, W, hVadd, hVmodule, hVfinite, hVnontrivial,
        hWadd, hWmodule, hWfinite, hWnontrivial, C, hC⟩
    exact
      ⟨{ leftSpace := V
         rightSpace := W
         leftAddCommGroup := hVadd
         leftModule := hVmodule
         leftModuleFinite := hVfinite
         leftNontrivial := hVnontrivial
         rightAddCommGroup := hWadd
         rightModule := hWmodule
         rightModuleFinite := hWfinite
         rightNontrivial := hWnontrivial
         witness := C
         embedding_eq := hC }⟩)

theorem completeTripleWitness_hasCanonicalEmbedding
    (d : LocalInductiveMcKayData P)
    (χ : PPrimeIrreducibleCharacter K p) :
    (d.completeTripleWitness χ).HasCanonicalEmbedding :=
  (d.completeTripleWitness χ).hasCanonicalEmbedding

end LocalInductiveMcKayData

namespace LayerComponentLocalData

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {Q : Sylow p (layer G)}
variable {D : LayerSylowCoordinateData G p Q}

/-- The component character occurring in the canonical component
factorization of a layer character. -/
abbrev coordinateCharacter
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (K : ComponentIndex G) :
    PPrimeIrreducibleCharacter K.1 p :=
  ((GroupTheory.layerPPrimeCharacterEquiv G p).symm θ).1 K

/-- The complete canonical local central-triple witness supplied at one
component coordinate of a layer character. -/
def coordinateCompleteTripleWitness
    (d : LayerComponentLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (K : ComponentIndex G) :
    CompleteLocalTripleWitness
      (d.data K).toEquivariant (coordinateCharacter θ K) :=
  (d.data K).completeTripleWitness (coordinateCharacter θ K)

theorem coordinateCompleteTripleWitness_hasCanonicalEmbedding
    (d : LayerComponentLocalData D)
    (θ : PPrimeIrreducibleCharacter (layer G) p)
    (K : ComponentIndex G) :
    (d.coordinateCompleteTripleWitness θ K).HasCanonicalEmbedding :=
  (d.coordinateCompleteTripleWitness θ K).hasCanonicalEmbedding

end LayerComponentLocalData

/-- The exact projective-descent input at the external-product stage.

For the two component multiplication maps, `P.kernel` and `Q.kernel` are the
central kernels.  The second field records operator-and-factor compatibility,
not merely ordinary-character scalar compatibility.  Turning this input into
an associated central-isomorphism witness on the quotient triples is the
currently missing projective character-triple descent construction. -/
structure CompleteCentralProductDescentInput
    {G H : Type}
    [Group G] [Finite G] [Group H] [Finite H]
    (P : InternalCentralProduct G) (Q : InternalCentralProduct H)
    (T : CharacterTriple (P.left × P.right))
    (U : CharacterTriple (Q.left × Q.right)) where
  /-- The witness assembled on the two external products. -/
  externalWitness : CompleteCentralIsomorphismWitness T U
  /-- Exact descent compatibility for its two chosen projective lifts. -/
  projectiveCompatibility :
    externalWitness.HasProjectiveQuotientCompatibility P.kernel Q.kernel

/-- The precise quotient-transport boundary for complete central witnesses.

This structure asks for a witness only on the two internal central-product
images.  It deliberately does not pretend that a product witness descends
through a central kernel: establishing that descent is the missing
projective-representation argument in the layer construction. -/
structure CompleteCentralProductImageWitness
    {G : Type} {H : Type}
    [Group G] [Finite G] [Group H] [Finite H]
    (P : InternalCentralProduct G) (Q : InternalCentralProduct H)
    (T : CharacterTriple P.subgroup)
    (U : CharacterTriple Q.subgroup) where
  /-- The assembled witness after passage to the internal images. -/
  complete : CompleteCentralIsomorphismWitness T U

namespace CompleteCentralProductImageWitness

variable {G : Type} {H : Type}
  [Group G] [Finite G] [Group H] [Finite H]
  {P : InternalCentralProduct G} {Q : InternalCentralProduct H}
  {T : CharacterTriple P.subgroup}
  {U : CharacterTriple Q.subgroup}

/-- Once the internal-image witness is available, its transport to the two
canonical quotient presentations is automatic. -/
def toQuotientPresentation
    (C : CompleteCentralProductImageWitness P Q T U) :
    CompleteCentralIsomorphismWitness
      (T.comap P.quotientEquiv) (U.comap Q.quotientEquiv) :=
  C.complete.centralProductQuotientComap P Q

end CompleteCentralProductImageWitness

end InductiveMcKay
end McKayConjecture
