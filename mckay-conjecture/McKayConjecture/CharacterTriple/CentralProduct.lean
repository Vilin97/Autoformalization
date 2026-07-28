/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralProductCharacter
import McKayConjecture.CharacterTriple.Transport

/-!
# Central products and central character-triple witnesses

This file records the witness operations supported by the current
character-triple API:

* product witnesses are obtained from tensor products;
* witnesses over internal central-product images transport canonically to
  the corresponding central quotients; and
* these operations combine with arbitrary relabellings.

Descending a witness *from the full external direct product* to a nontrivial
central quotient requires quotient character triples and exact descent of
all four chosen projective lifts.  Those data are not implied merely by the
scalar compatibility used to descend ordinary characters, so no such
unconditional theorem is asserted here.
-/

noncomputable section

open scoped TensorProduct

universe u v w x

namespace McKayConjecture
namespace CharacterTriple

namespace CentralIsomorphismWitness

section Product

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

/-- Existence of central-isomorphism witnesses is closed under products. -/
theorem centrallyIsomorphicVia_prod
    (hC : CentrallyIsomorphicVia T₁ U₁ V₁ W₁)
    (hD : CentrallyIsomorphicVia T₂ U₂ V₂ W₂) :
    CentrallyIsomorphicVia
      (T₁.prod T₂) (U₁.prod U₂)
      (V₁ ⊗[ℂ] V₂) (W₁ ⊗[ℂ] W₂) := by
  obtain ⟨C⟩ := hC
  obtain ⟨D⟩ := hD
  exact ⟨C.prod D⟩

/-- Form a product witness and then independently relabel its two product
ambient groups. -/
def prodComap
    {A' B' : Type*} [Finite A'] [Group A'] [Finite B'] [Group B']
    (C : CentralIsomorphismWitness T₁ U₁ V₁ W₁)
    (D : CentralIsomorphismWitness T₂ U₂ V₂ W₂)
    (eA : A' ≃* A₁ × A₂) (eB : B' ≃* B₁ × B₂) :
    CentralIsomorphismWitness
      ((T₁.prod T₂).comap eA) ((U₁.prod U₂).comap eB)
      (V₁ ⊗[ℂ] V₂) (W₁ ⊗[ℂ] W₂) :=
  (C.prod D).comap eA eB

/-- Product formation followed by relabelling preserves existence of a
central-isomorphism witness. -/
theorem centrallyIsomorphicVia_prod_comap
    {A' B' : Type*} [Finite A'] [Group A'] [Finite B'] [Group B']
    (eA : A' ≃* A₁ × A₂) (eB : B' ≃* B₁ × B₂)
    (hC : CentrallyIsomorphicVia T₁ U₁ V₁ W₁)
    (hD : CentrallyIsomorphicVia T₂ U₂ V₂ W₂) :
    CentrallyIsomorphicVia
      ((T₁.prod T₂).comap eA) ((U₁.prod U₂).comap eB)
      (V₁ ⊗[ℂ] V₂) (W₁ ⊗[ℂ] W₂) := by
  obtain ⟨C⟩ := hC
  obtain ⟨D⟩ := hD
  exact ⟨prodComap C D eA eB⟩

end Product

section QuotientTransport

variable {G : Type u} {H : Type v}
  [Finite G] [Group G] [Finite H] [Group H]
  (P : InternalCentralProduct G) (Q : InternalCentralProduct H)
  {T : CharacterTriple P.subgroup}
  {U : CharacterTriple Q.subgroup}
  {V W : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]

/-- Transport a witness on internal central-product images to their
canonical quotient presentations. -/
def centralProductQuotientComap
    (C : CentralIsomorphismWitness T U V W) :
    CentralIsomorphismWitness
      (T.comap P.quotientEquiv) (U.comap Q.quotientEquiv) V W :=
  C.comap P.quotientEquiv Q.quotientEquiv

/-- Existence of a witness is invariant under replacing internal
central-product images by their canonical central quotients. -/
theorem centrallyIsomorphicVia_centralProductQuotientComap
    (hC : CentrallyIsomorphicVia T U V W) :
    CentrallyIsomorphicVia
      (T.comap P.quotientEquiv) (U.comap Q.quotientEquiv) V W := by
  obtain ⟨C⟩ := hC
  exact ⟨centralProductQuotientComap P Q C⟩

end QuotientTransport

end CentralIsomorphismWitness
end CharacterTriple
end McKayConjecture
