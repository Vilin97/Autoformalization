/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.Transitivity
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Quotient isomorphism attached to a central character-triple witness

For a central isomorphism

`(A, X, χ) ≥c (B, M, χ')`,

the exact subgroup conditions `A = X B` and `X ∩ B = M` identify `B / M`
with `A / X`.  This file constructs that canonical quotient isomorphism from
the stored embedding, proves injectivity from the intersection condition, and
proves surjectivity from the product decomposition.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace CharacterTriple
namespace FactorMatchedIsomorphismWitness

local notation "CentralIsomorphismWitness" =>
  FactorMatchedIsomorphismWitness

variable {A : Type u} {B : Type v} [Finite A] [Finite B] [Group A] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {V W : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]

/-- The embedding sends the right normal subgroup into the left normal
subgroup, in the form expected by `QuotientGroup.map`. -/
theorem rightNormal_le_comap_leftNormal
    (C : CentralIsomorphismWitness T U V W) :
    U.normalSubgroup ≤ T.normalSubgroup.comap C.embedding := by
  intro m hm
  exact C.map_rightNormal_le_leftNormal ⟨m, hm, rfl⟩

/-- The canonical homomorphism `B / M → A / X`. -/
def quotientHom
    (C : CentralIsomorphismWitness T U V W) :
    B ⧸ U.normalSubgroup →* A ⧸ T.normalSubgroup :=
  QuotientGroup.map U.normalSubgroup T.normalSubgroup
    C.embedding C.rightNormal_le_comap_leftNormal

@[simp]
theorem quotientHom_mk
    (C : CentralIsomorphismWitness T U V W) (b : B) :
    C.quotientHom (QuotientGroup.mk' U.normalSubgroup b) =
      QuotientGroup.mk' T.normalSubgroup (C.embedding b) :=
  rfl

/-- The intersection condition makes the quotient homomorphism injective. -/
theorem quotientHom_injective
    (C : CentralIsomorphismWitness T U V W) :
    Function.Injective C.quotientHom := by
  intro q r hqr
  induction q using QuotientGroup.induction_on with
  | H b =>
      induction r using QuotientGroup.induction_on with
      | H c =>
          apply (QuotientGroup.eq_iff_div_mem
            (N := U.normalSubgroup)).2
          apply C.mem_rightNormal_of_embedding_mem_leftNormal
          have hquot :
              (C.embedding b : A ⧸ T.normalSubgroup) =
                (C.embedding c : A ⧸ T.normalSubgroup) := by
            exact hqr
          have hmem :=
            (QuotientGroup.eq_iff_div_mem
              (N := T.normalSubgroup)).1 hquot
          simpa only [map_div] using hmem

/-- The product condition `A = XB` makes the quotient homomorphism
surjective. -/
theorem quotientHom_surjective
    (C : CentralIsomorphismWitness T U V W) :
    Function.Surjective C.quotientHom := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H a =>
      obtain ⟨x, b, hxb⟩ := C.ambient_eq_product a
      refine ⟨QuotientGroup.mk' U.normalSubgroup b, ?_⟩
      change QuotientGroup.mk' T.normalSubgroup (C.embedding b) =
        QuotientGroup.mk' T.normalSubgroup a
      rw [← hxb, map_mul]
      have hx :
          QuotientGroup.mk' T.normalSubgroup (x : A) = 1 :=
        (QuotientGroup.eq_one_iff (x : A)).2 x.property
      rw [hx, one_mul]

/-- The canonical quotient-group isomorphism `B / M ≃ A / X`. -/
def quotientEquiv
    (C : CentralIsomorphismWitness T U V W) :
    B ⧸ U.normalSubgroup ≃* A ⧸ T.normalSubgroup :=
  MulEquiv.ofBijective C.quotientHom
    ⟨C.quotientHom_injective, C.quotientHom_surjective⟩

@[simp]
theorem quotientEquiv_mk
    (C : CentralIsomorphismWitness T U V W) (b : B) :
    C.quotientEquiv (QuotientGroup.mk' U.normalSubgroup b) =
      QuotientGroup.mk' T.normalSubgroup (C.embedding b) :=
  rfl

end FactorMatchedIsomorphismWitness

namespace CentralIsomorphismWitness

variable {A : Type u} {B : Type v} [Finite A] [Finite B] [Group A] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {V W : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]

theorem rightNormal_le_comap_leftNormal
    (C : CentralIsomorphismWitness T U V W) :
    U.normalSubgroup ≤ T.normalSubgroup.comap C.embedding :=
  C.toFactorMatchedIsomorphismWitness.rightNormal_le_comap_leftNormal

def quotientHom
    (C : CentralIsomorphismWitness T U V W) :
    B ⧸ U.normalSubgroup →* A ⧸ T.normalSubgroup :=
  C.toFactorMatchedIsomorphismWitness.quotientHom

@[simp]
theorem quotientHom_mk
    (C : CentralIsomorphismWitness T U V W) (b : B) :
    C.quotientHom (QuotientGroup.mk' U.normalSubgroup b) =
      QuotientGroup.mk' T.normalSubgroup (C.embedding b) :=
  C.toFactorMatchedIsomorphismWitness.quotientHom_mk b

theorem quotientHom_injective
    (C : CentralIsomorphismWitness T U V W) :
    Function.Injective C.quotientHom :=
  C.toFactorMatchedIsomorphismWitness.quotientHom_injective

theorem quotientHom_surjective
    (C : CentralIsomorphismWitness T U V W) :
    Function.Surjective C.quotientHom :=
  C.toFactorMatchedIsomorphismWitness.quotientHom_surjective

def quotientEquiv
    (C : CentralIsomorphismWitness T U V W) :
    B ⧸ U.normalSubgroup ≃* A ⧸ T.normalSubgroup :=
  C.toFactorMatchedIsomorphismWitness.quotientEquiv

@[simp]
theorem quotientEquiv_mk
    (C : CentralIsomorphismWitness T U V W) (b : B) :
    C.quotientEquiv (QuotientGroup.mk' U.normalSubgroup b) =
      QuotientGroup.mk' T.normalSubgroup (C.embedding b) :=
  C.toFactorMatchedIsomorphismWitness.quotientEquiv_mk b

end CentralIsomorphismWitness
end CharacterTriple
end McKayConjecture
