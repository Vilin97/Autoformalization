/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordPPrimeCorrespondence
import McKayConjecture.Character.OverAlongTransport

/-!
# Character fibres when the inertia group is the whole ambient group

If a normal-subgroup character is invariant under the whole ambient group,
its inertia group is `⊤`.  This file identifies the resulting inertia fibre
with the corresponding ambient character fibre.  Keeping this transport
separate avoids repeatedly unfolding the dependent inertia subgroup in
normal-Hall and Glauberman arguments.
-/

noncomputable section

namespace McKayConjecture

namespace CliffordCorrespondence

variable {G : Type} [Group G] [Fintype G]
variable (N : Subgroup G) [N.Normal]
variable (θ : IrreducibleCharacter N)

/-- When `θ` is invariant under all of `G`, its inertia group is canonically
isomorphic to `G`. -/
def inertiaTopEquiv
    (hinertia : IrreducibleCharacter.inertia N θ = ⊤) :
    IrreducibleCharacter.inertia N θ ≃* G :=
  (MulEquiv.subgroupCongr hinertia).trans Subgroup.topEquiv

@[simp]
theorem inertiaTopEquiv_apply_coe
    (hinertia : IrreducibleCharacter.inertia N θ = ⊤)
    (x : IrreducibleCharacter.inertia N θ) :
    inertiaTopEquiv N θ hinertia x = (x : G) :=
  rfl

/-- Induction from a full inertia subgroup is just transport along the
canonical equivalence from that subgroup to the ambient group. -/
theorem induce_inertia_eq_top_apply
    (hinertia : IrreducibleCharacter.inertia N θ = ⊤)
    (f :
      ClassFunction
        (IrreducibleCharacter.inertia N θ))
    (g : G) :
    ClassFunction.induce
        (IrreducibleCharacter.inertia N θ) f g =
      f ((inertiaTopEquiv N θ hinertia).symm g) := by
  let I := IrreducibleCharacter.inertia N θ
  let gI : I :=
    (inertiaTopEquiv N θ hinertia).symm g
  have hgI : (gI : G) = g :=
    (inertiaTopEquiv N θ hinertia).apply_symm_apply g
  change
    ClassFunction.induce I f g = f gI
  have hmem (x : G) :
      x⁻¹ * g * x ∈ I := by
    change
      x⁻¹ * g * x ∈
        IrreducibleCharacter.inertia N θ
    rw [hinertia]
    trivial
  have hterm (x : G) :
      ClassFunction.inductionTerm I f x g = f gI := by
    rw [ClassFunction.inductionTerm_of_mem I f (hmem x)]
    let xI : I :=
      ⟨x, by
        change
          x ∈ IrreducibleCharacter.inertia N θ
        rw [hinertia]
        trivial⟩
    have hconj :=
      ClassFunction.conj_apply f gI xI⁻¹
    calc
      f ⟨x⁻¹ * g * x, hmem x⟩ =
          f (xI⁻¹ * gI * (xI⁻¹)⁻¹) := by
        apply congrArg f
        apply Subtype.ext
        simp only [inv_inv]
        change
          x⁻¹ * g * x =
            x⁻¹ * (gI : G) * x
        rw [hgI]
      _ = f gI := hconj
  rw [ClassFunction.induce_apply]
  rw [Finset.sum_congr rfl (fun x _ ↦ hterm x),
    Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  have hcard :
      Nat.card I = Nat.card G :=
    Nat.card_congr
      (inertiaTopEquiv N θ hinertia).toEquiv
  rw [← Nat.card_eq_fintype_card, hcard]
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp

/-- The canonical inclusion of `N` in its full inertia group commutes with
the equivalence from that inertia group to the ambient group. -/
theorem inertiaTopEquiv_comp_inertiaInclusion
    (hinertia : IrreducibleCharacter.inertia N θ = ⊤) :
    (inertiaTopEquiv N θ hinertia).toMonoidHom.comp
        (inertiaInclusion N θ) =
      N.subtype := by
  ext n
  rfl

/-- For an ambient-invariant normal character, the prime-to-`p` inertia
fibre is canonically the ambient fibre over that character. -/
def pPrimeIrreducibleCharactersOverInertiaEquivAmbient
    (hinertia : IrreducibleCharacter.inertia N θ = ⊤)
    (p : ℕ) :
    PPrimeIrreducibleCharactersOverInertia N θ p ≃
      PPrimeIrreducibleCharactersOverAlong N.subtype θ p := by
  let e :=
    pPrimeIrreducibleCharactersOverAlongComapEquiv
      (inertiaTopEquiv N θ hinertia)
      (MulEquiv.refl N)
      N.subtype
      (inertiaInclusion N θ)
      (inertiaTopEquiv_comp_inertiaInclusion N θ hinertia)
      θ p
  simpa using e.symm

/-- Transport from a full inertia group to the ambient group is
identity-on-elements at the level of character values. -/
theorem pPrimeIrreducibleCharactersOverInertiaEquivAmbient_values
    (hinertia : IrreducibleCharacter.inertia N θ = ⊤)
    (p : ℕ)
    (χ : PPrimeIrreducibleCharactersOverInertia N θ p)
    (x : IrreducibleCharacter.inertia N θ) :
    ((pPrimeIrreducibleCharactersOverInertiaEquivAmbient
        N θ hinertia p χ).1.1.values (x : G)) =
      χ.1.1.values x := by
  change
    (χ.1.1.comap
        (inertiaTopEquiv N θ hinertia).symm).values
          (x : G) =
      χ.1.1.values x
  rw [IrreducibleCharacter.comap_values]
  congr 1

/-- Full-inertia transport does not change character degree. -/
theorem pPrimeIrreducibleCharactersOverInertiaEquivAmbient_degree
    (hinertia : IrreducibleCharacter.inertia N θ = ⊤)
    (p : ℕ)
    (χ : PPrimeIrreducibleCharactersOverInertia N θ p) :
    ((pPrimeIrreducibleCharactersOverInertiaEquivAmbient
        N θ hinertia p χ).1.1.degree) =
      χ.1.1.degree := by
  rfl

/-- For a full inertia subgroup, the prime-to-`p` Clifford
correspondence agrees exactly with the direct inertia-top transport. -/
theorem cliffordPPrimeCorrespondence_eq_inertiaTopAmbient
    (hinertia : IrreducibleCharacter.inertia N θ = ⊤)
    (p : ℕ)
    (hp : p.Prime)
    (hindex :
      ¬p ∣ (IrreducibleCharacter.inertia N θ).index)
    (χ :
      PPrimeIrreducibleCharactersOverInertia
        N θ p) :
    (CliffordEquivalence.cliffordPPrimeCorrespondence
        N θ hp hindex χ).1.1 =
      (pPrimeIrreducibleCharactersOverInertiaEquivAmbient
        N θ hinertia p χ).1.1 := by
  apply IrreducibleCharacter.ext
  funext g
  let x :=
    (inertiaTopEquiv N θ hinertia).symm g
  have hxg :
      (x : G) = g :=
    (inertiaTopEquiv N θ hinertia).apply_symm_apply g
  change
    (CliffordCorrespondence.inducedIrreducibleCharacter
      N θ χ.1.1
      (CliffordEquivalence.inertiaInduction_simple
        N θ χ.1.1 χ.1.2)).values g =
      (pPrimeIrreducibleCharactersOverInertiaEquivAmbient
        N θ hinertia p χ).1.1.values g
  have hind :=
    congrArg
      (fun f : ClassFunction G ↦ f g)
      (CliffordCorrespondence.inducedIrreducibleCharacter_toClassFunction
        N θ χ.1.1
        (CliffordEquivalence.inertiaInduction_simple
          N θ χ.1.1 χ.1.2))
  have hambient :=
    pPrimeIrreducibleCharactersOverInertiaEquivAmbient_values
      N θ hinertia p χ x
  rw [hxg] at hambient
  exact
    hind.trans
      ((induce_inertia_eq_top_apply
        N θ hinertia χ.1.1.toClassFunction g).trans
          hambient.symm)

/-- The inverse full-inertia transport is likewise
identity-on-elements. -/
theorem pPrimeIrreducibleCharactersOverInertiaEquivAmbient_symm_values
    (hinertia : IrreducibleCharacter.inertia N θ = ⊤)
    (p : ℕ)
    (χ : PPrimeIrreducibleCharactersOverAlong N.subtype θ p)
    (x : IrreducibleCharacter.inertia N θ) :
    (((pPrimeIrreducibleCharactersOverInertiaEquivAmbient
        N θ hinertia p).symm χ).1.1.values x) =
      χ.1.1.values (x : G) := by
  rfl

/-- Inverse full-inertia transport preserves degree. -/
theorem pPrimeIrreducibleCharactersOverInertiaEquivAmbient_symm_degree
    (hinertia : IrreducibleCharacter.inertia N θ = ⊤)
    (p : ℕ)
    (χ : PPrimeIrreducibleCharactersOverAlong N.subtype θ p) :
    (((pPrimeIrreducibleCharactersOverInertiaEquivAmbient
        N θ hinertia p).symm χ).1.1.degree) =
      χ.1.1.degree := by
  rfl

end CliffordCorrespondence

end McKayConjecture
