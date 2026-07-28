/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ClassFunctionTransport
import McKayConjecture.Character.Induction

/-!
# Naturality of character induction under group equivalences

Simultaneously relabelling an ambient finite group and a subgroup through a
commuting square preserves the classical induction formula.  The proof
works directly with induction summands and reindexes the ambient finite sum
through the supplied group equivalence.
-/

noncomputable section

namespace McKayConjecture
namespace ClassFunction

variable {G G' : Type} [Group G] [Group G']
variable (S : Subgroup G) (S' : Subgroup G')

/-- A commuting square of ambient and subgroup equivalences identifies
the corresponding summands in the classical induction formula. -/
theorem inductionTerm_comap_equiv
    (eG : G' ≃* G)
    (eS : S' ≃* S)
    (hcomm :
      eG.toMonoidHom.comp S'.subtype =
        S.subtype.comp eS.toMonoidHom)
    (θ : ClassFunction S)
    (x g : G') :
    inductionTerm S'
        (comapLinearEquiv eS θ) x g =
      inductionTerm S θ (eG x) (eG g) := by
  let y : G' := x⁻¹ * g * x
  let z : G := (eG x)⁻¹ * eG g * eG x
  have hyz : eG y = z := by
    simp [y, z]
  have hmem : y ∈ S' ↔ z ∈ S := by
    constructor
    · intro hy
      let ys : S' := ⟨y, hy⟩
      have hsquare :=
        DFunLike.congr_fun hcomm ys
      have heq : eG y = (eS ys : S) := hsquare
      rw [← hyz, heq]
      exact (eS ys).2
    · intro hz
      let zs : S := ⟨z, hz⟩
      let ys : S' := eS.symm zs
      have hsquare :=
        DFunLike.congr_fun hcomm ys
      have heq : eG (ys : G') = (eS ys : S) := hsquare
      have hys : (ys : G') = y := by
        apply eG.injective
        calc
          eG (ys : G') = (eS ys : S) := heq
          _ = z := by
            simpa [ys, zs] using
              congrArg Subtype.val (eS.apply_symm_apply zs)
          _ = eG y := hyz.symm
      rw [← hys]
      exact ys.2
  by_cases hy : y ∈ S'
  · have hz : z ∈ S := hmem.mp hy
    have hy' : x⁻¹ * g * x ∈ S' := by
      simpa [y] using hy
    have hz' : (eG x)⁻¹ * eG g * eG x ∈ S := by
      simpa [z] using hz
    rw [inductionTerm_of_mem S'
        (comapLinearEquiv eS θ) hy',
      inductionTerm_of_mem S θ hz']
    change
      θ (eS ⟨x⁻¹ * g * x, hy'⟩) =
        θ ⟨(eG x)⁻¹ * eG g * eG x, hz'⟩
    apply congrArg θ
    apply Subtype.ext
    have hsquare :=
      DFunLike.congr_fun hcomm
        (⟨x⁻¹ * g * x, hy'⟩ : S')
    calc
      ((eS ⟨x⁻¹ * g * x, hy'⟩ : S) : G) =
          eG (x⁻¹ * g * x) := hsquare.symm
      _ = (eG x)⁻¹ * eG g * eG x := by simp
  · have hz : z ∉ S := by
      exact fun hz ↦ hy (hmem.mpr hz)
    have hy' : x⁻¹ * g * x ∉ S' := by
      simpa [y] using hy
    have hz' : (eG x)⁻¹ * eG g * eG x ∉ S := by
      simpa [z] using hz
    rw [inductionTerm_of_not_mem S'
        (comapLinearEquiv eS θ) hy',
      inductionTerm_of_not_mem S θ hz']

/-- Pulling back an induced class function is the same as first pulling
back the subgroup class function and then inducing. -/
theorem induce_comap_equiv
    [Fintype G] [Fintype G']
    (eG : G' ≃* G)
    (eS : S' ≃* S)
    (hcomm :
      eG.toMonoidHom.comp S'.subtype =
        S.subtype.comp eS.toMonoidHom)
    (θ : ClassFunction S) :
    induce S' (comapLinearEquiv eS θ) =
      comapLinearEquiv eG (induce S θ) := by
  ext g
  rw [induce_apply, comapLinearEquiv_apply, induce_apply]
  rw [Nat.card_congr eS.toEquiv]
  congr 1
  calc
    ∑ x : G',
        inductionTerm S'
          (comapLinearEquiv eS θ) x g =
      ∑ x : G',
        inductionTerm S θ (eG x) (eG g) := by
          apply Finset.sum_congr rfl
          intro x _
          exact inductionTerm_comap_equiv
            S S' eG eS hcomm θ x g
    _ =
      ∑ x : G,
        inductionTerm S θ x (eG g) :=
          eG.toEquiv.sum_comp
            (fun x : G ↦ inductionTerm S θ x (eG g))

end ClassFunction
end McKayConjecture
