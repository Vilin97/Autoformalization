/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CyclicPGroupQuotientGallagher
import McKayConjecture.Character.CliffordDegree
import McKayConjecture.GroupTheory.PGroupMaximalCyclicQuotient

/-!
# Prime-to-`p` characters of finite `p`-groups

An irreducible character of a finite `p`-group whose degree is prime to
`p` is linear.  We prove this by induction through a normal maximal
subgroup.  Its quotient is a cyclic `p`-group; an active constituent
extends, and Gallagher's correspondence splits the ambient character
into that extension and a linear character of the cyclic quotient.
-/

noncomputable section

namespace McKayConjecture
namespace IrreducibleCharacter

open CliffordPartition

variable {p : ℕ} [Fact p.Prime]

private theorem degree_eq_one_of_isPGroup_of_isPPrimeDegree_aux
    (G : Type) [Group G] [Finite G]
    (hG : IsPGroup p G)
    (χ : IrreducibleCharacter G)
    (hχ : χ.IsPPrimeDegree p) :
    χ.degree = 1 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  by_cases hnontrivial : Nontrivial G
  · letI : Nontrivial G := hnontrivial
    obtain ⟨N, hNcoatom, hquotientP, hquotientCyclic⟩ :=
      McKayConjecture.GroupTheory.IsPGroup.exists_normal_isCoatom_cyclic_quotient
        hG
    letI : IsCyclic (G ⧸ N.toSubgroup) := hquotientCyclic
    let θ : IrreducibleCharacter N.toSubgroup :=
      χ.normalSimpleConstituent N.toSubgroup
    have hθp : θ.IsPPrimeDegree p :=
      χ.normalSimpleConstituent_isPPrimeDegree N.toSubgroup hχ
    have hNcard :
        Nat.card N.toSubgroup < Nat.card G := by
      calc
        Nat.card N.toSubgroup <
            Nat.card ↑(Set.univ : Set G) :=
          Set.Finite.card_lt_card
            Set.finite_univ hNcoatom.lt_top
        _ = Nat.card G :=
          Nat.card_congr (Equiv.Set.univ G)
    have hθdegree : θ.degree = 1 :=
      degree_eq_one_of_isPGroup_of_isPPrimeDegree_aux
        N.toSubgroup
        (hG.to_subgroup N.toSubgroup) θ hθp
    let θp : PPrimeIrreducibleCharacter N.toSubgroup p :=
      ⟨θ, hθp⟩
    have hactive : IsActivePPrimeCharacter N.toSubgroup θp := by
      refine ⟨?_⟩
      exact
        ⟨⟨χ,
            by
              simpa only [θp, θ,
                CliffordPartition.orbitOf] using
                CliffordPartition.liesOverOrbit_out_orbitOf
                  N.toSubgroup χ⟩,
          hχ⟩
    let ψp : PPrimeIrreducibleCharacter G p :=
      activeCyclicPGroupExtension
        N.toSubgroup hquotientP θp hactive
    have hψ :
        IsExtensionAlong N.toSubgroup.subtype θ ψp.1 :=
      activeCyclicPGroupExtension_isExtension
        N.toSubgroup hquotientP θp hactive
    let χOver :
        CliffordCorrespondence.IrreducibleCharactersOverAlong
          N.toSubgroup.subtype θ :=
      ⟨χ, χ.normalSimpleConstituent_liesOver N.toSubgroup⟩
    let beta : IrreducibleCharacter (G ⧸ N.toSubgroup) :=
      (gallagherCorrespondence hψ).symm χOver
    have hbetaDegree : beta.degree = 1 := by
      rw [← beta.realization_finrank]
      exact
        (CliffordRestriction.isIrreducible_of_simple
          beta.realization).finrank_eq_one_of_isMulCommutative
    have hforward :
        gallagherTensorCharacter hψ beta = χ := by
      exact congrArg Subtype.val
        ((gallagherCorrespondence hψ).apply_symm_apply χOver)
    rw [← hforward,
      gallagherTensorCharacter_degree hψ beta,
      hbetaDegree, mul_one, hψ.degree_eq, hθdegree]
  · letI : Subsingleton G :=
      not_nontrivial_iff_subsingleton.mp hnontrivial
    letI : IsMulCommutative G :=
      IsMulCommutative.of_comm
        (fun _ _ ↦ Subsingleton.elim _ _)
    rw [← χ.realization_finrank]
    exact
      (CliffordRestriction.isIrreducible_of_simple
        χ.realization).finrank_eq_one_of_isMulCommutative
termination_by Nat.card G

variable {G : Type} [Group G] [Finite G]

/-- An irreducible character of prime-to-`p` degree on a finite
`p`-group is linear. -/
theorem degree_eq_one_of_isPGroup_of_isPPrimeDegree
    (hG : IsPGroup p G)
    (χ : IrreducibleCharacter G)
    (hχ : χ.IsPPrimeDegree p) :
    χ.degree = 1 :=
  degree_eq_one_of_isPGroup_of_isPPrimeDegree_aux
    G hG χ hχ

end IrreducibleCharacter
end McKayConjecture
