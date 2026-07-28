/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.ProjectiveLinearLift
import McKayConjecture.CharacterTriple.ProjectiveRestriction

/-!
# Descent of chosen projective operators to a quotient

A projective-linear action always descends when its normal subgroup acts by
scalars, but that loses the chosen linear operators.  For inverse
multiplicity factors we need a stronger construction: if the chosen
operators are identity on a normal subgroup and the factor is one whenever
either input lies in that subgroup, the operators themselves are constant on
cosets.

This file descends those exact operators.  A representative of each coset is
used only to define the quotient representation; coset invariance proves that
pullback along the quotient map recovers the original projective
representation, including its factor.
-/

noncomputable section

universe u v w

namespace McKayConjecture
namespace CharacterTriple
namespace ProjectiveRepresentation

variable {K : Type u} {V : Type v} {G : Type w}
variable [Field K] [AddCommGroup V] [Module K V] [Group G]

/-- A factor is quotient-compatible when it is one whenever either input
lies in the normal subgroup. -/
structure FactorIsQuotientCompatible
    (P : ProjectiveRepresentation K G V) (N : Subgroup G) : Prop where
  factor_normal_left : ∀ (n : N) (g : G), P.factor (n : G) g = 1
  factor_normal_right : ∀ (g : G) (n : N), P.factor g (n : G) = 1

/-- Data ensuring that the chosen operators, rather than merely their
projective-linear classes, descend through `G ⧸ N`. -/
structure IsQuotientCompatible
    (P : ProjectiveRepresentation K G V) (N : Subgroup G) : Prop
    extends P.FactorIsQuotientCompatible N where
  operator_normal : ∀ n : N, P.operator (n : G) = 1

variable {P : ProjectiveRepresentation K G V}
variable {N : Subgroup G} [N.Normal]

/-- Compatible chosen operators depend only on the quotient coset. -/
theorem IsQuotientCompatible.operator_eq_of_mk_eq
    (hP : P.IsQuotientCompatible N)
    {g k : G}
    (hgk :
      QuotientGroup.mk' N g = QuotientGroup.mk' N k) :
    P.operator g = P.operator k := by
  obtain ⟨n, hn, hgn⟩ :=
    (QuotientGroup.mk'_eq_mk' (N := N)).mp hgk
  let nN : N := ⟨n, hn⟩
  have hmul := P.map_mul g n
  rw [hP.operator_normal nN,
    hP.factor_normal_right g nN, map_one, mul_one, one_mul,
    hgn] at hmul
  exact hmul

omit [N.Normal] in
/-- Multiplying the second input of a compatible factor by a normal element
does not change it. -/
theorem FactorIsQuotientCompatible.factor_mul_normal_right
    [Nontrivial V]
    (hP : P.FactorIsQuotientCompatible N)
    (g k : G) (n : N) :
    P.factor g (k * (n : G)) = P.factor g k := by
  have hcocycle := P.factor_cocycle g k (n : G)
  rw [hP.factor_normal_right (g * k) n,
    hP.factor_normal_right k n, one_mul, one_mul] at hcocycle
  exact hcocycle.symm

/-- Multiplying the first input of a compatible factor by a normal element
does not change it. -/
theorem FactorIsQuotientCompatible.factor_mul_normal_left
    [Nontrivial V]
    (hP : P.FactorIsQuotientCompatible N)
    (g k : G) (n : N) :
    P.factor (g * (n : G)) k = P.factor g k := by
  let conjugate : N :=
    ⟨k⁻¹ * (n : G) * k,
      by
        simpa using
          (inferInstance : N.Normal).conj_mem
            (n : G) n.property k⁻¹⟩
  have hconjugate :
      (n : G) * k = k * (conjugate : G) := by
    dsimp [conjugate]
    group
  have hcocycle := P.factor_cocycle g (n : G) k
  rw [hP.factor_normal_right g n,
    hP.factor_normal_left n k, mul_one, one_mul,
    hconjugate,
    hP.factor_mul_normal_right g k conjugate] at hcocycle
  exact hcocycle

/-- A compatible factor depends only on the two quotient cosets. -/
theorem FactorIsQuotientCompatible.factor_eq_of_mk_eq
    [Nontrivial V]
    (hP : P.FactorIsQuotientCompatible N)
    {g g' k k' : G}
    (hgg' :
      QuotientGroup.mk' N g = QuotientGroup.mk' N g')
    (hkk' :
      QuotientGroup.mk' N k = QuotientGroup.mk' N k') :
    P.factor g k = P.factor g' k' := by
  obtain ⟨n, hn, hgn⟩ :=
    (QuotientGroup.mk'_eq_mk' (N := N)).mp hgg'
  obtain ⟨m, hm, hkm⟩ :=
    (QuotientGroup.mk'_eq_mk' (N := N)).mp hkk'
  let nN : N := ⟨n, hn⟩
  let mN : N := ⟨m, hm⟩
  calc
    P.factor g k =
        P.factor (g * (nN : G)) k :=
      (hP.factor_mul_normal_left g k nN).symm
    _ = P.factor g' k := by rw [hgn]
    _ = P.factor g' (k * (mN : G)) :=
      (hP.factor_mul_normal_right g' k mN).symm
    _ = P.factor g' k' := by rw [hkm]

/-- A chosen representative of a quotient coset. -/
def quotientRepresentative (N : Subgroup G) [N.Normal]
    (q : G ⧸ N) : G :=
  Classical.choose (QuotientGroup.mk'_surjective N q)

@[simp]
theorem mk_quotientRepresentative (N : Subgroup G) [N.Normal]
    (q : G ⧸ N) :
    QuotientGroup.mk' N (quotientRepresentative N q) = q :=
  Classical.choose_spec (QuotientGroup.mk'_surjective N q)

/-- The exact chosen operator on a quotient coset. -/
def quotientOperator
    (P : ProjectiveRepresentation K G V) (N : Subgroup G) [N.Normal]
    (q : G ⧸ N) : V ≃ₗ[K] V :=
  P.operator (quotientRepresentative N q)

/-- The quotient factor obtained from the factors of the selected coset
representatives. -/
def quotientFactor
    (P : ProjectiveRepresentation K G V) (N : Subgroup G) [N.Normal]
    (q r : G ⧸ N) : Kˣ :=
  P.factor (quotientRepresentative N q)
    (quotientRepresentative N r)

/-- Descend a projective representation while retaining its chosen
operators exactly. -/
def quotientDescent
    (P : ProjectiveRepresentation K G V) (N : Subgroup G) [N.Normal]
    (hP : P.IsQuotientCompatible N) :
    ProjectiveRepresentation K (G ⧸ N) V where
  operator := quotientOperator P N
  factor := quotientFactor P N
  map_mul q r := by
    change
      P.operator (quotientRepresentative N q) *
          P.operator (quotientRepresentative N r) =
        scalarLinearEquiv K V
            (P.factor (quotientRepresentative N q)
              (quotientRepresentative N r)) *
          P.operator (quotientRepresentative N (q * r))
    calc
      P.operator (quotientRepresentative N q) *
          P.operator (quotientRepresentative N r) =
        scalarLinearEquiv K V
            (P.factor (quotientRepresentative N q)
              (quotientRepresentative N r)) *
          P.operator
            (quotientRepresentative N q *
              quotientRepresentative N r) :=
        P.map_mul _ _
      _ =
        scalarLinearEquiv K V
            (P.factor (quotientRepresentative N q)
              (quotientRepresentative N r)) *
          P.operator (quotientRepresentative N (q * r)) := by
        apply congrArg
          (fun f : V ≃ₗ[K] V ↦
            scalarLinearEquiv K V
                (P.factor (quotientRepresentative N q)
                  (quotientRepresentative N r)) * f)
        apply hP.operator_eq_of_mk_eq
        calc
          QuotientGroup.mk' N
              (quotientRepresentative N q *
                quotientRepresentative N r) =
              QuotientGroup.mk' N (quotientRepresentative N q) *
                QuotientGroup.mk' N (quotientRepresentative N r) :=
            (QuotientGroup.mk' N).map_mul _ _
          _ = q * r := by rw [mk_quotientRepresentative,
            mk_quotientRepresentative]
          _ =
              QuotientGroup.mk' N
                (quotientRepresentative N (q * r)) :=
            (mk_quotientRepresentative N (q * r)).symm

@[simp]
theorem quotientDescent_operator_mk
    (hP : P.IsQuotientCompatible N) (g : G) :
    (P.quotientDescent N hP).operator
        (QuotientGroup.mk' N g) =
      P.operator g := by
  change
    P.operator
        (quotientRepresentative N (QuotientGroup.mk' N g)) =
      P.operator g
  apply hP.operator_eq_of_mk_eq
  exact mk_quotientRepresentative N (QuotientGroup.mk' N g)

/-- Pulling the exact descent back along the quotient map recovers all
chosen operators. -/
theorem quotientDescent_comap_operator
    (hP : P.IsQuotientCompatible N) :
    ((P.quotientDescent N hP).comap
        (QuotientGroup.mk' N)).operator =
      P.operator := by
  funext g
  exact P.quotientDescent_operator_mk hP g

/-- On a nonzero module, exact operator recovery also recovers the selected
factor and hence the entire projective representation. -/
theorem quotientDescent_comap
    [Nontrivial V]
    (hP : P.IsQuotientCompatible N) :
    (P.quotientDescent N hP).comap
        (QuotientGroup.mk' N) =
      P :=
  ext_of_operator_eq _ _ (P.quotientDescent_comap_operator hP)

@[simp]
theorem quotientDescent_factor_mk
    [Nontrivial V]
    (hP : P.IsQuotientCompatible N) (g k : G) :
    (P.quotientDescent N hP).factor
        (QuotientGroup.mk' N g)
        (QuotientGroup.mk' N k) =
      P.factor g k := by
  have hfactor :=
    factor_eq_of_operator_eq
      ((P.quotientDescent N hP).comap (QuotientGroup.mk' N))
      P (P.quotientDescent_comap_operator hP)
  exact congrFun (congrFun hfactor g) k

end ProjectiveRepresentation
end CharacterTriple
end McKayConjecture
