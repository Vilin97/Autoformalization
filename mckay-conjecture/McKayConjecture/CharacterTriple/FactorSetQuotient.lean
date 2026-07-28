/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedRescale
import McKayConjecture.CharacterTriple.ProjectiveQuotientDescent

/-!
# Descent of projective factor sets to quotients

Let `N ◁ G`.  If the factor of a projective representation is one whenever
either argument lies in `N`, then it depends only on the two cosets modulo
`N`.  This file packages the descended cocycle as an actual `FactorSet` on
`G ⧸ N`.

Unlike `ProjectiveRepresentation.quotientDescent`, no hypothesis that the
operators themselves are trivial on `N` is needed.  This distinction is
essential for a projective representation associated with a character
triple: its factor descends through the normal subgroup, while its operators
restrict there to the nontrivial representation affording the normal
character.
-/

noncomputable section

universe u v w

namespace McKayConjecture
namespace CharacterTriple

namespace FactorSet

variable {G₀ : Type w} {C : Type u}
variable [Group G₀] [CommGroup C]
variable {α : FactorSet G₀ C}
variable {N₀ : Subgroup G₀} [N₀.Normal]

/-- A factor set is quotient-compatible with a normal subgroup when it is
one whenever either argument belongs to that subgroup. -/
structure IsQuotientCompatible
    (α : FactorSet G₀ C) (N₀ : Subgroup G₀) : Prop where
  factor_normal_left :
    ∀ (n : N₀) (g : G₀), α (n : G₀) g = 1
  factor_normal_right :
    ∀ (g : G₀) (n : N₀), α g (n : G₀) = 1

omit [N₀.Normal] in
/-- Multiplication of the second input by a normal element leaves a
quotient-compatible factor unchanged. -/
theorem IsQuotientCompatible.factor_mul_normal_right
    (hα : α.IsQuotientCompatible N₀)
    (g k : G₀) (n : N₀) :
    α g (k * (n : G₀)) = α g k := by
  have hcocycle := α.cocycle g k (n : G₀)
  rw [hα.factor_normal_right (g * k) n,
    hα.factor_normal_right k n, one_mul, one_mul] at hcocycle
  exact hcocycle.symm

/-- Multiplication of the first input by a normal element leaves a
quotient-compatible factor unchanged. -/
theorem IsQuotientCompatible.factor_mul_normal_left
    (hα : α.IsQuotientCompatible N₀)
    (g k : G₀) (n : N₀) :
    α (g * (n : G₀)) k = α g k := by
  let conjugate : N₀ :=
    ⟨k⁻¹ * (n : G₀) * k,
      by
        simpa using
          (inferInstance : N₀.Normal).conj_mem
            (n : G₀) n.property k⁻¹⟩
  have hconjugate :
      (n : G₀) * k = k * (conjugate : G₀) := by
    dsimp [conjugate]
    group
  have hcocycle := α.cocycle g (n : G₀) k
  rw [hα.factor_normal_right g n,
    hα.factor_normal_left n k, mul_one, one_mul,
    hconjugate,
    hα.factor_mul_normal_right g k conjugate] at hcocycle
  exact hcocycle

/-- A quotient-compatible factor depends only on its two quotient cosets. -/
theorem IsQuotientCompatible.factor_eq_of_mk_eq
    (hα : α.IsQuotientCompatible N₀)
    {g g' k k' : G₀}
    (hgg' :
      QuotientGroup.mk' N₀ g =
        QuotientGroup.mk' N₀ g')
    (hkk' :
      QuotientGroup.mk' N₀ k =
        QuotientGroup.mk' N₀ k') :
    α g k = α g' k' := by
  obtain ⟨n, hn, hgn⟩ :=
    (QuotientGroup.mk'_eq_mk' (N := N₀)).mp hgg'
  obtain ⟨m, hm, hkm⟩ :=
    (QuotientGroup.mk'_eq_mk' (N := N₀)).mp hkk'
  let nN : N₀ := ⟨n, hn⟩
  let mN : N₀ := ⟨m, hm⟩
  calc
    α g k =
        α (g * (nN : G₀)) k :=
      (hα.factor_mul_normal_left g k nN).symm
    _ = α g' k := by rw [hgn]
    _ =
        α g' (k * (mN : G₀)) :=
      (hα.factor_mul_normal_right g' k mN).symm
    _ = α g' k' := by rw [hkm]

/-- Descent of a quotient-compatible factor set to the quotient group. -/
def quotient
    (α : FactorSet G₀ C)
    (hα : α.IsQuotientCompatible N₀) :
    FactorSet (G₀ ⧸ N₀) C where
  toFun q r :=
    α (ProjectiveRepresentation.quotientRepresentative N₀ q)
      (ProjectiveRepresentation.quotientRepresentative N₀ r)
  cocycle' q r s := by
    let rep :=
      ProjectiveRepresentation.quotientRepresentative N₀
    change
      α (rep (q * r)) (rep s) *
          α (rep q) (rep r) =
        α (rep r) (rep s) *
          α (rep q) (rep (r * s))
    calc
      α (rep (q * r)) (rep s) *
          α (rep q) (rep r) =
        α (rep q * rep r) (rep s) *
          α (rep q) (rep r) := by
            congr 1
            apply hα.factor_eq_of_mk_eq
            · calc
                QuotientGroup.mk' N₀ (rep (q * r)) =
                    q * r :=
                  ProjectiveRepresentation.mk_quotientRepresentative
                    N₀ (q * r)
                _ =
                    QuotientGroup.mk' N₀ (rep q) *
                      QuotientGroup.mk' N₀ (rep r) := by
                  rw [ProjectiveRepresentation.mk_quotientRepresentative,
                    ProjectiveRepresentation.mk_quotientRepresentative]
                _ =
                    QuotientGroup.mk' N₀ (rep q * rep r) :=
                  ((QuotientGroup.mk' N₀).map_mul _ _).symm
            · rfl
      _ =
        α (rep r) (rep s) *
          α (rep q) (rep r * rep s) :=
        α.cocycle (rep q) (rep r) (rep s)
      _ =
        α (rep r) (rep s) *
          α (rep q) (rep (r * s)) := by
            congr 1
            apply hα.factor_eq_of_mk_eq
            · rfl
            · calc
                QuotientGroup.mk' N₀ (rep r * rep s) =
                    QuotientGroup.mk' N₀ (rep r) *
                      QuotientGroup.mk' N₀ (rep s) :=
                  (QuotientGroup.mk' N₀).map_mul _ _
                _ = r * s := by
                  rw [ProjectiveRepresentation.mk_quotientRepresentative,
                    ProjectiveRepresentation.mk_quotientRepresentative]
                _ =
                    QuotientGroup.mk' N₀ (rep (r * s)) :=
                  (ProjectiveRepresentation.mk_quotientRepresentative
                    N₀ (r * s)).symm

@[simp]
theorem quotient_apply
    (hα : α.IsQuotientCompatible N₀)
    (q r : G₀ ⧸ N₀) :
    α.quotient hα q r =
      α (ProjectiveRepresentation.quotientRepresentative N₀ q)
        (ProjectiveRepresentation.quotientRepresentative N₀ r) :=
  rfl

/-- Pullback of the quotient factor recovers the original factor. -/
@[simp]
theorem quotient_mk
    (hα : α.IsQuotientCompatible N₀)
    (g h : G₀) :
    α.quotient hα
        (QuotientGroup.mk' N₀ g)
        (QuotientGroup.mk' N₀ h) =
      α g h := by
  exact hα.factor_eq_of_mk_eq
    (ProjectiveRepresentation.mk_quotientRepresentative
      N₀ (QuotientGroup.mk' N₀ g))
    (ProjectiveRepresentation.mk_quotientRepresentative
      N₀ (QuotientGroup.mk' N₀ h))

/-- A normalized quotient-compatible factor descends to a normalized
factor set. -/
theorem quotient_isNormalized
    (hα : α.IsQuotientCompatible N₀)
    (hnormalized : α.IsNormalized) :
    (α.quotient hα).IsNormalized := by
  rw [isNormalized_iff_value_one_one]
  simpa using
    (α.quotient_mk hα (1 : G₀) (1 : G₀)).trans
      (hnormalized.1 1)

end FactorSet

namespace ProjectiveRepresentation

variable {K : Type u} {V : Type v} {G : Type w}
variable [Field K] [AddCommGroup V] [Module K V]
variable [Group G] [Nontrivial V]
variable {P : ProjectiveRepresentation K G V}
variable {N : Subgroup G} [N.Normal]

omit [N.Normal] in
/-- The quotient compatibility of a projective factor, regarded as a
property of its bundled factor set. -/
theorem FactorIsQuotientCompatible.toFactorSet
    (hP : P.FactorIsQuotientCompatible N) :
    P.factorSet.IsQuotientCompatible N where
  factor_normal_left := hP.factor_normal_left
  factor_normal_right := hP.factor_normal_right

/-- The factor set on the quotient obtained from any projective factor that
is trivial when one input belongs to the normal subgroup. -/
def quotientFactorSet
    (hP : P.FactorIsQuotientCompatible N) :
    FactorSet (G ⧸ N) Kˣ where
  toFun := P.quotientFactor N
  cocycle' q r s := by
    change
      P.factor
            (quotientRepresentative N (q * r))
            (quotientRepresentative N s) *
          P.factor
            (quotientRepresentative N q)
            (quotientRepresentative N r) =
        P.factor
            (quotientRepresentative N r)
            (quotientRepresentative N s) *
          P.factor
            (quotientRepresentative N q)
            (quotientRepresentative N (r * s))
    calc
      P.factor
            (quotientRepresentative N (q * r))
            (quotientRepresentative N s) *
          P.factor
            (quotientRepresentative N q)
            (quotientRepresentative N r) =
        P.factor
            (quotientRepresentative N q *
              quotientRepresentative N r)
            (quotientRepresentative N s) *
          P.factor
            (quotientRepresentative N q)
            (quotientRepresentative N r) := by
              congr 1
              apply hP.factor_eq_of_mk_eq
              · calc
                  QuotientGroup.mk' N
                        (quotientRepresentative N (q * r)) =
                      q * r :=
                    mk_quotientRepresentative N (q * r)
                  _ =
                      QuotientGroup.mk' N
                          (quotientRepresentative N q) *
                        QuotientGroup.mk' N
                          (quotientRepresentative N r) := by
                    rw [mk_quotientRepresentative,
                      mk_quotientRepresentative]
                  _ =
                      QuotientGroup.mk' N
                        (quotientRepresentative N q *
                          quotientRepresentative N r) :=
                    ((QuotientGroup.mk' N).map_mul _ _).symm
              · rfl
      _ =
        P.factor
            (quotientRepresentative N r)
            (quotientRepresentative N s) *
          P.factor
            (quotientRepresentative N q)
            (quotientRepresentative N r *
              quotientRepresentative N s) :=
        P.factor_cocycle
          (quotientRepresentative N q)
          (quotientRepresentative N r)
          (quotientRepresentative N s)
      _ =
        P.factor
            (quotientRepresentative N r)
            (quotientRepresentative N s) *
          P.factor
            (quotientRepresentative N q)
            (quotientRepresentative N (r * s)) := by
              congr 1
              apply hP.factor_eq_of_mk_eq
              · rfl
              · calc
                  QuotientGroup.mk' N
                        (quotientRepresentative N r *
                          quotientRepresentative N s) =
                      QuotientGroup.mk' N
                          (quotientRepresentative N r) *
                        QuotientGroup.mk' N
                          (quotientRepresentative N s) :=
                    (QuotientGroup.mk' N).map_mul _ _
                  _ = r * s := by
                    rw [mk_quotientRepresentative,
                      mk_quotientRepresentative]
                  _ =
                      QuotientGroup.mk' N
                        (quotientRepresentative N (r * s)) :=
                    (mk_quotientRepresentative N (r * s)).symm

@[simp]
theorem quotientFactorSet_apply
    (hP : P.FactorIsQuotientCompatible N)
    (q r : G ⧸ N) :
    P.quotientFactorSet hP q r =
      P.factor (quotientRepresentative N q)
        (quotientRepresentative N r) :=
  rfl

/-- Pulling the descended factor set back along the quotient map recovers
the original factor exactly. -/
@[simp]
theorem quotientFactorSet_mk
    (hP : P.FactorIsQuotientCompatible N)
    (g h : G) :
    P.quotientFactorSet hP
        (QuotientGroup.mk' N g)
        (QuotientGroup.mk' N h) =
      P.factor g h := by
  change
    P.factor
        (quotientRepresentative N
          (QuotientGroup.mk' N g))
        (quotientRepresentative N
          (QuotientGroup.mk' N h)) =
      P.factor g h
  exact hP.factor_eq_of_mk_eq
    (mk_quotientRepresentative N
      (QuotientGroup.mk' N g))
    (mk_quotientRepresentative N
      (QuotientGroup.mk' N h))

/-- Normalization descends from the original projective representation to
its quotient factor set. -/
theorem quotientFactorSet_isNormalized
    (hP : P.FactorIsQuotientCompatible N)
    (hnormalized : P.IsNormalized) :
    (P.quotientFactorSet hP).IsNormalized := by
  rw [FactorSet.isNormalized_iff_value_one_one]
  simpa using
    (P.quotientFactorSet_mk hP (1 : G) (1 : G)).trans
      ((P.factorSet_isNormalized hnormalized).1 1)

end ProjectiveRepresentation

namespace AssociatedProjectiveRepresentation

variable {A : Type w} [Group A] [Finite A]
variable {T : CharacterTriple A}
variable {W : Type}
variable [AddCommGroup W] [Module ℂ W]
variable [Module.Finite ℂ W] [Nontrivial W]
variable {Q : ProjectiveRepresentation ℂ A W}

/-- The factor of an associated projective representation is trivial as
soon as either argument belongs to the normal subgroup of its character
triple. -/
theorem factorIsQuotientCompatible
    (R : AssociatedProjectiveRepresentation T W Q) :
    Q.FactorIsQuotientCompatible T.normalSubgroup where
  factor_normal_left := R.factor_normal_left
  factor_normal_right := R.factor_normal_right

/-- The factor set of an associated projective representation, descended
to the outer quotient of its character triple. -/
def quotientFactorSet
    (R : AssociatedProjectiveRepresentation T W Q) :
    FactorSet (A ⧸ T.normalSubgroup) ℂˣ :=
  Q.quotientFactorSet R.factorIsQuotientCompatible

@[simp]
theorem quotientFactorSet_mk
    (R : AssociatedProjectiveRepresentation T W Q)
    (a b : A) :
    R.quotientFactorSet
        (QuotientGroup.mk' T.normalSubgroup a)
        (QuotientGroup.mk' T.normalSubgroup b) =
      Q.factor a b :=
  Q.quotientFactorSet_mk R.factorIsQuotientCompatible a b

/-- The descended factor set of an associated projective representation is
normalized. -/
theorem quotientFactorSet_isNormalized
    (R : AssociatedProjectiveRepresentation T W Q) :
    R.quotientFactorSet.IsNormalized :=
  Q.quotientFactorSet_isNormalized
    R.factorIsQuotientCompatible R.isNormalized

end AssociatedProjectiveRepresentation

end CharacterTriple
end McKayConjecture
