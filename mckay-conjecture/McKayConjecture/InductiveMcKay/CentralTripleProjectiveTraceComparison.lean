/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveComparison

/-!
# Projective comparisons from normalized traces

For two associated projective representations with matching factor sets,
the remaining scalar condition in a central character-triple comparison can
be checked numerically.  Schur's lemma makes both operators over matched
centralizer elements scalar.  Equality of their normalized traces then
forces those two nonzero scalars to coincide.

This file packages that argument as a constructor for
`CompleteCentralProjectiveComparisonData`.  It is particularly useful in the
central-intersection step: a Dade--Glauberman--Nagao construction may supply
the common factor set and a cross-multiplied trace identity without choosing
the common scalar separately.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple

variable {A B : Type}
variable [Group A] [Finite A] [Group B] [Finite B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {e : B →* A}

namespace CentralRestrictionGroupData

/-- If an embedded right element centralizes the left normal subgroup, then
the original right element centralizes the right normal subgroup.

Only injectivity of the embedding and the exact intersection condition are
needed, but stating the lemma on `CentralRestrictionGroupData` gives the
form used by projective-comparison constructors. -/
theorem mem_rightCentralizer_of_embedding_mem_leftCentralizer
    (g : CentralRestrictionGroupData T U e)
    (b : B)
    (hb :
      e b ∈
        Subgroup.centralizer
          (T.normalSubgroup : Set A)) :
    b ∈
      Subgroup.centralizer
        (U.normalSubgroup : Set B) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  apply g.embedding_injective
  have hey :
      e y ∈ T.normalSubgroup := by
    have hmap :
        e y ∈ U.normalSubgroup.map e :=
      ⟨y, hy, rfl⟩
    have hmapInf :
        e y ∈
          T.normalSubgroup ⊓
            MonoidHom.range e := by
      rw [g.intersection_eq]
      exact hmap
    exact hmapInf.1
  simpa using
    (Subgroup.mem_centralizer_iff.mp hb)
      (e y) hey

end CentralRestrictionGroupData

namespace CompleteCentralProjectiveComparisonData

variable {V W : Type}
variable [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W]
  [Module.Finite ℂ W] [Nontrivial W]
variable {P : ProjectiveRepresentation ℂ A V}
variable {Q : ProjectiveRepresentation ℂ B W}

/-- Two scalar projective operators have the same scalar when their
normalized traces agree.

The equality is cross-multiplied by the two dimensions, so it does not use
division in `ℂ`. -/
theorem exists_common_scalar_of_trace_cross
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (a : A) (b : B)
    (ha :
      a ∈
        Subgroup.centralizer
          (T.normalSubgroup : Set A))
    (hb :
      b ∈
        Subgroup.centralizer
          (U.normalSubgroup : Set B))
    (htrace :
      LinearMap.trace ℂ V
            (P.operator a : V →ₗ[ℂ] V) *
          (Module.finrank ℂ W : ℂ) =
        LinearMap.trace ℂ W
            (Q.operator b : W →ₗ[ℂ] W) *
          (Module.finrank ℂ V : ℂ)) :
    ∃ c : ℂˣ,
      P.operator a =
          scalarLinearEquiv ℂ V c ∧
        Q.operator b =
          scalarLinearEquiv ℂ W c := by
  obtain ⟨c, hc⟩ :=
    R.operator_centralizer_isScalar a ha
  obtain ⟨d, hd⟩ :=
    S.operator_centralizer_isScalar b hb
  have hleftTrace :
      LinearMap.trace ℂ V
          (P.operator a : V →ₗ[ℂ] V) =
        (c : ℂ) *
          (Module.finrank ℂ V : ℂ) := by
    rw [hc]
    have hscalar :
        ((scalarLinearEquiv ℂ V c :
            V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) =
          (c : ℂ) •
            (LinearMap.id : Module.End ℂ V) := by
      ext v
      simp
    rw [hscalar, map_smul, LinearMap.trace_id]
    rfl
  have hrightTrace :
      LinearMap.trace ℂ W
          (Q.operator b : W →ₗ[ℂ] W) =
        (d : ℂ) *
          (Module.finrank ℂ W : ℂ) := by
    rw [hd]
    have hscalar :
        ((scalarLinearEquiv ℂ W d :
            W ≃ₗ[ℂ] W) : W →ₗ[ℂ] W) =
          (d : ℂ) •
            (LinearMap.id : Module.End ℂ W) := by
      ext w
      simp
    rw [hscalar, map_smul, LinearMap.trace_id]
    rfl
  rw [hleftTrace, hrightTrace] at htrace
  have hV :
      (Module.finrank ℂ V : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hW :
      (Module.finrank ℂ W : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hcdValue : (c : ℂ) = (d : ℂ) := by
    apply
      mul_left_cancel₀
        (mul_ne_zero hV hW)
    calc
      (Module.finrank ℂ V : ℂ) *
            (Module.finrank ℂ W : ℂ) *
            (c : ℂ) =
          ((c : ℂ) *
              (Module.finrank ℂ V : ℂ)) *
            (Module.finrank ℂ W : ℂ) := by
              ring
      _ =
          ((d : ℂ) *
              (Module.finrank ℂ W : ℂ)) *
            (Module.finrank ℂ V : ℂ) :=
        htrace
      _ =
          (Module.finrank ℂ V : ℂ) *
            (Module.finrank ℂ W : ℂ) *
            (d : ℂ) := by
              ring
  have hcd : c = d :=
    Units.ext hcdValue
  exact
    ⟨c, hc, hcd ▸ hd⟩

/-- Construct the projective part of a central character-triple comparison
from matching factor sets and cross-multiplied normalized traces.

The right-centralizer membership and the common scalar are conclusions.
Thus callers need only provide the two associated lifts, the already-known
ordinary group data, factor agreement, and one numerical trace identity. -/
def ofAssociatedFactorAgreementTraceCross
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (g : CentralRestrictionGroupData T U e)
    (factorAgreement :
      ∀ b c : B,
        P.factor (e b) (e c) =
          Q.factor b c)
    (traceCross :
      ∀ b : B,
        e b ∈
            Subgroup.centralizer
              (T.normalSubgroup : Set A) →
          LinearMap.trace ℂ V
                (P.operator (e b) : V →ₗ[ℂ] V) *
              (Module.finrank ℂ W : ℂ) =
            LinearMap.trace ℂ W
                (Q.operator b : W →ₗ[ℂ] W) *
              (Module.finrank ℂ V : ℂ)) :
    CompleteCentralProjectiveComparisonData
      T U e where
  leftSpace := V
  rightSpace := W
  leftProjective := P
  leftAssociated := R
  rightProjective := Q
  rightAssociated := S
  factor_agreement := factorAgreement
  scalar_agreement := by
    intro b hb
    exact
      exists_common_scalar_of_trace_cross
        R S (e b) b hb
        (g.mem_rightCentralizer_of_embedding_mem_leftCentralizer
          b hb)
        (traceCross b hb)

end CompleteCentralProjectiveComparisonData

end InductiveMcKay
end McKayConjecture
