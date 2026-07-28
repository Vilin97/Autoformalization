/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedFiniteFactorNormalizerRestriction
import McKayConjecture.GroupTheory.CentralIndexQuotient

/-!
# A sharper central-index bound for associated factor extensions

The usual central-extension estimate bounds the central index of a
factor-set extension by the order of its base group.  For a factor obtained
from an associated projective representation, the center of the ambient
character-triple group gives a larger central subgroup upstairs.

Indeed, an ambient-central element acts by a scalar on the irreducible
normal-subgroup representation.  Its projective factor is therefore
symmetric with every other element.  The full preimage of the image of the
ambient center in the outer quotient is consequently central in the finite
factor extension.  This sharpens the bound from `|A / N|` to
`|A / (N Z(A))|`.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace AssociatedProjectiveRepresentation

open GroupTheory

variable {A : Type} [Group A] [Finite A]
variable {T : CharacterTriple A}
variable {V : Type}
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}

namespace AssociatedFiniteFactorNormalization

variable (R : AssociatedProjectiveRepresentation T V P)

/-- The finite factor of an associated lift is symmetric when one argument
is ambient-central. -/
theorem factorSet_comm_of_mem_center
    (F : AssociatedFiniteFactorNormalization R)
    (z a : A)
    (hz : z ∈ Subgroup.center A) :
    F.factorSet z a = F.factorSet a z := by
  apply Subtype.ext
  rw [F.factorSet_coe, F.factorSet_coe]
  apply scalarLinearEquiv_injective ℂ V
  have hzCentralizer :
      z ∈ Subgroup.centralizer
        (T.normalSubgroup : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact Subgroup.mem_center_iff.mp hz n
  obtain ⟨c, hc⟩ :=
    F.associated.operator_centralizer_isScalar
      z hzCentralizer
  have hza : z * a = a * z :=
    (Subgroup.mem_center_iff.mp hz a).symm
  apply mul_right_cancel
  calc
    scalarLinearEquiv ℂ V
          (F.projective.factor z a) *
        F.projective.operator (z * a) =
      F.projective.operator z *
        F.projective.operator a := by
          rw [F.projective.map_mul]
    _ =
      F.projective.operator a *
        F.projective.operator z := by
          rw [hc, scalarLinearEquiv_comm]
    _ =
      scalarLinearEquiv ℂ V
          (F.projective.factor a z) *
        F.projective.operator (a * z) :=
      F.projective.map_mul a z
    _ =
      scalarLinearEquiv ℂ V
          (F.projective.factor a z) *
        F.projective.operator (z * a) := by
          rw [hza]

/-- The descended finite factor is symmetric on the image of the ambient
center in the character-triple quotient. -/
theorem finiteQuotientFactorSet_comm_of_mem_map_center
    (F : AssociatedFiniteFactorNormalization R)
    (q r : A ⧸ T.normalSubgroup)
    (hq :
      q ∈
        (Subgroup.center A).map
          (QuotientGroup.mk' T.normalSubgroup)) :
    F.finiteQuotientFactorSet R q r =
      F.finiteQuotientFactorSet R r q := by
  obtain ⟨z, hz, rfl⟩ := hq
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective T.normalSubgroup r
  rw [F.finiteQuotientFactorSet_mk,
    F.finiteQuotientFactorSet_mk]
  exact F.factorSet_comm_of_mem_center R z a hz

/-- The full preimage of the image of the ambient center is central in the
finite quotient-factor extension. -/
theorem comap_map_center_le_factorExtension_center
    (F : AssociatedFiniteFactorNormalization R) :
    ((Subgroup.center A).map
        (QuotientGroup.mk' T.normalSubgroup)).comap
          (FactorSet.CentralExtensionGroup.projection
            (F.finiteQuotientFactorSet R)
            (F.finiteQuotientFactorSet_isNormalized R)) ≤
      Subgroup.center (F.FiniteFactorCentralExtensionGroup R) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply FactorSet.CentralExtensionGroup.ext
  · exact
      Subgroup.mem_center_iff.mp
        (map_center_quotient_le_center
          T.normalSubgroup hx)
        (FactorSet.CentralExtensionGroup.base
          (F.finiteQuotientFactorSet R)
          (F.finiteQuotientFactorSet_isNormalized R) y)
  · simp only [FactorSet.CentralExtensionGroup.coefficient_mul]
    rw [F.finiteQuotientFactorSet_comm_of_mem_map_center
      R
      (FactorSet.CentralExtensionGroup.base
        (F.finiteQuotientFactorSet R)
        (F.finiteQuotientFactorSet_isNormalized R) x)
      (FactorSet.CentralExtensionGroup.base
        (F.finiteQuotientFactorSet R)
        (F.finiteQuotientFactorSet_isNormalized R) y)
      hx]
    ac_rfl

/-- The central index of an associated finite factor extension is bounded
by the quotient after adjoining the ambient center to the normal subgroup. -/
theorem finiteFactorCentralExtension_centralIndex_le_card_quotient_sup_center
    (F : AssociatedFiniteFactorNormalization R) :
    centralIndex (F.FiniteFactorCentralExtensionGroup R) ≤
      Nat.card
        (A ⧸ (T.normalSubgroup ⊔ Subgroup.center A)) := by
  let alpha := F.finiteQuotientFactorSet R
  let hAlpha := F.finiteQuotientFactorSet_isNormalized R
  let pi :=
    FactorSet.CentralExtensionGroup.projection alpha hAlpha
  let Zbar :=
    (Subgroup.center A).map
      (QuotientGroup.mk' T.normalSubgroup)
  calc
    centralIndex (F.FiniteFactorCentralExtensionGroup R) =
        (Subgroup.center
          (F.FiniteFactorCentralExtensionGroup R)).index :=
      centralIndex_eq_center_index
        (F.FiniteFactorCentralExtensionGroup R)
    _ ≤ (Zbar.comap pi).index :=
      Subgroup.index_antitone
        (F.comap_map_center_le_factorExtension_center R)
    _ = Zbar.index :=
      Zbar.index_comap_of_surjective
        (FactorSet.CentralExtensionGroup.projection_surjective
          alpha hAlpha)
    _ = (T.normalSubgroup ⊔ Subgroup.center A).index :=
      index_map_center_quotient T.normalSubgroup
    _ =
        Nat.card
          (A ⧸ (T.normalSubgroup ⊔ Subgroup.center A)) :=
      rfl

/-- In particular, the finite factor extension has central index no larger
than that of the ambient character-triple group. -/
theorem finiteFactorCentralExtension_centralIndex_le
    (F : AssociatedFiniteFactorNormalization R) :
    centralIndex (F.FiniteFactorCentralExtensionGroup R) ≤
      centralIndex A :=
  (F.finiteFactorCentralExtension_centralIndex_le_card_quotient_sup_center
    R).trans
      (card_quotient_sup_center_le_centralIndex
        T.normalSubgroup)

/-- If the distinguished normal subgroup is noncentral, the associated
finite factor extension has strictly smaller central index than the ambient
character-triple group. -/
theorem finiteFactorCentralExtension_centralIndex_lt
    (F : AssociatedFiniteFactorNormalization R)
    (hTnoncentral :
      ¬T.normalSubgroup ≤ Subgroup.center A) :
    centralIndex (F.FiniteFactorCentralExtensionGroup R) <
      centralIndex A :=
  (F.finiteFactorCentralExtension_centralIndex_le_card_quotient_sup_center
    R).trans_lt
      ((card_quotient_sup_center_lt_centralIndex_iff
        (G := A) T.normalSubgroup).mpr hTnoncentral)

end AssociatedFiniteFactorNormalization
end AssociatedProjectiveRepresentation
end CharacterTriple
end McKayConjecture
