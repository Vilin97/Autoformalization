/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralScalar
import McKayConjecture.GroupTheory.CoprimeActionFixedPointProduct

/-!
# Faithful invariant characters fix the center

Let a group `P` act on a group `A`, and let `χ` be an irreducible complex
character of `A`.  If `χ` is invariant under the action and its chosen
realization is faithful, then `P` fixes `Z(A)` pointwise.

Indeed, Schur's lemma makes the realization operators of `z` and `g • z`
scalar for `z ∈ Z(A)`.  Invariance of the character makes the two scalars
equal, and faithfulness of the realization then gives `g • z = z`.

Combined with the sharp coprime-action criterion from
`CoprimeActionFixedPointProduct`, this supplies the centralizer containment
needed for the fixed-point-product restriction seam.  Faithfulness is stated
for the chosen realization; equivalently, its representation homomorphism is
injective.
-/

noncomputable section

namespace McKayConjecture
namespace IrreducibleCharacter

universe u v

variable {P : Type u} {A : Type v}
variable [Group P] [Group A] [MulDistribMulAction P A]

/-- An irreducible character is faithful when its chosen realization is a
faithful representation. -/
def IsFaithful (χ : IrreducibleCharacter A) : Prop :=
  Function.Injective χ.realization.ρ

/-- Invariance of an irreducible character under a group action, expressed
directly on character values. -/
def IsInvariantUnderAction
    (χ : IrreducibleCharacter A) : Prop :=
  ∀ (g : P) (a : A),
    χ.values (g • a) = χ.values a

/-- Automorphisms preserve the center. -/
private theorem action_mem_center
    (g : P) {z : A}
    (hz : z ∈ Subgroup.center A) :
    g • z ∈ Subgroup.center A := by
  have hfixed :=
    Subgroup.centerCharacteristic.fixed
      (GroupTheory.actionHom P A g)
  have hzComap :
      z ∈ Subgroup.comap
        (GroupTheory.actionHom P A g).toMonoidHom
        (Subgroup.center A) := by
    rw [hfixed]
    exact hz
  exact hzComap

/-- A faithful action-invariant irreducible character forces the acting
group to fix the center pointwise. -/
theorem center_le_fixedPoints_of_isFaithful_isInvariantUnderAction
    (χ : IrreducibleCharacter A)
    (hfaithful : χ.IsFaithful)
    (hinvariant : IsInvariantUnderAction (P := P) χ) :
    Subgroup.center A ≤ FixedPoints.subgroup P A := by
  intro z hz
  apply MulAction.mem_fixedPoints.mpr
  intro g
  have hgz : g • z ∈ Subgroup.center A :=
    action_mem_center g hz
  obtain ⟨c, hc⟩ :=
    χ.exists_realization_scalar_of_mem_center z hz
  obtain ⟨d, hd⟩ :=
    χ.exists_realization_scalar_of_mem_center (g • z) hgz
  have hscalarValues :
      d * (χ.degree : ℂ) =
        c * (χ.degree : ℂ) := by
    rw [← χ.values_eq_scalar_mul_degree (g • z) d hd,
      ← χ.values_eq_scalar_mul_degree z c hc]
    exact hinvariant g z
  have hdc : d = c :=
    mul_right_cancel₀
      (Nat.cast_ne_zero.mpr χ.degree_ne_zero)
      hscalarValues
  apply hfaithful
  rw [hd, hc, hdc]

/-- A faithful invariant irreducible character discharges the exact
centralizer condition for the coprime-action fixed-point product. -/
theorem centralizer_actionKernel_le_fixedPointProduct_range_of_faithful_invariant
    {p : ℕ}
    (hP : IsPGroup p P)
    (hA : GroupTheory.IsPPrimeGroup p A)
    (χ : IrreducibleCharacter A)
    (hfaithful : χ.IsFaithful)
    (hinvariant : IsInvariantUnderAction (P := P) χ) :
    Subgroup.centralizer
          (GroupTheory.actionKernel P A :
            Set (GroupTheory.actionSemidirectProduct P A)) ≤
        MonoidHom.range
          (GroupTheory.actionFixedPointProductEmbedding P A) :=
  GroupTheory.centralizer_actionKernel_le_fixedPointProduct_range
    P A hP hA
      (χ.center_le_fixedPoints_of_isFaithful_isInvariantUnderAction
        hfaithful hinvariant)

end IrreducibleCharacter
end McKayConjecture
