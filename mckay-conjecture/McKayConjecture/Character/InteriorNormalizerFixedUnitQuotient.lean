/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InteriorFaithfulNormalizerAction
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The fixed-unit quotient of an interior normalizer

For a faithful interior action, the units of the fixed algebra are
exactly the kernel of the normalizer action on the interior group.
Consequently their image is normal in the interior unit normalizer,
and the quotient is canonically isomorphic to the subgroup of
`Aut(P)` induced by normalizer conjugation.

This identifies the group-theoretic quotient that occurs in the
Puig--Turull fixed-unit character-extension problem.  In particular,
it is controlled by `Aut(P)`, but it is not in general a `p`-group.
-/

noncomputable section

namespace Representation
namespace InteriorAction

variable {p : ℕ}
variable {k P A : Type}
variable [CommRing k] [Group P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

variable (I : InteriorAction (P := P) (A := A))

/-- The image of the fixed-algebra units in the interior unit
normalizer. -/
abbrev fixedUnitRange : Subgroup I.unitNormalizer :=
  (I.fixedUnitToNormalizer (k := k)).range

/-- The inclusion of fixed-algebra units into the interior unit
normalizer is injective. -/
theorem fixedUnitToNormalizer_injective :
    Function.Injective
      (I.fixedUnitToNormalizer (k := k)) := by
  intro u v huv
  apply Units.ext
  apply Subtype.ext
  exact congrArg
    (fun s : I.unitNormalizer => (((s : Aˣ) : A)))
    huv

/-- A normalizer unit centralizing every implementing unit can be
regarded as a unit of the fixed algebra. -/
def unitNormalizerToFixedUnitOfCentralizes
    (s : I.unitNormalizer)
    (hs : ∀ g : P, Commute (s : Aˣ) (I.unit g)) :
    (fixedSubalgebra (k := k) (P := P) (A := A))ˣ where
  val :=
    ⟨((s : Aˣ) : A), fun g => by
      rw [I.smul_eq]
      have hcomm :
          Commute (((s : Aˣ) : A)) ((I.unit g : Aˣ) : A) :=
        (hs g).map (Units.coeHom A)
      rw [hcomm.eq.symm, mul_assoc]
      simp⟩
  inv :=
    ⟨(((s : Aˣ)⁻¹ : Aˣ) : A), fun g => by
      rw [I.smul_eq]
      have hcomm :
          Commute ((((s : Aˣ)⁻¹ : Aˣ) : A))
            ((I.unit g : Aˣ) : A) :=
        (hs g).inv_left.map (Units.coeHom A)
      rw [hcomm.eq.symm, mul_assoc]
      simp⟩
  val_inv := by
    apply Subtype.ext
    simp
  inv_val := by
    apply Subtype.ext
    simp

@[simp]
theorem fixedUnitToNormalizer_unitNormalizerToFixedUnitOfCentralizes
    (s : I.unitNormalizer)
    (hs : ∀ g : P, Commute (s : Aˣ) (I.unit g)) :
    I.fixedUnitToNormalizer (k := k)
        (I.unitNormalizerToFixedUnitOfCentralizes s hs) =
      s := by
  apply Subtype.ext
  apply Units.ext
  rfl

/-- Membership in the fixed-unit image is equivalent to centralizing
the implementing units. -/
theorem mem_fixedUnitRange_iff
    (s : I.unitNormalizer) :
    s ∈ I.fixedUnitRange (k := k) ↔
      ∀ g : P, Commute (s : Aˣ) (I.unit g) := by
  constructor
  · rintro ⟨u, rfl⟩ g
    exact I.fixedUnitToAmbient_mul_unit (k := k) u g
  · intro hs
    exact
      ⟨I.unitNormalizerToFixedUnitOfCentralizes s hs,
        I.fixedUnitToNormalizer_unitNormalizerToFixedUnitOfCentralizes
          s hs⟩

/-- For a faithful interior action, a normalizer unit acts trivially
on `P` exactly when it comes from a fixed-algebra unit. -/
theorem mem_faithfulNormalizerAction_ker_iff
    (hI : Function.Injective I.unit)
    (s : I.unitNormalizer) :
    s ∈ (I.faithfulNormalizerAction hI).ker ↔
      ∀ g : P, Commute (s : Aˣ) (I.unit g) := by
  constructor
  · intro hs g
    have hs' :
        I.normalizerMulAut hI s = 1 :=
      hs
    have hconj :=
      I.unit_normalizerMulAut hI s g
    rw [hs'] at hconj
    change
      I.unit g =
        (s : Aˣ) * I.unit g * (s : Aˣ)⁻¹ at hconj
    calc
      (s : Aˣ) * I.unit g =
          ((s : Aˣ) * I.unit g * (s : Aˣ)⁻¹) *
            (s : Aˣ) := by simp [mul_assoc]
      _ = I.unit g * (s : Aˣ) := by rw [← hconj]
  · intro hs
    change I.normalizerMulAut hI s = 1
    apply MulEquiv.ext
    intro g
    apply hI
    rw [I.unit_normalizerMulAut]
    change
      (s : Aˣ) * I.unit g * (s : Aˣ)⁻¹ =
        I.unit g
    rw [(hs g).eq, mul_assoc]
    simp

/-- The fixed-unit image is the kernel of the faithful normalizer
action on `P`. -/
theorem fixedUnitRange_eq_faithfulNormalizerAction_ker
    (hI : Function.Injective I.unit) :
    I.fixedUnitRange (k := k) =
      (I.faithfulNormalizerAction hI).ker := by
  ext s
  rw [I.mem_fixedUnitRange_iff,
    I.mem_faithfulNormalizerAction_ker_iff hI]

/-- The image of the fixed-algebra units is normal in the interior
unit normalizer when the interior action is faithful. -/
theorem fixedUnitRange_normal
    (hI : Function.Injective I.unit) :
    (I.fixedUnitRange (k := k)).Normal := by
  rw [I.fixedUnitRange_eq_faithfulNormalizerAction_ker hI]
  infer_instance

/-- The quotient of the interior unit normalizer by the fixed-unit
image is the subgroup of `Aut(P)` induced by normalizer conjugation. -/
def fixedUnitQuotientMulEquivNormalizerActionRange
    (hI : Function.Injective I.unit) :
    letI : (I.fixedUnitRange (k := k)).Normal :=
      I.fixedUnitRange_normal hI
    I.unitNormalizer ⧸ I.fixedUnitRange (k := k) ≃*
      (I.faithfulNormalizerAction hI).range := by
  letI : (I.fixedUnitRange (k := k)).Normal :=
    I.fixedUnitRange_normal hI
  exact
    (QuotientGroup.quotientMulEquivOfEq
      (I.fixedUnitRange_eq_faithfulNormalizerAction_ker hI)).trans
        (QuotientGroup.quotientKerEquivRange
          (I.faithfulNormalizerAction hI))

/-- The fixed-unit quotient is a `p`-group exactly when the induced
normalizer subgroup of `Aut(P)` is a `p`-group. -/
theorem isPGroup_fixedUnitQuotient_iff_normalizerActionRange
    (hI : Function.Injective I.unit) :
    letI : (I.fixedUnitRange (k := k)).Normal :=
      I.fixedUnitRange_normal hI
    IsPGroup p
        (I.unitNormalizer ⧸ I.fixedUnitRange (k := k)) ↔
      IsPGroup p (I.faithfulNormalizerAction hI).range := by
  letI : (I.fixedUnitRange (k := k)).Normal :=
    I.fixedUnitRange_normal hI
  let e :=
    I.fixedUnitQuotientMulEquivNormalizerActionRange
      (k := k) hI
  exact
    ⟨fun h => h.of_equiv e,
      fun h => h.of_equiv e.symm⟩

/-- A useful sufficient condition: if `Aut(P)` itself is a `p`-group,
then so is the fixed-unit quotient. -/
theorem isPGroup_fixedUnitQuotient_of_mulAut
    (hI : Function.Injective I.unit)
    (hAut : IsPGroup p (MulAut P)) :
    letI : (I.fixedUnitRange (k := k)).Normal :=
      I.fixedUnitRange_normal hI
    IsPGroup p
      (I.unitNormalizer ⧸ I.fixedUnitRange (k := k)) := by
  letI : (I.fixedUnitRange (k := k)).Normal :=
    I.fixedUnitRange_normal hI
  apply
    (I.isPGroup_fixedUnitQuotient_iff_normalizerActionRange
      (p := p) hI).2
  exact hAut.to_subgroup _

end InteriorAction
end Representation
