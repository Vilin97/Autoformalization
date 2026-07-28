/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.TwistedInteriorBrauerGradedCollapse

/-!
# Collapsing twisted Brauer components over an automorphism subgroup

For the normalizer-extension problem one does not need a collapse in
automorphism degrees never induced by a normalizer unit.  This file
sharpens the graded-collapse criterion from all of `Aut(P)` to an
arbitrary subgroup, and then specializes to the image of the faithful
normalizer action.

The resulting datum is still genuinely componentwise: one linear map
is chosen for each *induced automorphism*, it is normalized in degree
one, and it preserves every homogeneous product in the selected
subgroup.  Thus normalizer elements inducing the same automorphism
cannot be assigned unrelated maps.
-/

noncomputable section

namespace Representation
namespace InteriorAction

variable {k P A : Type}
variable [CommRing k] [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

variable (I : InteriorAction (P := P) (A := A))

/-- A normalized multiplicative collapse restricted to a subgroup of
the automorphism grading group. -/
structure TwistedBrauerSubgroupCollapse
    (H : Subgroup (MulAut P)) where
  /-- Linear collapse in a degree belonging to `H`. -/
  map :
    ∀ φ : H,
      I.TwistedBrauerComponent (k := k) (φ : MulAut P) →ₗ[k]
        BrauerQuotientAlgebra (k := k) (P := P) (A := A)
  /-- The identity-degree map is the canonical identification. -/
  map_identity :
    map 1 =
      (I.twistedBrauerIdentityEquiv (k := k)).toLinearMap
  /-- All homogeneous products in degrees from `H` are preserved. -/
  map_mul :
    ∀ (φ ψ : H)
      (x :
        I.TwistedBrauerComponent (k := k) (φ : MulAut P))
      (y :
        I.TwistedBrauerComponent (k := k) (ψ : MulAut P)),
      map (φ * ψ)
          (I.twistedBrauerMul (k := k)
            (φ : MulAut P) (ψ : MulAut P) x y) =
        map φ x * map ψ y

namespace TwistedBrauerSubgroupCollapse

variable {I : InteriorAction (P := P) (A := A)}
variable {H : Subgroup (MulAut P)}

/-- The subgroup identity maps the twisted identity to `1`. -/
@[simp]
theorem map_twistedBrauerOne
    (C : I.TwistedBrauerSubgroupCollapse (k := k) H) :
    C.map 1 (I.twistedBrauerOne (k := k)) = 1 := by
  rw [C.map_identity]
  exact I.twistedBrauerIdentityEquiv_one (k := k)

/-- Subgroup-indexed collapse maps commute with transport between equal
subgroup degrees. -/
@[simp]
theorem map_twistedBrauerComponentEquivOfEq
    (C : I.TwistedBrauerSubgroupCollapse (k := k) H)
    {φ ψ : H}
    (h : φ = ψ)
    (x :
      I.TwistedBrauerComponent (k := k) (φ : MulAut P)) :
    C.map ψ
        (I.twistedBrauerComponentEquivOfEq (k := k)
          (congrArg Subtype.val h) x) =
      C.map φ x := by
  subst ψ
  rfl

/-- Restrict a collapse defined in all automorphism degrees to any
automorphism subgroup. -/
def _root_.Representation.InteriorAction.TwistedBrauerGradedCollapse.restrict
    (C : I.TwistedBrauerGradedCollapse (k := k))
    (H : Subgroup (MulAut P)) :
    I.TwistedBrauerSubgroupCollapse (k := k) H where
  map := fun φ ↦ C.map (φ : MulAut P)
  map_identity := C.map_identity
  map_mul := by
    intro φ ψ x y
    exact C.map_mul (φ : MulAut P) (ψ : MulAut P) x y

/-- The weakest subgroup needed for the normalizer-extension
construction is the image of the faithful normalizer action. -/
abbrev NormalizerActionRangeCollapse
    (hI : Function.Injective I.unit) :=
  I.TwistedBrauerSubgroupCollapse (k := k)
    (I.faithfulNormalizerAction hI).range

/-- A collapse in all automorphism degrees restricts to the strictly
smaller datum over the induced normalizer-action subgroup. -/
theorem nonempty_normalizerActionRangeCollapse_of_nonempty_gradedCollapse
    (hI : Function.Injective I.unit)
    (hcollapse :
      Nonempty (I.TwistedBrauerGradedCollapse (k := k))) :
    Nonempty (NormalizerActionRangeCollapse (I := I) (k := k) hI) :=
  hcollapse.map
    (fun C ↦ C.restrict (I.faithfulNormalizerAction hI).range)

/-- A collapse over the induced normalizer-action subgroup pulls back
to a collapse of the normalizer-graded family. -/
def unitNormalizerGradedFamilyCollapse
    (hI : Function.Injective I.unit)
    (C : NormalizerActionRangeCollapse (I := I) (k := k) hI) :
    GradedMonoidFamily.Collapse
      (TwistedBrauerGradedCollapse.unitNormalizerGradedFamily
        (k := k) hI)
      (BrauerQuotientAlgebra (k := k) (P := P) (A := A)) where
  toFun := fun s ↦
    C.map ((I.faithfulNormalizerAction hI).rangeRestrict s)
  map_one := by
    let f := (I.faithfulNormalizerAction hI).rangeRestrict
    let h : f 1 = 1 := map_one f
    change
      C.map (f 1)
          (I.unitNormalizerTwistedBrauerOne (k := k) hI) =
        1
    calc
      _ = C.map 1
          (I.twistedBrauerComponentEquivOfEq (k := k)
            (congrArg Subtype.val h)
            (I.unitNormalizerTwistedBrauerOne (k := k) hI)) := by
              symm
              exact
                C.map_twistedBrauerComponentEquivOfEq h _
      _ = C.map 1 (I.twistedBrauerOne (k := k)) := by
            apply congrArg (C.map 1)
            convert
              I.unitNormalizerTwistedBrauerOne_eq_twistedBrauerOne
                (k := k) hI using 1 <;> rfl
      _ = 1 := C.map_twistedBrauerOne
  map_mul := by
    intro s t x y
    let f := (I.faithfulNormalizerAction hI).rangeRestrict
    let h : f (s * t) = f s * f t :=
      MonoidHom.map_mul f s t
    change
      C.map (f (s * t))
          (I.unitNormalizerTwistedBrauerMul
            (k := k) hI s t x y) =
        C.map (f s) x * C.map (f t) y
    simp only [InteriorAction.unitNormalizerTwistedBrauerMul]
    calc
      _ = C.map (f s * f t)
          (I.twistedBrauerMul (k := k)
            (I.normalizerMulAut hI s)
            (I.normalizerMulAut hI t) x y) := by
              exact
                C.map_twistedBrauerComponentEquivOfEq h.symm _
      _ = C.map (f s) x * C.map (f t) y :=
        C.map_mul (f s) (f t) x y

/-- The normalizer homomorphism assembled using only components in the
induced automorphism subgroup. -/
def unitNormalizerUnitsHom
    (hI : Function.Injective I.unit)
    (C : NormalizerActionRangeCollapse (I := I) (k := k) hI) :
    I.unitNormalizer →*
      (BrauerQuotientAlgebra (k := k) (P := P) (A := A))ˣ :=
  (C.unitNormalizerGradedFamilyCollapse hI).sectionUnitsHom
    (TwistedBrauerGradedCollapse.unitNormalizerGradedSection
      (k := k) hI)

/-- The assembled value is the subgroup-collapse image of the
homogeneous normalizer class. -/
@[simp]
theorem coe_unitNormalizerUnitsHom
    (hI : Function.Injective I.unit)
    (C : NormalizerActionRangeCollapse (I := I) (k := k) hI)
    (s : I.unitNormalizer) :
    (C.unitNormalizerUnitsHom hI s :
        BrauerQuotientAlgebra (k := k) (P := P) (A := A)) =
      C.map ((I.faithfulNormalizerAction hI).rangeRestrict s)
        (I.unitNormalizerTwistedBrauerClass (k := k) hI s) :=
  rfl

/-- Identity normalization on the induced automorphism subgroup sends
every fixed-unit class to its ordinary Brauer class. -/
theorem map_fixedUnitClass
    (hI : Function.Injective I.unit)
    (C : NormalizerActionRangeCollapse (I := I) (k := k) hI)
    (u : (fixedSubalgebra (k := k) (P := P) (A := A))ˣ) :
    C.map
        ((I.faithfulNormalizerAction hI).rangeRestrict
          (I.fixedUnitToNormalizer (k := k) u))
        (I.unitNormalizerTwistedBrauerClass (k := k) hI
          (I.fixedUnitToNormalizer (k := k) u)) =
      brauerAlgebraProjection (k := k) (P := P) (A := A) u := by
  let s := I.fixedUnitToNormalizer (k := k) u
  let f := (I.faithfulNormalizerAction hI).rangeRestrict
  have hs :
      I.normalizerMulAut hI s = 1 :=
    TwistedBrauerGradedCollapse.normalizerMulAut_fixedUnitToNormalizer
      (I := I) (k := k) hI u
  have h : f s = 1 := by
    apply Subtype.ext
    exact hs
  calc
    _ = C.map 1
        (I.twistedBrauerComponentEquivOfEq (k := k)
          (congrArg Subtype.val h)
          (I.unitNormalizerTwistedBrauerClass (k := k) hI s)) := by
            symm
            exact C.map_twistedBrauerComponentEquivOfEq h _
    _ = I.twistedBrauerIdentityEquiv (k := k)
        (I.twistedBrauerComponentEquivOfEq (k := k)
          (congrArg Subtype.val h)
          (I.unitNormalizerTwistedBrauerClass (k := k) hI s)) := by
            rw [C.map_identity]
            rfl
    _ = brauerAlgebraProjection
          (k := k) (P := P) (A := A) u := by
            convert
              TwistedBrauerGradedCollapse.twistedBrauerIdentityEquiv_fixedUnitClass
                (I := I) (k := k) hI u using 1
            all_goals rfl

/-- Underlying-value form of the fixed-unit comparison for a collapse
over the induced automorphism subgroup. -/
@[simp]
theorem coe_unitNormalizerUnitsHom_fixedUnit
    (hI : Function.Injective I.unit)
    (C : NormalizerActionRangeCollapse (I := I) (k := k) hI)
    (u : (fixedSubalgebra (k := k) (P := P) (A := A))ˣ) :
    (C.unitNormalizerUnitsHom hI
        (I.fixedUnitToNormalizer (k := k) u) :
      BrauerQuotientAlgebra (k := k) (P := P) (A := A)) =
      brauerAlgebraProjection (k := k) (P := P) (A := A) u :=
  C.map_fixedUnitClass hI u

/-- Unit-valued fixed-unit comparison for a collapse over the induced
automorphism subgroup. -/
@[simp]
theorem unitNormalizerUnitsHom_fixedUnit
    (hI : Function.Injective I.unit)
    (C : NormalizerActionRangeCollapse (I := I) (k := k) hI)
    (u : (fixedSubalgebra (k := k) (P := P) (A := A))ˣ) :
    C.unitNormalizerUnitsHom hI
        (I.fixedUnitToNormalizer (k := k) u) =
      fixedUnitBrauerProjection (k := k) (P := P) (A := A) u := by
  apply Units.ext
  exact C.coe_unitNormalizerUnitsHom_fixedUnit hI u

/-- The homomorphism assembled from an induced-action-range collapse
extends the ordinary fixed-unit Brauer map. -/
theorem unitNormalizerUnitsHom_comp_fixedUnitToNormalizer
    (hI : Function.Injective I.unit)
    (C : NormalizerActionRangeCollapse (I := I) (k := k) hI) :
    (C.unitNormalizerUnitsHom hI).comp
        (I.fixedUnitToNormalizer (k := k)) =
      fixedUnitBrauerProjection (k := k) (P := P) (A := A) := by
  apply MonoidHom.ext
  intro u
  exact C.unitNormalizerUnitsHom_fixedUnit hI u

end TwistedBrauerSubgroupCollapse
end InteriorAction
end Representation
