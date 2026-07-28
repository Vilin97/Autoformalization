/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralScalarPreservation
import McKayConjecture.InductiveMcKay.NumericalReduction

/-!
# The central-scalar numerical local condition

The numerical factor-extension argument in Rossi's Lemma 4.1 uses one
specific consequence of the full inductive McKay condition: corresponding
characters have the same normalized value on every central element.
Equivalently, the local correspondence preserves every prescribed central
scalar character.

`CentralScalarLocalCorrespondence` isolates exactly this weaker invariant.
It is strictly more informative than `LocalCorrespondence`, but it does not
carry automorphism equivariance or external semidirect character-triple
witnesses.  This is the natural induction datum for a proof whose final
target is only the numerical McKay theorem.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ}

/-- A numerical local correspondence preserving normalized character
values on the ambient center.

The cross-multiplied form avoids division and remains meaningful over the
integral character degrees:

`χ(z) Ω(χ)(1) = Ω(χ)(z) χ(1)`.
-/
structure CentralScalarLocalCorrespondence
    (P : Sylow p G)
    extends LocalCorrespondence P where
  /-- Exact central-value identity for every central element, expressed in
  the canonical copy inside the chosen intermediate subgroup. -/
  correspondence_central_cross :
    ∀ (χ : PPrimeIrreducibleCharacter G p)
      (z : G)
      (_hzcentral : z ∈ Subgroup.center G)
      (hzintermediate :
        z ∈ toLocalCorrespondence.intermediate),
      χ.1.values z *
          ((toLocalCorrespondence.correspondence χ).1.degree : ℂ) =
        (toLocalCorrespondence.correspondence χ).1.values
            ⟨z, hzintermediate⟩ *
          (χ.1.degree : ℂ)

namespace CentralScalarLocalCorrespondence

variable {P : Sylow p G}

/-- Forget the central-value identity. -/
def toLocal
    (d : CentralScalarLocalCorrespondence P) :
    LocalCorrespondence P :=
  d.toLocalCorrespondence

/-- The copy of an ambient subgroup in the chosen intermediate. -/
def subgroupInIntermediate
    (d : CentralScalarLocalCorrespondence P)
    (Z : Subgroup G) :
    Subgroup d.intermediate :=
  Z.comap d.intermediate.subtype

/-- The canonical copy of a contained ambient subgroup is isomorphic to
the original subgroup. -/
def subgroupInIntermediateEquiv
    (d : CentralScalarLocalCorrespondence P)
    (Z : Subgroup G) (hZ : Z ≤ d.intermediate) :
    d.subgroupInIntermediate Z ≃* Z :=
  Subgroup.subgroupOfEquivOfLe hZ

@[simp]
theorem subgroupInIntermediateEquiv_apply_coe
    (d : CentralScalarLocalCorrespondence P)
    (Z : Subgroup G) (hZ : Z ≤ d.intermediate)
    (z : d.subgroupInIntermediate Z) :
    ((d.subgroupInIntermediateEquiv Z hZ z : Z) : G) =
      ((z : d.intermediate) : G) :=
  rfl

/-- Pull a prescribed scalar character to the canonical intermediate
copy of its subgroup. -/
def centralScalarInIntermediate
    (d : CentralScalarLocalCorrespondence P)
    (Z : Subgroup G) (hZ : Z ≤ d.intermediate)
    (lambda : Z →* ℂˣ) :
    d.subgroupInIntermediate Z →* ℂˣ :=
  lambda.comp (d.subgroupInIntermediateEquiv Z hZ).toMonoidHom

@[simp]
theorem centralScalarInIntermediate_apply
    (d : CentralScalarLocalCorrespondence P)
    (Z : Subgroup G) (hZ : Z ≤ d.intermediate)
    (lambda : Z →* ℂˣ)
    (z : d.subgroupInIntermediate Z) :
    d.centralScalarInIntermediate Z hZ lambda z =
      lambda (d.subgroupInIntermediateEquiv Z hZ z) :=
  rfl

/-- The central cross identity is equivalent to preservation of every
prescribed scalar character. -/
theorem correspondence_hasCentralScalar_iff
    (d : CentralScalarLocalCorrespondence P)
    (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (hZ : Z ≤ d.intermediate)
    (lambda : Z →* ℂˣ)
    (χ : PPrimeIrreducibleCharacter G p) :
    χ.1.HasCentralScalar Z lambda ↔
      (d.correspondence χ).1.HasCentralScalar
        (d.subgroupInIntermediate Z)
        (d.centralScalarInIntermediate Z hZ lambda) := by
  constructor
  · intro hχ z
    let zG : Z :=
      d.subgroupInIntermediateEquiv Z hZ z
    have hcross :=
      d.correspondence_central_cross
        χ (zG : G) (hZcentral zG.property)
          (hZ zG.property)
    have hsource := hχ zG
    change
      (d.correspondence χ).1.values
          (z : d.intermediate) =
        ((lambda zG : ℂˣ) : ℂ) *
          ((d.correspondence χ).1.degree : ℂ)
    apply mul_right_cancel₀
      (Nat.cast_ne_zero.mpr χ.1.degree_ne_zero)
    calc
      (d.correspondence χ).1.values
            (z : d.intermediate) *
          (χ.1.degree : ℂ) =
        χ.1.values (zG : G) *
          ((d.correspondence χ).1.degree : ℂ) := by
            simpa [zG] using hcross.symm
      _ =
        (((lambda zG : ℂˣ) : ℂ) *
            (χ.1.degree : ℂ)) *
          ((d.correspondence χ).1.degree : ℂ) := by
            rw [hsource]
      _ =
        (((lambda zG : ℂˣ) : ℂ) *
            ((d.correspondence χ).1.degree : ℂ)) *
          (χ.1.degree : ℂ) := by
            ring
  · intro hlocal z
    let zI : d.subgroupInIntermediate Z :=
      ⟨⟨(z : G), hZ z.property⟩, z.property⟩
    have hcross :=
      d.correspondence_central_cross
        χ (z : G) (hZcentral z.property)
          (hZ z.property)
    have htarget := hlocal zI
    change
      χ.1.values (z : G) =
        ((lambda z : ℂˣ) : ℂ) *
          (χ.1.degree : ℂ)
    apply mul_right_cancel₀
      (Nat.cast_ne_zero.mpr
        (d.correspondence χ).1.degree_ne_zero)
    calc
      χ.1.values (z : G) *
          ((d.correspondence χ).1.degree : ℂ) =
        (d.correspondence χ).1.values
            (zI : d.intermediate) *
          (χ.1.degree : ℂ) := by
            simpa [zI] using hcross
      _ =
        (((d.centralScalarInIntermediate
              Z hZ lambda zI : ℂˣ) : ℂ) *
            ((d.correspondence χ).1.degree : ℂ)) *
          (χ.1.degree : ℂ) := by
            rw [htarget]
      _ =
        (((lambda z : ℂˣ) : ℂ) *
            (χ.1.degree : ℂ)) *
          ((d.correspondence χ).1.degree : ℂ) := by
            change
              (((lambda z : ℂˣ) : ℂ) *
                  ((d.correspondence χ).1.degree : ℂ)) *
                (χ.1.degree : ℂ) =
              (((lambda z : ℂˣ) : ℂ) *
                  (χ.1.degree : ℂ)) *
                ((d.correspondence χ).1.degree : ℂ)
            ring

/-- Restrict a central-scalar local correspondence to one prescribed
central scalar fibre. -/
def centralScalarCorrespondence
    (d : CentralScalarLocalCorrespondence P)
    (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (hZ : Z ≤ d.intermediate)
    (lambda : Z →* ℂˣ) :
    PPrimeCentralScalarCharacter G p Z lambda ≃
      PPrimeCentralScalarCharacter
        d.intermediate p
        (d.subgroupInIntermediate Z)
        (d.centralScalarInIntermediate Z hZ lambda) :=
  d.correspondence.subtypeEquiv
    (fun χ ↦
      d.correspondence_hasCentralScalar_iff
        Z hZcentral hZ lambda χ)

@[simp]
theorem centralScalarCorrespondence_apply_coe
    (d : CentralScalarLocalCorrespondence P)
    (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (hZ : Z ≤ d.intermediate)
    (lambda : Z →* ℂˣ)
    (χ : PPrimeCentralScalarCharacter G p Z lambda) :
    (d.centralScalarCorrespondence
      Z hZcentral hZ lambda χ).1 =
        d.correspondence χ.1 :=
  rfl

end CentralScalarLocalCorrespondence

namespace LocalInductiveMcKayData

variable {P : Sylow p G}

/-- Forget a full inductive-McKay datum to the exact weaker invariant
needed by scalar-fibre normalizer induction. -/
def toCentralScalarLocal
    (d : LocalInductiveMcKayData P) :
    CentralScalarLocalCorrespondence P where
  toLocalCorrespondence := d.toLocal
  correspondence_central_cross :=
    d.correspondence_central_cross

@[simp]
theorem toCentralScalarLocal_toLocal
    (d : LocalInductiveMcKayData P) :
    d.toCentralScalarLocal.toLocal = d.toLocal :=
  rfl

end LocalInductiveMcKayData
end InductiveMcKay
end McKayConjecture
