/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralScalar
import McKayConjecture.InductiveMcKay.CentralQuotientTriviality

/-!
# Preservation of prescribed central scalars

The central character-triple clause in local inductive-McKay data preserves
more than triviality on a central subgroup.  If an irreducible character
acts on a central subgroup through a prescribed linear character, then its
local correspondent acts through the same linear character on the canonical
copy of that subgroup.

The proof uses the cross-multiplied central-value identity already extracted
from the complete character-triple witness and cancels the nonzero character
degrees.  This is the fibre-preservation statement needed when applying the
induction hypothesis to a finite projective factor extension.
-/

noncomputable section

universe u

namespace McKayConjecture

namespace IrreducibleCharacter

variable {G : Type u} [Group G]

/-- An irreducible character has prescribed scalar action `λ` on `Z` when
its value at every `z` is `λ(z)` times its degree. -/
def HasCentralScalar
    (χ : IrreducibleCharacter G)
    (Z : Subgroup G) (lambda : Z →* ℂˣ) : Prop :=
  ∀ z : Z,
    χ.values (z : G) =
      ((lambda z : ℂˣ) : ℂ) * (χ.degree : ℂ)

end IrreducibleCharacter

/-- Prime-to-`p` irreducible characters with a prescribed scalar action on
a chosen subgroup. -/
def PPrimeCentralScalarCharacter
    (G : Type u) [Group G] (p : ℕ)
    (Z : Subgroup G) (lambda : Z →* ℂˣ) :=
  {χ : PPrimeIrreducibleCharacter G p //
    χ.1.HasCentralScalar Z lambda}

namespace InductiveMcKay
namespace LocalInductiveMcKayData

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} {P : Sylow p G}

/-- The canonical copy of an ambient subgroup contained in the local
intermediate is isomorphic to the original subgroup. -/
def subgroupInIntermediateEquiv
    (d : LocalInductiveMcKayData P)
    (Z : Subgroup G) (hZ : Z ≤ d.intermediate) :
    subgroupInIntermediate d Z ≃* Z :=
  Subgroup.subgroupOfEquivOfLe hZ

@[simp]
theorem subgroupInIntermediateEquiv_apply_coe
    (d : LocalInductiveMcKayData P)
    (Z : Subgroup G) (hZ : Z ≤ d.intermediate)
    (z : subgroupInIntermediate d Z) :
    ((subgroupInIntermediateEquiv d Z hZ z : Z) : G) =
      ((z : d.intermediate) : G) :=
  rfl

/-- Pull a prescribed central scalar character to the canonical copy of its
subgroup inside the local intermediate. -/
def centralScalarInIntermediate
    (d : LocalInductiveMcKayData P)
    (Z : Subgroup G) (hZ : Z ≤ d.intermediate)
    (lambda : Z →* ℂˣ) :
    subgroupInIntermediate d Z →* ℂˣ :=
  lambda.comp (subgroupInIntermediateEquiv d Z hZ).toMonoidHom

@[simp]
theorem centralScalarInIntermediate_apply
    (d : LocalInductiveMcKayData P)
    (Z : Subgroup G) (hZ : Z ≤ d.intermediate)
    (lambda : Z →* ℂˣ)
    (z : subgroupInIntermediate d Z) :
    d.centralScalarInIntermediate Z hZ lambda z =
      lambda (d.subgroupInIntermediateEquiv Z hZ z) :=
  rfl

/-- The local inductive-McKay correspondence preserves a prescribed scalar
character on every ambient central subgroup contained in the intermediate. -/
theorem correspondence_hasCentralScalar_iff
    (d : LocalInductiveMcKayData P)
    (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (hZ : Z ≤ d.intermediate)
    (lambda : Z →* ℂˣ)
    (χ : PPrimeIrreducibleCharacter G p) :
    χ.1.HasCentralScalar Z lambda ↔
      (d.correspondence χ).1.HasCentralScalar
        (subgroupInIntermediate d Z)
        (d.centralScalarInIntermediate Z hZ lambda) := by
  constructor
  · intro hχ z
    let zG : Z :=
      d.subgroupInIntermediateEquiv Z hZ z
    have hcross :=
      d.correspondence_central_cross χ
        (zG : G) (hZcentral zG.property)
        (show (zG : G) ∈ d.intermediate from hZ zG.property)
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
    let zI : subgroupInIntermediate d Z :=
      ⟨⟨(z : G), hZ z.property⟩, z.property⟩
    have hcross :=
      d.correspondence_central_cross χ
        (z : G) (hZcentral z.property)
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
        (((d.centralScalarInIntermediate Z hZ lambda zI :
              ℂˣ) : ℂ) *
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

/-- Restrict the local correspondence to the fibre having a fixed scalar
character on a central subgroup. -/
def centralScalarCorrespondence
    (d : LocalInductiveMcKayData P)
    (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (hZ : Z ≤ d.intermediate)
    (lambda : Z →* ℂˣ) :
    PPrimeCentralScalarCharacter G p Z lambda ≃
      PPrimeCentralScalarCharacter
        d.intermediate p
        (subgroupInIntermediate d Z)
        (d.centralScalarInIntermediate Z hZ lambda) :=
  d.correspondence.subtypeEquiv
    (fun χ ↦
      d.correspondence_hasCentralScalar_iff
        Z hZcentral hZ lambda χ)

@[simp]
theorem centralScalarCorrespondence_apply_coe
    (d : LocalInductiveMcKayData P)
    (Z : Subgroup G)
    (hZcentral : Z ≤ Subgroup.center G)
    (hZ : Z ≤ d.intermediate)
    (lambda : Z →* ℂˣ)
    (χ : PPrimeCentralScalarCharacter G p Z lambda) :
    (d.centralScalarCorrespondence
      Z hZcentral hZ lambda χ).1 =
        d.correspondence χ.1 :=
  rfl

end LocalInductiveMcKayData
end InductiveMcKay
end McKayConjecture
