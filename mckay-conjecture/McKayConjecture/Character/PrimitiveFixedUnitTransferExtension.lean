/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InvariantCharacterTransferExtension
import McKayConjecture.Character.PrimitiveFixedUnitBrauerCharacter
import Mathlib.FieldTheory.Finite.Basic

/-!
# A transfer criterion for primitive fixed-unit extensions

For a faithful primitive Dade algebra, fixed-algebra units form the
kernel of the interior normalizer action, and their Brauer character
is invariant under the whole normalizer.  Transfer therefore extends
that character whenever the order of its target is coprime to the
index of the fixed-unit subgroup.

Over a finite field of characteristic `p`, the primitive Brauer
quotient has the same unit-group order as the coefficient field, hence
order prime to every finite `p`-group.  Consequently the fixed-unit
character extends if the induced normalizer subgroup of `Aut(P)` (or
equivalently the fixed-unit quotient) is a `p`-group.

The final quotient hypothesis is essential: the induced subgroup of
`Aut(P)` need not be a `p`-group for a general primitive Dade algebra.
-/

noncomputable section

namespace Representation
namespace InteriorAction

variable {p : ℕ} [Fact p.Prime]
variable {k P A : Type}
variable [Field k] [CharP k p]
variable [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

variable (I : InteriorAction (P := P) (A := A))

/-- Fixed-algebra units are canonically isomorphic to their image in
the interior unit normalizer. -/
def fixedUnitMulEquivFixedUnitRange :
    (fixedSubalgebra (k := k) (P := P) (A := A))ˣ ≃*
      I.fixedUnitRange (k := k) :=
  MonoidHom.ofInjective I.fixedUnitToNormalizer_injective

omit [Fintype P] in
@[simp]
theorem coe_fixedUnitMulEquivFixedUnitRange
    (u : (fixedSubalgebra (k := k) (P := P) (A := A))ˣ) :
    (I.fixedUnitMulEquivFixedUnitRange (k := k) u :
        I.unitNormalizer) =
      I.fixedUnitToNormalizer (k := k) u :=
  rfl

/-- The Brauer projection, regarded as a character of the fixed-unit
subgroup of the interior unit normalizer. -/
def fixedUnitRangeBrauerProjection :
    I.fixedUnitRange (k := k) →*
      (BrauerQuotientAlgebra (k := k) (P := P) (A := A))ˣ :=
  (fixedUnitBrauerProjection (k := k) (P := P) (A := A)).comp
    (I.fixedUnitMulEquivFixedUnitRange (k := k)).symm.toMonoidHom

@[simp]
theorem fixedUnitRangeBrauerProjection_fixedUnit
    (u : (fixedSubalgebra (k := k) (P := P) (A := A))ˣ) :
    I.fixedUnitRangeBrauerProjection (k := k)
        (I.fixedUnitMulEquivFixedUnitRange (k := k) u) =
      fixedUnitBrauerProjection (k := k) (P := P) (A := A) u := by
  simp [fixedUnitRangeBrauerProjection]

/-- Pull the fixed-unit Brauer projection back to scalar units through
a specified scalar identification. -/
def fixedUnitRangeScalarBrauerCharacter
    (Z : BrauerScalarIdentification (k := k) (P := P) (A := A)) :
    I.fixedUnitRange (k := k) →* kˣ :=
  Z.equiv.symm.toMonoidHom.comp
    (I.fixedUnitRangeBrauerProjection (k := k))

/-- In the faithful primitive case, the scalar-valued Brauer
character on the fixed-unit subgroup is conjugation-invariant. -/
theorem fixedUnitRangeScalarBrauerCharacter_isConjugationInvariant
    (S : DadeAlgebra p k P A)
    (hI : Function.Injective I.unit)
    (hprimitive : S.IsBrauerPrimitive)
    (Z : BrauerScalarIdentification (k := k) (P := P) (A := A)) :
    letI : (I.fixedUnitRange (k := k)).Normal :=
      I.fixedUnitRange_normal hI
    MonoidHom.IsConjugationInvariant
      (I.fixedUnitRange (k := k))
      (I.fixedUnitRangeScalarBrauerCharacter (k := k) Z) := by
  letI : (I.fixedUnitRange (k := k)).Normal :=
    I.fixedUnitRange_normal hI
  intro s c
  let e :=
    I.fixedUnitMulEquivFixedUnitRange (k := k)
  obtain ⟨u, rfl⟩ := e.surjective c
  let u' :=
    I.normalizerConjFixedUnit (k := k) s u
  have hconj :
      (⟨s⁻¹ * (e u : I.unitNormalizer) * s,
          (inferInstance :
            (I.fixedUnitRange (k := k)).Normal).conj_mem'
              (e u) (e u).property s⟩ :
          I.fixedUnitRange (k := k)) =
        e u' := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rfl
  rw [hconj]
  simp only [fixedUnitRangeScalarBrauerCharacter,
    MonoidHom.comp_apply]
  rw [I.fixedUnitRangeBrauerProjection_fixedUnit,
    I.fixedUnitRangeBrauerProjection_fixedUnit]
  exact congrArg Z.equiv.symm
    (I.fixedUnitBrauerProjection_normalizerConjFixedUnit
      S hI hprimitive s u)

/-- Coprime-index form of the primitive fixed-unit extension
criterion. -/
theorem hasBrauerNormalizerHomExtension_of_isBrauerPrimitive_of_scalar_coprime
    [Finite I.unitNormalizer]
    [Finite k]
    (S : DadeAlgebra p k P A)
    (hI : Function.Injective I.unit)
    (hprimitive : S.IsBrauerPrimitive)
    (Z : BrauerScalarIdentification (k := k) (P := P) (A := A))
    (hcoprime :
      Nat.Coprime
        (Nat.card kˣ)
        (I.fixedUnitRange (k := k)).index) :
    HasBrauerNormalizerHomExtension (k := k) I := by
  letI : (I.fixedUnitRange (k := k)).Normal :=
    I.fixedUnitRange_normal hI
  obtain ⟨ψ, hψ⟩ :=
    MonoidHom.exists_extension_of_isConjugationInvariant_of_coprime
      (I.fixedUnitRange (k := k))
      (I.fixedUnitRangeScalarBrauerCharacter (k := k) Z)
      (I.fixedUnitRangeScalarBrauerCharacter_isConjugationInvariant
        S hI hprimitive Z)
      hcoprime
  refine
    ⟨{ hom := Z.equiv.toMonoidHom.comp ψ
       extends_fixedUnit := ?_ }⟩
  apply MonoidHom.ext
  intro u
  have hu :=
    congrArg
      (fun f :
        I.fixedUnitRange (k := k) →* kˣ =>
        f (I.fixedUnitMulEquivFixedUnitRange (k := k) u))
      hψ
  change
    ψ
        (I.fixedUnitMulEquivFixedUnitRange
          (k := k) u : I.unitNormalizer) =
      I.fixedUnitRangeScalarBrauerCharacter (k := k) Z
        (I.fixedUnitMulEquivFixedUnitRange (k := k) u) at hu
  simp only [fixedUnitRangeScalarBrauerCharacter,
    MonoidHom.comp_apply,
    fixedUnitRangeBrauerProjection_fixedUnit,
    coe_fixedUnitMulEquivFixedUnitRange] at hu
  change
    Z.equiv
        (ψ (I.fixedUnitToNormalizer (k := k) u)) =
      fixedUnitBrauerProjection
        (k := k) (P := P) (A := A) u
  rw [hu]
  exact Z.equiv.apply_symm_apply _

/-- The multiplicative group of a finite field of characteristic `p`
has order coprime to every finite `p`-group. -/
private theorem finiteFieldUnits_card_coprime_isPGroup
    [Finite k]
    {Q : Type} [Group Q] [Finite Q]
    (hQ : IsPGroup p Q) :
    Nat.Coprime (Nat.card kˣ) (Nat.card Q) := by
  letI := Fintype.ofFinite k
  obtain ⟨n, hp, hk⟩ :=
    FiniteField.card k p
  obtain ⟨m, hQcard⟩ :=
    IsPGroup.iff_card.mp hQ
  rw [Nat.card_units, Nat.card_eq_fintype_card,
    hk, hQcard]
  have hpow :
      Nat.Coprime (p ^ (n : ℕ) - 1) (p ^ (n : ℕ)) := by
    rw [Nat.coprime_self_sub_left]
    · exact Nat.coprime_one_left _
    · exact Nat.one_le_pow _ _ hp.pos
  have hp' :
      Nat.Coprime (p ^ (n : ℕ) - 1) p :=
    hpow.of_dvd_right (dvd_pow_self p n.ne_zero)
  exact hp'.pow_right m

/-- Finite-field specialization: if the fixed-unit quotient is a
`p`-group, transfer supplies the homomorphism part of the primitive
Brauer-normalizer extension. -/
theorem hasBrauerNormalizerHomExtension_of_isBrauerPrimitive_of_isPGroup_quotient
    [Finite k] [Finite A]
    (S : DadeAlgebra p k P A)
    (hI : Function.Injective I.unit)
    (hprimitive : S.IsBrauerPrimitive)
    (hquotient :
      letI : (I.fixedUnitRange (k := k)).Normal :=
        I.fixedUnitRange_normal hI
      IsPGroup p
        (I.unitNormalizer ⧸ I.fixedUnitRange (k := k))) :
    HasBrauerNormalizerHomExtension (k := k) I := by
  let hfin :=
    (S.finrank_brauerQuotientAlgebra_eq_one_iff_isBrauerPrimitive).2
      hprimitive
  let Z :=
    brauerScalarIdentificationOfFinrankOne
      (k := k) (P := P) (A := A) hfin
  letI : (I.fixedUnitRange (k := k)).Normal :=
    I.fixedUnitRange_normal hI
  apply
    I.hasBrauerNormalizerHomExtension_of_isBrauerPrimitive_of_scalar_coprime
      S hI hprimitive Z
  rw [Subgroup.index_eq_card]
  exact
    finiteFieldUnits_card_coprime_isPGroup
      (k := k) hquotient

/-- Full-extension form of the finite-field transfer criterion. -/
theorem hasBrauerNormalizerExtension_of_isBrauerPrimitive_of_isPGroup_quotient
    [Finite k] [Finite A]
    (S : DadeAlgebra p k P A)
    (hI : Function.Injective I.unit)
    (hprimitive : S.IsBrauerPrimitive)
    (hquotient :
      letI : (I.fixedUnitRange (k := k)).Normal :=
        I.fixedUnitRange_normal hI
      IsPGroup p
        (I.unitNormalizer ⧸ I.fixedUnitRange (k := k))) :
    HasBrauerNormalizerExtension (k := k) I :=
  S.hasBrauerNormalizerExtension_of_isBrauerPrimitive
    I hI hprimitive
    (I.hasBrauerNormalizerHomExtension_of_isBrauerPrimitive_of_isPGroup_quotient
      S hI hprimitive hquotient)

end InteriorAction
end Representation
