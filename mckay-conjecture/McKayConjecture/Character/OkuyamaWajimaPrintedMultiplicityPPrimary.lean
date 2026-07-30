/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.OkuyamaWajimaPrintedExtension
import McKayConjecture.CharacterTriple.EquivariantMultiplicityMismatchPGroup
import McKayConjecture.CharacterTriple.EquivariantMultiplicityMismatchPPrimaryValues
import McKayConjecture.CharacterTriple.ProjectiveCrossCharacteristicCoefficientReduction

/-!
# An optional `p`-primary obstruction route toward Okuyama--Wajima

The optional projective-obstruction route leaves one projective statement:
the canonical factor mismatch on the Glauberman multiplicity space is
`p`-primary.  This file reduces that statement to coefficient arithmetic.

There are two useful levels.

* A direct, gauge-dependent sufficient condition says that all values of
  the canonical mismatch factor set have a common `p`-power exponent.
* The exact gauge-independent residue obstruction is obtained by
  determinant-normalizing the multiplicity-space projective action and
  retaining only the prime-to-`p` part of its finite roots-of-unity factor.
  The discarded factor is unconditionally `p`-primary.  The desired seam
  is therefore equivalent to splitting the retained factor.

The retained factor has a uniform prime-to-`p` exponent, proved below.
Consequently its splitting is the irreducible missing coefficient fact:
it is precisely the part that cannot follow from order arithmetic alone.
It is not a consequence stated or proved by the 1980 induction argument,
which establishes extension-existence equivalence directly rather than
equality of obstruction classes.

No assertion here identifies this modular coefficient reduction with a
proof of the full printed theorem.
-/

noncomputable section

namespace McKayConjecture

open CharacterTriple

variable {p : ℕ} [Fact p.Prime]
variable {A : Type} [Group A] [Finite A]
variable (K Q U : Subgroup A) [K.Normal]

/-! ## The multiplicity-space projective representation -/

/-- The canonical projective action on the Glauberman multiplicity space,
specialized to conjugation by `U ≤ N_A(Q)`. -/
abbrev okuyamaWajimaPrintedProjectiveMultiplicityRepresentation
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) :
    ProjectiveRepresentation ℂ U
      (GlaubermanCorrespondence.ProjectiveMultiplicitySpace d theta) :=
  EquivariantMultiplicityMismatch.projective
    (okuyamaWajimaKernelConjugationAction K U)
    (okuyamaWajimaFixedPointConjugationAction K Q U hU)
    (coprimeFixedPointsInclusion K Q)
    (okuyamaWajimaConjugationActions_compatible K Q U hU)
    theta.1.1
    (d.characterEquiv theta).1
    (okuyamaWajimaKernelConjugationAction_invariant
      K Q U theta hinvariant)
    (okuyamaWajimaFixedPointConjugationAction_invariant
      K Q U hU d theta hinvariant)

omit [Fact p.Prime] [Finite A] in
/-- The defining Glauberman multiplicity is nonzero, hence its
intertwining space is a nontrivial complex vector space. -/
theorem okuyamaWajimaPrintedProjectiveMultiplicitySpace_nontrivial
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p) :
    Nontrivial
      (GlaubermanCorrespondence.ProjectiveMultiplicitySpace d theta) := by
  apply Module.nontrivial_of_finrank_pos (R := ℂ)
  apply Nat.pos_of_ne_zero
  intro hzero
  exact
    (GlaubermanCorrespondence.projectiveMultiplicitySpace_finrank_isPPrime
      d theta) (hzero ▸ dvd_zero p)

omit [Finite A] in
/-- Since the Glauberman multiplicity is prime to `p`, its prime-to-`p`
part is the whole multiplicity. -/
theorem okuyamaWajimaPrintedProjectiveMultiplicity_primeToPart_eq_finrank
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p) :
    _root_.Representation.primeToPart p
        (Module.finrank ℂ
          (GlaubermanCorrespondence.ProjectiveMultiplicitySpace
            d theta)) =
      Module.finrank ℂ
        (GlaubermanCorrespondence.ProjectiveMultiplicitySpace
          d theta) := by
  exact
    (Nat.ordCompl_eq_self_iff_zero_or_not_dvd
      (Module.finrank ℂ
        (GlaubermanCorrespondence.ProjectiveMultiplicitySpace d theta))
      Fact.out).mpr
      (Or.inr
        (GlaubermanCorrespondence.projectiveMultiplicitySpace_finrank_isPPrime
          d theta))

/-- The factor set of the actual multiplicity-space projective
representation is the canonical external mismatch. -/
theorem okuyamaWajimaPrintedProjectiveMultiplicityRepresentation_factorSet
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    [Nontrivial
      (GlaubermanCorrespondence.ProjectiveMultiplicitySpace d theta)] :
    (okuyamaWajimaPrintedProjectiveMultiplicityRepresentation
      K Q U hU d theta hinvariant).factorSet =
      GlaubermanCorrespondence.ProjectiveMultiplicityFactorSet
        (okuyamaWajimaKernelConjugationAction K U)
        (okuyamaWajimaFixedPointConjugationAction K Q U hU)
        d theta
        (okuyamaWajimaKernelConjugationAction_invariant
          K Q U theta hinvariant)
        (okuyamaWajimaFixedPointConjugationAction_invariant
          K Q U hU d theta hinvariant) := by
  letI :
      Nontrivial
        (GlaubermanCorrespondence.ProjectiveMultiplicitySpace d theta) :=
    okuyamaWajimaPrintedProjectiveMultiplicitySpace_nontrivial
      K Q d theta
  exact
    EquivariantMultiplicityMismatch.projective_factorSet
      (okuyamaWajimaKernelConjugationAction K U)
      (okuyamaWajimaFixedPointConjugationAction K Q U hU)
      (coprimeFixedPointsInclusion K Q)
      (okuyamaWajimaConjugationActions_compatible K Q U hU)
      theta.1.1
      (d.characterEquiv theta).1
      (okuyamaWajimaKernelConjugationAction_invariant
        K Q U theta hinvariant)
      (okuyamaWajimaFixedPointConjugationAction_invariant
        K Q U hU d theta hinvariant)

/-! ## The narrow direct coefficient-order criterion -/

/-- A gauge-dependent but pointwise coefficient formulation: every value
of the canonical mismatch has one common `p`-power exponent. -/
def InvariantOkuyamaWajimaPrintedMultiplicityValuesHavePPowerExponent
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) : Prop :=
  ∃ k : ℕ, ∀ u v : U,
    GlaubermanCorrespondence.ProjectiveMultiplicityFactorSet
          (okuyamaWajimaKernelConjugationAction K U)
          (okuyamaWajimaFixedPointConjugationAction K Q U hU)
          d theta
          (okuyamaWajimaKernelConjugationAction_invariant
            K Q U theta hinvariant)
          (okuyamaWajimaFixedPointConjugationAction_invariant
            K Q U hU d theta hinvariant) u v ^
        p ^ k =
      1

/-- Uniform `p`-power order of the mismatch coefficients implies the
`p`-primary seam directly, without constructing an auxiliary coefficient
group. -/
theorem invariantOkuyamaWajimaPrintedProjectiveMultiplicityPPrimary_of_values
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hvalues :
      InvariantOkuyamaWajimaPrintedMultiplicityValuesHavePPowerExponent
        K Q U hU d theta hinvariant) :
    InvariantOkuyamaWajimaPrintedProjectiveMultiplicityPPrimary
      K Q U hU d theta hinvariant := by
  obtain ⟨k, hk⟩ := hvalues
  refine ⟨k, ?_⟩
  exact
    FactorSet.nsmul_h2Class_eq_zero_of_forall_pow_eq_one
      (GlaubermanCorrespondence.ProjectiveMultiplicityFactorSet
        (okuyamaWajimaKernelConjugationAction K U)
        (okuyamaWajimaFixedPointConjugationAction K Q U hU)
        d theta
        (okuyamaWajimaKernelConjugationAction_invariant
          K Q U theta hinvariant)
        (okuyamaWajimaFixedPointConjugationAction_invariant
          K Q U hU d theta hinvariant))
      (p ^ k) hk

/-- An exact realization of the mismatch in a finite commutative
`p`-group of coefficients is a bundled version of the same coefficient
criterion. -/
theorem invariantOkuyamaWajimaPrintedProjectiveMultiplicityPPrimary_of_pGroup_coefficients
    {C : Type} [CommGroup C] [Finite C]
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hC : IsPGroup p C)
    (c : FactorSet U C)
    (ι : C →* ℂˣ)
    (hfactor :
      GlaubermanCorrespondence.ProjectiveMultiplicityFactorSet
          (okuyamaWajimaKernelConjugationAction K U)
          (okuyamaWajimaFixedPointConjugationAction K Q U hU)
          d theta
          (okuyamaWajimaKernelConjugationAction_invariant
            K Q U theta hinvariant)
          (okuyamaWajimaFixedPointConjugationAction_invariant
            K Q U hU d theta hinvariant) =
        c.map ι) :
    InvariantOkuyamaWajimaPrintedProjectiveMultiplicityPPrimary
      K Q U hU d theta hinvariant :=
  EquivariantMultiplicityMismatch.isQPrimary_of_pGroup_coefficients
    (okuyamaWajimaKernelConjugationAction K U)
    (okuyamaWajimaFixedPointConjugationAction K Q U hU)
    theta.1.1
    (d.characterEquiv theta).1
    (okuyamaWajimaKernelConjugationAction_invariant
      K Q U theta hinvariant)
    (okuyamaWajimaFixedPointConjugationAction_invariant
      K Q U hU d theta hinvariant)
    p hC c ι hfactor

/-- Irrespective of `p`, finiteness of `U` gives the canonical mismatch
class the unconditional annihilator `|U|`. -/
theorem okuyamaWajimaPrintedProjectiveMultiplicity_natCard_nsmul_eq_zero
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) :
    letI := trivialMulDistribMulAction U ℂˣ
    Nat.card U •
        (GlaubermanCorrespondence.ProjectiveMultiplicityFactorSet
          (okuyamaWajimaKernelConjugationAction K U)
          (okuyamaWajimaFixedPointConjugationAction K Q U hU)
          d theta
          (okuyamaWajimaKernelConjugationAction_invariant
            K Q U theta hinvariant)
          (okuyamaWajimaFixedPointConjugationAction_invariant
            K Q U hU d theta hinvariant)).h2Class =
      0 :=
  FactorSet.natCard_nsmul_h2Class_eq_zero _

/-- On a `p`-group acting subgroup the desired seam is unconditional.
This is the maximal conclusion obtainable merely from the order of the
acting group. -/
theorem invariantOkuyamaWajimaPrintedProjectiveMultiplicityPPrimary_of_isPGroup
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hUgroup : IsPGroup p U) :
    InvariantOkuyamaWajimaPrintedProjectiveMultiplicityPPrimary
      K Q U hU d theta hinvariant :=
  EquivariantMultiplicityMismatch.isQPrimary_of_isPGroup
    (okuyamaWajimaKernelConjugationAction K U)
    (okuyamaWajimaFixedPointConjugationAction K Q U hU)
    theta.1.1
    (d.characterEquiv theta).1
    (okuyamaWajimaKernelConjugationAction_invariant
      K Q U theta hinvariant)
    (okuyamaWajimaFixedPointConjugationAction_invariant
      K Q U hU d theta hinvariant)
    p hUgroup

/-! ## The exact prime-to-`p` residue obstruction -/

/-- The retained prime-to-`p` coefficient factor of the
determinant-normalized multiplicity-space projective representation. -/
def okuyamaWajimaPrintedProjectiveMultiplicityPrimeToPFactor
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) :
    FactorSet U ℂˣ := by
  letI :
      Nontrivial
        (GlaubermanCorrespondence.ProjectiveMultiplicitySpace d theta) :=
    okuyamaWajimaPrintedProjectiveMultiplicitySpace_nontrivial
      K Q d theta
  let P :=
    okuyamaWajimaPrintedProjectiveMultiplicityRepresentation
      K Q U hU d theta hinvariant
  exact
    (P.finiteFactorCrossCharacteristicReduction p).map
      (_root_.Representation.finiteFieldUnitsToComplexUnits
        (_root_.Representation.PrimeToCoefficientField p
          (Module.finrank ℂ
            (GlaubermanCorrespondence.ProjectiveMultiplicitySpace
              d theta))))

/-- Every retained coefficient has order dividing the prime-to-`p` part
of the multiplicity dimension. -/
theorem okuyamaWajimaPrintedProjectiveMultiplicityPrimeToPFactor_pow
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (u v : U) :
    okuyamaWajimaPrintedProjectiveMultiplicityPrimeToPFactor
          K Q U hU d theta hinvariant u v ^
        _root_.Representation.primeToPart p
          (Module.finrank ℂ
            (GlaubermanCorrespondence.ProjectiveMultiplicitySpace
              d theta)) =
      1 := by
  letI :
      Nontrivial
        (GlaubermanCorrespondence.ProjectiveMultiplicitySpace d theta) :=
    okuyamaWajimaPrintedProjectiveMultiplicitySpace_nontrivial
      K Q d theta
  letI :
      NeZero
        (Module.finrank ℂ
          (GlaubermanCorrespondence.ProjectiveMultiplicitySpace
            d theta)) :=
    ⟨Module.finrank_pos.ne'⟩
  simp only [
    okuyamaWajimaPrintedProjectiveMultiplicityPrimeToPFactor,
    FactorSet.map_apply,
    ProjectiveRepresentation.finiteFactorCrossCharacteristicReduction_apply,
    _root_.Representation.finiteFieldUnitsToComplexUnits_crossCharacteristicCoefficientReduction]
  exact
    congrArg
      (fun z :
        rootsOfUnity
          (Module.finrank ℂ
            (GlaubermanCorrespondence.ProjectiveMultiplicitySpace
              d theta)) ℂ ↦ (z : ℂˣ))
      (_root_.Representation.primeToRootsProjection_pow_primeToPart
        p
        (Module.finrank ℂ
          (GlaubermanCorrespondence.ProjectiveMultiplicitySpace
            d theta))
        ((okuyamaWajimaPrintedProjectiveMultiplicityRepresentation
          K Q U hU d theta hinvariant).finiteFactorSet u v))

/-- Hence the retained residue class has an unconditional annihilator
coprime to `p`. -/
theorem okuyamaWajimaPrintedProjectiveMultiplicityPrimeToPFactor_nsmul_eq_zero
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) :
    letI := trivialMulDistribMulAction U ℂˣ
    _root_.Representation.primeToPart p
          (Module.finrank ℂ
            (GlaubermanCorrespondence.ProjectiveMultiplicitySpace
              d theta)) •
        (okuyamaWajimaPrintedProjectiveMultiplicityPrimeToPFactor
          K Q U hU d theta hinvariant).h2Class =
      0 :=
  FactorSet.nsmul_h2Class_eq_zero_of_forall_pow_eq_one
    (okuyamaWajimaPrintedProjectiveMultiplicityPrimeToPFactor
      K Q U hU d theta hinvariant)
    (_root_.Representation.primeToPart p
      (Module.finrank ℂ
        (GlaubermanCorrespondence.ProjectiveMultiplicitySpace d theta)))
    (okuyamaWajimaPrintedProjectiveMultiplicityPrimeToPFactor_pow
      K Q U hU d theta hinvariant)

/-- In the Glauberman case the preceding prime-to-`p` annihilator is
literally the ordinary restriction multiplicity. -/
theorem okuyamaWajimaPrintedProjectiveMultiplicityPrimeToPFactor_finrank_nsmul_eq_zero
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) :
    letI := trivialMulDistribMulAction U ℂˣ
    Module.finrank ℂ
          (GlaubermanCorrespondence.ProjectiveMultiplicitySpace
            d theta) •
        (okuyamaWajimaPrintedProjectiveMultiplicityPrimeToPFactor
          K Q U hU d theta hinvariant).h2Class =
      0 := by
  rw [←
    okuyamaWajimaPrintedProjectiveMultiplicity_primeToPart_eq_finrank
      K Q d theta]
  exact
    okuyamaWajimaPrintedProjectiveMultiplicityPrimeToPFactor_nsmul_eq_zero
      K Q U hU d theta hinvariant

/-- The one irreducible coefficient statement left after all unconditional
order arithmetic: the retained prime-to-`p` factor is split in `H²`. -/
def InvariantOkuyamaWajimaPrintedMultiplicityPrimeToPFactorIsSplit
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) : Prop :=
  letI := trivialMulDistribMulAction U ℂˣ
  (okuyamaWajimaPrintedProjectiveMultiplicityPrimeToPFactor
    K Q U hU d theta hinvariant).h2Class =
    0

/-- Splitting the retained prime-to-`p` coefficient factor implies the
desired `p`-primary seam. -/
theorem invariantOkuyamaWajimaPrintedProjectiveMultiplicityPPrimary_of_primeToPFactor
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hsplit :
      InvariantOkuyamaWajimaPrintedMultiplicityPrimeToPFactorIsSplit
        K Q U hU d theta hinvariant) :
    InvariantOkuyamaWajimaPrintedProjectiveMultiplicityPPrimary
      K Q U hU d theta hinvariant := by
  letI :
      Nontrivial
        (GlaubermanCorrespondence.ProjectiveMultiplicitySpace d theta) :=
    okuyamaWajimaPrintedProjectiveMultiplicitySpace_nontrivial
      K Q d theta
  let P :=
    okuyamaWajimaPrintedProjectiveMultiplicityRepresentation
      K Q U hU d theta hinvariant
  obtain ⟨k, hk⟩ :=
    P.exists_pow_nsmul_factorSet_h2Class_eq_zero_of_reduction
      p hsplit
  refine ⟨k, ?_⟩
  have hfactor :
      P.factorSet =
        EquivariantMultiplicityMismatch.factorSet
          (okuyamaWajimaKernelConjugationAction K U)
          (okuyamaWajimaFixedPointConjugationAction K Q U hU)
          theta.1.1
          (d.characterEquiv theta).1
          (okuyamaWajimaKernelConjugationAction_invariant
            K Q U theta hinvariant)
          (okuyamaWajimaFixedPointConjugationAction_invariant
            K Q U hU d theta hinvariant) :=
    EquivariantMultiplicityMismatch.projective_factorSet
      (okuyamaWajimaKernelConjugationAction K U)
      (okuyamaWajimaFixedPointConjugationAction K Q U hU)
      (coprimeFixedPointsInclusion K Q)
      (okuyamaWajimaConjugationActions_compatible K Q U hU)
      theta.1.1
      (d.characterEquiv theta).1
      (okuyamaWajimaKernelConjugationAction_invariant
        K Q U theta hinvariant)
      (okuyamaWajimaFixedPointConjugationAction_invariant
        K Q U hU d theta hinvariant)
  change
    p ^ k •
        (EquivariantMultiplicityMismatch.factorSet
          (okuyamaWajimaKernelConjugationAction K U)
          (okuyamaWajimaFixedPointConjugationAction K Q U hU)
          theta.1.1
          (d.characterEquiv theta).1
          (okuyamaWajimaKernelConjugationAction_invariant
            K Q U theta hinvariant)
          (okuyamaWajimaFixedPointConjugationAction_invariant
            K Q U hU d theta hinvariant)).h2Class =
      0
  rw [← hfactor]
  exact hk

/-- Conversely, a `p`-primary canonical mismatch has split
prime-to-`p` residue.  The proof uses the exact coefficient decomposition:
the finite factor is the product of its `p`-primary remainder and the
retained factor.  The latter is therefore killed both by a `p`-power and
by the prime-to-`p` part of the multiplicity dimension. -/
theorem invariantOkuyamaWajimaPrintedMultiplicityPrimeToPFactorIsSplit_of_pPrimary
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1)
    (hprimary :
      InvariantOkuyamaWajimaPrintedProjectiveMultiplicityPPrimary
        K Q U hU d theta hinvariant) :
    InvariantOkuyamaWajimaPrintedMultiplicityPrimeToPFactorIsSplit
      K Q U hU d theta hinvariant := by
  let V :=
    GlaubermanCorrespondence.ProjectiveMultiplicitySpace d theta
  letI : Nontrivial V :=
    okuyamaWajimaPrintedProjectiveMultiplicitySpace_nontrivial
      K Q d theta
  let n := Module.finrank ℂ V
  letI : NeZero n := ⟨Module.finrank_pos.ne'⟩
  let P :=
    okuyamaWajimaPrintedProjectiveMultiplicityRepresentation
      K Q U hU d theta hinvariant
  let beta : FactorSet U ℂˣ :=
    (P.finiteFactorCrossCharacteristicReduction p).map
      (_root_.Representation.finiteFieldUnitsToComplexUnits
        (_root_.Representation.PrimeToCoefficientField p n))
  let remainder : FactorSet U ℂˣ :=
    (P.finiteFactorSet.primePrimaryRemainder p n).map
      ((rootsOfUnity n ℂ).subtype.comp
        ((_root_.Representation.primeToRootsProjection p n).ker.subtype))
  letI := trivialMulDistribMulAction U ℂˣ
  obtain ⟨k, hk⟩ := hprimary
  have hfactor :
      P.factorSet =
        EquivariantMultiplicityMismatch.factorSet
          (okuyamaWajimaKernelConjugationAction K U)
          (okuyamaWajimaFixedPointConjugationAction K Q U hU)
          theta.1.1
          (d.characterEquiv theta).1
          (okuyamaWajimaKernelConjugationAction_invariant
            K Q U theta hinvariant)
          (okuyamaWajimaFixedPointConjugationAction_invariant
            K Q U hU d theta hinvariant) :=
    EquivariantMultiplicityMismatch.projective_factorSet
      (okuyamaWajimaKernelConjugationAction K U)
      (okuyamaWajimaFixedPointConjugationAction K Q U hU)
      (coprimeFixedPointsInclusion K Q)
      (okuyamaWajimaConjugationActions_compatible K Q U hU)
      theta.1.1
      (d.characterEquiv theta).1
      (okuyamaWajimaKernelConjugationAction_invariant
        K Q U theta hinvariant)
      (okuyamaWajimaFixedPointConjugationAction_invariant
        K Q U hU d theta hinvariant)
  have hkP :
      p ^ k • P.factorSet.h2Class = 0 := by
    rw [hfactor]
    exact hk
  obtain ⟨l, hl⟩ :=
    FactorSet.exists_pow_nsmul_primePrimaryRemainder_h2Class_eq_zero
      p n P.finiteFactorSet
  have hclasses :
      P.factorSet.h2Class =
        (P.finiteFactorSet.map
          (rootsOfUnity n ℂ).subtype).h2Class := by
    calc
      P.factorSet.h2Class =
          P.finiteFactorNormalize.factorSet.h2Class :=
        FactorSet.h2Class_eq_of_cohomologous
          P.factorSet_cohomologous_finiteFactorNormalize
      _ =
          (P.finiteFactorSet.map
            (rootsOfUnity n ℂ).subtype).h2Class :=
        congrArg FactorSet.h2Class
          P.finiteFactorSet_map_subtype.symm
  have hdecomp :
      (P.finiteFactorSet.map
          (rootsOfUnity n ℂ).subtype).h2Class =
        remainder.h2Class + beta.h2Class := by
    have h :=
      congrArg FactorSet.h2Class
        (FactorSet.map_subtype_eq_primePrimaryRemainder_mul_liftedReduction
          p n P.finiteFactorSet)
    rw [FactorSet.h2Class_mul] at h
    simpa [remainder, beta,
      ProjectiveRepresentation.finiteFactorCrossCharacteristicReduction]
      using h
  have hkP' :
      p ^ (k + l) • P.factorSet.h2Class = 0 := by
    rw [pow_add, mul_nsmul, hkP]
    simp
  have hlR :
      p ^ l • remainder.h2Class = 0 := by
    simpa [remainder] using hl
  have hlR' :
      p ^ (k + l) • remainder.h2Class = 0 := by
    have heq :
        p ^ (k + l) = p ^ l * p ^ k := by
      rw [pow_add, mul_comm]
    rw [heq, mul_nsmul, hlR]
    simp
  have hfinite :
      p ^ (k + l) •
          (P.finiteFactorSet.map
            (rootsOfUnity n ℂ).subtype).h2Class =
        0 := by
    rw [← hclasses]
    exact hkP'
  have hbetaPrimary :
      p ^ (k + l) • beta.h2Class = 0 := by
    rw [hdecomp, nsmul_add, hlR', zero_add] at hfinite
    exact hfinite
  have hbetaPrimeTo :
      _root_.Representation.primeToPart p n •
          beta.h2Class =
        0 := by
    simpa [beta, P, n, V,
      okuyamaWajimaPrintedProjectiveMultiplicityPrimeToPFactor]
      using
        (okuyamaWajimaPrintedProjectiveMultiplicityPrimeToPFactor_nsmul_eq_zero
          K Q U hU d theta hinvariant)
  have hcoprime :
      Nat.Coprime
        (p ^ (k + l))
        (_root_.Representation.primeToPart p n) :=
    (_root_.Representation.prime_coprime_primeToPart p n).pow_left
      (k + l)
  have hbeta :
      beta.h2Class = 0 :=
    eq_zero_of_coprime_nsmul_eq_zero
      hcoprime hbetaPrimary hbetaPrimeTo
  change
    (okuyamaWajimaPrintedProjectiveMultiplicityPrimeToPFactor
      K Q U hU d theta hinvariant).h2Class =
      0
  simpa [beta, P, n, V,
    okuyamaWajimaPrintedProjectiveMultiplicityPrimeToPFactor]
    using hbeta

/-- Exact coefficient reformulation of the remaining projective seam:
it is equivalent to splitting the retained prime-to-`p` residue factor. -/
theorem invariantOkuyamaWajimaPrintedProjectiveMultiplicityPPrimary_iff_primeToPFactor
    (hU : U ≤ Subgroup.normalizer (Q : Set A))
    (d : GlaubermanCorrespondence K Q p)
    (theta : PInvariantPPrimeIrreducibleCharacter K Q p)
    (hinvariant : ∀ a : A, a • theta.1.1 = theta.1.1) :
    InvariantOkuyamaWajimaPrintedProjectiveMultiplicityPPrimary
        K Q U hU d theta hinvariant ↔
      InvariantOkuyamaWajimaPrintedMultiplicityPrimeToPFactorIsSplit
        K Q U hU d theta hinvariant :=
  ⟨invariantOkuyamaWajimaPrintedMultiplicityPrimeToPFactorIsSplit_of_pPrimary
      K Q U hU d theta hinvariant,
    invariantOkuyamaWajimaPrintedProjectiveMultiplicityPPrimary_of_primeToPFactor
      K Q U hU d theta hinvariant⟩

end McKayConjecture
