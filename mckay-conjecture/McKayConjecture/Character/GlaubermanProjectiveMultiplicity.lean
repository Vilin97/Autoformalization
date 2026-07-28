/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanCorrespondence
import McKayConjecture.CharacterTriple.EquivariantMultiplicityMismatch

/-!
# The projective action on a Glauberman multiplicity space

For a classical Glauberman pair `θ ↔ θ*`, the defining multiplicity

`[θ|_{C_K(P)} : θ*]`

is prime to `p`.  If an auxiliary group `Γ` acts compatibly on `K` and
`C_K(P)` and fixes both characters, the corresponding Hom-space carries the
external projective mismatch action constructed in
`EquivariantMultiplicityMismatch`.

Thus its determinant kills the mismatch class by an integer prime to `p`.
The class vanishes as soon as the remaining representation-theoretic input
shows that this mismatch is `p`-primary.
-/

noncomputable section

namespace McKayConjecture
namespace GlaubermanCorrespondence

open CharacterTriple

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable {K P : Subgroup G} [K.Normal]

/-- The canonical Hom-space measuring the defining Glauberman restriction
multiplicity. -/
abbrev ProjectiveMultiplicitySpace
    (d : GlaubermanCorrespondence K P p)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :=
  EquivariantMultiplicityMismatch.Space
    (coprimeFixedPointsInclusion K P)
    θ.1.1
    (d.characterEquiv θ).1

omit [Finite G] [Fact p.Prime] in
/-- The dimension of the canonical Glauberman Hom-space is exactly the
defining restriction multiplicity. -/
theorem projectiveMultiplicitySpace_finrank
    (d : GlaubermanCorrespondence K P p)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    Module.finrank ℂ (ProjectiveMultiplicitySpace d θ) =
      CliffordCorrespondence.restrictionMultiplicity
        (coprimeFixedPointsInclusion K P)
        (d.characterEquiv θ).1
        θ.1.1 :=
  EquivariantMultiplicityMismatch.finrank_space_eq_restrictionMultiplicity
    (coprimeFixedPointsInclusion K P)
    θ.1.1
    (d.characterEquiv θ).1

omit [Finite G] [Fact p.Prime] in
/-- The canonical Glauberman Hom-space has dimension prime to `p`. -/
theorem projectiveMultiplicitySpace_finrank_isPPrime
    (d : GlaubermanCorrespondence K P p)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    ¬p ∣ Module.finrank ℂ (ProjectiveMultiplicitySpace d θ) := by
  rw [projectiveMultiplicitySpace_finrank d θ]
  exact d.multiplicity_isPPrime θ

variable {Γ : Type} [Group Γ]
variable
  (α : Γ →* MulAut K)
  (β : Γ →* MulAut (coprimeFixedPoints K P))
variable
  (hcompat :
    ∀ (γ : Γ) (x : coprimeFixedPoints K P),
      coprimeFixedPointsInclusion K P (β γ x) =
        α γ (coprimeFixedPointsInclusion K P x))

/-- The external factor mismatch attached to an invariant Glauberman pair.
Its pointwise value is the quotient of the source and correspondent
intertwiner factors. -/
abbrev ProjectiveMultiplicityFactorSet
    (d : GlaubermanCorrespondence K P p)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (hθ : IsInvariant α θ.1.1)
    (hθstar : IsInvariant β (d.characterEquiv θ).1) :
    FactorSet Γ ℂˣ :=
  EquivariantMultiplicityMismatch.factorSet
    α β θ.1.1 (d.characterEquiv θ).1 hθ hθstar

/-- The exact remaining `p`-primary input in the projective Glauberman
multiplicity argument. -/
def ProjectiveMultiplicityMismatchIsPPrimary
    (d : GlaubermanCorrespondence K P p)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (hθ : IsInvariant α θ.1.1)
    (hθstar : IsInvariant β (d.characterEquiv θ).1) : Prop :=
  EquivariantMultiplicityMismatch.IsQPrimary
    α β θ.1.1 (d.characterEquiv θ).1 hθ hθstar p

omit [Fact p.Prime] in
include hcompat in
/-- The determinant of the Glauberman multiplicity-space action annihilates
the external mismatch class by the prime-to-`p` multiplicity. -/
theorem projectiveMultiplicitySpace_finrank_nsmul_factorSet_h2Class_eq_zero
    (d : GlaubermanCorrespondence K P p)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (hθ : IsInvariant α θ.1.1)
    (hθstar : IsInvariant β (d.characterEquiv θ).1)
    [Nontrivial (ProjectiveMultiplicitySpace d θ)] :
    letI := trivialMulDistribMulAction Γ ℂˣ
    Module.finrank ℂ (ProjectiveMultiplicitySpace d θ) •
        (ProjectiveMultiplicityFactorSet
          α β d θ hθ hθstar).h2Class =
      0 :=
  EquivariantMultiplicityMismatch.finrank_nsmul_factorSet_h2Class_eq_zero
    α β (coprimeFixedPointsInclusion K P) hcompat
    θ.1.1 (d.characterEquiv θ).1 hθ hθstar

include hcompat in
/-- The projective mismatch of a Glauberman pair vanishes once it is known
to be `p`-primary. -/
theorem projectiveMultiplicityFactorSet_h2Class_eq_zero_of_pPrimary
    (d : GlaubermanCorrespondence K P p)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (hθ : IsInvariant α θ.1.1)
    (hθstar : IsInvariant β (d.characterEquiv θ).1)
    (hprimary :
      ProjectiveMultiplicityMismatchIsPPrimary
        α β d θ hθ hθstar) :
    letI := trivialMulDistribMulAction Γ ℂˣ
    (ProjectiveMultiplicityFactorSet
      α β d θ hθ hθstar).h2Class =
      0 :=
  EquivariantMultiplicityMismatch.factorSet_h2Class_eq_zero_of_multiplicity_prime_to_of_qPrimary
      α β (coprimeFixedPointsInclusion K P) hcompat
      θ.1.1 (d.characterEquiv θ).1 hθ hθstar p
      (projectiveMultiplicitySpace_finrank_isPPrime d θ)
      hprimary

end GlaubermanCorrespondence
end McKayConjecture
