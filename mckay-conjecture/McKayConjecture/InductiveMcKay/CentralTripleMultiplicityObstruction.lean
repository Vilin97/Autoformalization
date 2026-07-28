/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.FactorSetCoprimeClassVanishing
import McKayConjecture.CharacterTriple.ProjectiveMultiplicityMismatch
import McKayConjecture.InductiveMcKay.CentralTripleProjectiveObstructionClass

/-!
# Killing a central-triple obstruction by a prime-to-`q` multiplicity

For two character triples related by central-restriction group data, the
projective action on their normal restriction-multiplicity space represents
the difference of the two intrinsic obstruction classes.  Its determinant
shows that the multiplicity dimension annihilates this difference.

Consequently, a prime-to-`q` multiplicity forces obstruction agreement as
soon as the mismatch class is `q`-primary.  This isolates the two genuinely
different inputs in the Glauberman route:

* the classical correspondence supplies a prime-to-`q` multiplicity;
* the Dade--Glauberman--Nagao argument must prove that the projective
  mismatch is `q`-primary.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple

variable {A B : Type}
variable [Group A] [Finite A] [Group B] [Finite B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {e : B →* A}
variable {V W : Type}
variable [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W]
  [Module.Finite ℂ W] [Nontrivial W]
variable {P : ProjectiveRepresentation ℂ A V}
variable {Q : ProjectiveRepresentation ℂ B W}

namespace CentralRestrictionGroupData

/-- The quotient-factor mismatch is `q`-primary when some power of `q`
annihilates its `H²` class. -/
def MultiplicityMismatchIsQPrimary
    (g : CentralRestrictionGroupData T U e)
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (q : ℕ) : Prop :=
  ∃ k : ℕ,
    letI :=
      trivialMulDistribMulAction
        (B ⧸ U.normalSubgroup) ℂˣ
    q ^ k •
        (R.quotientFactorSetAlong g *
          S.quotientFactorSet⁻¹).h2Class =
      0

/-- A prime-to-`q` restriction multiplicity and a `q`-primary mismatch
force quotient-factor class agreement. -/
theorem quotientFactorH2ClassAgreement_of_multiplicity_prime_to_of_mismatch_qPrimary
    (g : CentralRestrictionGroupData T U e)
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (q : ℕ) [Fact q.Prime]
    (hmultiplicity :
      ¬q ∣ Module.finrank ℂ
        (ProjectiveMultiplicityMismatch.Space R S g))
    (hprimary :
      g.MultiplicityMismatchIsQPrimary R S q) :
    R.QuotientFactorH2ClassAgreement S g := by
  have hpositive :
      0 < Module.finrank ℂ
        (ProjectiveMultiplicityMismatch.Space R S g) := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hmultiplicity (hzero ▸ dvd_zero q)
  letI :
      Nontrivial
        (ProjectiveMultiplicityMismatch.Space R S g) :=
    Module.nontrivial_of_finrank_pos hpositive
  obtain ⟨k, hk⟩ := hprimary
  have hdimension :=
    ProjectiveMultiplicityMismatch.finrank_nsmul_quotientFactorMismatch_h2Class_eq_zero
      R S g
  have hcoprime :
      Nat.Coprime
        (Module.finrank ℂ
          (ProjectiveMultiplicityMismatch.Space R S g))
        (q ^ k) :=
    (Fact.out : q.Prime).coprime_pow_of_not_dvd
      hmultiplicity
  have hzero :
      letI :=
        trivialMulDistribMulAction
          (B ⧸ U.normalSubgroup) ℂˣ
      (R.quotientFactorSetAlong g *
        S.quotientFactorSet⁻¹).h2Class = 0 :=
    CharacterTriple.eq_zero_of_coprime_nsmul_eq_zero
      hcoprime hdimension hk
  exact
    ProjectiveMultiplicityMismatch.quotientFactorH2ClassAgreement_of_mismatch_eq_zero
      R S g hzero

/-- Intrinsic form of the same criterion: prime-to-`q` multiplicity and
`q`-primary mismatch prove equality of the two character-triple obstruction
classes. -/
theorem projectiveObstructionClassAgreement_of_multiplicity_prime_to_of_mismatch_qPrimary
    (g : CentralRestrictionGroupData T U e)
    (R : AssociatedProjectiveRepresentation T V P)
    (S : AssociatedProjectiveRepresentation U W Q)
    (q : ℕ) [Fact q.Prime]
    (hmultiplicity :
      ¬q ∣ Module.finrank ℂ
        (ProjectiveMultiplicityMismatch.Space R S g))
    (hprimary :
      g.MultiplicityMismatchIsQPrimary R S q) :
    g.ProjectiveObstructionClassAgreement := by
  exact
    (R.quotientFactorH2ClassAgreement_iff_projectiveObstructionClass
      S g).mp
      (g.quotientFactorH2ClassAgreement_of_multiplicity_prime_to_of_mismatch_qPrimary
        R S q hmultiplicity hprimary)

end CentralRestrictionGroupData
end InductiveMcKay
end McKayConjecture
