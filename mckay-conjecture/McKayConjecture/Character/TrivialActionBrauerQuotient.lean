/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.BrauerTraceIdeal
import McKayConjecture.Character.TrivialAlgebraAction
import Mathlib.GroupTheory.PGroup
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Brauer quotients of trivial actions

Let a finite `p`-group act trivially on a module over a ring of
characteristic `p`.  The relative trace from a proper subgroup is the
subgroup index times its input.  That index is a positive power of
`p`, so every such trace vanishes.

For an algebra this makes the Brauer trace ideal zero.  Consequently
the canonical Brauer quotient is explicitly isomorphic, as an algebra,
to the original algebra.
-/

noncomputable section

open scoped BigOperators

namespace Representation

variable {p : ℕ}
variable {k P V : Type}
variable [CommRing k] [Group P]
variable [AddCommGroup V] [Module k V]

noncomputable local instance trivialActionQuotientFintype
    [Finite P]
    (Q : Subgroup P) :
    Fintype (P ⧸ Q) :=
  Fintype.ofFinite (P ⧸ Q)

/-- For a trivial representation, every vector is invariant.  This is
the identity-on-elements linear equivalence with the invariant
submodule. -/
def invariantsLinearEquivOfIsTrivial
    (rho : Representation k P V) [rho.IsTrivial] :
    V ≃ₗ[k] invariants rho where
  toFun v := ⟨v, fun g ↦ rho.isTrivial_apply g v⟩
  invFun v := v
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem invariantsLinearEquivOfIsTrivial_apply
    (rho : Representation k P V) [rho.IsTrivial]
    (v : V) :
    ((invariantsLinearEquivOfIsTrivial rho v :
      invariants rho) : V) = v :=
  rfl

@[simp]
theorem invariantsLinearEquivOfIsTrivial_symm_apply
    (rho : Representation k P V) [rho.IsTrivial]
    (v : invariants rho) :
    (invariantsLinearEquivOfIsTrivial rho).symm v = (v : V) :=
  rfl

/-- For a trivial representation, relative trace is multiplication by
the subgroup index. -/
theorem relativeTrace_eq_card_smul_of_isTrivial
    [Fintype P]
    (rho : Representation k P V) [rho.IsTrivial]
    (Q : Subgroup P)
    (x : invariants (rho.comp Q.subtype)) :
    relativeTrace rho Q x =
      (Nat.card (P ⧸ Q) : k) •
        invariantsLinearEquivOfIsTrivial rho (x : V) := by
  apply Subtype.ext
  change
    (∑ c : P ⧸ Q, rho c.out (x : V)) =
      (Nat.card (P ⧸ Q) : k) • (x : V)
  simp only [rho.isTrivial_apply, Finset.sum_const,
    Finset.card_univ, Nat.card_eq_fintype_card,
    Nat.cast_smul_eq_nsmul]

/-- A proper subgroup of a finite `p`-group has index divisible by
`p`. -/
theorem prime_dvd_card_quotient_of_isPGroup
    [Finite P]
    [Fact p.Prime]
    (hP : IsPGroup p P)
    (Q : Subgroup P)
    (hQ : Q < ⊤) :
    p ∣ Nat.card (P ⧸ Q) := by
  obtain ⟨n, hn⟩ := hP.index Q
  change p ∣ Q.index
  rcases n with _ | n
  · simp only [pow_zero] at hn
    exact (hQ.ne (Subgroup.index_eq_one.mp hn)).elim
  · rw [hn]
    exact dvd_pow_self p (Nat.succ_ne_zero n)

/-- Every proper-subgroup relative trace of a trivial representation
of a finite `p`-group vanishes in characteristic `p`. -/
theorem relativeTrace_eq_zero_of_isTrivial_isPGroup
    [Fintype P]
    [CharP k p] [Fact p.Prime]
    (rho : Representation k P V) [rho.IsTrivial]
    (hP : IsPGroup p P)
    (Q : Subgroup P)
    (hQ : Q < ⊤)
    (x : invariants (rho.comp Q.subtype)) :
    relativeTrace rho Q x = 0 := by
  rw [relativeTrace_eq_card_smul_of_isTrivial]
  have hcard :
      (Nat.card (P ⧸ Q) : k) = 0 :=
    (CharP.cast_eq_zero_iff k p _).2
      (prime_dvd_card_quotient_of_isPGroup hP Q hQ)
  rw [hcard, zero_smul]

section Algebra

variable {A : Type}
variable [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

/-- Under a pointwise trivial algebra action, relative trace is
multiplication by the subgroup index. -/
theorem fixedRelativeTrace_eq_card_smul_of_trivialAction
    (htriv : IsTrivialAlgebraAction P A)
    (Q : Subgroup P)
    (x : fixedSubalgebra (k := k) (P := Q) (A := A)) :
    fixedRelativeTrace (k := k) (P := P) (A := A) Q x =
      (Nat.card (P ⧸ Q) : k) •
        fixedSubalgebraAlgEquivOfTrivialAction
          (k := k) (P := P) (A := A) htriv (x : A) := by
  apply Subtype.ext
  change
    (∑ c : P ⧸ Q, c.out • (x : A)) =
      (Nat.card (P ⧸ Q) : k) • (x : A)
  calc
    (∑ c : P ⧸ Q, c.out • (x : A)) =
        ∑ _c : P ⧸ Q, (x : A) := by
      apply Fintype.sum_congr
      intro c
      exact htriv c.out x
    _ = (Nat.card (P ⧸ Q) : k) • (x : A) := by
      simp only [Finset.sum_const, Finset.card_univ,
        Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]

/-- In characteristic `p`, every proper-subgroup relative trace for a
trivial finite `p`-group algebra action is zero. -/
theorem fixedRelativeTrace_eq_zero_of_trivialAction_isPGroup
    [CharP k p] [Fact p.Prime]
    (htriv : IsTrivialAlgebraAction P A)
    (hP : IsPGroup p P)
    (Q : Subgroup P)
    (hQ : Q < ⊤)
    (x : fixedSubalgebra (k := k) (P := Q) (A := A)) :
    fixedRelativeTrace (k := k) (P := P) (A := A) Q x =
      0 := by
  rw [fixedRelativeTrace_eq_card_smul_of_trivialAction htriv]
  have hcard :
      (Nat.card (P ⧸ Q) : k) = 0 :=
    (CharP.cast_eq_zero_iff k p _).2
      (prime_dvd_card_quotient_of_isPGroup hP Q hQ)
  rw [hcard, zero_smul]

/-- Each proper relative-trace ideal is zero for a trivial action in
the defining characteristic. -/
theorem fixedRelativeTraceIdeal_eq_bot_of_trivialAction_isPGroup
    [CharP k p] [Fact p.Prime]
    (htriv : IsTrivialAlgebraAction P A)
    (hP : IsPGroup p P)
    (Q : Subgroup P)
    (hQ : Q < ⊤) :
    fixedRelativeTraceIdeal (k := k) (P := P) (A := A) Q =
      ⊥ := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [fixedRelativeTrace_eq_zero_of_trivialAction_isPGroup
      htriv hP Q hQ]
    exact (Ideal.zero_mem _)
  · exact bot_le

/-- The total Brauer trace ideal of a trivial finite `p`-group action
in characteristic `p` is zero. -/
theorem brauerTraceIdeal_eq_bot_of_trivialAction_isPGroup
    [CharP k p] [Fact p.Prime]
    (htriv : IsTrivialAlgebraAction P A)
    (hP : IsPGroup p P) :
    brauerTraceIdeal (k := k) (P := P) (A := A) =
      ⊥ := by
  rw [brauerTraceIdeal, iSup_eq_bot]
  intro Q
  rw [iSup_eq_bot]
  intro hQ
  exact
    fixedRelativeTraceIdeal_eq_bot_of_trivialAction_isPGroup
      htriv hP Q hQ

/-- The Brauer quotient of a genuinely trivial finite `p`-group
algebra action in characteristic `p` is the original algebra. -/
def brauerQuotientAlgebraEquivOfTrivialAction
    [CharP k p] [Fact p.Prime]
    (htriv : IsTrivialAlgebraAction P A)
    (hP : IsPGroup p P) :
    A ≃ₐ[k]
      BrauerQuotientAlgebra (k := k) (P := P) (A := A) :=
  (fixedSubalgebraAlgEquivOfTrivialAction
      (k := k) (P := P) (A := A) htriv).trans
    (((Ideal.quotientEquivAlgOfEq k
      (brauerTraceIdeal_eq_bot_of_trivialAction_isPGroup
        htriv hP)).trans
      (AlgEquiv.quotientBot k
        (fixedSubalgebra (k := k) (P := P) (A := A)))).symm)

@[simp]
theorem brauerQuotientAlgebraEquivOfTrivialAction_apply
    [CharP k p] [Fact p.Prime]
    (htriv : IsTrivialAlgebraAction P A)
    (hP : IsPGroup p P)
    (a : A) :
    brauerQuotientAlgebraEquivOfTrivialAction htriv hP a =
      brauerAlgebraProjection (k := k) (P := P) (A := A)
        (fixedSubalgebraAlgEquivOfTrivialAction
          (k := k) (P := P) (A := A) htriv a) := by
  rfl

end Algebra

section CanonicalTrivialAlgebraAction

variable {A : Type}
variable [Fintype P]
variable [Ring A] [Algebra k A]

/-- Every proper relative trace vanishes for the canonical trivial
algebra action of a finite `p`-group in characteristic `p`. -/
theorem trivialAlgebra_fixedRelativeTrace_eq_zero
    [CharP k p] [Fact p.Prime]
    (hP : IsPGroup p P)
    (Q : Subgroup P)
    (hQ : Q < ⊤) :
    letI : MulSemiringAction P A :=
      trivialAlgebraMulSemiringAction P A
    letI : SMulCommClass P k A :=
      trivialAlgebraSMulCommClass P k A
    ∀ x : fixedSubalgebra (k := k) (P := Q) (A := A),
      fixedRelativeTrace (k := k) (P := P) (A := A) Q x =
        0 := by
  letI : MulSemiringAction P A :=
    trivialAlgebraMulSemiringAction P A
  letI : SMulCommClass P k A :=
    trivialAlgebraSMulCommClass P k A
  intro x
  exact
    fixedRelativeTrace_eq_zero_of_trivialAction_isPGroup
      (isTrivialAlgebraAction_trivial P A) hP Q hQ x

/-- For the canonical trivial action, the Brauer quotient is
constructively algebra-equivalent to the original algebra. -/
def trivialAlgebraBrauerQuotientEquiv
    [CharP k p] [Fact p.Prime]
    (hP : IsPGroup p P) :
    letI : MulSemiringAction P A :=
      trivialAlgebraMulSemiringAction P A
    letI : SMulCommClass P k A :=
      trivialAlgebraSMulCommClass P k A
    A ≃ₐ[k]
      BrauerQuotientAlgebra (k := k) (P := P) (A := A) := by
  letI : MulSemiringAction P A :=
    trivialAlgebraMulSemiringAction P A
  letI : SMulCommClass P k A :=
    trivialAlgebraSMulCommClass P k A
  exact
    brauerQuotientAlgebraEquivOfTrivialAction
      (isTrivialAlgebraAction_trivial P A) hP

end CanonicalTrivialAlgebraAction

end Representation
