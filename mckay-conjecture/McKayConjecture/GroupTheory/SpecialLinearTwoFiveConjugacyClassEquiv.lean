/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.SpecialLinearTwoFiveConjugacyClasses

/-!
# Indexing the conjugacy classes of `SL(2, 𝔽₅)`

The unique-representative certificate upgrades the nine displayed rows to
an equivalence with the abstract quotient type of conjugacy classes.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- The nine certified representatives index the abstract conjugacy-class
quotient without duplication. -/
def specialLinearTwoFiveConjugacyClassEquiv :
    SpecialLinearTwoFiveConjugacyClass ≃
      ConjClasses SpecialLinearTwoFive :=
  Equiv.ofBijective
    (fun c =>
      ConjClasses.mk
        (specialLinearTwoFiveConjugacyRepresentative c)) <| by
      constructor
      · intro c d h
        have hcd :
            IsConj
              (specialLinearTwoFiveConjugacyRepresentative c)
              (specialLinearTwoFiveConjugacyRepresentative d) :=
          ConjClasses.mk_eq_mk_iff_isConj.mp h
        obtain ⟨e, he, heUnique⟩ :=
          specialLinearTwoFive_existsUnique_conjugacyClass
            (specialLinearTwoFiveConjugacyRepresentative c)
        exact
          (heUnique c (IsConj.refl _)).trans
            (heUnique d hcd).symm
      · intro q
        refine Quotient.inductionOn' q ?_
        intro g
        obtain ⟨c, hc, _⟩ :=
          specialLinearTwoFive_existsUnique_conjugacyClass g
        exact
          ⟨c,
            (ConjClasses.mk_eq_mk_iff_isConj.mpr hc).symm⟩

/-- `SL(2, 𝔽₅)` has exactly nine conjugacy classes. -/
theorem natCard_conjClasses_specialLinearTwoFive :
    Nat.card (ConjClasses SpecialLinearTwoFive) = 9 := by
  rw [← Nat.card_congr
    specialLinearTwoFiveConjugacyClassEquiv]
  exact Nat.card_fin 9

end GroupTheory
end McKayConjecture
