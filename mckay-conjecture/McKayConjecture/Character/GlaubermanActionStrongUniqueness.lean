/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanActionStrong

/-!
# Uniqueness of strong action Glauberman correspondences

The full restriction-multiplicity characterization in a strong action
Glauberman correspondence determines its character equivalence pointwise.
Thus the entire packaged correspondence is unique whenever it exists.
-/

noncomputable section

namespace McKayConjecture

variable (P A : Type) [Group P] [Group A]
variable [MulDistribMulAction P A]
variable {p : ℕ}

namespace StrongActionGlaubermanCorrespondence

/-- Any two strong action Glauberman character equivalences agree. -/
theorem characterEquiv_eq
    (d e : StrongActionGlaubermanCorrespondence P A p) :
    d.characterEquiv = e.characterEquiv := by
  ext theta
  apply Subtype.ext
  exact
    (d.eq_correspondent_of_multiplicity_isPPrime
        theta
        (e.characterEquiv theta).1
        (e.multiplicity_isPPrime theta)).symm

/-- A strong action Glauberman correspondence is unique whenever it
exists. -/
theorem eq
    (d e : StrongActionGlaubermanCorrespondence P A p) :
    d = e := by
  have h := characterEquiv_eq P A d e
  cases d
  cases e
  cases h
  rfl

end StrongActionGlaubermanCorrespondence

/-- The strong action Glauberman interface has at most one inhabitant. -/
instance strongActionGlaubermanCorrespondenceSubsingleton :
    Subsingleton (StrongActionGlaubermanCorrespondence P A p) :=
  ⟨StrongActionGlaubermanCorrespondence.eq P A⟩

end McKayConjecture
