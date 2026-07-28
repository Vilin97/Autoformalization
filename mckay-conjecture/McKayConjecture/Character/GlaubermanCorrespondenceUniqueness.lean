/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanCorrespondence

/-!
# Uniqueness of the Glauberman correspondence

The Glauberman correspondence is characterized pointwise by the unique
restriction multiplicity prime to `p`.  Consequently two packaged
correspondences have the same character equivalence, and hence are equal.

This lets downstream constructions work with one canonical correspondence
and transport their conclusions to any value of the public
`GlaubermanCorrespondence` interface.
-/

noncomputable section

namespace McKayConjecture

open CliffordCorrespondence

variable {G : Type} [Group G]
variable {p : ℕ}
variable {K P : Subgroup G} [K.Normal]

namespace GlaubermanCorrespondence

/-- The numerical characterization forces any two Glauberman character
equivalences to agree. -/
theorem characterEquiv_eq
    (d e : GlaubermanCorrespondence K P p) :
    d.characterEquiv = e.characterEquiv := by
  ext theta
  exact
    (d.eq_correspondent_of_multiplicity_isPPrime
        theta
        (e.characterEquiv theta)
        (e.multiplicity_isPPrime theta)).symm

/-- The ordinary Glauberman correspondence is unique whenever it exists. -/
theorem eq
    (d e : GlaubermanCorrespondence K P p) :
    d = e := by
  have h := characterEquiv_eq d e
  cases d
  cases e
  cases h
  rfl

end GlaubermanCorrespondence

/-- The numerical Glauberman interface has at most one inhabitant. -/
instance glaubermanCorrespondenceSubsingleton :
    Subsingleton (GlaubermanCorrespondence K P p) :=
  ⟨GlaubermanCorrespondence.eq⟩

end McKayConjecture
