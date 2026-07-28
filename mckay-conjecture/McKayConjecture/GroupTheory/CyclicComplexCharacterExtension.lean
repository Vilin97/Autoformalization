/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Extending characters from finite cyclic groups

Every character from a subgroup of a finite cyclic group to the complex
units extends to the whole group.  This is the multiplicative form of
extension into the divisible group `ℂˣ`; the proof uses finite-abelian
duality and the existence of complex roots of unity.

The second part packages the standard factorization of a homomorphism
through the range of another homomorphism when the corresponding kernel
inclusion holds.
-/

noncomputable section

namespace MonoidHom

variable {G H A : Type*}
variable [Group G] [Group H] [Group A]

/-- A homomorphism whose kernel contains the kernel of `f` factors
canonically, up to the noncomputable choice of preimages, through the
range of `f`. -/
def factorThroughRange
    (f : G →* H)
    (g : G →* A)
    (hker : f.ker ≤ g.ker) :
    f.range →* A :=
  f.rangeRestrict.liftOfSurjective
    f.rangeRestrict_surjective
    ⟨g, by simpa only [ker_rangeRestrict] using hker⟩

@[simp]
theorem factorThroughRange_apply
    (f : G →* H)
    (g : G →* A)
    (hker : f.ker ≤ g.ker)
    (x : G) :
    factorThroughRange f g hker (f.rangeRestrict x) =
      g x := by
  change
    (f.rangeRestrict.liftOfRightInverse
      (Function.surjInv f.rangeRestrict_surjective)
      (Function.rightInverse_surjInv
        f.rangeRestrict_surjective)
      ⟨g, by simpa only [ker_rangeRestrict] using hker⟩)
        (f.rangeRestrict x) =
      g x
  exact
    f.rangeRestrict.liftOfRightInverse_comp_apply
      (Function.surjInv f.rangeRestrict_surjective)
      (Function.rightInverse_surjInv
        f.rangeRestrict_surjective)
      ⟨g, by simpa only [ker_rangeRestrict] using hker⟩
      x

/-- Every complex character of a subgroup of a finite cyclic group
extends to a character of the whole group. -/
theorem exists_extension_to_complexUnits_of_isCyclic
    [Finite G] [IsCyclic G]
    (S : Subgroup G)
    (χ : S →* ℂˣ) :
    ∃ κ : G →* ℂˣ, κ.domRestrict S = χ := by
  letI : CommGroup G :=
    IsCyclic.commGroup
  exact
    (MonoidHom.domRestrict_surjective ℂ S) χ

end MonoidHom
