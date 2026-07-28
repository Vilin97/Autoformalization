/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DadeAlgebraPrimitiveDimension
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalSelectedSummandArithmetic
import McKayConjecture.InductiveMcKay.NormalSubgroupCentralIntersectionGlaubermanCanonicalNormalizerLift

/-!
# Recovering the Glauberman multiplicity from a reduced Dade module

If a cross-characteristic model of the canonical selected summand preserves
dimension, Brauer primitivity of its endomorphism Dade algebra already forces
the required prime-to-`q` multiplicity.  Thus the multiplicity hypothesis in
the reduced-factor boundary is not independent once the Dade algebra is
realized on the correct module.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction
namespace Proposition45

open CharacterTriple
open ComplementReduction
open GroupTheory

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- A dimension-preserving cross-characteristic model whose endomorphism
algebra is Brauer-primitive supplies the prime-to-`q` normal-restriction
multiplicity required by the final obstruction argument. -/
theorem
    productAmbientGlaubermanNormalRestrictionMultiplicityIsPPrime_of_reducedEndomorphismDade
    (hcentral :
      C ⊓ (S : Subgroup X) ≤ Subgroup.center X)
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (g : ProductGlaubermanCorrespondence S C hcentral)
    (theta :
      PPrimeIrreducibleCharacter (product S C) q)
    {k P V : Type}
    [Field k] [CharP k q]
    [Group P] [Fintype P]
    [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V]
    [MulSemiringAction P (Module.End k V)]
    [SMulCommClass P k (Module.End k V)]
    (D : _root_.Representation.DadeAlgebra q k P (Module.End k V))
    (hprimitive : D.IsBrauerPrimitive)
    (hrank :
      Module.finrank k V =
        Module.finrank ℂ
          (ProductAmbientGlaubermanCanonicalSelectedSummand
            S C hcentral hgenerate g theta)) :
    ProductAmbientGlaubermanNormalRestrictionMultiplicityIsPPrime
      S C hcentral hgenerate g theta := by
  unfold ProductAmbientGlaubermanNormalRestrictionMultiplicityIsPPrime
  rw [
    ← productAmbientGlaubermanCanonicalSelectedSummand_finrank
      S C hcentral hgenerate g theta,
    ← hrank]
  exact
    D.not_dvd_finrank_of_endomorphism_isBrauerPrimitive hprimitive

end Proposition45
end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
