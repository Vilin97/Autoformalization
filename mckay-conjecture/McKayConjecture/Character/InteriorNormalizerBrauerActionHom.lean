/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InteriorNormalizerBrauerAction

/-!
# The interior normalizer action on the Brauer quotient

Conjugation is oriented throughout this development as
`a ↦ s⁻¹ * a * s`.  It is therefore contravariant in `s`: the
automorphism attached to `s * t` is the composite of those attached
to `s` and then to `t`.  Equivalently, these automorphisms form an
honest action of the opposite of the interior unit normalizer.
-/

noncomputable section

namespace Representation

variable {k P A : Type}
variable [CommRing k] [Group P] [Fintype P]
variable [Ring A] [Algebra k A]
variable [MulSemiringAction P A] [SMulCommClass P k A]

namespace InteriorAction

variable (I : InteriorAction (P := P) (A := A))

/-- Conjugation by the identity normalizer unit acts trivially on the
Brauer quotient. -/
@[simp]
theorem normalizerConjBrauerAlgEquiv_one
    (hI : Function.Injective I.unit) :
    I.normalizerConjBrauerAlgEquiv (k := k) hI 1 = 1 := by
  apply AlgEquiv.ext
  intro x
  obtain ⟨c, rfl⟩ :=
    brauerAlgebraProjection_surjective
      (k := k) (P := P) (A := A) x
  rw [I.normalizerConjBrauerAlgEquiv_brauerAlgebraProjection]
  change
    brauerAlgebraProjection (k := k) (P := P) (A := A) _ =
      brauerAlgebraProjection (k := k) (P := P) (A := A) c
  congr 1
  apply Subtype.ext
  simp [normalizerConjFixedAlgEquiv_apply_coe]

/-- With the convention `a ↦ s⁻¹ * a * s`, normalizer conjugation is
antimultiplicative in the normalizing unit. -/
theorem normalizerConjBrauerAlgEquiv_mul
    (hI : Function.Injective I.unit)
    (s t : I.unitNormalizer) :
    I.normalizerConjBrauerAlgEquiv (k := k) hI (s * t) =
      I.normalizerConjBrauerAlgEquiv (k := k) hI t *
        I.normalizerConjBrauerAlgEquiv (k := k) hI s := by
  apply AlgEquiv.ext
  intro x
  obtain ⟨c, rfl⟩ :=
    brauerAlgebraProjection_surjective
      (k := k) (P := P) (A := A) x
  simp only [AlgEquiv.mul_apply,
    I.normalizerConjBrauerAlgEquiv_brauerAlgebraProjection]
  congr 1
  apply Subtype.ext
  simp [normalizerConjFixedAlgEquiv_apply_coe, mul_assoc]

/-- The honest algebra-automorphism action of the opposite interior
unit normalizer on the Brauer quotient. -/
def normalizerConjBrauerAlgAutHom
    (hI : Function.Injective I.unit) :
    I.unitNormalizerᵐᵒᵖ →*
      (BrauerQuotientAlgebra (k := k) (P := P) (A := A) ≃ₐ[k]
        BrauerQuotientAlgebra (k := k) (P := P) (A := A)) where
  toFun s :=
    I.normalizerConjBrauerAlgEquiv (k := k) hI s.unop
  map_one' := I.normalizerConjBrauerAlgEquiv_one hI
  map_mul' s t := by
    rw [MulOpposite.unop_mul]
    exact I.normalizerConjBrauerAlgEquiv_mul hI t.unop s.unop

@[simp]
theorem normalizerConjBrauerAlgAutHom_apply
    (hI : Function.Injective I.unit)
    (s : I.unitNormalizerᵐᵒᵖ)
    (x : BrauerQuotientAlgebra (k := k) (P := P) (A := A)) :
    I.normalizerConjBrauerAlgAutHom (k := k) hI s x =
      I.normalizerConjBrauerAlgEquiv (k := k) hI s.unop x :=
  rfl

@[simp]
theorem normalizerConjBrauerAlgAutHom_one_apply
    (hI : Function.Injective I.unit)
    (x : BrauerQuotientAlgebra (k := k) (P := P) (A := A)) :
    I.normalizerConjBrauerAlgAutHom (k := k) hI 1 x = x := by
  simp

@[simp]
theorem normalizerConjBrauerAlgAutHom_mul_apply
    (hI : Function.Injective I.unit)
    (s t : I.unitNormalizerᵐᵒᵖ)
    (x : BrauerQuotientAlgebra (k := k) (P := P) (A := A)) :
    I.normalizerConjBrauerAlgAutHom (k := k) hI (s * t) x =
      I.normalizerConjBrauerAlgAutHom (k := k) hI s
        (I.normalizerConjBrauerAlgAutHom (k := k) hI t x) := by
  rw [map_mul]
  rfl

@[simp]
theorem normalizerConjBrauerAlgAutHom_brauerAlgebraProjection
    (hI : Function.Injective I.unit)
    (s : I.unitNormalizerᵐᵒᵖ)
    (c : fixedSubalgebra (k := k) (P := P) (A := A)) :
    I.normalizerConjBrauerAlgAutHom (k := k) hI s
        (brauerAlgebraProjection (k := k) (P := P) (A := A) c) =
      brauerAlgebraProjection (k := k) (P := P) (A := A)
        (I.normalizerConjFixedAlgEquiv (k := k) s.unop c) :=
  rfl

end InteriorAction
end Representation
