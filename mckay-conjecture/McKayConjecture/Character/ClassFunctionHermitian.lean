/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.IrreducibleCharacterBasis
import McKayConjecture.Character.InverseConjugate

/-!
# The Hermitian pairing on complex class functions

The existing class-function pairing is bilinear and evaluates its
second argument at the inverse.  For Fourier estimates it is useful to
also record the usual Hermitian pairing.  Ordinary irreducible
characters identify the two pairings, and completeness gives Parseval's
identity.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace McKayConjecture
namespace ClassFunction

variable {G : Type} [Group G] [Finite G]

/-- The normalized Hermitian pairing on complex class functions. -/
def normalizedHermitianPairing
    (f k : ClassFunction G) : ℂ := by
  letI : Fintype G := Fintype.ofFinite G
  exact
    (Nat.card G : ℂ)⁻¹ *
      ∑ g : G, f g * conj (k g)

private def normalizedHermitianPairingLeft
    (k : ClassFunction G) :
    ClassFunction G →ₗ[ℂ] ℂ := by
  letI : Fintype G := Fintype.ofFinite G
  refine
    { toFun := fun f ↦ normalizedHermitianPairing f k
      map_add' := ?_
      map_smul' := ?_ }
  · intro f₁ f₂
    simp only [normalizedHermitianPairing,
      AddMemClass.coe_add, Pi.add_apply, add_mul,
      Finset.sum_add_distrib]
    ring
  · intro a f
    simp only [normalizedHermitianPairing,
      SetLike.val_smul, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro g _hg
    ring

/-- The Hermitian pairing is linear in its first argument. -/
theorem normalizedHermitianPairing_sum_left
    {ι : Type*} [Fintype ι]
    (f : ι → ClassFunction G) (k : ClassFunction G) :
    normalizedHermitianPairing (∑ i, f i) k =
      ∑ i, normalizedHermitianPairing (f i) k := by
  change
    normalizedHermitianPairingLeft k (∑ i, f i) =
      ∑ i, normalizedHermitianPairingLeft k (f i)
  simpa using
    map_sum (normalizedHermitianPairingLeft k) f Finset.univ

/-- Scalar multiplication in the first argument leaves the scalar
unconjugated. -/
theorem normalizedHermitianPairing_smul_left
    (a : ℂ) (f k : ClassFunction G) :
    normalizedHermitianPairing (a • f) k =
      a * normalizedHermitianPairing f k := by
  change
    normalizedHermitianPairingLeft k (a • f) =
      a * normalizedHermitianPairingLeft k f
  exact map_smul (normalizedHermitianPairingLeft k) a f

/-- Conjugate symmetry of the normalized Hermitian pairing. -/
theorem normalizedHermitianPairing_conj_symm
    (f k : ClassFunction G) :
    normalizedHermitianPairing k f =
      conj (normalizedHermitianPairing f k) := by
  letI : Fintype G := Fintype.ofFinite G
  change
    (Nat.card G : ℂ)⁻¹ *
        ∑ g : G, k g * conj (f g) =
      conj
        ((Nat.card G : ℂ)⁻¹ *
          ∑ g : G, f g * conj (k g))
  rw [map_mul, map_inv₀, map_natCast, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro g _hg
  rw [map_mul, Complex.conj_conj]
  ring

/-- Against an ordinary irreducible character, the Hermitian pairing
is the existing inverse-value bilinear pairing. -/
theorem normalizedHermitianPairing_irreducible_right
    (f : ClassFunction G) (χ : IrreducibleCharacter G) :
    normalizedHermitianPairing f χ.toClassFunction =
      normalizedPairing f χ.toClassFunction := by
  letI : Fintype G := Fintype.ofFinite G
  change
    (Nat.card G : ℂ)⁻¹ *
        ∑ g : G, f g * conj (χ.values g) =
      (Nat.card G : ℂ)⁻¹ *
        ∑ g : G, f g * χ.values g⁻¹
  congr 1
  apply Finset.sum_congr rfl
  intro g _hg
  rw [IrreducibleCharacter.value_inv_eq_conj]

/-- The sum of the squared norms of the irreducible Fourier
coefficients of a class function. -/
def fourierCoefficientNormSqSum
    (f : ClassFunction G) : ℂ := by
  letI : Fintype (IrreducibleCharacter G) :=
    irreducibleCharacterBasisFintype
  exact
    ∑ χ : IrreducibleCharacter G,
      normalizedPairing f χ.toClassFunction *
        conj (normalizedPairing f χ.toClassFunction)

/-- Parseval's identity for irreducible Fourier coefficients of a
complex class function. -/
theorem normalizedHermitianPairing_self_eq_fourierCoefficientNormSqSum
    (f : ClassFunction G) :
    normalizedHermitianPairing f f =
      fourierCoefficientNormSqSum f := by
  classical
  letI : Fintype (IrreducibleCharacter G) :=
    irreducibleCharacterBasisFintype
  rw [fourierCoefficientNormSqSum]
  calc
    normalizedHermitianPairing f f =
        normalizedHermitianPairing
          (∑ χ : IrreducibleCharacter G,
            normalizedPairing f χ.toClassFunction •
              χ.toClassFunction)
          f := by
      exact congrArg
        (fun k : ClassFunction G ↦
          normalizedHermitianPairing k f)
        (irreducibleCharacter_fourierExpansion f)
    _ = ∑ χ : IrreducibleCharacter G,
          normalizedHermitianPairing
            (normalizedPairing f χ.toClassFunction •
              χ.toClassFunction)
            f :=
      normalizedHermitianPairing_sum_left _ _
    _ = ∑ χ : IrreducibleCharacter G,
          normalizedPairing f χ.toClassFunction *
            normalizedHermitianPairing χ.toClassFunction f := by
      apply Finset.sum_congr rfl
      intro χ _hχ
      exact normalizedHermitianPairing_smul_left _ _ _
    _ = ∑ χ : IrreducibleCharacter G,
          normalizedPairing f χ.toClassFunction *
            conj
              (normalizedHermitianPairing
                f χ.toClassFunction) := by
      apply Finset.sum_congr rfl
      intro χ _hχ
      rw [normalizedHermitianPairing_conj_symm]
    _ = _ := by
      simp_rw [normalizedHermitianPairing_irreducible_right]

end ClassFunction
end McKayConjecture
