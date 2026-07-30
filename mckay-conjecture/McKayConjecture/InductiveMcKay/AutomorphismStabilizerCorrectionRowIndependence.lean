/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixLocalAutomorphismAction
import McKayConjecture.InductiveMcKay.AutomorphismStabilizerCorrection
import McKayConjecture.InductiveMcKay.NormalizerInnerAutomorphismStabilizer

/-!
# Independence of the Sylow correction on local character rows

An automorphism can be corrected into the stabilizer of a fixed Sylow
subgroup by any element carrying its image Sylow subgroup back to the
chosen one.  Two such correcting elements differ by an element of the
Sylow normalizer.  Hence the resulting stabilizer automorphisms differ by
an inner normalizer automorphism.

Inner normalizer automorphisms act trivially on irreducible characters of
the normalizer.  Consequently the semantic local row permutation is
independent of the noncanonical Sylow-conjugacy choice.  This permits
finite calculations to use an explicit correction while the public
construction retains the abstract chosen correction.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace InductiveMcKay
namespace SylowAutStabilizer

variable {G : Type u} [Group G] [Finite G]
  {p : ℕ} [Fact p.Prime]

/-- Correct an automorphism using a specified element carrying its image
of `P` back to `P`. -/
def correctedWithConjugator
    (P : Sylow p G)
    (a : MulAut G)
    (g : G)
    (hg : g • (a • P) = P) :
  SylowAutStabilizer P :=
  ⟨MulAut.conj g * a, by
    rw [mem_iff, mul_smul, ← Sylow.smul_def]
    exact hg⟩

@[simp]
theorem correctedWithConjugator_coe
    (P : Sylow p G)
    (a : MulAut G)
    (g : G)
    (hg : g • (a • P) = P) :
    (correctedWithConjugator P a g hg : MulAut G) =
      MulAut.conj g * a :=
  rfl

/-- The chosen correction is the specialization using the abstract
Sylow-conjugacy witness. -/
theorem correctedWithConjugator_correctionConjugator
    (P : Sylow p G)
    (a : MulAut G) :
    correctedWithConjugator P a
        (correctionConjugator P a)
        (correctionConjugator_smul P a) =
      corrected P a := by
  apply Subtype.ext
  rfl

/-- The quotient of two valid correcting elements lies in the Sylow
normalizer. -/
def correctionRatioNormalizer
    (P : Sylow p G)
    (a : MulAut G)
    (g h : G)
    (hg : g • (a • P) = P)
    (hh : h • (a • P) = P) :
    SylowNormalizer P :=
  ⟨g * h⁻¹, Sylow.smul_eq_iff_mem_normalizer.mp (by
    have hh' := congrArg (fun Q : Sylow p G ↦ h⁻¹ • Q) hh
    have hhInv : a • P = h⁻¹ • P := by
      simpa [← mul_smul] using hh'
    rw [mul_smul, ← hhInv, hg])⟩

/-- Two specified corrections differ on the left by conjugation with the
normalizer element given by their ratio. -/
theorem correctedWithConjugator_eq_normalizerInner_mul
    (P : Sylow p G)
    (a : MulAut G)
    (g h : G)
    (hg : g • (a • P) = P)
    (hh : h • (a • P) = P) :
    correctedWithConjugator P a g hg =
      normalizerInnerHom P
          (correctionRatioNormalizer P a g h hg hh) *
        correctedWithConjugator P a h hh := by
  apply Subtype.ext
  change
    MulAut.conj g * a =
      MulAut.conj (g * h⁻¹) * (MulAut.conj h * a)
  simp only [map_mul, map_inv]
  simp [mul_assoc]

/-- Transporting local prime-to-`p` characters through an arbitrary row
enumeration gives the same permutation for any two valid corrections. -/
theorem normalizerPPrimeRowPermutation_correctedWithConjugator_eq
    (P : Sylow p G)
    (a : MulAut G)
    (g h : G)
    (hg : g • (a • P) = P)
    (hh : h • (a • P) = P)
    {Row : Type v} [Fintype Row]
    (e :
      Row ≃
        PPrimeIrreducibleCharacter (SylowNormalizer P) p) :
    normalizerPPrimeRowPermutation P e
        (correctedWithConjugator P a g hg) =
      normalizerPPrimeRowPermutation P e
        (correctedWithConjugator P a h hh) := by
  rw [correctedWithConjugator_eq_normalizerInner_mul,
    normalizerPPrimeRowPermutation_mul]
  have hInner :
      normalizerPPrimeRowPermutation P e
          (normalizerInnerHom P
            (correctionRatioNormalizer P a g h hg hh)) =
        1 := by
    apply Equiv.ext
    intro r
    apply e.injective
    simp
  rw [hInner, one_mul]

/-- In particular, an explicit correction has the same local row action
as the abstract correction selected by Sylow conjugacy. -/
theorem normalizerPPrimeRowPermutation_correctedWithConjugator_eq_corrected
    (P : Sylow p G)
    (a : MulAut G)
    (g : G)
    (hg : g • (a • P) = P)
    {Row : Type v} [Fintype Row]
    (e :
      Row ≃
        PPrimeIrreducibleCharacter (SylowNormalizer P) p) :
    normalizerPPrimeRowPermutation P e
        (correctedWithConjugator P a g hg) =
      normalizerPPrimeRowPermutation P e (corrected P a) := by
  rw [← correctedWithConjugator_correctionConjugator P a]
  exact
    normalizerPPrimeRowPermutation_correctedWithConjugator_eq
      P a g (correctionConjugator P a) hg
        (correctionConjugator_smul P a) e

end SylowAutStabilizer
end InductiveMcKay
end McKayConjecture
