/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CrossCharacteristicCoefficientReduction
import McKayConjecture.CharacterTriple.FiniteRootResidueKernel

/-!
# Comparing cyclotomic residue fields with the explicit coefficient field

The integral-lattice construction naturally reduces coefficients into
a residue field of the cyclotomic coefficient ring.  The explicit
cross-characteristic construction instead uses
`PrimeToCoefficientField q n`.

This file packages the exact coefficient-level bridge between them: a
ring homomorphism which carries the residue of every complex `n`th root
to `crossCharacteristicCoefficientReduction q n`.  No representation,
Dade-algebra, or normalizer data occur here.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace FiniteRootCoefficientRing

open Representation

variable (q n : ℕ) [Fact q.Prime] [NeZero n]

/-- A field embedding from the chosen cyclotomic residue field to the
concrete cross-characteristic coefficient field, required to carry
every reduced complex root to the explicit coefficient reduction.

Producing this structure is precisely the remaining coefficient-field
comparison problem between the two constructions. -/
structure CrossCharacteristicResidueEmbedding where
  toRingHom :
    ResidueFieldAbovePrime q n →+*
      PrimeToCoefficientField q n
  map_root :
    (Units.map toRingHom.toMonoidHom).comp
        (rootToResidueField q n) =
      crossCharacteristicCoefficientReduction q n

/-!
## An unconditional residue-compatible Galois field

The maximal ideal above `q` and the cyclic-group equivalence used in
`crossCharacteristicCoefficientReduction` are chosen independently.
Consequently, a homomorphism with the prescribed `map_root` field is
not automatic: two primitive prime-to-`q` roots in a finite field need
not belong to the same Frobenius orbit.

There is, however, a canonical way to remove that choice mismatch.
Replace the independently chosen coefficient field by the Galois field
having exactly the degree of the chosen residue field, and transport
the residue reduction along a chosen finite-field equivalence.  This is
the smallest Galois-field model of the whole chosen residue field.
-/

noncomputable instance residueFieldAbovePrimeZModAlgebra :
    Algebra (ZMod q) (ResidueFieldAbovePrime q n) :=
  ZMod.algebra (ResidueFieldAbovePrime q n) q

/-- The degree over the prime field of the chosen cyclotomic residue
field. -/
def residueDegree : ℕ :=
  Module.finrank (ZMod q) (ResidueFieldAbovePrime q n)

theorem residueDegree_pos :
    0 < residueDegree q n :=
  Module.finrank_pos

noncomputable instance residueDegree_neZero :
    NeZero (residueDegree q n) :=
  ⟨(residueDegree_pos q n).ne'⟩

/-- A concrete Galois-field model having exactly the cardinality of the
chosen cyclotomic residue field. -/
abbrev ResidueCompatibleCoefficientField :=
  GaloisField q (residueDegree q n)

theorem natCard_residueCompatibleCoefficientField :
    Nat.card (ResidueCompatibleCoefficientField q n) =
      q ^ residueDegree q n :=
  GaloisField.card q (residueDegree q n)
    (residueDegree_pos q n).ne'

/-- A chosen finite-field equivalence from the cyclotomic residue field
to its minimal Galois-field model. -/
def residueFieldAlgEquivCompatibleCoefficientField :
    ResidueFieldAbovePrime q n ≃ₐ[ZMod q]
      ResidueCompatibleCoefficientField q n :=
  GaloisField.algEquivGaloisField q (residueDegree q n)
    (FiniteField.pow_finrank_eq_natCard q
      (ResidueFieldAbovePrime q n)).symm

/-- The underlying field embedding into the residue-compatible
coefficient field. -/
def residueCompatibleCoefficientEmbedding :
    ResidueFieldAbovePrime q n →+*
      ResidueCompatibleCoefficientField q n :=
  (residueFieldAlgEquivCompatibleCoefficientField q n).toRingEquiv.toRingHom

/-- Cross-characteristic coefficient reduction compatible by
construction with the chosen maximal ideal above `q`. -/
def residueCompatibleCoefficientReduction :
    rootsOfUnity n ℂ →*
      (ResidueCompatibleCoefficientField q n)ˣ :=
  (Units.map
      (residueCompatibleCoefficientEmbedding q n).toMonoidHom).comp
    (rootToResidueField q n)

@[simp]
theorem residueCompatibleCoefficientReduction_apply
    (z : rootsOfUnity n ℂ) :
    residueCompatibleCoefficientReduction q n z =
      Units.map
        (residueCompatibleCoefficientEmbedding q n).toMonoidHom
        (rootToResidueField q n z) :=
  rfl

/-- Passing to the minimal compatible Galois-field model does not
change the kernel of coefficient reduction. -/
theorem residueCompatibleCoefficientReduction_ker :
    (residueCompatibleCoefficientReduction q n).ker =
      (rootToResidueField q n).ker := by
  exact
    MonoidHom.ker_comp_of_injective
      (rootToResidueField q n)
      (Units.map
        (residueCompatibleCoefficientEmbedding q n).toMonoidHom)
      (Units.map_injective
        (residueFieldAlgEquivCompatibleCoefficientField q n).injective)

/-- The compatible finite-field model kills exactly the `q`-primary
part of the complex roots. -/
theorem residueCompatibleCoefficientReduction_ker_eq_primeToRootsProjection :
    (residueCompatibleCoefficientReduction q n).ker =
      (primeToRootsProjection q n).ker := by
  rw [residueCompatibleCoefficientReduction_ker,
    rootToResidueField_ker]

/-- A transport from the minimal residue-compatible Galois field to the
older explicit coefficient field which also respects the prescribed
root reduction.

This is the exact extra datum missing from an unconditional
`CrossCharacteristicResidueEmbedding`: it is a Frobenius-orbit
compatibility condition, not merely a cardinality condition. -/
structure CompatibleReductionTransport where
  toRingHom :
    ResidueCompatibleCoefficientField q n →+*
      PrimeToCoefficientField q n
  map_root (z : rootsOfUnity n ℂ) :
    Units.map toRingHom.toMonoidHom
        (residueCompatibleCoefficientReduction q n z) =
      crossCharacteristicCoefficientReduction q n z

/-- A compatible transport from the minimal Galois-field model gives
the originally requested residue-field embedding. -/
def CrossCharacteristicResidueEmbedding.ofCompatibleTransport
    (T : CompatibleReductionTransport q n) :
    CrossCharacteristicResidueEmbedding q n where
  toRingHom :=
    T.toRingHom.comp (residueCompatibleCoefficientEmbedding q n)
  map_root := by
    apply MonoidHom.ext
    intro z
    apply Units.ext
    exact congrArg Units.val (T.map_root z)

/-- Conversely, an embedding into the older explicit coefficient field
induces a compatible transport out of the minimal Galois-field model. -/
def CrossCharacteristicResidueEmbedding.toCompatibleTransport
    (E : CrossCharacteristicResidueEmbedding q n) :
    CompatibleReductionTransport q n where
  toRingHom :=
    E.toRingHom.comp
      (residueFieldAlgEquivCompatibleCoefficientField q n).symm.toRingEquiv.toRingHom
  map_root z := by
    apply Units.ext
    simpa [residueCompatibleCoefficientReduction,
      residueCompatibleCoefficientEmbedding] using
      congrArg Units.val (DFunLike.congr_fun E.map_root z)

/-- Exact existence criterion for the originally requested embedding:
the independently chosen reduction must be transportable from the
minimal residue-compatible Galois-field model. -/
theorem nonempty_crossCharacteristicResidueEmbedding_iff :
    Nonempty (CrossCharacteristicResidueEmbedding q n) ↔
      Nonempty (CompatibleReductionTransport q n) :=
  ⟨fun ⟨E⟩ ↦ ⟨E.toCompatibleTransport q n⟩,
    fun ⟨T⟩ ↦ ⟨CrossCharacteristicResidueEmbedding.ofCompatibleTransport
      q n T⟩⟩

/-- Any embedding of the chosen residue field into a finite extension
of the prime field forces the residue degree to divide the target
degree. -/
theorem residueDegree_dvd_finrank_of_ringHom
    {K : Type*} [Field K] [Finite K] [Algebra (ZMod q) K]
    (f : ResidueFieldAbovePrime q n →+* K) :
    residueDegree q n ∣ Module.finrank (ZMod q) K := by
  let fAlg : ResidueFieldAbovePrime q n →ₐ[ZMod q] K :=
    { f with
      commutes' := fun x ↦
        DFunLike.congr_fun
          (Subsingleton.elim
            (f.comp
              (algebraMap
                (ZMod q) (ResidueFieldAbovePrime q n)))
            (algebraMap (ZMod q) K))
          x }
  exact
    FiniteField.nonempty_algHom_iff_finrank_dvd.mp
      ⟨fAlg⟩

/-- In particular, existence of the originally requested embedding
forces the chosen residue degree to divide the degree of the old
explicit Galois field.  This necessary divisibility condition does not
by itself imply the prescribed-root compatibility. -/
theorem residueDegree_dvd_totient_primeToPart
    (E : CrossCharacteristicResidueEmbedding q n) :
    residueDegree q n ∣ Nat.totient (primeToPart q n) := by
  have h :=
    residueDegree_dvd_finrank_of_ringHom q n E.toRingHom
  simpa only [
    GaloisField.finrank q
      (Nat.totient_pos.mpr (primeToPart_pos q n)).ne'] using h

namespace CrossCharacteristicResidueEmbedding

variable
  (E : CrossCharacteristicResidueEmbedding q n)

/-- The induced homomorphism on residue-field units. -/
def unitsHom :
    (ResidueFieldAbovePrime q n)ˣ →*
      (PrimeToCoefficientField q n)ˣ :=
  Units.map E.toRingHom.toMonoidHom

@[simp]
theorem unitsHom_rootToResidueField
    (z : rootsOfUnity n ℂ) :
    unitsHom q n E
        (rootToResidueField q n z) =
      crossCharacteristicCoefficientReduction q n z := by
  exact
    DFunLike.congr_fun
      (CrossCharacteristicResidueEmbedding.map_root E) z

end CrossCharacteristicResidueEmbedding

end FiniteRootCoefficientRing
end CharacterTriple
end McKayConjecture
