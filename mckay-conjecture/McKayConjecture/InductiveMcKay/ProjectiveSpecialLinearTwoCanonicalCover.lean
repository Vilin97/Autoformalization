/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.CentralExtensionSylowNormalizer
import McKayConjecture.GroupTheory.UniversalCoverDominatesPerfectCover
import McKayConjecture.InductiveMcKay.ProjectiveSpecialLinearTwoFamilyReduction

/-!
# Canonical covers of the simple PSL₂ representatives

For every parameter in the simple PSL₂ family, this file records the
honest chain of central extensions

`FreePresentation.Cover PSL(2,q) → SL(2,q) → PSL(2,q)`.

The left-hand source is a genuine universal central extension.  The
special-linear group is a finite perfect central cover, so universality
supplies a canonical surjective central comparison map onto it.

The special-linear cover is deliberately not declared universal.  Such a
statement requires a separate centrally-closedness or Schur-multiplier
calculation and is not even true uniformly: the small fields producing
`A₅` and `A₆` are exceptional and must reuse their separate universal
covers.

The generic central-extension API then gives compatible Sylow lifts and
surjective central extensions between their normalizers.  No local
inductive-McKay data are asserted.
-/

noncomputable section

open scoped IsMulCommutative

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-! ### The perfect special-linear central cover -/

/-- The canonical `SL(2, 𝔽_{r^n})` lying over a parameterized
`PSL(2, 𝔽_{r^n})` representative. -/
abbrev projectiveSpecialLinearTwoSpecialLinearCover
    (a : ProjectiveSpecialLinearTwoSimpleParameter) : Type :=
  letI : Fact a.characteristic.Prime :=
    ⟨a.characteristic_prime⟩
  Matrix.SpecialLinearGroup
    (Fin 2) (GaloisField a.characteristic a.degree)

/-- The canonical special-linear cover is finite. -/
theorem projectiveSpecialLinearTwoSpecialLinearCover_finite
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    Finite (projectiveSpecialLinearTwoSpecialLinearCover a) := by
  letI : Fact a.characteristic.Prime :=
    ⟨a.characteristic_prime⟩
  change
    Finite
      (Matrix.SpecialLinearGroup
        (Fin 2) (GaloisField a.characteristic a.degree))
  infer_instance

/-- The canonical special-linear cover is perfect. -/
theorem projectiveSpecialLinearTwoSpecialLinearCover_isPerfect
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    Group.IsPerfect
      (projectiveSpecialLinearTwoSpecialLinearCover a) := by
  letI : Fact a.characteristic.Prime :=
    ⟨a.characteristic_prime⟩
  let F := GaloisField a.characteristic a.degree
  have hcard : 4 ≤ Nat.card F := by
    dsimp only [F]
    rw [GaloisField.card
      a.characteristic a.degree a.degree_ne_zero]
    exact a.four_le_card
  obtain ⟨x, hx0, hx2⟩ :=
    exists_ne_zero_sq_ne_one_of_four_le_natCard hcard
  exact
    ⟨Matrix.SL2.commutator_eq_top hx0 hx2⟩

/-- The quotient map `SL(2,q) → PSL(2,q)` as a central extension. -/
def projectiveSpecialLinearTwoSpecialLinearCentralExtension
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    CentralExtension
      (projectiveSpecialLinearTwoSpecialLinearCover a)
      (projectiveSpecialLinearTwoRepresentative a) := by
  letI : Fact a.characteristic.Prime :=
    ⟨a.characteristic_prime⟩
  change
    CentralExtension
      (Matrix.SpecialLinearGroup
        (Fin 2) (GaloisField a.characteristic a.degree))
      (Matrix.SpecialLinearGroup
        (Fin 2) (GaloisField a.characteristic a.degree) ⧸
          Subgroup.center
            (Matrix.SpecialLinearGroup
              (Fin 2) (GaloisField a.characteristic a.degree)))
  exact
    centralQuotientExtension
      (Matrix.SpecialLinearGroup
        (Fin 2) (GaloisField a.characteristic a.degree))

/-- The kernel of the special-linear projection is exactly its center. -/
@[simp]
theorem
    projectiveSpecialLinearTwoSpecialLinearCentralExtension_ker_eq_center
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    (projectiveSpecialLinearTwoSpecialLinearCentralExtension
      a).projection.ker =
        Subgroup.center
          (projectiveSpecialLinearTwoSpecialLinearCover a) :=
  (projectiveSpecialLinearTwoSpecialLinearCentralExtension a).ker_eq_center
    (projectiveSpecialLinearTwoRepresentative_isSimpleGroup a)
    (projectiveSpecialLinearTwoRepresentative_not_isMulCommutative a)

/-- The special-linear cover is quasisimple. -/
theorem projectiveSpecialLinearTwoSpecialLinearCover_isQuasisimple
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    IsQuasisimple
      (projectiveSpecialLinearTwoSpecialLinearCover a) :=
  (projectiveSpecialLinearTwoSpecialLinearCentralExtension a).source_isQuasisimple
    (projectiveSpecialLinearTwoSpecialLinearCover_isPerfect a)
    (projectiveSpecialLinearTwoRepresentative_isSimpleGroup a)
    (projectiveSpecialLinearTwoRepresentative_not_isMulCommutative a)

/-! ### The genuine free-presentation universal cover -/

/-- The canonical free-presentation universal cover of a parameterized
PSL₂ representative. -/
abbrev projectiveSpecialLinearTwoUniversalCover
    (a : ProjectiveSpecialLinearTwoSimpleParameter) : Type :=
  FreePresentation.Cover
    (projectiveSpecialLinearTwoRepresentative a)

/-- The canonical universal central extension of a parameterized PSL₂
representative. -/
def projectiveSpecialLinearTwoUniversalCentralExtension
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    UniversalCentralExtension
      (projectiveSpecialLinearTwoUniversalCover a)
      (projectiveSpecialLinearTwoRepresentative a) :=
  FreePresentation.universalCentralExtension
    (projectiveSpecialLinearTwoRepresentative_isPerfect a)

/-- The free-presentation universal cover is perfect. -/
instance projectiveSpecialLinearTwoUniversalCover_isPerfect
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    Group.IsPerfect
      (projectiveSpecialLinearTwoUniversalCover a) :=
  (projectiveSpecialLinearTwoUniversalCentralExtension a).sourcePerfect

/-- The free-presentation universal cover is finite. -/
instance projectiveSpecialLinearTwoUniversalCover_finite
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    Finite (projectiveSpecialLinearTwoUniversalCover a) :=
  (projectiveSpecialLinearTwoUniversalCentralExtension
    a).toCentralExtension.finite_source
      (projectiveSpecialLinearTwoUniversalCentralExtension a).sourcePerfect

/-- Universality gives a canonical surjective central map from the genuine
universal cover onto the perfect special-linear cover. -/
def projectiveSpecialLinearTwoUniversalCoverToSpecialLinear
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    CentralExtension
      (projectiveSpecialLinearTwoUniversalCover a)
      (projectiveSpecialLinearTwoSpecialLinearCover a) :=
  (projectiveSpecialLinearTwoUniversalCentralExtension
    a).centralExtensionToPerfectCover
      (projectiveSpecialLinearTwoSpecialLinearCentralExtension a)
      (projectiveSpecialLinearTwoSpecialLinearCover_isPerfect a)

/-- The universal-to-special-linear comparison commutes with the two
projections to `PSL(2,q)`. -/
theorem
    projectiveSpecialLinearTwoUniversalCoverToSpecialLinear_commutes
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    (projectiveSpecialLinearTwoSpecialLinearCentralExtension a).projection.comp
        (projectiveSpecialLinearTwoUniversalCoverToSpecialLinear a).projection =
      (projectiveSpecialLinearTwoUniversalCentralExtension
        a).toCentralExtension.projection :=
  (projectiveSpecialLinearTwoUniversalCentralExtension
    a).mapToCentralExtension_commutes
      (projectiveSpecialLinearTwoSpecialLinearCentralExtension a)

/-! ### Compatible Sylow lifts and normalizer extensions -/

/-- A fixed Sylow subgroup of the projective representative. -/
def projectiveSpecialLinearTwoRepresentativeSylow
    (p : ℕ)
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    Sylow p (projectiveSpecialLinearTwoRepresentative a) :=
  default

/-- The unique Sylow subgroup of the special-linear cover mapping onto the
fixed projective Sylow subgroup. -/
def projectiveSpecialLinearTwoSpecialLinearSylow
    (p : ℕ) [Fact p.Prime]
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    Sylow p (projectiveSpecialLinearTwoSpecialLinearCover a) :=
  (projectiveSpecialLinearTwoSpecialLinearCentralExtension a).sylowLift
    (projectiveSpecialLinearTwoRepresentativeSylow p a)

/-- The chosen special-linear Sylow maps onto the chosen projective Sylow. -/
@[simp]
theorem projectiveSpecialLinearTwoSpecialLinearSylow_map
    (p : ℕ) [Fact p.Prime]
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    ((projectiveSpecialLinearTwoSpecialLinearSylow p a :
        Sylow p (projectiveSpecialLinearTwoSpecialLinearCover a)) :
      Subgroup (projectiveSpecialLinearTwoSpecialLinearCover a)).map
        (projectiveSpecialLinearTwoSpecialLinearCentralExtension
          a).projection =
      (projectiveSpecialLinearTwoRepresentativeSylow p a :
        Subgroup (projectiveSpecialLinearTwoRepresentative a)) :=
  (projectiveSpecialLinearTwoSpecialLinearCentralExtension
    a).sylowLift_map
      (projectiveSpecialLinearTwoRepresentativeSylow p a)

/-- Restriction of `SL(2,q) → PSL(2,q)` to the corresponding Sylow
normalizers is again a surjective central extension. -/
def projectiveSpecialLinearTwoSpecialLinearSylowNormalizerExtension
    (p : ℕ) [Fact p.Prime]
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    CentralExtension
      (Subgroup.normalizer
        (projectiveSpecialLinearTwoSpecialLinearSylow p a :
          Set (projectiveSpecialLinearTwoSpecialLinearCover a)))
      (Subgroup.normalizer
        (projectiveSpecialLinearTwoRepresentativeSylow p a :
          Set (projectiveSpecialLinearTwoRepresentative a))) :=
  (projectiveSpecialLinearTwoSpecialLinearCentralExtension
    a).sylowNormalizerCentralExtension
      (projectiveSpecialLinearTwoRepresentativeSylow p a)

/-- The unique Sylow subgroup of the genuine universal cover mapping onto
the chosen special-linear Sylow subgroup. -/
def projectiveSpecialLinearTwoUniversalCoverSylow
    (p : ℕ) [Fact p.Prime]
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    Sylow p (projectiveSpecialLinearTwoUniversalCover a) :=
  (projectiveSpecialLinearTwoUniversalCoverToSpecialLinear a).sylowLift
    (projectiveSpecialLinearTwoSpecialLinearSylow p a)

/-- The chosen universal-cover Sylow maps onto the chosen special-linear
Sylow. -/
@[simp]
theorem projectiveSpecialLinearTwoUniversalCoverSylow_map
    (p : ℕ) [Fact p.Prime]
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    ((projectiveSpecialLinearTwoUniversalCoverSylow p a :
        Sylow p (projectiveSpecialLinearTwoUniversalCover a)) :
      Subgroup (projectiveSpecialLinearTwoUniversalCover a)).map
        (projectiveSpecialLinearTwoUniversalCoverToSpecialLinear
          a).projection =
      (projectiveSpecialLinearTwoSpecialLinearSylow p a :
        Subgroup (projectiveSpecialLinearTwoSpecialLinearCover a)) :=
  (projectiveSpecialLinearTwoUniversalCoverToSpecialLinear
    a).sylowLift_map
      (projectiveSpecialLinearTwoSpecialLinearSylow p a)

/-- Restriction of the universal-to-special-linear comparison to the
corresponding Sylow normalizers is again a surjective central extension. -/
def projectiveSpecialLinearTwoUniversalCoverSylowNormalizerExtension
    (p : ℕ) [Fact p.Prime]
    (a : ProjectiveSpecialLinearTwoSimpleParameter) :
    CentralExtension
      (Subgroup.normalizer
        (projectiveSpecialLinearTwoUniversalCoverSylow p a :
          Set (projectiveSpecialLinearTwoUniversalCover a)))
      (Subgroup.normalizer
        (projectiveSpecialLinearTwoSpecialLinearSylow p a :
          Set (projectiveSpecialLinearTwoSpecialLinearCover a))) :=
  (projectiveSpecialLinearTwoUniversalCoverToSpecialLinear
    a).sylowNormalizerCentralExtension
      (projectiveSpecialLinearTwoSpecialLinearSylow p a)

end InductiveMcKay
end McKayConjecture
