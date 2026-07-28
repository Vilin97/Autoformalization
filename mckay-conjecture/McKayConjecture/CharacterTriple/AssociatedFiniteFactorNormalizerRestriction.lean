/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedFiniteFactorQuotient
import McKayConjecture.CharacterTriple.FactorSetCentralExtensionNormalizer
import McKayConjecture.CharacterTriple.SubgroupRestriction

/-!
# Restricting a finite factor extension to a quotient Sylow normalizer

Let `T = (A, N, ζ)` be a character triple and let `S` be a Sylow subgroup
of `A / N`.  Write `D = N_{A/N}(S)` and let `B` be the full preimage of
`D` in `A`.

The canonical copy `N.subgroupOf B` defines a restricted character triple
on `B`.  The association-preserving finite normalization of an associated
projective lift restricts literally to an associated projective lift of this
triple.

The determinant normalization is not run a second time on `B`: doing so
would make new representative choices.  Instead, this file pulls the fixed
finite quotient factor set back along the canonical equivalence

`B / N ≃* D`.

This pulled-back factor set is exactly the factor of the restricted normalized
lift.  Consequently its concrete factor extension is canonically isomorphic
to the normalizer of the unique Sylow lift in the original concrete factor
extension.  The equivalence preserves the base projection and the coefficient
embedding.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace CharacterTriple
namespace AssociatedProjectiveRepresentation

variable {A : Type u} [Finite A] [Group A]
variable {T : CharacterTriple A}
variable {V : Type}
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ A V}
variable {p : ℕ} [Fact p.Prime]

/-- The full preimage in `A` of the normalizer of a Sylow subgroup of the
outer quotient `A / N`. -/
abbrev quotientSylowNormalizerPreimage
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    Subgroup A :=
  (Subgroup.normalizer
      (S : Set (A ⧸ T.normalSubgroup))).comap
    (QuotientGroup.mk' T.normalSubgroup)

omit [Fact p.Prime] in
/-- The normal subgroup of the triple lies in the full preimage of every
quotient Sylow normalizer. -/
theorem normalSubgroup_le_quotientSylowNormalizerPreimage
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    T.normalSubgroup ≤
      quotientSylowNormalizerPreimage T S := by
  intro n hn
  change
    QuotientGroup.mk' T.normalSubgroup n ∈
      Subgroup.normalizer
        (S : Set (A ⧸ T.normalSubgroup))
  rw [show
      QuotientGroup.mk' T.normalSubgroup n = 1 from
        (QuotientGroup.eq_one_iff n).mpr hn]
  exact
    (Subgroup.normalizer
      (S : Set (A ⧸ T.normalSubgroup))).one_mem

/-- The character triple on the full preimage of the quotient Sylow
normalizer, with its canonical copy of the original normal subgroup. -/
abbrev quotientSylowNormalizerRestrictionTriple
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    CharacterTriple
      (quotientSylowNormalizerPreimage T S) :=
  T.restrictTo
    (quotientSylowNormalizerPreimage T S)
    (normalSubgroup_le_quotientSylowNormalizerPreimage
      T S)

/-- The association-preserving finite normalization, restricted literally to
the full preimage of the quotient Sylow normalizer. -/
def associatedFiniteFactorNormalizerRestriction
    (R : AssociatedProjectiveRepresentation T V P)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    AssociatedProjectiveRepresentation
      (quotientSylowNormalizerRestrictionTriple T S) V
      (R.associatedFiniteFactorProjective.comap
        (quotientSylowNormalizerPreimage T S).subtype) :=
  R.associatedFiniteFactorAssociated.restrictTo
    (quotientSylowNormalizerPreimage T S)
    (normalSubgroup_le_quotientSylowNormalizerPreimage
      T S)

/-- Projection from the full preimage to the quotient Sylow normalizer. -/
def quotientSylowNormalizerHom
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    quotientSylowNormalizerPreimage T S →*
      Subgroup.normalizer
        (S : Set (A ⧸ T.normalSubgroup)) :=
  (((QuotientGroup.mk' T.normalSubgroup).domRestrict
      (quotientSylowNormalizerPreimage T S)).codRestrict
    (Subgroup.normalizer
      (S : Set (A ⧸ T.normalSubgroup)))
    (fun x ↦ x.property))

omit [Fact p.Prime] in
@[simp]
theorem quotientSylowNormalizerHom_apply_coe
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (x : quotientSylowNormalizerPreimage T S) :
    ((quotientSylowNormalizerHom T S x :
        Subgroup.normalizer
          (S : Set (A ⧸ T.normalSubgroup))) :
      A ⧸ T.normalSubgroup) =
        QuotientGroup.mk' T.normalSubgroup (x : A) :=
  rfl

omit [Fact p.Prime] in
/-- The projection from the full preimage onto the quotient normalizer is
surjective. -/
theorem quotientSylowNormalizerHom_surjective
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    Function.Surjective
      (quotientSylowNormalizerHom T S) := by
  intro y
  obtain ⟨a, ha⟩ :=
    QuotientGroup.mk'_surjective
      T.normalSubgroup (y : A ⧸ T.normalSubgroup)
  let x : quotientSylowNormalizerPreimage T S :=
    ⟨a, by
      change
        QuotientGroup.mk' T.normalSubgroup a ∈
          Subgroup.normalizer
            (S : Set (A ⧸ T.normalSubgroup))
      rw [ha]
      exact y.property⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact ha

omit [Fact p.Prime] in
/-- The kernel of the projection from the full preimage is the canonical
copy of `N`. -/
@[simp]
theorem quotientSylowNormalizerHom_ker
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    (quotientSylowNormalizerHom T S).ker =
      (quotientSylowNormalizerRestrictionTriple
        T S).normalSubgroup := by
  ext x
  rw [MonoidHom.mem_ker, Subtype.ext_iff]
  change
    QuotientGroup.mk' T.normalSubgroup (x : A) = 1 ↔
      (x : A) ∈ T.normalSubgroup
  exact QuotientGroup.eq_one_iff (x : A)

/-- The canonical quotient identification

`B / N ≃* N_{A/N}(S)`.
-/
def quotientSylowNormalizerEquiv
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    (quotientSylowNormalizerPreimage T S ⧸
        (quotientSylowNormalizerRestrictionTriple
          T S).normalSubgroup) ≃*
      Subgroup.normalizer
        (S : Set (A ⧸ T.normalSubgroup)) :=
  QuotientGroup.liftEquiv
    (quotientSylowNormalizerRestrictionTriple
      T S).normalSubgroup
    (quotientSylowNormalizerHom_surjective T S)
    (quotientSylowNormalizerHom_ker T S).symm

omit [Fact p.Prime] in
@[simp]
theorem quotientSylowNormalizerEquiv_mk
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (x : quotientSylowNormalizerPreimage T S) :
    quotientSylowNormalizerEquiv T S
        (QuotientGroup.mk x) =
      quotientSylowNormalizerHom T S x :=
  QuotientGroup.liftEquiv_mk
    (quotientSylowNormalizerRestrictionTriple
      T S).normalSubgroup
    (quotientSylowNormalizerHom_surjective T S)
    (quotientSylowNormalizerHom_ker T S).symm x

omit [Module.Finite ℂ V] [Nontrivial V] [Fact p.Prime] in
/-- The restricted and original normal subgroups have equal cardinality, so
the fixed finite coefficient exponent remains valid after restriction. -/
theorem associatedFactorExponent_restriction_eq
    (T : CharacterTriple A)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    associatedFactorExponent
        (quotientSylowNormalizerRestrictionTriple T S) V =
      associatedFactorExponent T V := by
  unfold associatedFactorExponent
  congr 1
  exact
    Nat.card_congr
      (T.normalSubgroupInEquiv
        (quotientSylowNormalizerPreimage T S)
        (normalSubgroup_le_quotientSylowNormalizerPreimage
          T S)).toEquiv

/-- The fixed finite quotient factor set, pulled back through
`B / N ≃* N_{A/N}(S)`.  This avoids making a second set of determinant
normalization choices after restriction. -/
def normalizerRestrictionFiniteQuotientFactorSet
    (R : AssociatedProjectiveRepresentation T V P)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    FactorSet
      (quotientSylowNormalizerPreimage T S ⧸
        (quotientSylowNormalizerRestrictionTriple
          T S).normalSubgroup)
      (rootsOfUnity (associatedFactorExponent T V) ℂ) :=
  FactorSet.CentralExtensionGroup.sylowNormalizerFactorSet
    R.associatedFiniteQuotientFactorSet S
    (quotientSylowNormalizerEquiv T S)

omit [Fact p.Prime] in
/-- The pulled-back finite quotient factor set is normalized. -/
theorem normalizerRestrictionFiniteQuotientFactorSet_isNormalized
    (R : AssociatedProjectiveRepresentation T V P)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    (R.normalizerRestrictionFiniteQuotientFactorSet S
      ).IsNormalized :=
  FactorSet.CentralExtensionGroup.sylowNormalizerFactorSet_isNormalized
      R.associatedFiniteQuotientFactorSet
      R.associatedFiniteQuotientFactorSet_isNormalized
      S (quotientSylowNormalizerEquiv T S)

omit [Fact p.Prime] in
/-- On quotient classes represented by elements of `B`, the restricted
finite factor is literally the original finite factor. -/
@[simp]
theorem normalizerRestrictionFiniteQuotientFactorSet_mk
    (R : AssociatedProjectiveRepresentation T V P)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (x y : quotientSylowNormalizerPreimage T S) :
    R.normalizerRestrictionFiniteQuotientFactorSet S
        (QuotientGroup.mk x)
        (QuotientGroup.mk y) =
      R.associatedFiniteFactorSet (x : A) (y : A) := by
  change
    R.associatedFiniteQuotientFactorSet
        (((quotientSylowNormalizerEquiv T S
          (QuotientGroup.mk x) :
            Subgroup.normalizer
              (S : Set (A ⧸ T.normalSubgroup))) :
          A ⧸ T.normalSubgroup))
        (((quotientSylowNormalizerEquiv T S
          (QuotientGroup.mk y) :
            Subgroup.normalizer
              (S : Set (A ⧸ T.normalSubgroup))) :
          A ⧸ T.normalSubgroup)) =
      R.associatedFiniteFactorSet (x : A) (y : A)
  rw [quotientSylowNormalizerEquiv_mk,
    quotientSylowNormalizerEquiv_mk]
  exact
    R.associatedFiniteQuotientFactorSet_mk
      (x : A) (y : A)

omit [Fact p.Prime] in
/-- Forgetting the finite coefficient group recovers the exact factor of the
literally restricted normalized projective representation. -/
@[simp]
theorem normalizerRestrictionFiniteQuotientFactorSet_mk_coe
    (R : AssociatedProjectiveRepresentation T V P)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (x y : quotientSylowNormalizerPreimage T S) :
    ((R.normalizerRestrictionFiniteQuotientFactorSet S
          (QuotientGroup.mk x)
          (QuotientGroup.mk y) :
        rootsOfUnity
          (associatedFactorExponent T V) ℂ) : ℂˣ) =
      (R.associatedFiniteFactorProjective.comap
        (quotientSylowNormalizerPreimage T S).subtype
        ).factor x y := by
  rw [R.normalizerRestrictionFiniteQuotientFactorSet_mk S]
  exact
    R.associatedFiniteFactorSet_coe
      (x : A) (y : A)

/-- The concrete finite factor extension attached to the restricted fixed
normalization. -/
abbrev AssociatedFiniteFactorNormalizerRestrictionGroup
    (R : AssociatedProjectiveRepresentation T V P)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :=
  FactorSet.CentralExtensionGroup
    (R.normalizerRestrictionFiniteQuotientFactorSet S)
    (R.normalizerRestrictionFiniteQuotientFactorSet_isNormalized S)

/-- The normalizer of the Sylow lift in the original concrete finite factor
extension is canonically isomorphic to the concrete finite factor extension
of the restricted fixed normalization. -/
def associatedFiniteFactorSylowLiftNormalizerEquiv
    (R : AssociatedProjectiveRepresentation T V P)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    Subgroup.normalizer
        ((R.associatedFiniteFactorCentralExtension).sylowLift S :
          Set R.AssociatedFiniteFactorCentralExtensionGroup) ≃*
      R.AssociatedFiniteFactorNormalizerRestrictionGroup S :=
  FactorSet.CentralExtensionGroup.sylowLiftNormalizerEquivComap
      R.associatedFiniteQuotientFactorSet
      R.associatedFiniteQuotientFactorSet_isNormalized
      S (quotientSylowNormalizerEquiv T S)

/-- Compatibility of the normalizer equivalence with the original restricted
projection and the canonical quotient identification `B/N ≃ N_{A/N}(S)`. -/
@[simp]
theorem associatedFiniteFactorSylowLiftNormalizerEquiv_projection
    (R : AssociatedProjectiveRepresentation T V P)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (x :
      Subgroup.normalizer
        ((R.associatedFiniteFactorCentralExtension).sylowLift S :
          Set R.AssociatedFiniteFactorCentralExtensionGroup)) :
    quotientSylowNormalizerEquiv T S
        (FactorSet.CentralExtensionGroup.projection
          (R.normalizerRestrictionFiniteQuotientFactorSet S)
          (R.normalizerRestrictionFiniteQuotientFactorSet_isNormalized S)
          (R.associatedFiniteFactorSylowLiftNormalizerEquiv S x)) =
      GroupTheory.CentralExtension.sylowNormalizerProjection
        R.associatedFiniteFactorCentralExtension S x :=
  FactorSet.CentralExtensionGroup.sylowLiftNormalizerEquivComap_projection
      R.associatedFiniteQuotientFactorSet
      R.associatedFiniteQuotientFactorSet_isNormalized
      S (quotientSylowNormalizerEquiv T S) x

/-- The normalizer equivalence preserves the finite coefficient coordinate. -/
@[simp]
theorem associatedFiniteFactorSylowLiftNormalizerEquiv_coefficient
    (R : AssociatedProjectiveRepresentation T V P)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (x :
      Subgroup.normalizer
        ((R.associatedFiniteFactorCentralExtension).sylowLift S :
          Set R.AssociatedFiniteFactorCentralExtensionGroup)) :
    FactorSet.CentralExtensionGroup.coefficient
        (R.normalizerRestrictionFiniteQuotientFactorSet S)
        (R.normalizerRestrictionFiniteQuotientFactorSet_isNormalized S)
        (R.associatedFiniteFactorSylowLiftNormalizerEquiv S x) =
      FactorSet.CentralExtensionGroup.coefficient
        R.associatedFiniteQuotientFactorSet
        R.associatedFiniteQuotientFactorSet_isNormalized
        (x : R.AssociatedFiniteFactorCentralExtensionGroup) :=
  FactorSet.CentralExtensionGroup.sylowLiftNormalizerEquivComap_coefficient
      R.associatedFiniteQuotientFactorSet
      R.associatedFiniteQuotientFactorSet_isNormalized
      S (quotientSylowNormalizerEquiv T S) x

/-- The original coefficient embedding, regarded in the Sylow-lift
normalizer. -/
abbrev associatedFiniteFactorCoefficientEmbeddingToSylowLiftNormalizer
    (R : AssociatedProjectiveRepresentation T V P)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :=
  FactorSet.CentralExtensionGroup.coefficientEmbeddingToSylowLiftNormalizer
      R.associatedFiniteQuotientFactorSet
      R.associatedFiniteQuotientFactorSet_isNormalized S

/-- The normalizer equivalence preserves the canonical coefficient
embedding. -/
@[simp]
theorem associatedFiniteFactorSylowLiftNormalizerEquiv_coefficientEmbedding
    (R : AssociatedProjectiveRepresentation T V P)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (c :
      rootsOfUnity (associatedFactorExponent T V) ℂ) :
    R.associatedFiniteFactorSylowLiftNormalizerEquiv S
        (R.associatedFiniteFactorCoefficientEmbeddingToSylowLiftNormalizer
          S c) =
      FactorSet.CentralExtensionGroup.coefficientEmbedding
        (R.normalizerRestrictionFiniteQuotientFactorSet S)
        (R.normalizerRestrictionFiniteQuotientFactorSet_isNormalized S)
        c :=
  FactorSet.CentralExtensionGroup.sylowLiftNormalizerEquivComap_coefficientEmbedding
      R.associatedFiniteQuotientFactorSet
      R.associatedFiniteQuotientFactorSet_isNormalized
      S (quotientSylowNormalizerEquiv T S) c

/-! ## A bridge for an arbitrary fixed finite-normalization package

The preceding API specializes the canonical normalization produced from `R`.
The following namespace works with any fixed
`AssociatedFiniteFactorNormalization R`.  In particular, no equality with a
new normalization chosen after restriction is required.
-/

namespace AssociatedFiniteFactorNormalization

variable (R : AssociatedProjectiveRepresentation T V P)

/-- Quotient compatibility of the finite factor set stored in an arbitrary
fixed normalization package. -/
theorem factorSet_isQuotientCompatible
    (F : AssociatedFiniteFactorNormalization R) :
    F.factorSet.IsQuotientCompatible T.normalSubgroup where
  factor_normal_left x a := by
    apply Subtype.ext
    change
      ((F.factorSet (x : A) a :
          rootsOfUnity
            (associatedFactorExponent T V) ℂ) : ℂˣ) =
        1
    rw [F.factorSet_coe]
    exact F.associated.factor_normal_left x a
  factor_normal_right a x := by
    apply Subtype.ext
    change
      ((F.factorSet a (x : A) :
          rootsOfUnity
            (associatedFactorExponent T V) ℂ) : ℂˣ) =
        1
    rw [F.factorSet_coe]
    exact F.associated.factor_normal_right a x

/-- The finite factor set stored in a fixed normalization package is
normalized. -/
theorem factorSet_isNormalized
    (F : AssociatedFiniteFactorNormalization R) :
    F.factorSet.IsNormalized := by
  have hprojective :
      F.projective.factorSet.IsNormalized :=
    F.projective.factorSet_isNormalized F.isNormalized
  constructor
  · intro a
    apply Subtype.ext
    change
      ((F.factorSet 1 a :
          rootsOfUnity
            (associatedFactorExponent T V) ℂ) : ℂˣ) =
        1
    rw [F.factorSet_coe]
    exact hprojective.1 a
  · intro a
    apply Subtype.ext
    change
      ((F.factorSet a 1 :
          rootsOfUnity
            (associatedFactorExponent T V) ℂ) : ℂˣ) =
        1
    rw [F.factorSet_coe]
    exact hprojective.2 a

/-- The fixed finite factor set descended to `A / N`. -/
def finiteQuotientFactorSet
    (F : AssociatedFiniteFactorNormalization R) :
    FactorSet (A ⧸ T.normalSubgroup)
      (rootsOfUnity (associatedFactorExponent T V) ℂ) :=
  F.factorSet.quotient
    (F.factorSet_isQuotientCompatible R)

@[simp]
theorem finiteQuotientFactorSet_mk
    (F : AssociatedFiniteFactorNormalization R)
    (a b : A) :
    F.finiteQuotientFactorSet R
        (QuotientGroup.mk' T.normalSubgroup a)
        (QuotientGroup.mk' T.normalSubgroup b) =
      F.factorSet a b :=
  FactorSet.quotient_mk
    (F.factorSet_isQuotientCompatible R) a b

/-- The quotient factor of the fixed package is normalized. -/
theorem finiteQuotientFactorSet_isNormalized
    (F : AssociatedFiniteFactorNormalization R) :
    (F.finiteQuotientFactorSet R).IsNormalized :=
  FactorSet.quotient_isNormalized
    (F.factorSet_isQuotientCompatible R)
    (F.factorSet_isNormalized R)

/-- The concrete finite factor extension attached to an arbitrary fixed
normalization package. -/
abbrev FiniteFactorCentralExtensionGroup
    (F : AssociatedFiniteFactorNormalization R) :=
  FactorSet.CentralExtensionGroup
    (F.finiteQuotientFactorSet R)
    (F.finiteQuotientFactorSet_isNormalized R)

/-- The central extension structure on the concrete extension attached to a
fixed normalization package. -/
def finiteFactorCentralExtension
    (F : AssociatedFiniteFactorNormalization R) :
    GroupTheory.CentralExtension
      (F.FiniteFactorCentralExtensionGroup R)
      (A ⧸ T.normalSubgroup) :=
  FactorSet.CentralExtensionGroup.centralExtension
    (F.finiteQuotientFactorSet R)
    (F.finiteQuotientFactorSet_isNormalized R)

/-- The literal restriction of the projective representation stored in a
fixed finite-normalization package remains associated with the canonical
restricted triple. -/
def normalizerRestrictionAssociated
    (F : AssociatedFiniteFactorNormalization R)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    AssociatedProjectiveRepresentation
      (quotientSylowNormalizerRestrictionTriple T S) V
      (F.projective.comap
        (quotientSylowNormalizerPreimage T S).subtype) :=
  F.associated.restrictTo
    (quotientSylowNormalizerPreimage T S)
    (normalSubgroup_le_quotientSylowNormalizerPreimage
      T S)

/-- Pull the quotient factor set of a fixed normalization package back
through `B/N ≃* N_{A/N}(S)`. -/
def normalizerRestrictionFiniteQuotientFactorSet
    (F : AssociatedFiniteFactorNormalization R)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    FactorSet
      (quotientSylowNormalizerPreimage T S ⧸
        (quotientSylowNormalizerRestrictionTriple
          T S).normalSubgroup)
      (rootsOfUnity (associatedFactorExponent T V) ℂ) :=
  FactorSet.CentralExtensionGroup.sylowNormalizerFactorSet
    (F.finiteQuotientFactorSet R) S
    (quotientSylowNormalizerEquiv T S)

omit [Fact p.Prime] in
/-- The restricted factor set of a fixed normalization package is
normalized. -/
theorem normalizerRestrictionFiniteQuotientFactorSet_isNormalized
    (F : AssociatedFiniteFactorNormalization R)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    (F.normalizerRestrictionFiniteQuotientFactorSet R S
      ).IsNormalized :=
  FactorSet.CentralExtensionGroup.sylowNormalizerFactorSet_isNormalized
    (F.finiteQuotientFactorSet R)
    (F.finiteQuotientFactorSet_isNormalized R)
    S (quotientSylowNormalizerEquiv T S)

omit [Fact p.Prime] in
/-- The pulled-back factor of the fixed package agrees literally with its
ambient finite factor on representatives from `B`. -/
@[simp]
theorem normalizerRestrictionFiniteQuotientFactorSet_mk
    (F : AssociatedFiniteFactorNormalization R)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (x y : quotientSylowNormalizerPreimage T S) :
    F.normalizerRestrictionFiniteQuotientFactorSet R S
        (QuotientGroup.mk x)
        (QuotientGroup.mk y) =
      F.factorSet (x : A) (y : A) := by
  change
    F.finiteQuotientFactorSet R
        (((quotientSylowNormalizerEquiv T S
          (QuotientGroup.mk x) :
            Subgroup.normalizer
              (S : Set (A ⧸ T.normalSubgroup))) :
          A ⧸ T.normalSubgroup))
        (((quotientSylowNormalizerEquiv T S
          (QuotientGroup.mk y) :
            Subgroup.normalizer
              (S : Set (A ⧸ T.normalSubgroup))) :
          A ⧸ T.normalSubgroup)) =
      F.factorSet (x : A) (y : A)
  rw [quotientSylowNormalizerEquiv_mk,
    quotientSylowNormalizerEquiv_mk]
  exact F.finiteQuotientFactorSet_mk R (x : A) (y : A)

omit [Fact p.Prime] in
/-- After forgetting the finite coefficient group, the pulled-back factor is
the exact factor of `F.projective.comap B.subtype`. -/
@[simp]
theorem normalizerRestrictionFiniteQuotientFactorSet_mk_coe
    (F : AssociatedFiniteFactorNormalization R)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (x y : quotientSylowNormalizerPreimage T S) :
    ((F.normalizerRestrictionFiniteQuotientFactorSet R S
          (QuotientGroup.mk x)
          (QuotientGroup.mk y) :
        rootsOfUnity
          (associatedFactorExponent T V) ℂ) : ℂˣ) =
      (F.projective.comap
        (quotientSylowNormalizerPreimage T S).subtype
        ).factor x y := by
  rw [F.normalizerRestrictionFiniteQuotientFactorSet_mk
    R S]
  exact F.factorSet_coe (x : A) (y : A)

/-- The concrete finite factor extension attached to the literal restriction
of a fixed normalization package. -/
abbrev NormalizerRestrictionGroup
    (F : AssociatedFiniteFactorNormalization R)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :=
  FactorSet.CentralExtensionGroup
    (F.normalizerRestrictionFiniteQuotientFactorSet R S)
    (F.normalizerRestrictionFiniteQuotientFactorSet_isNormalized
      R S)

/-- The normalizer of the Sylow lift in the concrete extension of a fixed
normalization package is canonically the concrete extension of its literal
restriction. -/
def sylowLiftNormalizerEquiv
    (F : AssociatedFiniteFactorNormalization R)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :
    Subgroup.normalizer
        ((F.finiteFactorCentralExtension R).sylowLift S :
          Set (F.FiniteFactorCentralExtensionGroup R)) ≃*
      F.NormalizerRestrictionGroup R S :=
  FactorSet.CentralExtensionGroup.sylowLiftNormalizerEquivComap
    (F.finiteQuotientFactorSet R)
    (F.finiteQuotientFactorSet_isNormalized R)
    S (quotientSylowNormalizerEquiv T S)

/-- The package-level normalizer equivalence preserves base projection. -/
@[simp]
theorem sylowLiftNormalizerEquiv_projection
    (F : AssociatedFiniteFactorNormalization R)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (x :
      Subgroup.normalizer
        ((F.finiteFactorCentralExtension R).sylowLift S :
          Set (F.FiniteFactorCentralExtensionGroup R))) :
    quotientSylowNormalizerEquiv T S
        (FactorSet.CentralExtensionGroup.projection
          (F.normalizerRestrictionFiniteQuotientFactorSet R S)
          (F.normalizerRestrictionFiniteQuotientFactorSet_isNormalized
            R S)
          (F.sylowLiftNormalizerEquiv R S x)) =
      GroupTheory.CentralExtension.sylowNormalizerProjection
        (F.finiteFactorCentralExtension R) S x :=
  FactorSet.CentralExtensionGroup.sylowLiftNormalizerEquivComap_projection
      (F.finiteQuotientFactorSet R)
      (F.finiteQuotientFactorSet_isNormalized R)
      S (quotientSylowNormalizerEquiv T S) x

/-- The package-level normalizer equivalence preserves the coefficient
coordinate. -/
@[simp]
theorem sylowLiftNormalizerEquiv_coefficient
    (F : AssociatedFiniteFactorNormalization R)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (x :
      Subgroup.normalizer
        ((F.finiteFactorCentralExtension R).sylowLift S :
          Set (F.FiniteFactorCentralExtensionGroup R))) :
    FactorSet.CentralExtensionGroup.coefficient
        (F.normalizerRestrictionFiniteQuotientFactorSet R S)
        (F.normalizerRestrictionFiniteQuotientFactorSet_isNormalized
          R S)
        (F.sylowLiftNormalizerEquiv R S x) =
      FactorSet.CentralExtensionGroup.coefficient
        (F.finiteQuotientFactorSet R)
        (F.finiteQuotientFactorSet_isNormalized R)
        (x : F.FiniteFactorCentralExtensionGroup R) :=
  FactorSet.CentralExtensionGroup.sylowLiftNormalizerEquivComap_coefficient
      (F.finiteQuotientFactorSet R)
      (F.finiteQuotientFactorSet_isNormalized R)
      S (quotientSylowNormalizerEquiv T S) x

/-- The coefficient embedding of a fixed package, regarded inside the
normalizer of its Sylow lift. -/
abbrev coefficientEmbeddingToSylowLiftNormalizer
    (F : AssociatedFiniteFactorNormalization R)
    (S : Sylow p (A ⧸ T.normalSubgroup)) :=
  FactorSet.CentralExtensionGroup.coefficientEmbeddingToSylowLiftNormalizer
      (F.finiteQuotientFactorSet R)
      (F.finiteQuotientFactorSet_isNormalized R) S

/-- The package-level normalizer equivalence preserves the canonical
coefficient embedding. -/
@[simp]
theorem sylowLiftNormalizerEquiv_coefficientEmbedding
    (F : AssociatedFiniteFactorNormalization R)
    (S : Sylow p (A ⧸ T.normalSubgroup))
    (c :
      rootsOfUnity (associatedFactorExponent T V) ℂ) :
    F.sylowLiftNormalizerEquiv R S
        (F.coefficientEmbeddingToSylowLiftNormalizer R S c) =
      FactorSet.CentralExtensionGroup.coefficientEmbedding
        (F.normalizerRestrictionFiniteQuotientFactorSet R S)
        (F.normalizerRestrictionFiniteQuotientFactorSet_isNormalized
          R S) c :=
  FactorSet.CentralExtensionGroup.sylowLiftNormalizerEquivComap_coefficientEmbedding
      (F.finiteQuotientFactorSet R)
      (F.finiteQuotientFactorSet_isNormalized R)
      S (quotientSylowNormalizerEquiv T S) c

end AssociatedFiniteFactorNormalization

end AssociatedProjectiveRepresentation
end CharacterTriple
end McKayConjecture
