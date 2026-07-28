/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.Construction
import McKayConjecture.Character.CyclicExtensionIntertwiner
import McKayConjecture.Character.GallagherCorrespondence
import McKayConjecture.CharacterTriple.AssociatedFiniteFactorQuotient
import McKayConjecture.CharacterTriple.FactorSetCoprimeSplitting
import McKayConjecture.GroupTheory.PPrimeCore
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Coprime linearization of associated projective representations

For a character triple whose normal subgroup has prime-to-`p` order and
whose quotient is a `p`-group, the association-preserving finite factor set
has coefficient order coprime to its base order. Schur--Zassenhaus therefore
trivializes that factor set. This file rescales the associated projective
representation to an honest irreducible representation without changing its
normal-subgroup restriction.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace CharacterTriple

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

namespace AssociatedProjectiveRepresentation

variable {T : CharacterTriple G}
variable {V : Type}
variable [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [Nontrivial V]
variable {P : ProjectiveRepresentation ℂ G V}

theorem associatedFactorExponent_not_dvd
    (_R : AssociatedProjectiveRepresentation T V P)
    (hN : GroupTheory.IsPPrimeGroup p T.normalSubgroup)
    (hdegree :
      ¬p ∣ Module.finrank ℂ V) :
    ¬p ∣ associatedFactorExponent T V := by
  rw [associatedFactorExponent]
  intro hdivides
  rcases (Fact.out : p.Prime).dvd_mul.mp hdivides with
    hleft | hright
  · exact hdegree hleft
  · exact
      ((GroupTheory.isPPrimeGroup_iff_not_dvd
        (G := T.normalSubgroup) Fact.out).mp hN) hright

theorem associatedFactorOrders_coprime
    (R : AssociatedProjectiveRepresentation T V P)
    (hN : GroupTheory.IsPPrimeGroup p T.normalSubgroup)
    (hquotient : IsPGroup p (G ⧸ T.normalSubgroup))
    (hdegree :
      ¬p ∣ Module.finrank ℂ V) :
    Nat.Coprime
      (Nat.card
        (rootsOfUnity (associatedFactorExponent T V) ℂ))
      (Nat.card (G ⧸ T.normalSubgroup)) := by
  rw [Complex.card_rootsOfUnity]
  obtain ⟨n, hn⟩ :=
    IsPGroup.iff_card.mp hquotient
  rw [hn]
  exact
    (Fact.out : p.Prime).coprime_pow_of_not_dvd
      (R.associatedFactorExponent_not_dvd hN hdegree)

/-- A projective lift associated with a prime-to-`p` character of a normal
Hall `p'`-subgroup can be rescaled, without changing its restriction, to
have factor identically one. -/
theorem exists_factorOne_associated_of_coprime
    (R : AssociatedProjectiveRepresentation T V P)
    (hN : GroupTheory.IsPPrimeGroup p T.normalSubgroup)
    (hquotient : IsPGroup p (G ⧸ T.normalSubgroup))
    (hdegree :
      ¬p ∣ Module.finrank ℂ V) :
    ∃ Q : ProjectiveRepresentation ℂ G V,
      Nonempty (AssociatedProjectiveRepresentation T V Q) ∧
        ∀ g h : G, Q.factor g h = 1 := by
  let alpha := R.associatedFiniteQuotientFactorSet
  obtain ⟨c, hc_one, hc_gauge⟩ :=
    FactorSet.exists_normalized_gauge_eq_one_of_coprime
      alpha
      R.associatedFiniteQuotientFactorSet_isNormalized
      (R.associatedFactorOrders_coprime
        hN hquotient hdegree)
  let cComplex : G ⧸ T.normalSubgroup → ℂˣ :=
    fun q ↦
      ((c q :
        rootsOfUnity (associatedFactorExponent T V) ℂ) : ℂˣ)
  let Q : ProjectiveRepresentation ℂ G V :=
    R.associatedFiniteFactorProjective.rescale
      (quotientScalar cComplex)
  have hcComplex_one : cComplex 1 = 1 := by
    change
      ((c 1 :
        rootsOfUnity (associatedFactorExponent T V) ℂ) : ℂˣ) = 1
    rw [hc_one]
    rfl
  refine
    ⟨Q,
      ⟨R.associatedFiniteFactorAssociated.rescaleByQuotientScalar
        cComplex hcComplex_one⟩,
      ?_⟩
  intro g h
  let q := QuotientGroup.mk' T.normalSubgroup g
  let r := QuotientGroup.mk' T.normalSubgroup h
  have hroot :=
    congrArg
      (fun beta :
        FactorSet (G ⧸ T.normalSubgroup)
          (rootsOfUnity (associatedFactorExponent T V) ℂ) ↦
        beta q r)
      hc_gauge
  simp only [FactorSet.gauge_apply, FactorSet.one_apply] at hroot
  have hcomplex :=
    congrArg
      (fun z :
        rootsOfUnity (associatedFactorExponent T V) ℂ ↦
        (z : ℂˣ))
      hroot
  change
    cComplex q * cComplex r / cComplex (q * r) *
        ((alpha q r :
          rootsOfUnity (associatedFactorExponent T V) ℂ) : ℂˣ) =
      1 at hcomplex
  change
    quotientScalar cComplex g *
          quotientScalar cComplex h /
          quotientScalar cComplex (g * h) *
          R.associatedFiniteFactorProjective.factor g h =
        1
  rw [quotientScalar_apply, quotientScalar_apply,
    quotientScalar_apply, map_mul]
  rw [← R.associatedFiniteQuotientFactorSet_mk_coe g h]
  exact hcomplex

/-- The ordinary representation obtained when an associated projective
representation has trivial factor. -/
def factorOneFDRep
    (_R : AssociatedProjectiveRepresentation T V P)
    (hfactor : ∀ g h : G, P.factor g h = 1) :
    FDRep ℂ G :=
  FDRep.of
    (linearRepresentationOfAction
      (P.linearActionOfFactorOne hfactor))

/-- The restriction of the factor-one representation is the associated
normal-subgroup representation. -/
theorem factorOneFDRep_restriction
    (R : AssociatedProjectiveRepresentation T V P)
    (hfactor : ∀ g h : G, P.factor g h = 1) :
    (factorOneFDRep R hfactor).ρ.comp T.normalSubgroup.subtype =
      linearRepresentationOfAction R.restriction := by
  ext x v
  change P.operator (x : G) v = R.restriction x v
  rw [R.restriction_apply]

/-- A factor-one associated representation is irreducible, because its
restriction to the normal subgroup is already irreducible. -/
theorem factorOneFDRep_simple
    (R : AssociatedProjectiveRepresentation T V P)
    (hfactor : ∀ g h : G, P.factor g h = 1) :
    Simple (factorOneFDRep R hfactor) := by
  letI : Simple R.fdRestriction :=
    R.restriction_simple
  have hrestriction :
      Representation.IsIrreducible
        (linearRepresentationOfAction R.restriction) :=
    CliffordRestriction.isIrreducible_of_simple R.fdRestriction
  have hcomp :
      Representation.IsIrreducible
        ((factorOneFDRep R hfactor).ρ.comp
          T.normalSubgroup.subtype) := by
    rw [R.factorOneFDRep_restriction hfactor]
    exact hrestriction
  have hambient :
      Representation.IsIrreducible
        (factorOneFDRep R hfactor).ρ :=
    RepresentationTheory.Representation.isIrreducible_of_isIrreducible_comp
      (factorOneFDRep R hfactor).ρ hcomp
  letI :
      Representation.IsIrreducible
        (factorOneFDRep R hfactor).ρ :=
    hambient
  exact
    RepresentationTheory.simple_fdRep_of_isIrreducible
      (factorOneFDRep R hfactor).ρ

/-- The irreducible character afforded by a factor-one associated
representation. -/
def extensionCharacterOfFactorOne
    (R : AssociatedProjectiveRepresentation T V P)
    (hfactor : ∀ g h : G, P.factor g h = 1) :
    IrreducibleCharacter G := by
  letI : Simple (factorOneFDRep R hfactor) :=
    R.factorOneFDRep_simple hfactor
  exact IrreducibleCharacter.ofSimple
    (factorOneFDRep R hfactor)

@[simp]
theorem extensionCharacterOfFactorOne_degree
    (R : AssociatedProjectiveRepresentation T V P)
    (hfactor : ∀ g h : G, P.factor g h = 1) :
    (R.extensionCharacterOfFactorOne hfactor).degree =
      Module.finrank ℂ V := by
  letI : Simple (factorOneFDRep R hfactor) :=
    R.factorOneFDRep_simple hfactor
  rfl

theorem extensionCharacterOfFactorOne_isExtension
    (R : AssociatedProjectiveRepresentation T V P)
    (hfactor : ∀ g h : G, P.factor g h = 1) :
    IrreducibleCharacter.IsExtensionAlong
      T.normalSubgroup.subtype T.character
      (R.extensionCharacterOfFactorOne hfactor) := by
  intro x
  letI : Simple (factorOneFDRep R hfactor) :=
    R.factorOneFDRep_simple hfactor
  change
    (factorOneFDRep R hfactor).character (x : G) =
      T.character.values x
  rw [← congrFun R.fdRestriction_character x]
  change
    LinearMap.trace ℂ V
        (P.operator (x : G)).toLinearMap =
      LinearMap.trace ℂ V
        (R.restriction x).toLinearMap
  rw [R.restriction_apply]

end AssociatedProjectiveRepresentation
end CharacterTriple
end McKayConjecture
