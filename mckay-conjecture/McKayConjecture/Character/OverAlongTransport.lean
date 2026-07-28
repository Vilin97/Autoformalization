/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordEquivalence
import McKayConjecture.Character.Transport

/-!
# Transporting character fibres along commuting group equivalences

This file proves that the predicate of lying over a character is invariant
under simultaneous relabelling of the ambient and source groups.  The proof
works at the level of intertwining spaces, so it applies to arbitrary
homomorphisms in a commuting square.
-/

noncomputable section

open CategoryTheory

universe u₁ u₂ u₃ u₄ v₁ v₂

namespace McKayConjecture

namespace IrreducibleCharacter

variable {G : Type u₁} {H : Type u₂} [Finite G] [Finite H]
variable [Group G] [Group H]

/-- The chosen realization of a pulled-back irreducible character is
isomorphic to the literal restriction of the original chosen realization. -/
def comapRealizationIso
    (e : H ≃* G) (χ : IrreducibleCharacter G) :
    (χ.comap e).realization ≅
      FDRep.res e.toMonoidHom χ.realization := by
  letI : Simple (FDRep.res e.toMonoidHom χ.realization) :=
    FDRep.simple_res_mulEquiv e χ.realization
  apply Classical.choice
  apply FDRep.nonempty_iso_of_character_eq
  funext h
  rw [(χ.comap e).realization_character]
  change χ.values (e h) = χ.realization.character (e h)
  exact (congrFun χ.realization_character (e h)).symm

end IrreducibleCharacter

namespace FDRep

variable {K : Type v₁} [Field K]
variable {G : Type u₁} [Group G]
variable {V : Type v₂} {W : Type u₂}
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

/-- An isomorphism of finite-dimensional representations, viewed as an
equivalence of the underlying unbundled representations. -/
def representationEquivOfIso
    {X Y : FDRep K G} (i : X ≅ Y) :
    Representation.Equiv X.ρ Y.ρ := by
  let e := FDRep.isoToLinearEquiv i
  apply Representation.Equiv.mk e
  intro g
  have hconj := FDRep.Iso.conj_ρ i g
  apply LinearMap.ext
  intro v
  have hv := LinearMap.congr_fun hconj (e v)
  simpa [e, LinearEquiv.conj_apply] using hv.symm

/-- The standard equivalence between categorical morphisms of `FDRep` and
unbundled intertwining maps. -/
def homIntertwiningEquiv
    (X Y : FDRep K G) :
    (X ⟶ Y) ≃ₗ[K]
      Representation.IntertwiningMap X.ρ Y.ρ :=
  (FDRep.forget₂HomLinearEquiv X Y).symm |>.trans
    (Rep.homLinearEquiv _ _)

end FDRep

namespace Representation

variable {K : Type v₁} [Field K]
variable {G : Type u₁} {H : Type u₂} [Group G] [Group H]
variable {V : Type v₂} {W : Type u₃}
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

/-- Pulling both actions back along a group isomorphism leaves the underlying
intertwining map unchanged and gives a linear equivalence of intertwining
spaces. -/
def intertwiningMapComapEquiv
    (e : H ≃* G)
    (ρ : Representation K G V)
    (σ : Representation K G W) :
    Representation.IntertwiningMap ρ σ ≃ₗ[K]
      Representation.IntertwiningMap
        (ρ.comp e.toMonoidHom)
        (σ.comp e.toMonoidHom) where
  toFun f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' h := f.isIntertwining' (e h) }
  invFun f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' g := by
        simpa using f.isIntertwining' (e.symm g) }
  left_inv f := by
    apply Representation.IntertwiningMap.ext
    rfl
  right_inv f := by
    apply Representation.IntertwiningMap.ext
    rfl
  map_add' f g := by
    apply Representation.IntertwiningMap.ext
    rfl
  map_smul' c f := by
    apply Representation.IntertwiningMap.ext
    rfl

variable {X : Type u₄}
variable [AddCommGroup X] [Module K X]
variable {ρ : Representation K G V}
variable {σ : Representation K G W}
variable {ρ' : Representation K G X}

/-- Simultaneous equivalence of the source and target actions identifies
their intertwining spaces. -/
def intertwiningMapCongr
    (eV : Representation.Equiv ρ' ρ)
    {W' : Type u₂} [AddCommGroup W'] [Module K W']
    {σ' : Representation K G W'}
    (eW : Representation.Equiv σ' σ) :
    Representation.IntertwiningMap ρ σ ≃ₗ[K]
      Representation.IntertwiningMap ρ' σ' where
  toFun f :=
    eW.symm.toIntertwiningMap.comp
      (f.comp eV.toIntertwiningMap)
  invFun f :=
    eW.toIntertwiningMap.comp
      (f.comp eV.symm.toIntertwiningMap)
  left_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    simp
  right_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    simp
  map_add' f g := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact eW.symm.map_add (f (eV x)) (g (eV x))
  map_smul' c f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact eW.symm.map_smul c (f (eV x))

end Representation

namespace CliffordCorrespondence

variable {G G' H H' : Type}
variable [Finite G] [Finite G'] [Finite H] [Finite H']
variable [Group G] [Group G'] [Group H] [Group H']

/-- A commuting square of group equivalences induces a linear equivalence
between the two restriction-intertwining spaces. -/
def restrictionHomEquiv
    (eG : G' ≃* G)
    (eH : H' ≃* H)
    (φ : H →* G)
    (φ' : H' →* G')
    (hcomm :
      eG.toMonoidHom.comp φ' =
        φ.comp eH.toMonoidHom)
    (η : IrreducibleCharacter H)
    (χ : IrreducibleCharacter G) :
    (η.realization ⟶
        FDRep.res φ χ.realization) ≃ₗ[ℂ]
      ((η.comap eH).realization ⟶
        FDRep.res φ' (χ.comap eG).realization) := by
  let oldHom :=
    FDRep.homIntertwiningEquiv
      η.realization (FDRep.res φ χ.realization)
  let oldRestriction :=
    CliffordEquivalence.restrictionAlongRepresentationEquiv
      φ χ.realization
  let exposeOldRestriction :=
    Representation.intertwiningMapCongr
      (Representation.Equiv.refl η.realization.ρ)
      oldRestriction.symm
  let relabel :=
    Representation.intertwiningMapComapEquiv
      eH η.realization.ρ
      (χ.realization.ρ.comp φ)
  have htarget :
      (χ.realization.ρ.comp φ).comp eH.toMonoidHom =
        (χ.realization.ρ.comp eG.toMonoidHom).comp φ' := by
    apply MonoidHom.ext
    intro h
    change
      χ.realization.ρ (φ (eH h)) =
        χ.realization.ρ (eG (φ' h))
    exact congrArg χ.realization.ρ
      (congrArg (fun f : H' →* G => f h) hcomm).symm
  let relabel' :
      Representation.IntertwiningMap
          η.realization.ρ
          (χ.realization.ρ.comp φ) ≃ₗ[ℂ]
        Representation.IntertwiningMap
          (η.realization.ρ.comp eH.toMonoidHom)
          ((χ.realization.ρ.comp eG.toMonoidHom).comp φ') := by
    rw [← htarget]
    exact relabel
  let iη :=
    IrreducibleCharacter.comapRealizationIso eH η
  let iχ :=
    IrreducibleCharacter.comapRealizationIso eG χ
  let eη :=
    FDRep.representationEquivOfIso iη
  let eχ :=
    FDRep.representationEquivOfIso iχ
  let eχRestricted :=
    Mackey.compEquiv φ' eχ
  let newRestriction :=
    CliffordEquivalence.restrictionAlongRepresentationEquiv
      φ' (χ.comap eG).realization
  let hideNewRealizations :=
    Representation.intertwiningMapCongr
      eη
      (newRestriction.trans eχRestricted)
  let newHom :=
    FDRep.homIntertwiningEquiv
      (η.comap eH).realization
      (FDRep.res φ' (χ.comap eG).realization)
  exact
    oldHom.trans
      (exposeOldRestriction.trans
        (relabel'.trans
          (hideNewRealizations.trans newHom.symm)))

/-- Restriction multiplicity is unchanged by simultaneous relabelling of
the ambient and source groups through a commuting square of equivalences. -/
theorem restrictionMultiplicity_comap_equiv
    (eG : G' ≃* G)
    (eH : H' ≃* H)
    (φ : H →* G)
    (φ' : H' →* G')
    (hcomm :
      eG.toMonoidHom.comp φ' =
        φ.comp eH.toMonoidHom)
    (η : IrreducibleCharacter H)
    (χ : IrreducibleCharacter G) :
    restrictionMultiplicity φ'
        (η.comap eH) (χ.comap eG) =
      restrictionMultiplicity φ η χ := by
  rw [restrictionMultiplicity, restrictionMultiplicity]
  exact
    (restrictionHomEquiv
      eG eH φ φ' hcomm η χ).finrank_eq.symm

/-- Lying over a normal character is invariant under a commuting square of
ambient and source group equivalences. -/
theorem liesOverAlong_comap_equiv_iff
    (eG : G' ≃* G)
    (eH : H' ≃* H)
    (φ : H →* G)
    (φ' : H' →* G')
    (hcomm :
      eG.toMonoidHom.comp φ' =
        φ.comp eH.toMonoidHom)
    (η : IrreducibleCharacter H)
    (χ : IrreducibleCharacter G) :
    LiesOverAlong φ'
        (η.comap eH) (χ.comap eG) ↔
      LiesOverAlong φ η χ := by
  rw [LiesOverAlong, LiesOverAlong,
    restrictionMultiplicity_comap_equiv
      eG eH φ φ' hcomm η χ]

/-- Simultaneous relabelling of a commuting square transports the entire
prime-to-`p` character fibre. -/
def pPrimeIrreducibleCharactersOverAlongComapEquiv
    (eG : G' ≃* G)
    (eH : H' ≃* H)
    (φ : H →* G)
    (φ' : H' →* G')
    (hcomm :
      eG.toMonoidHom.comp φ' =
        φ.comp eH.toMonoidHom)
    (η : IrreducibleCharacter H)
    (p : ℕ) :
    PPrimeIrreducibleCharactersOverAlong φ η p ≃
      PPrimeIrreducibleCharactersOverAlong
        φ' (η.comap eH) p where
  toFun χ :=
    ⟨⟨χ.1.1.comap eG,
        (liesOverAlong_comap_equiv_iff
          eG eH φ φ' hcomm η χ.1.1).2 χ.1.2⟩,
      χ.2⟩
  invFun χ :=
    ⟨⟨χ.1.1.comap eG.symm, by
        apply
          (liesOverAlong_comap_equiv_iff
            eG eH φ φ' hcomm η
              (χ.1.1.comap eG.symm)).1
        simpa using χ.1.2⟩,
      χ.2⟩
  left_inv χ := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  right_inv χ := by
    apply Subtype.ext
    apply Subtype.ext
    simp

end CliffordCorrespondence

end McKayConjecture
