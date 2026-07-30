/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.InvariantCharacterTransferExtension
import McKayConjecture.Character.GallagherCorrespondence
import McKayConjecture.Character.OverAlongTransport
import McKayConjecture.Character.Twist
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Lying-over fibres under invariant linear twists

Let `φ : H →* G`, let `μ : H →* ℂˣ`, and suppose that
`λ : G →* ℂˣ` restricts to `μ`.  Simultaneously twisting a source character
by `μ` and an ambient character by `λ` does not change the restriction
intertwining space.  Consequently, ambient twisting gives an explicit
equivalence

`Irr(G | η) ≃ Irr(G | μ η)`.

The second part supplies the extension needed in the normal-Sylow
application.  A conjugation-invariant complex linear character of a normal
Sylow subgroup extends to the ambient finite group: choose a
Schur--Zassenhaus complement and extend trivially across it.  A quotient
wrapper then inflates such an extension from `G / K` to `G` and applies the
fibre-twist equivalence over the full preimage of the Sylow subgroup.

The source and target applications are intentionally independent.  No
identification of their linear parameters or of their chosen extensions is
required.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture

namespace IrreducibleCharacter

variable {G : Type} [Group G] [Finite G]

/-- The chosen realization of a linear twist is isomorphic to the literal
twist of the chosen realization. -/
def twistRealizationIso
    (lam : G →* ℂˣ) (χ : IrreducibleCharacter G) :
    (twist lam χ).realization ≅
      twistFDRep lam χ.realization := by
  letI : Simple (twistFDRep lam χ.realization) :=
    twistFDRep_simple lam χ.realization
  apply Classical.choice
  apply FDRep.nonempty_iso_of_character_eq
  funext g
  rw [(twist lam χ).realization_character]
  simp

/-- The multiplicative-linear part of Gallagher's correspondence is
literally twisting the chosen extension by the inflated quotient
character. -/
theorem gallagherTensorCharacter_linear_eq_twist
    {H : Subgroup G} [H.Normal]
    {chi : IrreducibleCharacter H}
    {psi : IrreducibleCharacter G}
    (hpsi : IsExtensionAlong H.subtype chi psi)
    (mu : G ⧸ H →* ℂˣ) :
    gallagherTensorCharacter hpsi (linear mu) =
      twist (inflateLinearCharacter H mu) psi := by
  apply IrreducibleCharacter.ext
  funext g
  rw [gallagherTensorCharacter_values, linear_values,
    twist_values, inflateLinearCharacter_apply]
  exact mul_comm _ _

end IrreducibleCharacter

namespace Representation

variable {V W : Type}
variable [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
variable [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]

/-- Multiplying both actions by compatible linear characters does not
change their intertwining space. -/
def intertwiningMapCompatibleTwistEquiv
    {G H : Type} [Group G] [Group H]
    (φ : H →* G)
    (mu : H →* ℂˣ) (lam : G →* ℂˣ)
    (hcompat : lam.comp φ = mu)
    (ρ : Representation ℂ H V)
    (σ : Representation ℂ G W) :
    Representation.IntertwiningMap ρ (σ.comp φ) ≃ₗ[ℂ]
      Representation.IntertwiningMap
        (IrreducibleCharacter.twistRepresentation mu (FDRep.of ρ))
        ((IrreducibleCharacter.twistRepresentation lam
          (FDRep.of σ)).comp φ) where
  toFun f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' h := by
        apply LinearMap.ext
        intro v
        have hi :=
          LinearMap.congr_fun (f.isIntertwining' h) v
        have hc :
            lam (φ h) = mu h :=
          DFunLike.congr_fun hcompat h
        change
          f.toLinearMap ((mu h : ℂ) • ρ h v) =
            (lam (φ h) : ℂ) •
              σ (φ h) (f.toLinearMap v)
        rw [f.toLinearMap.map_smul, hc]
        exact congrArg (fun z => (mu h : ℂ) • z) hi }
  invFun f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' h := by
        apply LinearMap.ext
        intro v
        have hi :=
          LinearMap.congr_fun (f.isIntertwining' h) v
        have hc :
            lam (φ h) = mu h :=
          DFunLike.congr_fun hcompat h
        change
          f.toLinearMap (ρ h v) =
            σ (φ h) (f.toLinearMap v)
        change
          f.toLinearMap ((mu h : ℂ) • ρ h v) =
            (lam (φ h) : ℂ) •
              σ (φ h) (f.toLinearMap v) at hi
        rw [f.toLinearMap.map_smul, hc] at hi
        have hi' :=
          congrArg (fun z => ((mu h : ℂ)⁻¹) • z) hi
        simpa [smul_smul,
          inv_mul_cancel₀ (Units.ne_zero (mu h))] using hi' }
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

end Representation

namespace CliffordCorrespondence

variable {G H : Type} [Group G] [Group H]
variable [Finite G] [Finite H]

/-- Compatible linear twisting gives a linear equivalence of the two
restriction-Hom spaces. -/
def restrictionHomTwistEquiv
    (φ : H →* G)
    (eta : IrreducibleCharacter H)
    (chi : IrreducibleCharacter G)
    (mu : H →* ℂˣ) (lam : G →* ℂˣ)
    (hcompat : lam.comp φ = mu) :
    (eta.realization ⟶ FDRep.res φ chi.realization) ≃ₗ[ℂ]
      ((IrreducibleCharacter.twist mu eta).realization ⟶
        FDRep.res φ
          (IrreducibleCharacter.twist lam chi).realization) := by
  let oldHom :=
    FDRep.homIntertwiningEquiv
      eta.realization (FDRep.res φ chi.realization)
  let oldRestriction :=
    CliffordEquivalence.restrictionAlongRepresentationEquiv
      φ chi.realization
  let exposeOldRestriction :=
    Representation.intertwiningMapCongr
      (Representation.Equiv.refl eta.realization.ρ)
      oldRestriction.symm
  let literalTwist :=
    Representation.intertwiningMapCompatibleTwistEquiv
      φ mu lam hcompat eta.realization.ρ chi.realization.ρ
  let ieta :=
    IrreducibleCharacter.twistRealizationIso mu eta
  let ichi :=
    IrreducibleCharacter.twistRealizationIso lam chi
  let eeta :=
    FDRep.representationEquivOfIso ieta
  let echi :=
    FDRep.representationEquivOfIso ichi
  let echiRestricted :=
    Mackey.compEquiv φ echi
  let newRestriction :=
    CliffordEquivalence.restrictionAlongRepresentationEquiv
      φ (IrreducibleCharacter.twist lam chi).realization
  let hideNewRealizations :=
    Representation.intertwiningMapCongr
      eeta (newRestriction.trans echiRestricted)
  let newHom :=
    FDRep.homIntertwiningEquiv
      (IrreducibleCharacter.twist mu eta).realization
      (FDRep.res φ
        (IrreducibleCharacter.twist lam chi).realization)
  exact
    oldHom.trans
      (exposeOldRestriction.trans
        (literalTwist.trans
          (hideNewRealizations.trans newHom.symm)))

/-- Restriction multiplicity is unchanged when source and ambient
characters are twisted by compatible linear characters. -/
theorem restrictionMultiplicity_twist
    (φ : H →* G)
    (eta : IrreducibleCharacter H)
    (chi : IrreducibleCharacter G)
    (mu : H →* ℂˣ) (lam : G →* ℂˣ)
    (hcompat : lam.comp φ = mu) :
    restrictionMultiplicity φ
        (IrreducibleCharacter.twist mu eta)
        (IrreducibleCharacter.twist lam chi) =
      restrictionMultiplicity φ eta chi := by
  rw [restrictionMultiplicity, restrictionMultiplicity]
  exact
    (restrictionHomTwistEquiv
      φ eta chi mu lam hcompat).finrank_eq.symm

/-- Lying over is unchanged when source and ambient characters are twisted
by compatible linear characters. -/
theorem liesOverAlong_twist_iff
    (φ : H →* G)
    (eta : IrreducibleCharacter H)
    (chi : IrreducibleCharacter G)
    (mu : H →* ℂˣ) (lam : G →* ℂˣ)
    (hcompat : lam.comp φ = mu) :
    LiesOverAlong φ
        (IrreducibleCharacter.twist mu eta)
        (IrreducibleCharacter.twist lam chi) ↔
      LiesOverAlong φ eta chi := by
  rw [LiesOverAlong, LiesOverAlong,
    restrictionMultiplicity_twist
      φ eta chi mu lam hcompat]

/-- Twisting by an ambient linear extension identifies the corresponding
ordinary lying-over fibres.  The inverse twists by `lam⁻¹`. -/
def twistOverEquiv_of_linearExtension
    (φ : H →* G)
    (eta : IrreducibleCharacter H)
    (mu : H →* ℂˣ) (lam : G →* ℂˣ)
    (hcompat : lam.comp φ = mu) :
    IrreducibleCharactersOverAlong φ eta ≃
      IrreducibleCharactersOverAlong φ
        (IrreducibleCharacter.twist mu eta) where
  toFun chi :=
    ⟨IrreducibleCharacter.twist lam chi.1,
      (liesOverAlong_twist_iff
        φ eta chi.1 mu lam hcompat).2 chi.2⟩
  invFun psi :=
    ⟨IrreducibleCharacter.twist lam⁻¹ psi.1, by
      apply
        (liesOverAlong_twist_iff
          φ eta
            (IrreducibleCharacter.twist lam⁻¹ psi.1)
            mu lam hcompat).1
      have hcancel : lam * lam⁻¹ = 1 :=
        mul_inv_cancel lam
      simpa only [← IrreducibleCharacter.twist_mul,
        hcancel, IrreducibleCharacter.twist_one] using psi.2⟩
  left_inv chi := by
    apply Subtype.ext
    change
      IrreducibleCharacter.twist lam⁻¹
          (IrreducibleCharacter.twist lam chi.1) =
        chi.1
    have hcancel : lam⁻¹ * lam = 1 :=
      inv_mul_cancel lam
    calc
      IrreducibleCharacter.twist lam⁻¹
          (IrreducibleCharacter.twist lam chi.1) =
        IrreducibleCharacter.twist (lam⁻¹ * lam) chi.1 :=
          (IrreducibleCharacter.twist_mul lam⁻¹ lam chi.1).symm
      _ = IrreducibleCharacter.twist 1 chi.1 := by
        exact congrArg
          (fun nu => IrreducibleCharacter.twist nu chi.1)
          hcancel
      _ = chi.1 :=
        IrreducibleCharacter.twist_one chi.1
  right_inv psi := by
    apply Subtype.ext
    change
      IrreducibleCharacter.twist lam
          (IrreducibleCharacter.twist lam⁻¹ psi.1) =
        psi.1
    have hcancel : lam * lam⁻¹ = 1 :=
      mul_inv_cancel lam
    calc
      IrreducibleCharacter.twist lam
          (IrreducibleCharacter.twist lam⁻¹ psi.1) =
        IrreducibleCharacter.twist (lam * lam⁻¹) psi.1 :=
          (IrreducibleCharacter.twist_mul lam lam⁻¹ psi.1).symm
      _ = IrreducibleCharacter.twist 1 psi.1 := by
        exact congrArg
          (fun nu => IrreducibleCharacter.twist nu psi.1)
          hcancel
      _ = psi.1 :=
        IrreducibleCharacter.twist_one psi.1

/-- Independent source and target twists preserve any established
base-fibre cardinality equality.  There is deliberately no hypothesis
relating `mu₁` to `mu₂` or `lam₁` to `lam₂`. -/
theorem natCard_independentTwists_eq_of_base_eq
    {G₁ H₁ G₂ H₂ : Type}
    [Group G₁] [Group H₁] [Finite G₁] [Finite H₁]
    [Group G₂] [Group H₂] [Finite G₂] [Finite H₂]
    (φ₁ : H₁ →* G₁) (φ₂ : H₂ →* G₂)
    (eta₁ : IrreducibleCharacter H₁)
    (eta₂ : IrreducibleCharacter H₂)
    (mu₁ : H₁ →* ℂˣ) (lam₁ : G₁ →* ℂˣ)
    (mu₂ : H₂ →* ℂˣ) (lam₂ : G₂ →* ℂˣ)
    (hcompat₁ : lam₁.comp φ₁ = mu₁)
    (hcompat₂ : lam₂.comp φ₂ = mu₂)
    (hbase :
      Nat.card (IrreducibleCharactersOverAlong φ₁ eta₁) =
        Nat.card (IrreducibleCharactersOverAlong φ₂ eta₂)) :
    Nat.card
        (IrreducibleCharactersOverAlong φ₁
          (IrreducibleCharacter.twist mu₁ eta₁)) =
      Nat.card
        (IrreducibleCharactersOverAlong φ₂
          (IrreducibleCharacter.twist mu₂ eta₂)) := by
  calc
    Nat.card
        (IrreducibleCharactersOverAlong φ₁
          (IrreducibleCharacter.twist mu₁ eta₁)) =
      Nat.card
        (IrreducibleCharactersOverAlong φ₁ eta₁) :=
      (Nat.card_congr
        (twistOverEquiv_of_linearExtension
          φ₁ eta₁ mu₁ lam₁ hcompat₁)).symm
    _ =
      Nat.card
        (IrreducibleCharactersOverAlong φ₂ eta₂) :=
      hbase
    _ =
      Nat.card
        (IrreducibleCharactersOverAlong φ₂
          (IrreducibleCharacter.twist mu₂ eta₂)) :=
      Nat.card_congr
        (twistOverEquiv_of_linearExtension
          φ₂ eta₂ mu₂ lam₂ hcompat₂)

end CliffordCorrespondence

namespace GroupTheory

/-- Invariance of the associated linear irreducible character is the
conjugation-invariance needed by the normal-Sylow extension construction. -/
theorem complexLinearCharacter_isConjugationInvariant_of_linear_invariant
    {G : Type} [Group G]
    (P : Subgroup G) [P.Normal]
    (mu : P →* ℂˣ)
    (hmu :
      ∀ g : G,
        IrreducibleCharacter.conjBy P g
            (IrreducibleCharacter.linear mu) =
          IrreducibleCharacter.linear mu) :
    MonoidHom.IsConjugationInvariant P mu := by
  intro g x
  have hx :=
    congrArg
      (fun chi : IrreducibleCharacter P => chi.values x)
      (hmu g)
  apply Units.ext
  simp only [IrreducibleCharacter.conjBy_values,
    IrreducibleCharacter.linear_values] at hx
  let y : P :=
    ⟨g⁻¹ * (x : G) * g,
      (inferInstance : P.Normal).conj_mem'
        (x : G) x.property g⟩
  change (mu y : ℂ) = (mu x : ℂ)
  have hy :
      y = (MulAut.conjNormal g).symm x := by
    apply Subtype.ext
    simp [y]
  rw [hy]
  exact hx

/-- Inertia equal to the whole ambient group supplies the preceding
invariance hypothesis for a linear character. -/
theorem complexLinearCharacter_isConjugationInvariant_of_inertia_eq_top
    {G : Type} [Group G]
    (P : Subgroup G) [P.Normal]
    (mu : P →* ℂˣ)
    (hinertia :
      IrreducibleCharacter.inertia P
          (IrreducibleCharacter.linear mu) =
        ⊤) :
    MonoidHom.IsConjugationInvariant P mu := by
  apply
    complexLinearCharacter_isConjugationInvariant_of_linear_invariant
  intro g
  apply
    (IrreducibleCharacter.mem_inertia_iff
      P (IrreducibleCharacter.linear mu) g).1
  rw [hinertia]
  exact Subgroup.mem_top g

/-- A conjugation-invariant complex linear character of a normal subgroup
extends across any chosen complement. -/
theorem exists_complexLinearCharacter_extension_of_invariant_of_isComplement
    {G : Type} [Group G]
    (P U : Subgroup G) [P.Normal]
    (hcomplement : P.IsComplement' U)
    (mu : P →* ℂˣ)
    (hmu : MonoidHom.IsConjugationInvariant P mu) :
    ∃ lam : G →* ℂˣ,
      lam.comp P.subtype = mu := by
  let action : U →* MulAut P :=
    P.normalizerMonoidHom.comp
      (Subgroup.inclusion (P.normalizer_eq_top ▸ le_top))
  have haction :
      ∀ u : U,
        mu.comp (action u).toMonoidHom =
          (MulAut.conj ((1 : U →* ℂˣ) u)).toMonoidHom.comp mu := by
    intro u
    apply MonoidHom.ext
    intro x
    change mu (action u x) = 1 * mu x * 1⁻¹
    rw [one_mul, inv_one, mul_one]
    have hactionValue :
        action u x =
          (⟨(u : G) * (x : G) * (u : G)⁻¹,
              (inferInstance : P.Normal).conj_mem
                (x : G) x.property (u : G)⟩ : P) := by
      apply Subtype.ext
      rfl
    rw [hactionValue]
    simpa using hmu ((u : G)⁻¹) x
  let sdExtension :
      P ⋊[action] U →* ℂˣ :=
    SemidirectProduct.lift mu (1 : U →* ℂˣ) haction
  let e : P ⋊[action] U ≃* G :=
    SemidirectProduct.mulEquivSubgroup hcomplement
  let lam : G →* ℂˣ :=
    sdExtension.comp e.symm.toMonoidHom
  refine ⟨lam, ?_⟩
  apply MonoidHom.ext
  intro x
  change sdExtension (e.symm (x : G)) = mu x
  have he :
      e.symm (x : G) = SemidirectProduct.inl x := by
    apply e.injective
    rw [e.apply_symm_apply]
    dsimp only [e, SemidirectProduct.mulEquivSubgroup,
      SemidirectProduct.monoidHomSubgroup,
      SemidirectProduct.lift, SemidirectProduct.inl]
    exact (mul_one (x : G)).symm
  rw [he]
  exact SemidirectProduct.lift_inl mu
    (1 : U →* ℂˣ) haction x

/-- A conjugation-invariant complex linear character of a normal Sylow
subgroup extends to the ambient finite group. -/
theorem exists_complexLinearCharacter_extension_of_normalSylow
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) [(P : Subgroup G).Normal]
    (mu : (P : Subgroup G) →* ℂˣ)
    (hmu :
      MonoidHom.IsConjugationInvariant
        (P : Subgroup G) mu) :
    ∃ lam : G →* ℂˣ,
      lam.comp (P : Subgroup G).subtype = mu := by
  obtain ⟨U, hU⟩ :=
    Subgroup.exists_right_complement'_of_coprime
      P.card_coprime_index
  exact
    exists_complexLinearCharacter_extension_of_invariant_of_isComplement
      (P : Subgroup G) U hU mu hmu

/-- The canonical homomorphism from the full preimage of a quotient
subgroup to that quotient subgroup. -/
def quotientSubgroupProjection
    {G : Type} [Group G]
    (K : Subgroup G) [K.Normal]
    (P : Subgroup (G ⧸ K)) :
    P.comap (QuotientGroup.mk' K) →* P where
  toFun x :=
    ⟨QuotientGroup.mk' K (x : G), x.property⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp

@[simp]
theorem quotientSubgroupProjection_apply
    {G : Type} [Group G]
    (K : Subgroup G) [K.Normal]
    (P : Subgroup (G ⧸ K))
    (x : P.comap (QuotientGroup.mk' K)) :
    (quotientSubgroupProjection K P x : G ⧸ K) =
      QuotientGroup.mk' K (x : G) :=
  rfl

/-- A normal-Sylow parameter in a quotient inflates to an ambient linear
character extending its pullback to the full preimage. -/
theorem exists_inflatedLinearExtension_of_normalQuotientSylow
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (K : Subgroup G) [K.Normal]
    (P : Sylow p (G ⧸ K))
    [(P : Subgroup (G ⧸ K)).Normal]
    (mu : (P : Subgroup (G ⧸ K)) →* ℂˣ)
    (hmu :
      MonoidHom.IsConjugationInvariant
        (P : Subgroup (G ⧸ K)) mu) :
    ∃ lam : G →* ℂˣ,
      lam.comp
          ((P : Subgroup (G ⧸ K)).comap
            (QuotientGroup.mk' K)).subtype =
        mu.comp
          (quotientSubgroupProjection
            K (P : Subgroup (G ⧸ K))) := by
  obtain ⟨lamBar, hlamBar⟩ :=
    exists_complexLinearCharacter_extension_of_normalSylow
      P mu hmu
  refine
    ⟨lamBar.comp (QuotientGroup.mk' K), ?_⟩
  apply MonoidHom.ext
  intro x
  have hs :=
    DFunLike.congr_fun hlamBar
      (quotientSubgroupProjection
        K (P : Subgroup (G ⧸ K)) x)
  exact hs

/-- A chosen inflated extension of a normal-Sylow parameter in a quotient. -/
def inflatedNormalQuotientSylowLinearExtension
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (K : Subgroup G) [K.Normal]
    (P : Sylow p (G ⧸ K))
    [(P : Subgroup (G ⧸ K)).Normal]
    (mu : (P : Subgroup (G ⧸ K)) →* ℂˣ)
    (hmu :
      MonoidHom.IsConjugationInvariant
        (P : Subgroup (G ⧸ K)) mu) :
    G →* ℂˣ :=
  Classical.choose
    (exists_inflatedLinearExtension_of_normalQuotientSylow
      K P mu hmu)

/-- The chosen inflated extension restricts to the pulled-back quotient
parameter on the full preimage. -/
theorem inflatedNormalQuotientSylowLinearExtension_spec
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (K : Subgroup G) [K.Normal]
    (P : Sylow p (G ⧸ K))
    [(P : Subgroup (G ⧸ K)).Normal]
    (mu : (P : Subgroup (G ⧸ K)) →* ℂˣ)
    (hmu :
      MonoidHom.IsConjugationInvariant
        (P : Subgroup (G ⧸ K)) mu) :
    (inflatedNormalQuotientSylowLinearExtension
        K P mu hmu).comp
          ((P : Subgroup (G ⧸ K)).comap
            (QuotientGroup.mk' K)).subtype =
      mu.comp
        (quotientSubgroupProjection
          K (P : Subgroup (G ⧸ K))) :=
  Classical.choose_spec
    (exists_inflatedLinearExtension_of_normalQuotientSylow
      K P mu hmu)

end GroupTheory

namespace CliffordCorrespondence

/-- The explicit fibre twist attached to an invariant normal-Sylow
parameter in an ambient quotient. -/
def twistOverEquiv_of_normalQuotientSylowParameter
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (K : Subgroup G) [K.Normal]
    (P : Sylow p (G ⧸ K))
    [(P : Subgroup (G ⧸ K)).Normal]
    (mu : (P : Subgroup (G ⧸ K)) →* ℂˣ)
    (hmu :
      MonoidHom.IsConjugationInvariant
        (P : Subgroup (G ⧸ K)) mu)
    (alpha :
      IrreducibleCharacter
        ((P : Subgroup (G ⧸ K)).comap
          (QuotientGroup.mk' K))) :
    IrreducibleCharactersOverAlong
        ((P : Subgroup (G ⧸ K)).comap
          (QuotientGroup.mk' K)).subtype alpha ≃
      IrreducibleCharactersOverAlong
        ((P : Subgroup (G ⧸ K)).comap
          (QuotientGroup.mk' K)).subtype
        (IrreducibleCharacter.twist
          (mu.comp
            (GroupTheory.quotientSubgroupProjection
              K (P : Subgroup (G ⧸ K))))
          alpha) :=
  twistOverEquiv_of_linearExtension
    ((P : Subgroup (G ⧸ K)).comap
      (QuotientGroup.mk' K)).subtype
    alpha
    (mu.comp
      (GroupTheory.quotientSubgroupProjection
        K (P : Subgroup (G ⧸ K))))
    (GroupTheory.inflatedNormalQuotientSylowLinearExtension
      K P mu hmu)
    (GroupTheory.inflatedNormalQuotientSylowLinearExtension_spec
      K P mu hmu)

end CliffordCorrespondence

end McKayConjecture
