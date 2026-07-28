/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ExtensionLinearTwist

/-!
# Gallagher classification of irreducible character extensions

Let `H ⊴ K`, let `χ ∈ Irr(H)`, and fix an extension `ψ ∈ Irr(K)` of
`χ`.  Gallagher's extension theorem says that every other extension is
obtained by twisting `ψ` by a unique linear character inflated from `K/H`.

This file first records the elementary correspondence between linear
characters of `K/H` and linear characters of `K` trivial on `H`.  It then
combines that correspondence with
`IrreducibleCharacter.IsExtensionAlong.exists_eq_twist` to give the
classification of extensions.

The full Gallagher theorem also parametrizes all irreducible characters
lying over `χ` by all irreducible characters of `K/H`; that version requires
a general tensor-product construction for the project's
`IrreducibleCharacter` API.  The theorem here is the degree-preserving
extension case, equivalently the linear-character part of Gallagher's
theorem.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Corollary 6.17.
* P. X. Gallagher, *Group characters and normal Hall subgroups*,
  Nagoya Math. J. 21 (1962), 223–230.
-/

noncomputable section

open CategoryTheory

universe u

namespace McKayConjecture
namespace IrreducibleCharacter

variable {K : Type u} [Group K]
variable (H : Subgroup K) [hH : H.Normal]

/-! ### Linear characters of a quotient -/

/-- Linear characters of `K` whose restriction to `H` is trivial. -/
def LinearCharactersTrivialOn :=
  {lam : K →* ℂˣ // ∀ h : H, lam (h : K) = 1}

/-- Inflation of a linear character from `K/H` to `K`. -/
def inflateLinearCharacter (beta : K ⧸ H →* ℂˣ) : K →* ℂˣ :=
  beta.comp (QuotientGroup.mk' H)

@[simp]
theorem inflateLinearCharacter_apply
    (beta : K ⧸ H →* ℂˣ) (g : K) :
    inflateLinearCharacter H beta g =
      beta (QuotientGroup.mk' H g) :=
  rfl

@[simp]
theorem inflateLinearCharacter_subgroup
    (beta : K ⧸ H →* ℂˣ) (h : H) :
    inflateLinearCharacter H beta (h : K) = 1 := by
  rw [inflateLinearCharacter_apply]
  have hh : (h : K) ∈ H := h.property
  have hq : QuotientGroup.mk' H (h : K) = 1 :=
    (QuotientGroup.eq_one_iff (h : K)).2 hh
  rw [hq, map_one]

/-- Inflation identifies the linear characters of `K/H` with the linear
characters of `K` trivial on `H`. -/
def quotientLinearCharacterEquiv :
    (K ⧸ H →* ℂˣ) ≃ LinearCharactersTrivialOn H where
  toFun beta :=
    ⟨inflateLinearCharacter H beta,
      inflateLinearCharacter_subgroup H beta⟩
  invFun lam :=
    QuotientGroup.lift H lam.1 (by
      intro g hg
      exact MonoidHom.mem_ker.mpr
        (lam.2 ⟨g, hg⟩))
  left_inv beta := by
    apply MonoidHom.ext
    intro q
    obtain ⟨g, rfl⟩ :=
      QuotientGroup.mk'_surjective H q
    rfl
  right_inv lam := by
    apply Subtype.ext
    exact QuotientGroup.lift_comp_mk' H lam.1
      (by
        intro g hg
        exact MonoidHom.mem_ker.mpr
          (lam.2 ⟨g, hg⟩))

@[simp]
theorem quotientLinearCharacterEquiv_apply_coe
    (beta : K ⧸ H →* ℂˣ) :
    (quotientLinearCharacterEquiv H beta :
      LinearCharactersTrivialOn H).1 =
        inflateLinearCharacter H beta :=
  rfl

/-! ### The extension family -/

/-- The irreducible characters of `K` extending `χ`. -/
def Extensions (χ : IrreducibleCharacter H) :=
  {phi : IrreducibleCharacter K //
    IsExtensionAlong H.subtype χ phi}

variable {H}
variable {χ : IrreducibleCharacter H}
variable {ψ : IrreducibleCharacter K}

/-- Twist a fixed extension by an inflated linear character of `K/H`. -/
def quotientTwistExtension
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (beta : K ⧸ H →* ℂˣ) :
    Extensions H χ :=
  ⟨twist (inflateLinearCharacter H beta) ψ,
    hψ.twist_isExtensionAlong
      (inflateLinearCharacter H beta)
      (inflateLinearCharacter_subgroup H beta)⟩

@[simp]
theorem quotientTwistExtension_coe
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (beta : K ⧸ H →* ℂˣ) :
    (quotientTwistExtension hψ beta).1 =
        twist (inflateLinearCharacter H beta) ψ :=
  rfl

/-- Every irreducible extension of `χ` is a twist of a fixed extension by
a linear character inflated from `K/H`. -/
theorem quotientTwistExtension_surjective
    [Finite K]
    (hψ : IsExtensionAlong H.subtype χ ψ) :
    Function.Surjective (quotientTwistExtension hψ) := by
  intro phi
  obtain ⟨lam, hlam, hphi⟩ :=
    hψ.exists_eq_twist phi.2
  let lamH : LinearCharactersTrivialOn H :=
    ⟨lam, hlam⟩
  let beta : K ⧸ H →* ℂˣ :=
    (quotientLinearCharacterEquiv H).symm lamH
  refine ⟨beta, Subtype.ext ?_⟩
  change twist (inflateLinearCharacter H beta) ψ = phi.1
  have hinflate :
      inflateLinearCharacter H beta = lam := by
    exact congrArg Subtype.val
      ((quotientLinearCharacterEquiv H).apply_symm_apply lamH)
  rw [hinflate, ← hphi]

/-! ### Freeness of twisting -/

omit hH in
/-- Linear characters trivial on `H` act freely on an irreducible
extension of an irreducible `H`-character.

The key point is the same Schur argument as in Gallagher's theorem.  An
intertwiner between two twists commutes with the restriction to `H`, so it
is a nonzero scalar.  Its ambient intertwining relation then forces the two
linear characters to agree. -/
theorem twist_injective_on_linearCharactersTrivialOn
    [Finite K]
    (hψ : IsExtensionAlong H.subtype χ ψ) :
    Function.Injective
      (fun lam : LinearCharactersTrivialOn H ↦
        twist lam.1 ψ) := by
  classical
  intro lam mu htwist
  let ρ : Representation ℂ K ψ.realization :=
    ψ.realization.ρ
  let ρlam : Representation ℂ K ψ.realization :=
    twistRepresentation lam.1 ψ.realization
  let ρmu : Representation ℂ K ψ.realization :=
    twistRepresentation mu.1 ψ.realization
  letI : Simple (twistFDRep lam.1 ψ.realization) :=
    twistFDRep_simple lam.1 ψ.realization
  letI : Representation.IsIrreducible ρlam := by
    exact CliffordRestriction.isIrreducible_of_simple
      (twistFDRep lam.1 ψ.realization)
  have hchar : ρmu.character = ρlam.character := by
    funext g
    calc
      ρmu.character g =
          (mu.1 g : ℂ) *
            ψ.realization.character g := by
        exact twistFDRep_character mu.1 ψ.realization g
      _ = (lam.1 g : ℂ) *
            ψ.realization.character g := by
        rw [ψ.realization_character]
        have hg :=
          congrArg
            (fun phi : IrreducibleCharacter K ↦ phi.values g)
            htwist
        simpa only [twist_values] using hg.symm
      _ = ρlam.character g := by
        exact
          (twistFDRep_character lam.1
            ψ.realization g).symm
  obtain ⟨T⟩ :=
    Representation.nonempty_equiv_of_character_eq_irreducible
      ρlam ρmu hchar
  let res : Representation ℂ H ψ.realization :=
    ρ.comp H.subtype
  let ρχ : Representation ℂ H χ.realization :=
    χ.realization.ρ
  letI : Representation.IsIrreducible ρχ :=
    CliffordRestriction.isIrreducible_of_simple χ.realization
  have hreschar : res.character = ρχ.character := by
    funext h
    calc
      res.character h =
          ψ.realization.character (h : K) := rfl
      _ = ψ.values (h : K) :=
        congrFun ψ.realization_character (h : K)
      _ = χ.values h := hψ h
      _ = χ.realization.character h :=
        (congrFun χ.realization_character h).symm
      _ = ρχ.character h := rfl
  obtain ⟨Phi⟩ :=
    Representation.nonempty_equiv_of_character_eq_irreducible
      ρχ res hreschar
  letI : Representation.IsIrreducible res :=
    Representation.IsIrreducible.of_equiv Phi
  have hcomm : ∀ h : H,
      res h * T.toLinearMap =
        T.toLinearMap * res h := by
    intro h
    have hinter := T.isIntertwining' (h : K)
    change
      T.toLinearMap ∘ₗ
          ((lam.1 (h : K) : ℂ) • ρ (h : K)) =
        ((mu.1 (h : K) : ℂ) • ρ (h : K)) ∘ₗ
          T.toLinearMap
      at hinter
    rw [lam.2 h, mu.2 h, Units.val_one, one_smul]
      at hinter
    change
      ρ (h : K) * T.toLinearMap =
        T.toLinearMap * ρ (h : K)
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp]
    exact hinter.symm
  obtain ⟨c, hc⟩ :=
    RepresentationTheory.exists_smul_id_of_forall_mul_comm
      res T.toLinearMap hcomm
  letI : Nontrivial ψ.realization :=
    CliffordRestriction.nontrivial_of_simple ψ.realization
  have hc0 : c ≠ 0 := by
    intro hczero
    have hTzero : T.toLinearMap = 0 := by
      simpa only [hczero, zero_smul] using hc
    obtain ⟨v, hv⟩ := exists_ne (0 : ψ.realization)
    apply hv
    apply T.toLinearEquiv.injective
    change T.toLinearMap v = T.toLinearMap 0
    rw [hTzero]
    rfl
  apply Subtype.ext
  apply MonoidHom.ext
  intro g
  apply Units.ext
  obtain ⟨v, hv⟩ := exists_ne (0 : ψ.realization)
  have hρv : ρ g v ≠ 0 := by
    intro hzero
    apply hv
    calc
      v = ρ 1 v := by
        rw [map_one]
        rfl
      _ = ρ (g⁻¹ * g) v := by
        rw [inv_mul_cancel]
      _ = ρ g⁻¹ (ρ g v) := by
        rw [map_mul]
        rfl
      _ = ρ g⁻¹ 0 := by rw [hzero]
      _ = 0 := map_zero _
  have hinter := T.isIntertwining' g
  change
    T.toLinearMap ∘ₗ ((lam.1 g : ℂ) • ρ g) =
      ((mu.1 g : ℂ) • ρ g) ∘ₗ T.toLinearMap
    at hinter
  rw [hc] at hinter
  have hscalarMap := LinearMap.congr_fun hinter v
  simp only [LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply, map_smul, smul_smul] at hscalarMap
  have hscalar :
      (lam.1 g : ℂ) * c =
        c * (mu.1 g : ℂ) :=
    smul_left_injective ℂ hρv hscalarMap
  exact mul_right_cancel₀ hc0
    (hscalar.trans (mul_comm c (mu.1 g : ℂ)))

/-! ### Gallagher's equivalence for extensions -/

/-- Twisting by inflated quotient linear characters is injective on a
fixed irreducible extension. -/
theorem quotientTwistExtension_injective
    [Finite K]
    (hψ : IsExtensionAlong H.subtype χ ψ) :
    Function.Injective (quotientTwistExtension hψ) := by
  intro beta gamma htwist
  have hcharacter :
      twist (inflateLinearCharacter H beta) ψ =
        twist (inflateLinearCharacter H gamma) ψ :=
    congrArg Subtype.val htwist
  have htrivial :
      quotientLinearCharacterEquiv H beta =
        quotientLinearCharacterEquiv H gamma := by
    apply twist_injective_on_linearCharactersTrivialOn hψ
    simpa only [quotientLinearCharacterEquiv_apply_coe]
      using hcharacter
  exact (quotientLinearCharacterEquiv H).injective htrivial

/-- **Gallagher's classification for extensions.**  Once one irreducible
extension `ψ` of `χ` is fixed, twisting by linear characters of `K/H`
gives an equivalence onto all irreducible extensions of `χ`. -/
def gallagherExtensionEquiv
    [Finite K]
    (hψ : IsExtensionAlong H.subtype χ ψ) :
    (K ⧸ H →* ℂˣ) ≃ Extensions H χ :=
  Equiv.ofBijective
    (quotientTwistExtension hψ)
    ⟨quotientTwistExtension_injective hψ,
      quotientTwistExtension_surjective hψ⟩

@[simp]
theorem gallagherExtensionEquiv_apply
    [Finite K]
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (beta : K ⧸ H →* ℂˣ) :
    (gallagherExtensionEquiv hψ beta).1 =
      twist (inflateLinearCharacter H beta) ψ :=
  rfl

/-- Explicit existence and uniqueness form of Gallagher's extension
classification. -/
theorem existsUnique_quotientLinearCharacter_twist
    [Finite K]
    (hψ : IsExtensionAlong H.subtype χ ψ)
    (phi : Extensions H χ) :
    ∃! beta : K ⧸ H →* ℂˣ,
      phi.1 = twist (inflateLinearCharacter H beta) ψ := by
  let beta := (gallagherExtensionEquiv hψ).symm phi
  have hbeta :
      phi.1 =
        twist (inflateLinearCharacter H beta) ψ := by
    have h :=
      (gallagherExtensionEquiv hψ).apply_symm_apply phi
    simpa only [gallagherExtensionEquiv_apply] using
      (congrArg Subtype.val h).symm
  refine ⟨beta, hbeta, ?_⟩
  · intro gamma hgamma
    apply (gallagherExtensionEquiv hψ).injective
    apply Subtype.ext
    rw [gallagherExtensionEquiv_apply]
    exact hgamma.symm.trans hbeta

end IrreducibleCharacter
end McKayConjecture
