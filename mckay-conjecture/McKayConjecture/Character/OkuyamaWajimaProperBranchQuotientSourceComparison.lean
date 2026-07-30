/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ExtensionLinearTwist
import McKayConjecture.Character.OkuyamaWajimaProperBranchQuotientInduction
import McKayConjecture.Character.PPrimeDeterminantRoot
import McKayConjecture.Character.QuotientDescent

/-!
# Source-extension comparison in the proper quotient branch

Let `J ◁ X` be a `p'`-group and let `Q ◁ X` be a `p`-group centralizing
`J`.  If a prime-to-`p` character of `J` extends to `X`, an arbitrary
extension need not initially be trivial on `Q`.  Its restriction to `J` is
irreducible, however, so Schur's lemma makes every element of `Q` act by a
scalar.

The determinant character of the extension is raised first to `|J|`, making
it trivial on `J`, and then to a Bézout inverse of
`degree * |J|` modulo `|Q|`.  The resulting ambient linear character is
still trivial on `J` and recovers the scalar action on `Q`.  Twisting by its
inverse therefore preserves the extension on `J` and makes it descend
through `Q`.

This gives the exact source-coordinate comparison needed for the first
recursive call in the printed Okuyama--Wajima proof.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace IrreducibleCharacter

universe u

section RelativeDeterminantNormalization

variable {X : Type u} [Group X] [Finite X]
variable {J : Subgroup X}

/-- An element centralizing the source subgroup acts by a scalar in any
ambient extension of an irreducible source character. -/
theorem exists_realization_scalar_of_centralizes_extension
    (psi : IrreducibleCharacter J)
    (eta : IrreducibleCharacter X)
    (heta : IsExtensionAlong J.subtype psi eta)
    (x : X)
    (hx : x ∈ Subgroup.centralizer (J : Set X)) :
    ∃ c : ℂ,
      eta.realization.ρ x =
        c • (LinearMap.id : Module.End ℂ eta.realization) := by
  let V : FDRep ℂ J :=
    FDRep.of (eta.realization.ρ.comp J.subtype)
  have hchar :
      V.character = psi.realization.character := by
    funext j
    change eta.realization.character (j : X) =
      psi.realization.character j
    rw [eta.realization_character, psi.realization_character]
    exact heta j
  letI hpsiIrreducible :
      Representation.IsIrreducible psi.realization.ρ :=
    CliffordRestriction.isIrreducible_of_simple psi.realization
  obtain ⟨e⟩ :=
    Representation.nonempty_equiv_of_character_eq_irreducible
      psi.realization.ρ V.ρ hchar
  letI hVIrreducible :
      Representation.IsIrreducible V.ρ :=
    Representation.IsIrreducible.of_equiv e
  letI hVSimple : Simple V :=
    FDRep.simple_of_representation_isIrreducible V.ρ
  let f : V ⟶ V :=
    ⟨InducedCategory.homMk
        (ModuleCat.ofHom (eta.realization.ρ x)),
      fun j => by
        apply FGModuleCat.hom_ext
        ext v
        change
          eta.realization.ρ x
              (eta.realization.ρ (j : X) v) =
            eta.realization.ρ (j : X)
              (eta.realization.ρ x v)
        rw [← Module.End.mul_apply, ← Module.End.mul_apply,
          ← map_mul, ← map_mul]
        exact congrArg
          (fun y : X => eta.realization.ρ y v)
          ((Subgroup.mem_centralizer_iff.mp hx)
            (j : X) j.2).symm⟩
  obtain ⟨c, hc⟩ :=
    endomorphism_simple_eq_smul_id ℂ f
  refine ⟨c, ?_⟩
  apply LinearMap.ext
  intro v
  have hv := ConcreteCategory.congr_hom hc v
  change c • v = eta.realization.ρ x v at hv
  exact hv.symm

/-- The relative determinant character used to remove a commuting
`p`-kernel from an extension.

The first exponent kills the restriction to `J`; the second exponent
inverts `eta.degree * |J|` modulo `|Q|`. -/
def relativeDeterminantNormalizingCharacter
    (J Q : Subgroup X)
    (eta : IrreducibleCharacter X) :
    X →* ℂˣ :=
  ((determinantParameter eta) ^ Nat.card J) ^
    (Nat.card Q).gcdB (eta.degree * Nat.card J)

theorem relativeDeterminantNormalizingCharacter_eq_one_on_source
    (J Q : Subgroup X)
    (eta : IrreducibleCharacter X)
    (j : J) :
    relativeDeterminantNormalizingCharacter J Q eta (j : X) = 1 := by
  have hpow :
      determinantParameter eta (j : X) ^ Nat.card J = 1 := by
    calc
      determinantParameter eta (j : X) ^ Nat.card J =
          determinantParameter eta ((j : X) ^ Nat.card J) := by
            rw [map_pow]
      _ = determinantParameter eta (((j ^ Nat.card J : J) : X)) := rfl
      _ = 1 := by
        rw [pow_card_eq_one']
        exact map_one (determinantParameter eta)
  change
    (determinantParameter eta (j : X) ^ Nat.card J) ^
        (Nat.card Q).gcdB (eta.degree * Nat.card J) =
      1
  rw [hpow, one_zpow]

theorem relativeDeterminantNormalizingCharacter_eq_scalarUnit_on_kernel
    (J Q : Subgroup X)
    (eta : IrreducibleCharacter X)
    (hcoprime :
      (Nat.card Q).Coprime (eta.degree * Nat.card J))
    (q : Q)
    (c : ℂ)
    (hc :
      eta.realization.ρ (q : X) =
        c • (LinearMap.id : Module.End ℂ eta.realization)) :
    relativeDeterminantNormalizingCharacter J Q eta (q : X) =
      Units.mk0 c
        (scalar_ne_zero_of_finite_source
          eta Q.subtype q c hc) := by
  let cu : ℂˣ :=
    Units.mk0 c
      (scalar_ne_zero_of_finite_source
        eta Q.subtype q c hc)
  have horder : cu ^ Nat.card Q = 1 := by
    apply Units.ext
    simpa [cu] using
      scalar_pow_natCard_eq_one
        eta Q.subtype q c hc
  have hdet :
      determinantParameter eta (q : X) =
        cu ^ eta.degree := by
    apply Units.ext
    simpa [cu] using
      determinantParameter_eq_scalar_pow
        eta (q : X) c hc
  have hroot :
      cu =
        (cu ^ (eta.degree * Nat.card J)) ^
          (Nat.card Q).gcdB (eta.degree * Nat.card J) :=
    eq_pow_gcdB_of_pow_eq_one
      cu (Nat.card Q) (eta.degree * Nat.card J)
      hcoprime horder
  change
    (determinantParameter eta (q : X) ^ Nat.card J) ^
        (Nat.card Q).gcdB (eta.degree * Nat.card J) =
      cu
  rw [hdet, ← pow_mul]
  exact hroot.symm

variable {p : ℕ} [Fact p.Prime]

/-- The kernel order is coprime to the exponent used in relative
determinant normalization. -/
theorem kernel_card_coprime_extension_degree_mul_source_card
    (J Q : Subgroup X)
    (psi : IrreducibleCharacter J)
    (eta : IrreducibleCharacter X)
    (heta : IsExtensionAlong J.subtype psi eta)
    (hQ : IsPGroup p Q)
    (hJ : GroupTheory.IsPPrimeGroup p J)
    (hpsi : psi.IsPPrimeDegree p) :
    (Nat.card Q).Coprime (eta.degree * Nat.card J) := by
  have hpDegree :
      p.Coprime eta.degree := by
    rw [heta.degree_eq]
    exact
      (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
        hpsi
  have hpProduct :
      p.Coprime (eta.degree * Nat.card J) :=
    hpDegree.mul_right hJ
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  rw [hn]
  exact hpProduct.pow_left n

/-- A commuting `p`-kernel can be removed from an extension of a
prime-to-`p` character on a `p'`-source.

The returned extension is literally trivial on the kernel, so it is ready
for ordinary quotient descent. -/
theorem exists_extension_trivialOn_of_commuting_p_kernel
    (J Q : Subgroup X)
    (psi : IrreducibleCharacter J)
    (hQ : IsPGroup p Q)
    (hJ : GroupTheory.IsPPrimeGroup p J)
    (hpsi : psi.IsPPrimeDegree p)
    (hcentral :
      Q ≤ Subgroup.centralizer (J : Set X))
    (eta : IrreducibleCharacter X)
    (heta : IsExtensionAlong J.subtype psi eta) :
    ∃ eta0 : IrreducibleCharacter X,
      IsExtensionAlong J.subtype psi eta0 ∧
        eta0.TrivialOn Q := by
  have hcoprime :
      (Nat.card Q).Coprime (eta.degree * Nat.card J) :=
    kernel_card_coprime_extension_degree_mul_source_card
      J Q psi eta heta hQ hJ hpsi
  let lam : X →* ℂˣ :=
    relativeDeterminantNormalizingCharacter J Q eta
  let eta0 : IrreducibleCharacter X :=
    twist lam⁻¹ eta
  have hlamSource :
      ∀ j : J, lam⁻¹ (j : X) = 1 := by
    intro j
    change (lam (j : X))⁻¹ = 1
    rw [
      relativeDeterminantNormalizingCharacter_eq_one_on_source
        J Q eta j]
    exact inv_one
  have heta0Extension :
      IsExtensionAlong J.subtype psi eta0 := by
    exact heta.twist_of_eq_one lam⁻¹ hlamSource
  have heta0Trivial :
      eta0.TrivialOn Q := by
    letI :
        Simple (twistFDRep lam⁻¹ eta.realization) :=
      twistFDRep_simple lam⁻¹ eta.realization
    change
      (ofSimple
        (twistFDRep lam⁻¹ eta.realization)).TrivialOn Q
    apply
      (trivialOn_ofSimple_iff Q
        (twistFDRep lam⁻¹ eta.realization)).2
    intro q
    obtain ⟨c, hc⟩ :=
      exists_realization_scalar_of_centralizes_extension
        psi eta heta (q : X) (hcentral q.2)
    have hc0 : c ≠ 0 :=
      scalar_ne_zero_of_finite_source
        eta Q.subtype q c hc
    let cu : ℂˣ :=
      Units.mk0 c hc0
    have hlam :
        lam (q : X) = cu := by
      exact
        relativeDeterminantNormalizingCharacter_eq_scalarUnit_on_kernel
          J Q eta hcoprime q c hc
    change
      ((lam⁻¹ (q : X) : ℂˣ) : ℂ) •
          eta.realization.ρ (q : X) =
        LinearMap.id
    rw [hc]
    have hlamInv :
        lam⁻¹ (q : X) = cu⁻¹ := by
      change (lam (q : X))⁻¹ = cu⁻¹
      exact congrArg Inv.inv hlam
    rw [hlamInv]
    apply LinearMap.ext
    intro v
    simp only [LinearMap.smul_apply, LinearMap.id_apply,
      smul_smul, cu, Units.val_inv_eq_inv_val,
      Units.val_mk0]
    rw [inv_mul_cancel₀ hc0, one_smul]
  exact ⟨eta0, heta0Extension, heta0Trivial⟩

end RelativeDeterminantNormalization

section QuotientImageExtensionComparison

variable {X : Type u} [Group X] [Finite X]
variable {p : ℕ} [Fact p.Prime]

/-- Extension existence is unchanged after quotienting by a commuting
`p`-kernel and transporting the `p'`-source to its quotient image.

The equivalence `e` is kept explicit so the theorem applies directly to
literal image-subgroup coordinates. -/
theorem exists_extension_quotient_image_iff
    (J Q : Subgroup X) [Q.Normal]
    (psi : IrreducibleCharacter J)
    (e :
      J ≃*
        J.map (QuotientGroup.mk' Q))
    (he :
      ∀ j : J,
        ((e j :
            J.map (QuotientGroup.mk' Q)) :
          X ⧸ Q) =
            QuotientGroup.mk' Q (j : X))
    (hQ : IsPGroup p Q)
    (hJ : GroupTheory.IsPPrimeGroup p J)
    (hpsi : psi.IsPPrimeDegree p)
    (hcentral :
      Q ≤ Subgroup.centralizer (J : Set X)) :
    (∃ etaBar : IrreducibleCharacter (X ⧸ Q),
        IsExtensionAlong
          (J.map (QuotientGroup.mk' Q)).subtype
          (psi.comap e.symm) etaBar) ↔
      ∃ eta : IrreducibleCharacter X,
        IsExtensionAlong J.subtype psi eta := by
  constructor
  · rintro ⟨etaBar, hetaBar⟩
    refine ⟨inflate Q etaBar, ?_⟩
    intro j
    calc
      (inflate Q etaBar).values (j : X) =
          etaBar.values
            (QuotientGroup.mk' Q (j : X)) :=
        inflate_values Q etaBar (j : X)
      _ =
          etaBar.values
            ((e j :
                J.map (QuotientGroup.mk' Q)) :
              X ⧸ Q) := by
        rw [he j]
      _ =
          (psi.comap e.symm).values (e j) :=
        hetaBar (e j)
      _ = psi.values j := by
        rw [comap_values, e.symm_apply_apply]
  · rintro ⟨eta, heta⟩
    obtain ⟨eta0, heta0, heta0Trivial⟩ :=
      exists_extension_trivialOn_of_commuting_p_kernel
        J Q psi hQ hJ hpsi hcentral eta heta
    let etaBar : IrreducibleCharacter (X ⧸ Q) :=
      descend Q ⟨eta0, heta0Trivial⟩
    refine ⟨etaBar, ?_⟩
    intro z
    let j : J := e.symm z
    have hz :
        (z : X ⧸ Q) =
          QuotientGroup.mk' Q (j : X) := by
      calc
        (z : X ⧸ Q) =
            ((e j :
                J.map (QuotientGroup.mk' Q)) :
              X ⧸ Q) := by
          exact congrArg Subtype.val
            (e.apply_symm_apply z).symm
        _ = QuotientGroup.mk' Q (j : X) :=
          he j
    calc
      etaBar.values
          ((z :
              J.map (QuotientGroup.mk' Q)) :
            X ⧸ Q) =
          etaBar.values
            (QuotientGroup.mk' Q (j : X)) := by
        rw [hz]
      _ = eta0.values (j : X) := by
        exact
          descend_values_mk Q
            ⟨eta0, heta0Trivial⟩ (j : X)
      _ = psi.values j :=
        heta0 j
      _ = (psi.comap e.symm).values z := by
        rfl

end QuotientImageExtensionComparison

end IrreducibleCharacter

open CharacterTriple
open GroupTheory

section OkuyamaWajimaProperBranchSourceComparison

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (K : Subgroup G) [K.Normal]
variable (P : Sylow p G)
variable (Q : Subgroup P) [Q.Normal]

local instance properBranchQuotientSourceComparisonAction :
    MulDistribMulAction P K :=
  subgroupConjugationMulDistribMulAction K (P : Subgroup G)

variable
  (theta :
    PInvariantPPrimeIrreducibleCharacter
      K (P : Subgroup G) p)
  (hinvariant :
    ∀ g : G, g • theta.1.1 = theta.1.1)
  (gQ :
    GlaubermanCorrespondence K
      (okuyamaWajimaProperBranchQ P Q) p)

/-- The literal quotient kernel, viewed inside `N_G(Q)`, is a
`p`-group. -/
theorem okuyamaWajimaProperBranchQuotientKernel_isPGroup :
    IsPGroup p
      (okuyamaWajimaProperBranchQuotientKernel P Q) := by
  exact
    (okuyamaWajimaProperBranchAmbientQ_isPGroup P Q).of_equiv
      (Subgroup.subgroupOfEquivOfLe
        (show
          okuyamaWajimaProperBranchQ P Q ≤
            okuyamaWajimaProperBranchQuotientAmbient P Q
          from Subgroup.le_normalizer)).symm

/-- Inside `N_G(Q)`, the quotient kernel `Q` centralizes the intermediate
source kernel `C_K(Q)`. -/
theorem okuyamaWajimaProperBranchQuotientKernel_le_centralizer_sourceKernel :
    okuyamaWajimaProperBranchQuotientKernel P Q ≤
      Subgroup.centralizer
        (okuyamaWajimaProperBranchQuotientSourceKernel
          K P Q theta hinvariant gQ :
          Set
            (okuyamaWajimaProperBranchQuotientAmbient P Q)) := by
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  apply Subtype.ext
  have hjCentral :
      ((j :
          okuyamaWajimaProperBranchQuotientAmbient P Q) : G) ∈
        Subgroup.centralizer
          (okuyamaWajimaProperBranchQ P Q : Set G) :=
    hj.2
  have hcomm :
      (((q :
          okuyamaWajimaProperBranchQuotientAmbient P Q) : G) *
        ((j :
          okuyamaWajimaProperBranchQuotientAmbient P Q) : G)) =
      (((j :
          okuyamaWajimaProperBranchQuotientAmbient P Q) : G) *
        ((q :
          okuyamaWajimaProperBranchQuotientAmbient P Q) : G)) :=
    (Subgroup.mem_centralizer_iff.mp hjCentral)
      ((q :
        okuyamaWajimaProperBranchQuotientAmbient P Q) : G)
      hq
  exact hcomm.symm

/-- The source field of the proper-branch quotient coordinate comparison.

Thus the transported source character on `N_G(Q) / Q` extends precisely
when the original intermediate character extends to `N_G(Q)`. -/
theorem
    okuyamaWajimaProperBranchQuotientSourceExtensionCoordinateComparison
    (hK : IsPPrimeGroup p K) :
    OkuyamaWajimaProperBranchThetaExtendsToG
        (okuyamaWajimaProperBranchQuotientImageKernel
          K P Q theta hinvariant gQ)
        (okuyamaWajimaProperBranchQuotientSylow P Q)
        (okuyamaWajimaProperBranchQuotientInvariantSourceCharacter
          K P Q theta hinvariant gQ hK)
        (okuyamaWajimaProperBranchQuotientSourceCharacter_invariant
          K P Q theta hinvariant gQ hK) ↔
      OkuyamaWajimaProperBranchPsiExtendsToQNormalizer
        K P Q theta hinvariant gQ := by
  let X :=
    okuyamaWajimaProperBranchQuotientAmbient P Q
  let J :=
    okuyamaWajimaProperBranchQuotientSourceKernel
      K P Q theta hinvariant gQ
  let QX :=
    okuyamaWajimaProperBranchQuotientKernel P Q
  let psi :
      IrreducibleCharacter J :=
    (okuyamaWajimaProperBranchPsiNormalizerTriple
      K P Q theta hinvariant gQ).character
  let e :
      J ≃*
        J.map (QuotientGroup.mk' QX) :=
    okuyamaWajimaProperBranchQuotientSourceKernelEquiv
      K P Q theta hinvariant gQ hK
  have he :
      ∀ j : J,
        ((e j : J.map (QuotientGroup.mk' QX)) :
          X ⧸ QX) =
            QuotientGroup.mk' QX (j : X) := by
    intro j
    exact
      okuyamaWajimaProperBranchQuotientSourceKernelEquiv_apply_coe
        K P Q theta hinvariant gQ hK j
  have hcomparison :=
    IrreducibleCharacter.exists_extension_quotient_image_iff
      J QX psi e he
      (okuyamaWajimaProperBranchQuotientKernel_isPGroup P Q)
      (okuyamaWajimaProperBranchPsiTriple_kernel_isPPrime
        K P Q theta hinvariant gQ hK)
      (okuyamaWajimaProperBranchPsiTriple_character_isPPrimeDegree
        K P Q theta hinvariant gQ)
      (okuyamaWajimaProperBranchQuotientKernel_le_centralizer_sourceKernel
        K P Q theta hinvariant gQ)
  exact hcomparison

end OkuyamaWajimaProperBranchSourceComparison

end McKayConjecture
