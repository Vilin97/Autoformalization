/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.DeterminantEquivalenceTransport
import McKayConjecture.Character.DeterminantRootTwist
import McKayConjecture.Character.OkuyamaWajimaBaseCount
import McKayConjecture.CharacterTriple.NormalHallPPrimeExtension
import McKayConjecture.GroupTheory.NormalComplementQuotient
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Canonical base extensions for Okuyama--Wajima

An invariant character of a normal Hall `p′`-subgroup has many extensions
across a `p`-group quotient.  There is nevertheless a canonical one: among
the extensions, choose the unique character whose determinant is trivial on
every Sylow `p`-subgroup.

This file develops the determinant normalization independently of the
Okuyama--Wajima coordinates.  The construction starts from any extension,
uses the determinant root on a complementary Sylow subgroup, and twists by
its inverse inflated through the semidirect-product projection.
-/

noncomputable section

namespace McKayConjecture

open CharacterTriple
open GroupTheory
open scoped Pointwise

namespace IrreducibleCharacter

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- The projection onto the second factor of a normal-complement
decomposition. -/
def normalComplementProjection
    (N P : Subgroup G) [N.Normal]
    (hcomplement : N.IsComplement' P) :
    G →* P :=
  SemidirectProduct.rightHom.comp
    (SemidirectProduct.mulEquivSubgroup hcomplement).symm.toMonoidHom

@[simp]
theorem normalComplementProjection_apply_kernel
    (N P : Subgroup G) [N.Normal]
    (hcomplement : N.IsComplement' P)
    (x : N) :
    normalComplementProjection N P hcomplement (x : G) = 1 := by
  let e := SemidirectProduct.mulEquivSubgroup hcomplement
  have hx :
      e.symm (x : G) = SemidirectProduct.inl x := by
    apply e.injective
    rw [e.apply_symm_apply]
    simp [e, SemidirectProduct.mulEquivSubgroup_apply]
  change SemidirectProduct.rightHom (e.symm (x : G)) = 1
  rw [hx]
  exact SemidirectProduct.rightHom_inl x

@[simp]
theorem normalComplementProjection_apply_factor
    (N P : Subgroup G) [N.Normal]
    (hcomplement : N.IsComplement' P)
    (x : P) :
    normalComplementProjection N P hcomplement (x : G) = x := by
  let e := SemidirectProduct.mulEquivSubgroup hcomplement
  have hx :
      e.symm (x : G) = SemidirectProduct.inr x := by
    apply e.injective
    rw [e.apply_symm_apply]
    simp [e, SemidirectProduct.mulEquivSubgroup_apply]
  change SemidirectProduct.rightHom (e.symm (x : G)) = x
  rw [hx]
  exact SemidirectProduct.rightHom_inr x

/-- A character is determinant-normalized at `p` if its determinant is
trivial on every Sylow `p`-subgroup.  Quantifying over all Sylow subgroups
makes this property invariant under arbitrary automorphisms. -/
def IsDeterminantNormalizedAtPrime
    (χ : IrreducibleCharacter G) : Prop :=
  ∀ (P : Sylow p G) (x : P),
    determinantParameter χ (x : G) = 1

/-- The determinant root on a complementary Sylow subgroup. -/
def normalHallDeterminantRoot
    (P : Sylow p G)
    (χ : IrreducibleCharacter G)
    (hdegree : (Nat.card P).Coprime χ.degree) :
    P →* ℂˣ :=
  determinantRootParameter χ (P : Subgroup G).subtype hdegree

/-- The inverse determinant root, inflated through a normal-complement
projection. -/
def normalHallDeterminantNormalizingCharacter
    (N : Subgroup G) [N.Normal]
    (P : Sylow p G)
    (hcomplement : N.IsComplement' (P : Subgroup G))
    (χ : IrreducibleCharacter G)
    (hdegree : (Nat.card P).Coprime χ.degree) :
    G →* ℂˣ :=
  (normalHallDeterminantRoot P χ hdegree)⁻¹.comp
    (normalComplementProjection
      N (P : Subgroup G) hcomplement)

/-- Twist an extension so that its determinant is trivial on the chosen
complementary Sylow subgroup. -/
def normalHallDeterminantNormalizedCharacter
    (N : Subgroup G) [N.Normal]
    (P : Sylow p G)
    (hcomplement : N.IsComplement' (P : Subgroup G))
    (χ : IrreducibleCharacter G)
    (hdegree : (Nat.card P).Coprime χ.degree) :
    IrreducibleCharacter G :=
  twist
    (normalHallDeterminantNormalizingCharacter
      N P hcomplement χ hdegree)
    χ

theorem normalHallDeterminantRoot_pow_degree
    (P : Sylow p G)
    (χ : IrreducibleCharacter G)
    (hdegree : (Nat.card P).Coprime χ.degree)
    (x : P) :
    normalHallDeterminantRoot P χ hdegree x ^ χ.degree =
      determinantParameter χ (x : G) := by
  let z := determinantParameter χ (x : G)
  have hzOrder : z ^ Nat.card P = 1 := by
    calc
      z ^ Nat.card P =
          determinantParameter χ
            ((x : G) ^ Nat.card P) :=
        (map_pow (determinantParameter χ)
          (x : G) (Nat.card P)).symm
      _ =
          determinantParameter χ
            (((x ^ Nat.card P : P) : G)) := rfl
      _ = 1 := by
        have hxpow : x ^ Nat.card P = 1 :=
          pow_card_eq_one'
        rw [hxpow]
        simp
  have hroot :=
    eq_pow_gcdB_of_pow_eq_one
      z (Nat.card P) χ.degree hdegree hzOrder
  change
    (z ^ (Nat.card P).gcdB χ.degree) ^ χ.degree = z
  calc
    (z ^ (Nat.card P).gcdB χ.degree) ^ χ.degree =
        (z ^ χ.degree) ^ (Nat.card P).gcdB χ.degree := by
      simp only [← zpow_natCast, ← zpow_mul]
      rw [mul_comm]
    _ = z := hroot.symm

@[simp]
theorem normalHallDeterminantNormalizingCharacter_apply_kernel
    (N : Subgroup G) [N.Normal]
    (P : Sylow p G)
    (hcomplement : N.IsComplement' (P : Subgroup G))
    (χ : IrreducibleCharacter G)
    (hdegree : (Nat.card P).Coprime χ.degree)
    (x : N) :
    normalHallDeterminantNormalizingCharacter
        N P hcomplement χ hdegree (x : G) =
      1 := by
  simp [normalHallDeterminantNormalizingCharacter]

theorem normalHallDeterminantNormalizedCharacter_isExtension
    (N : Subgroup G) [N.Normal]
    (P : Sylow p G)
    (hcomplement : N.IsComplement' (P : Subgroup G))
    {θ : IrreducibleCharacter N}
    {χ : IrreducibleCharacter G}
    (hχ : IsExtensionAlong N.subtype θ χ)
    (hdegree : (Nat.card P).Coprime χ.degree) :
    IsExtensionAlong N.subtype θ
      (normalHallDeterminantNormalizedCharacter
        N P hcomplement χ hdegree) := by
  intro x
  rw [normalHallDeterminantNormalizedCharacter, twist_values]
  have hnormalizer :=
    normalHallDeterminantNormalizingCharacter_apply_kernel
      N P hcomplement χ hdegree x
  change
    ((normalHallDeterminantNormalizingCharacter
        N P hcomplement χ hdegree (x : G) : ℂˣ) : ℂ) *
        χ.values (x : G) =
      θ.values x
  rw [hnormalizer, Units.val_one, one_mul]
  exact hχ x

theorem normalHallDeterminantNormalizedCharacter_at_factor
    (N : Subgroup G) [N.Normal]
    (P : Sylow p G)
    (hcomplement : N.IsComplement' (P : Subgroup G))
    (χ : IrreducibleCharacter G)
    (hdegree : (Nat.card P).Coprime χ.degree)
    (x : P) :
    determinantParameter
        (normalHallDeterminantNormalizedCharacter
          N P hcomplement χ hdegree)
        (x : G) =
      1 := by
  rw [normalHallDeterminantNormalizedCharacter,
    determinantParameter_twist]
  simp only [MonoidHom.mul_apply, MonoidHom.pow_apply]
  have hnormalizer :
      normalHallDeterminantNormalizingCharacter
          N P hcomplement χ hdegree (x : G) =
        (normalHallDeterminantRoot P χ hdegree x)⁻¹ := by
    simp [normalHallDeterminantNormalizingCharacter]
  rw [hnormalizer]
  change
    ((normalHallDeterminantRoot P χ hdegree x)⁻¹) ^
          χ.degree *
        determinantParameter χ (x : G) =
      1
  rw [inv_pow,
    normalHallDeterminantRoot_pow_degree P χ hdegree x,
    inv_mul_cancel]

/-- A homomorphism trivial on one Sylow subgroup is trivial on all Sylow
subgroups. -/
theorem monoidHom_eq_one_on_all_sylow_of_eq_one_on
    (P : Sylow p G)
    (f : G →* ℂˣ)
    (hf : ∀ x : P, f (x : G) = 1) :
    ∀ (Q : Sylow p G) (x : Q), f (x : G) = 1 := by
  intro Q x
  obtain ⟨g, hg⟩ :=
    MulAction.exists_smul_eq G P Q
  have hxSylow :
      (x : G) ∈ (g • P : Sylow p G) := by
    rw [hg]
    exact x.property
  have hx :
      (x : G) ∈
        (MulAut.conj g) • (P : Subgroup G) := by
    rw [← Sylow.coe_subgroup_smul]
    exact hxSylow
  obtain ⟨y, hyP, hyx⟩ :=
    (Subgroup.mem_smul_pointwise_iff_exists
      (x : G) (MulAut.conj g) (P : Subgroup G)).mp hx
  let yP : P := ⟨y, hyP⟩
  have hfy : f y = 1 := hf yP
  rw [← hyx]
  change f (g * y * g⁻¹) = 1
  simpa using hfy

theorem normalHallDeterminantNormalizedCharacter_isNormalized
    (N : Subgroup G) [N.Normal]
    (P : Sylow p G)
    (hcomplement : N.IsComplement' (P : Subgroup G))
    (χ : IrreducibleCharacter G)
    (hdegree : (Nat.card P).Coprime χ.degree) :
    IsDeterminantNormalizedAtPrime
      (p := p)
      (normalHallDeterminantNormalizedCharacter
        N P hcomplement χ hdegree) := by
  apply
    monoidHom_eq_one_on_all_sylow_of_eq_one_on P
  exact
    normalHallDeterminantNormalizedCharacter_at_factor
      N P hcomplement χ hdegree

/-- Determinant normalization is preserved by every automorphism. -/
theorem IsDeterminantNormalizedAtPrime.comap_mulAut
    {χ : IrreducibleCharacter G}
    (hχ : IsDeterminantNormalizedAtPrime (p := p) χ)
    (e : MulAut G) :
    IsDeterminantNormalizedAtPrime
      (p := p) (χ.comap e) := by
  intro P x
  let Q : Sylow p G := e • P
  let y : Q :=
    ⟨e (x : G), by
      change
        e (x : G) ∈
          e • (P : Subgroup G)
      simpa using
        (Subgroup.smul_mem_pointwise_smul
          (x : G) e (P : Subgroup G) x.property)⟩
  have hy := hχ Q y
  have hdet :=
    DFunLike.congr_fun
      (determinantParameter_comap e χ) (x : G)
  exact hdet.trans hy

/-- Two extensions of the same character that are determinant-normalized
at `p` are equal as soon as the normal subgroup and a Sylow subgroup
generate the ambient group. -/
theorem eq_of_isExtension_of_isDeterminantNormalizedAtPrime
    (N : Subgroup G) [N.Normal]
    (P : Sylow p G)
    (hgenerate : N ⊔ (P : Subgroup G) = ⊤)
    {θ : IrreducibleCharacter N}
    {χ₁ χ₂ : IrreducibleCharacter G}
    (hχ₁ : IsExtensionAlong N.subtype θ χ₁)
    (hχ₂ : IsExtensionAlong N.subtype θ χ₂)
    (hnormal₁ :
      IsDeterminantNormalizedAtPrime (p := p) χ₁)
    (hnormal₂ :
      IsDeterminantNormalizedAtPrime (p := p) χ₂)
    (hdegree : (Nat.card P).Coprime θ.degree) :
    χ₁ = χ₂ := by
  obtain ⟨lam, hlamN, htwist⟩ :=
    hχ₁.exists_eq_twist hχ₂
  have hdegree₁ :
      (Nat.card P).Coprime χ₁.degree := by
    simpa only [hχ₁.degree_eq] using hdegree
  have hlamP :
      ∀ x : P, lam (x : G) = 1 := by
    intro x
    have hdet₂ := hnormal₂ P x
    rw [htwist, determinantParameter_twist] at hdet₂
    simp only [MonoidHom.mul_apply,
      MonoidHom.pow_apply] at hdet₂
    rw [hnormal₁ P x, mul_one] at hdet₂
    have hlamOrder :
        lam (x : G) ^ Nat.card P = 1 := by
      calc
        lam (x : G) ^ Nat.card P =
            lam ((x : G) ^ Nat.card P) :=
          (map_pow lam (x : G) (Nat.card P)).symm
        _ =
            lam (((x ^ Nat.card P : P) : G)) := rfl
        _ = 1 := by
          have hxpow : x ^ Nat.card P = 1 :=
            pow_card_eq_one'
          rw [hxpow]
          simp
    have hrecover :=
      eq_pow_gcdB_of_pow_eq_one
        (lam (x : G)) (Nat.card P) χ₁.degree
        hdegree₁ hlamOrder
    rw [hdet₂, one_zpow] at hrecover
    exact hrecover
  have hker :
      (⊤ : Subgroup G) ≤ lam.ker := by
    rw [← hgenerate]
    apply sup_le
    · intro x hx
      exact
        (MonoidHom.mem_ker).2
          (hlamN ⟨x, hx⟩)
    · intro x hx
      exact
        (MonoidHom.mem_ker).2
          (hlamP ⟨x, hx⟩)
  have hlam : lam = 1 := by
    apply MonoidHom.ext
    intro x
    exact
      (MonoidHom.mem_ker).1
        (hker (Subgroup.mem_top x))
  rw [htwist, hlam, twist_one]

/-- Existence and uniqueness of the determinant-normalized extension
across a normal Hall `p′`-subgroup. -/
theorem existsUnique_determinantNormalizedExtension_of_normalHall
    (N : Subgroup G) [N.Normal]
    (P : Sylow p G)
    (hN : IsPPrimeGroup p N)
    (hgenerate : N ⊔ (P : Subgroup G) = ⊤)
    (θ : IrreducibleCharacter N)
    (hinertia : inertia N θ = ⊤)
    (hdegree : θ.IsPPrimeDegree p) :
    ∃! χ : IrreducibleCharacter G,
      IsExtensionAlong N.subtype θ χ ∧
        IsDeterminantNormalizedAtPrime (p := p) χ := by
  have hcard :
      (Nat.card P).Coprime (Nat.card N) := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    rw [hn]
    exact hN.pow_left n
  have hdisjoint :
      Disjoint (P : Subgroup G) N :=
    Subgroup.disjoint_of_coprime_natCard hcard
  let hcomplement :
      N.IsComplement' (P : Subgroup G) :=
    (isComplement'_of_normal_disjoint_sup_eq_top
      N (P : Subgroup G) hdisjoint hgenerate).symm
  have hquotient : IsPGroup p (G ⧸ N) :=
    quotient_isPGroup_of_sup_eq_top
      N (P : Subgroup G) P.isPGroup' hgenerate
  obtain ⟨χ, hχ⟩ :=
    CharacterTriple.exists_pPrime_extension_of_normalHall_inertiaTop
      N θ hinertia hN hquotient hdegree
  have hχdegree :
      (Nat.card P).Coprime χ.1.degree := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    have hpdegree :
        p.Coprime χ.1.degree :=
      (Fact.out : p.Prime).coprime_iff_not_dvd.mpr χ.2
    rw [hn]
    exact hpdegree.pow_left n
  let χ₀ :=
    normalHallDeterminantNormalizedCharacter
      N P hcomplement χ.1 hχdegree
  have hχ₀Extension :
      IsExtensionAlong N.subtype θ χ₀ :=
    normalHallDeterminantNormalizedCharacter_isExtension
      N P hcomplement hχ hχdegree
  have hχ₀Normalized :
      IsDeterminantNormalizedAtPrime (p := p) χ₀ :=
    normalHallDeterminantNormalizedCharacter_isNormalized
      N P hcomplement χ.1 hχdegree
  refine
    ⟨χ₀, ⟨hχ₀Extension, hχ₀Normalized⟩, ?_⟩
  intro ψ hψ
  exact
    eq_of_isExtension_of_isDeterminantNormalizedAtPrime
      N P hgenerate
      hψ.1 hχ₀Extension hψ.2 hχ₀Normalized
      (by
        obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
        have hpdegree :
            p.Coprime θ.degree :=
          (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
            hdegree
        rw [hn]
        exact hpdegree.pow_left n)

end IrreducibleCharacter

namespace IrreducibleCharacter

variable {A : Type} [Group A] [Finite A]
variable {p : ℕ} [Fact p.Prime]

/-- Transporting an ambient-invariant character to its internal copy in an
intermediate subgroup gives full inertia there. -/
theorem inertia_internalCopy_eq_top_of_ambient_invariant
    (L N : Subgroup A) [N.Normal]
    (hNL : N ≤ L)
    (θ : IrreducibleCharacter N)
    (hinvariant : ∀ g : A, g • θ = θ) :
    inertia (N.subgroupOf L)
        (θ.comap (Subgroup.subgroupOfEquivOfLe hNL)) =
      ⊤ := by
  apply top_unique
  intro g _hg
  rw [mem_inertia_iff]
  apply IrreducibleCharacter.ext
  funext n
  have hvalue :=
    congrArg
      (fun η : IrreducibleCharacter N ↦
        η.values
          (Subgroup.subgroupOfEquivOfLe hNL n))
      (hinvariant (g : A))
  change
    θ.values
        ((MulAut.conjNormal (H := N) (g : A)).symm
          (Subgroup.subgroupOfEquivOfLe hNL n)) =
      θ.values
        (Subgroup.subgroupOfEquivOfLe hNL n) at hvalue
  exact hvalue

/-- The unique determinant-normalized Hall extension is invariant under
every ambient conjugation that preserves the normal product and the kernel
character. -/
theorem determinantNormalizedExtension_invariant
    (L N : Subgroup A) [L.Normal] [N.Normal]
    (hNL : N ≤ L)
    (P : Sylow p L)
    (hgenerate :
      N.subgroupOf L ⊔ (P : Subgroup L) = ⊤)
    (θ : IrreducibleCharacter N)
    (χ : IrreducibleCharacter L)
    (hχ :
      IsExtensionAlong (Subgroup.inclusion hNL) θ χ)
    (hnormal :
      IsDeterminantNormalizedAtPrime (p := p) χ)
    (hinvariant : ∀ g : A, g • θ = θ)
    (hdegree : (Nat.card P).Coprime θ.degree) :
    ∀ (g : A) (x : L),
      χ.values (conjugateNormalElement L inferInstance g x) =
        χ.values x := by
  let N' := N.subgroupOf L
  let eN : N' ≃* N :=
    Subgroup.subgroupOfEquivOfLe hNL
  let θ' : IrreducibleCharacter N' :=
    θ.comap eN
  have hχ' :
      IsExtensionAlong N'.subtype θ' χ := by
    intro x
    exact hχ (eN x)
  intro g x
  let eL : MulAut L :=
    MulAut.conjNormal (H := L) g
  let χg : IrreducibleCharacter L :=
    χ.comap eL
  have hχg' :
      IsExtensionAlong N'.subtype θ' χg := by
    intro n
    let nN : N := eN n
    let ngN : N :=
      MulAut.conjNormal (H := N) g nN
    have hextension :
        χ.values (Subgroup.inclusion hNL ngN) =
          θ.values ngN :=
      hχ ngN
    have hinvariantValue :=
      congrArg
        (fun η : IrreducibleCharacter N ↦ η.values nN)
        (hinvariant g⁻¹)
    have hconjugate :
        (MulAut.conjNormal (H := N) g⁻¹).symm nN =
          ngN := by
      apply Subtype.ext
      simp [ngN, nN]
    change
      θ.values
          ((MulAut.conjNormal (H := N) g⁻¹).symm nN) =
        θ.values nN at hinvariantValue
    rw [hconjugate] at hinvariantValue
    change
      χ.values (eL (N'.subtype n)) =
        θ.values nN
    calc
      χ.values (eL (N'.subtype n)) =
          χ.values (Subgroup.inclusion hNL ngN) := by
        congr 1
      _ = θ.values ngN := hextension
      _ = θ.values nN := hinvariantValue
  have hnormalg :
      IsDeterminantNormalizedAtPrime (p := p) χg :=
    hnormal.comap_mulAut eL
  have hdegree' :
      (Nat.card P).Coprime θ'.degree := by
    simpa only [θ', comap_degree] using hdegree
  have heq : χ = χg :=
    eq_of_isExtension_of_isDeterminantNormalizedAtPrime
      N' P hgenerate hχ' hχg'
      hnormal hnormalg hdegree'
  have hvalue :=
    congrArg
      (fun η : IrreducibleCharacter L ↦ η.values x)
      heq
  exact hvalue.symm

end IrreducibleCharacter

namespace CharacterTriple

variable {A : Type} [Group A] [Finite A]

/-- The value-form invariance stored by a character triple is the usual
fixed-point statement for the ambient conjugation action. -/
theorem character_smul_eq
    (T : CharacterTriple A) (g : A) :
    g • T.character = T.character := by
  apply IrreducibleCharacter.ext
  funext x
  have hvalue :=
    T.invariant_conjNormal g⁻¹ x
  change
    T.character.values
        ((MulAut.conjNormal (H := T.normalSubgroup) g).symm x) =
      T.character.values x
  simpa using hvalue

end CharacterTriple

/-! ### The source and target Okuyama--Wajima extensions -/

variable {Γ : Type} [Group Γ] [Finite Γ]
variable {p : ℕ} [Fact p.Prime]

/-- Ambient invariance of the kernel character supplies the complete
canonical base-extension package used by the Okuyama--Wajima base count.

Both extensions are the unique determinant-normalized normal-Hall
extensions. -/
theorem okuyamaWajimaCanonicalBaseExtensionHypothesis_of_invariant
    (S : Sylow p Γ)
    (K : Subgroup Γ) [K.Normal]
    (hK : IsPPrimeGroup p K)
    (hKS : (K ⊔ (S : Subgroup Γ)).Normal)
    (d : GlaubermanCorrespondence K (S : Subgroup Γ) p)
    (θ :
      PInvariantPPrimeIrreducibleCharacter
        K (S : Subgroup Γ) p)
    (hinvariant : ∀ g : Γ, g • θ.1.1 = θ.1.1) :
    OkuyamaWajimaCanonicalBaseExtensionHypothesis
      S K hKS d θ := by
  let Ls : Subgroup Γ := K ⊔ (S : Subgroup Γ)
  let Ns : Subgroup Ls := K.subgroupOf Ls
  let Ps : Sylow p Ls :=
    S.subtype (show (S : Subgroup Γ) ≤ Ls from le_sup_right)
  let eNs : Ns ≃* K :=
    Subgroup.subgroupOfEquivOfLe
      (show K ≤ Ls from le_sup_left)
  let θs : IrreducibleCharacter Ns :=
    θ.1.1.comap eNs
  letI : Ls.Normal := hKS
  have hNsPPrime : IsPPrimeGroup p Ns :=
    hK.of_equiv eNs.symm
  have hsourceGenerate :
      Ns ⊔ (Ps : Subgroup Ls) = ⊤ := by
    change
      K.subgroupOf Ls ⊔
          (S : Subgroup Γ).subgroupOf Ls =
        ⊤
    rw [← Subgroup.subgroupOf_sup
      (show K ≤ Ls from le_sup_left)
      (show (S : Subgroup Γ) ≤ Ls from le_sup_right)]
    exact Subgroup.subgroupOf_self Ls
  have hθsInertia :
      IrreducibleCharacter.inertia Ns θs = ⊤ :=
    IrreducibleCharacter.inertia_internalCopy_eq_top_of_ambient_invariant
      Ls K (show K ≤ Ls from le_sup_left)
      θ.1.1 hinvariant
  have hθsDegree : θs.IsPPrimeDegree p := by
    exact θ.1.2
  obtain ⟨sourceExtension,
      hsourceExtensionInternal,
      hsourceNormalized⟩ :=
    (IrreducibleCharacter.existsUnique_determinantNormalizedExtension_of_normalHall
      Ns Ps hNsPPrime hsourceGenerate θs
      hθsInertia hθsDegree).exists
  have hsourceExtension :
      IrreducibleCharacter.IsExtensionAlong
        (Subgroup.inclusion
          (show K ≤ Ls from le_sup_left))
        θ.1.1 sourceExtension := by
    intro x
    let xNs : Ns :=
      ⟨Subgroup.inclusion
          (show K ≤ Ls from le_sup_left) x,
        x.property⟩
    have hx := hsourceExtensionInternal xNs
    change
      sourceExtension.values
          (Subgroup.inclusion
            (show K ≤ Ls from le_sup_left) x) =
        θ.1.1.values x
    exact hx
  have hsourceDegree :
      (Nat.card Ps).Coprime θ.1.1.degree := by
    obtain ⟨n, hn⟩ := Ps.isPGroup'.exists_card_eq
    have hpdegree :
        p.Coprime θ.1.1.degree :=
      (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
        θ.1.2
    rw [hn]
    exact hpdegree.pow_left n
  have hsourceInvariant :
      ∀ (g : Γ) (x : Ls),
        sourceExtension.values
            (conjugateNormalElement Ls hKS g x) =
          sourceExtension.values x :=
    IrreducibleCharacter.determinantNormalizedExtension_invariant
      Ls K (show K ≤ Ls from le_sup_left)
      Ps hsourceGenerate θ.1.1 sourceExtension
      hsourceExtension hsourceNormalized hinvariant
      hsourceDegree
  let H : Subgroup Γ :=
    Subgroup.normalizer ((S : Subgroup Γ) : Set Γ)
  let Lt : Subgroup H :=
    okuyamaWajimaInternalNormalProduct
      K (S : Subgroup Γ)
  let Nt : Subgroup H :=
    okuyamaWajimaInternalFixedPoints
      K (S : Subgroup Γ)
  let PtH : Sylow p H :=
    okuyamaWajimaSylowInNormalizer S
  have hPtHLe : (PtH : Subgroup H) ≤ Lt := by
    change
      okuyamaWajimaInternalSylow (S : Subgroup Γ) ≤
        okuyamaWajimaInternalNormalProduct
          K (S : Subgroup Γ)
    rw [internalNormalProduct_eq_fixedPoints_sup_sylow
      S K hK]
    exact le_sup_right
  let Pt : Sylow p Lt :=
    PtH.subtype hPtHLe
  let eNt : Nt.subgroupOf Lt ≃* Nt :=
    Subgroup.subgroupOfEquivOfLe
      (internalFixedPoints_le_internalNormalProduct
        K (S : Subgroup Γ))
  let θt : IrreducibleCharacter Nt :=
    okuyamaWajimaInternalFixedPointCharacter
      S K d θ
  let θtL : IrreducibleCharacter (Nt.subgroupOf Lt) :=
    θt.comap eNt
  letI : Nt.Normal :=
    internalFixedPoints_normal K (S : Subgroup Γ)
  letI : Lt.Normal :=
    internalNormalProduct_normal
      K (S : Subgroup Γ) hKS
  have hfixedPointsPPrime :
      IsPPrimeGroup p
        (coprimeFixedPoints K (S : Subgroup Γ)) := by
    let D :=
      coprimeFixedPoints K (S : Subgroup Γ)
    let DK : Subgroup K :=
      D.subgroupOf K
    have hDK : IsPPrimeGroup p DK :=
      hK.to_subgroup DK
    exact
      hDK.of_equiv
        (Subgroup.subgroupOfEquivOfLe
          (show D ≤ K from inf_le_left))
  have hNtPPrime : IsPPrimeGroup p Nt := by
    exact
      hfixedPointsPPrime.of_equiv
        (Subgroup.subgroupOfEquivOfLe
          (show
            coprimeFixedPoints K (S : Subgroup Γ) ≤ H from
            inf_le_right.trans
              (Subgroup.centralizer_le_normalizer
                ((S : Subgroup Γ) : Set Γ)))).symm
  have hNtLPPrime :
      IsPPrimeGroup p (Nt.subgroupOf Lt) :=
    hNtPPrime.of_equiv eNt.symm
  have htargetGenerate :
      Nt.subgroupOf Lt ⊔ (Pt : Subgroup Lt) = ⊤ := by
    change
      Nt.subgroupOf Lt ⊔
          (okuyamaWajimaInternalSylow
            (S : Subgroup Γ)).subgroupOf Lt =
        ⊤
    rw [← Subgroup.subgroupOf_sup
      (internalFixedPoints_le_internalNormalProduct
        K (S : Subgroup Γ))
      (show
        okuyamaWajimaInternalSylow (S : Subgroup Γ) ≤ Lt by
        change
          okuyamaWajimaInternalSylow
              (S : Subgroup Γ) ≤
            okuyamaWajimaInternalNormalProduct
              K (S : Subgroup Γ)
        rw [internalNormalProduct_eq_fixedPoints_sup_sylow
          S K hK]
        exact le_sup_right)]
    rw [← internalNormalProduct_eq_fixedPoints_sup_sylow
      S K hK]
    exact Subgroup.subgroupOf_self Lt
  let Tt : CharacterTriple H :=
    invariantOkuyamaWajimaTargetTriple
      K (S : Subgroup Γ) H le_rfl
      (show
        coprimeFixedPoints K (S : Subgroup Γ) ≤ H from
        inf_le_right.trans
          (Subgroup.centralizer_le_normalizer
            ((S : Subgroup Γ) : Set Γ)))
      d θ hinvariant
  have hθtInvariant :
      ∀ g : H, g • θt = θt := by
    intro g
    exact CharacterTriple.character_smul_eq Tt g
  have hθtLInertia :
      IrreducibleCharacter.inertia
          (Nt.subgroupOf Lt) θtL =
        ⊤ :=
    IrreducibleCharacter.inertia_internalCopy_eq_top_of_ambient_invariant
      Lt Nt
      (internalFixedPoints_le_internalNormalProduct
        K (S : Subgroup Γ))
      θt hθtInvariant
  have hθtDegree : θt.IsPPrimeDegree p := by
    exact (d.characterEquiv θ).2
  have hθtLDegree : θtL.IsPPrimeDegree p := by
    exact hθtDegree
  obtain ⟨targetExtension,
      htargetExtensionInternal,
      htargetNormalized⟩ :=
    (IrreducibleCharacter.existsUnique_determinantNormalizedExtension_of_normalHall
      (Nt.subgroupOf Lt) Pt hNtLPPrime
      htargetGenerate θtL hθtLInertia
      hθtLDegree).exists
  have htargetExtension :
      IrreducibleCharacter.IsExtensionAlong
        (Subgroup.inclusion
          (internalFixedPoints_le_internalNormalProduct
            K (S : Subgroup Γ)))
        θt targetExtension := by
    intro x
    let xNtL : Nt.subgroupOf Lt :=
      ⟨Subgroup.inclusion
          (internalFixedPoints_le_internalNormalProduct
            K (S : Subgroup Γ)) x,
        x.property⟩
    have hx := htargetExtensionInternal xNtL
    change
      targetExtension.values
          (Subgroup.inclusion
            (internalFixedPoints_le_internalNormalProduct
              K (S : Subgroup Γ)) x) =
        θt.values x
    exact hx
  have htargetDegree :
      (Nat.card Pt).Coprime θt.degree := by
    obtain ⟨n, hn⟩ := Pt.isPGroup'.exists_card_eq
    have hpdegree :
        p.Coprime θt.degree :=
      (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
        hθtDegree
    rw [hn]
    exact hpdegree.pow_left n
  have htargetInvariant :
      ∀ (g : H) (x : Lt),
        targetExtension.values
            (conjugateNormalElement Lt inferInstance g x) =
          targetExtension.values x :=
    IrreducibleCharacter.determinantNormalizedExtension_invariant
      Lt Nt
      (internalFixedPoints_le_internalNormalProduct
        K (S : Subgroup Γ))
      Pt htargetGenerate θt targetExtension
      htargetExtension htargetNormalized hθtInvariant
      htargetDegree
  exact
    ⟨⟨sourceExtension,
      hsourceExtension,
      hsourceInvariant,
      targetExtension,
      htargetExtension,
      htargetInvariant⟩⟩

end McKayConjecture
