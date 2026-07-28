/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.PGroup
import McKayConjecture.InductiveMcKay.NormalSubgroupJoinCenterReduction

/-!
# Reduction for a normal subgroup with central Sylow intersection

This file isolates the group-theoretic shell of Rossi's Theorem 4.4 and
Proposition 4.5.  Let `K ◁ G`, let `P ∈ Syl_p(G)`, and put

`L = K P = K ⊔ P`.

The quotient `L/K` is a `p`-group, `P` remains Sylow in `L`, and the
hypothesis `K ∩ P ≤ Z(G)` gives the central intersection required by
Theorem 4.4.  If the preceding Corollary 4.3 reduction supplies
`G = K N_G(P)`, then `L` is normal in `G` and
`G = L N_G(P)`.

Rossi's Theorem 4.4 supplies a character bijection

`Irr_{p'}(L) ≃ Irr_{p'}(N_L(P))`.

That exact bijection is a direct parameter below, not a disguised local
correspondence.  After transporting its target to
`L ∩ N_G(P) ◁ N_G(P)`, the existing matched central-triple Clifford
assembler constructs the ambient correspondence provided the bijection is
`N_G(P)`-equivariant and carries the stated complete central witnesses.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay
namespace NormalSubgroupCentralIntersectionReduction

open CharacterTriple
open GroupTheory

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (P : Sylow p G) (K : Subgroup G) [K.Normal]

/-- The subgroup `KP`, expressed as the join of `K` and the chosen Sylow
subgroup. -/
abbrev product : Subgroup G :=
  K ⊔ (P : Subgroup G)

/-- The chosen ambient Sylow subgroup, restricted to `KP`. -/
abbrev productSylow : Sylow p (product P K) :=
  sylowIn P (product P K) le_sup_right

/-- The normal kernel `K`, viewed internally in `KP`. -/
abbrev internalKernel : Subgroup (product P K) :=
  K.subgroupOf (product P K)

/-- The internal copy of `K` is normal in `KP`. -/
instance internalKernelNormal :
    (internalKernel P K).Normal :=
  inferInstance

omit [Finite G] [Fact p.Prime] [K.Normal] in
/-- Mapping the internal kernel back into `G` recovers `K`. -/
theorem map_internalKernel_subtype :
    (internalKernel P K).map (product P K).subtype = K :=
  Subgroup.map_subgroupOf_eq_of_le le_sup_left

omit [Finite G] [Fact p.Prime] [K.Normal] in
/-- Mapping the restricted Sylow subgroup back into `G` recovers `P`. -/
theorem map_productSylow_subtype :
    (productSylow P K : Subgroup (product P K)).map
        (product P K).subtype =
      (P : Subgroup G) :=
  Subgroup.map_subgroupOf_eq_of_le le_sup_right

omit [Finite G] [Fact p.Prime] [K.Normal] in
/-- Internally, `K` and `P` generate `KP`. -/
theorem internalKernel_sup_productSylow :
    internalKernel P K ⊔
        (productSylow P K :
          Subgroup (product P K)) =
      ⊤ := by
  exact
    codisjoint_iff.mp
      (Subgroup.codisjoint_subgroupOf_sup
        K (P : Subgroup G))

omit [Finite G] [Fact p.Prime] [K.Normal] in
/-- The internal intersection maps to the literal ambient intersection
`K ∩ P`. -/
theorem map_internalKernel_inf_productSylow :
    (internalKernel P K ⊓
        (productSylow P K :
          Subgroup (product P K))).map
          (product P K).subtype =
      K ⊓ (P : Subgroup G) := by
  rw [Subgroup.map_inf _ _
      (product P K).subtype
      (product P K).subtype_injective,
    map_internalKernel_subtype,
    map_productSylow_subtype]

omit [Finite G] [Fact p.Prime] in
/-- The quotient `KP/K` is a `p`-group. -/
theorem quotientInternalKernel_isPGroup :
    IsPGroup p
      ((product P K) ⧸ internalKernel P K) := by
  let π :
      product P K →*
        (product P K) ⧸ internalKernel P K :=
    QuotientGroup.mk' (internalKernel P K)
  have hmap :
      (productSylow P K :
          Subgroup (product P K)).map π =
        ⊤ := by
    have hsup :=
      congrArg
        (fun H : Subgroup (product P K) =>
          H.map π)
        (internalKernel_sup_productSylow P K)
    have hkernel :
        (internalKernel P K).map π = ⊥ := by
      dsimp only [π]
      exact
        QuotientGroup.map_mk'_self
          (internalKernel P K)
    have htop :
        (⊤ : Subgroup (product P K)).map π =
          ⊤ :=
      Subgroup.map_top_of_surjective π (by
        simpa only [π] using
          (QuotientGroup.mk'_surjective
            (internalKernel P K)))
    rw [Subgroup.map_sup, hkernel,
      bot_sup_eq, htop] at hsup
    exact hsup
  have hp :
      IsPGroup p
        ((productSylow P K :
          Subgroup (product P K)).map π) :=
    (productSylow P K).isPGroup'.map π
  rw [hmap] at hp
  exact hp.of_equiv Subgroup.topEquiv

omit [Finite G] [Fact p.Prime] [K.Normal] in
/-- A central ambient intersection is central inside `KP`. -/
theorem internalKernel_inf_productSylow_le_center
    (hcentral :
      K ⊓ (P : Subgroup G) ≤ Subgroup.center G) :
    internalKernel P K ⊓
        (productSylow P K :
          Subgroup (product P K)) ≤
      Subgroup.center (product P K) := by
  intro x hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply Subtype.ext
  exact
    Subgroup.mem_center_iff.mp
      (hcentral ⟨hx.1, hx.2⟩) y.1

omit [Finite G] [Fact p.Prime] [K.Normal] in
/-- The normalizer of the restricted Sylow subgroup is the restriction of
the ambient normalizer. -/
theorem normalizer_productSylow_eq_subgroupOf :
    Subgroup.normalizer
        (productSylow P K :
          Set (product P K)) =
      (Subgroup.normalizer (P : Set G)).subgroupOf
        (product P K) :=
  normalizer_sylowIn_eq_subgroupOf
    P (product P K) le_sup_right

omit [Finite G] [Fact p.Prime] [K.Normal] in
/-- Mapping `N_{KP}(P)` into `G` gives
`KP ∩ N_G(P)`. -/
theorem map_normalizer_productSylow_subtype :
    (Subgroup.normalizer
      (productSylow P K :
        Set (product P K))).map
        (product P K).subtype =
      product P K ⊓
        Subgroup.normalizer (P : Set G) := by
  rw [normalizer_productSylow_eq_subgroupOf P K,
    Subgroup.subgroupOf_map_subtype, inf_comm]

omit [Finite G] [Fact p.Prime] [K.Normal] in
/-- If `G = K N_G(P)`, then `KP` and `N_G(P)` also generate `G`. -/
theorem product_sup_normalizer_eq_top
    (hgenerate :
      K ⊔ Subgroup.normalizer (P : Set G) = ⊤) :
    product P K ⊔
        Subgroup.normalizer (P : Set G) =
      ⊤ := by
  apply top_unique
  rw [← hgenerate]
  exact
    sup_le
      (le_sup_left.trans le_sup_left)
      le_sup_right

omit [Finite G] [Fact p.Prime] in
/-- Under the same generation equality, `KP` is normal in `G`. -/
theorem product_normal
    (hgenerate :
      K ⊔ Subgroup.normalizer (P : Set G) = ⊤) :
    (product P K).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff]
  apply top_unique
  rw [← hgenerate]
  refine sup_le ?_ ?_
  · exact
      (show K ≤ product P K from le_sup_left).trans
        Subgroup.le_normalizer
  · have h :=
      Subgroup.normalizer_le_normalizer_sup_normal
        (G := G) (H := (P : Subgroup G)) (K := K)
    rw [sup_comm (P : Subgroup G) K] at h
    exact h

/-! ## Transporting `N_{KP}(P)` into `N_G(P)` -/

omit [Finite G] [Fact p.Prime] [K.Normal] in
/-- Swap the two presentations of an ambient intersection:
`A ∩ B` internal to `B` and `B ∩ A` internal to `A`. -/
def subgroupOfSwapEquiv (A B : Subgroup G) :
    A.subgroupOf B ≃* B.subgroupOf A where
  toFun x :=
    ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun x :=
    ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The ambient Sylow normalizer. -/
abbrev ambientNormalizer : Subgroup G :=
  Subgroup.normalizer (P : Set G)

/-- The intersection `KP ∩ N_G(P)`, viewed internally as a subgroup of
`N_G(P)`. -/
abbrev internalProductNormalizer :
    Subgroup (ambientNormalizer P) :=
  (product P K).subgroupOf (ambientNormalizer P)

omit [Finite G] [Fact p.Prime] [K.Normal] in
/-- Canonical equivalence between the Theorem 4.4 target
`N_{KP}(P)` and `KP ∩ N_G(P)` internal to `N_G(P)`. -/
def productNormalizerEquivInternal :
    Subgroup.normalizer
        (productSylow P K :
          Set (product P K)) ≃*
      internalProductNormalizer P K :=
  (MulEquiv.subgroupCongr
    (normalizer_productSylow_eq_subgroupOf P K)).trans
      (subgroupOfSwapEquiv
        (ambientNormalizer P) (product P K))

omit [Finite G] [Fact p.Prime] in
/-- If `G = K N_G(P)`, then the internal intersection
`KP ∩ N_G(P)` is normal in `N_G(P)`. -/
theorem internalProductNormalizer_normal
    (hgenerate :
      K ⊔ Subgroup.normalizer (P : Set G) = ⊤) :
    (internalProductNormalizer P K).Normal := by
  letI : (product P K).Normal :=
    product_normal P K hgenerate
  infer_instance

/-- Transport the exact Theorem 4.4 character bijection from
`N_{KP}(P)` to the copy of that group internal to `N_G(P)`. -/
def internalTheorem44CharacterEquiv
    (theorem44Equiv :
      PPrimeIrreducibleCharacter (product P K) p ≃
        PPrimeIrreducibleCharacter
          (Subgroup.normalizer
            (productSylow P K :
              Set (product P K))) p) :
    PPrimeIrreducibleCharacter (product P K) p ≃
      PPrimeIrreducibleCharacter
        (internalProductNormalizer P K) p :=
  theorem44Equiv.trans
    (IrreducibleCharacter.pPrimeComapEquiv p
      (productNormalizerEquivInternal P K).symm)

/-! ## Character-theoretic completion

As elsewhere in the active Clifford API, this final assembly is currently
restricted to groups in `Type`.  The group-theoretic results above remain
universe-polymorphic.
-/

section CliffordAssembly

variable {X : Type} [Group X] [Finite X]
variable {q : ℕ} [Fact q.Prime]
variable (S : Sylow q X) (C : Subgroup X) [C.Normal]

/-- The exact character-theoretic content of Rossi's Theorem 4.4 needed
after the group-theoretic `CP` reduction.

The fields expose the Okuyama--Wajima/DGN character equivalence, its
normalizer equivariance, and the matched central character-triple witnesses.
The conclusion is not itself a local correspondence. -/
structure Theorem44CharacterData
    (S : Sylow q X) (C : Subgroup X) [C.Normal]
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤) where
  characterEquiv :
    PPrimeIrreducibleCharacter (product S C) q ≃
      PPrimeIrreducibleCharacter
        (Subgroup.normalizer
          (productSylow S C :
            Set (product S C))) q
  characterEquiv_smul :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal
        S C hgenerate
    ∀ (h : ambientNormalizer S)
      (θ :
        PPrimeIrreducibleCharacter
          (product S C) q),
      internalTheorem44CharacterEquiv
          S C characterEquiv (h • θ) =
        h • internalTheorem44CharacterEquiv
          S C characterEquiv θ
  centralWitness :
    letI : (product S C).Normal :=
      product_normal S C hgenerate
    letI :
        (internalProductNormalizer S C).Normal :=
      internalProductNormalizer_normal
        S C hgenerate
    ∀ θ :
        PPrimeIrreducibleCharacter
          (product S C) q,
      CompleteCentralIsomorphismWitness
        (ofInertia (product S C) θ.1)
        (ofInertia
          (internalProductNormalizer S C)
          (internalTheorem44CharacterEquiv
            S C characterEquiv θ).1)

/-- Assemble the ambient `p'`-character equivalence from the exact
Theorem 4.4 bijection on `CP`.

The direct character-level inputs retained here are precisely:

* the Okuyama--Wajima/DGN bijection
  `Irr_{p'}(CP) ≃ Irr_{p'}(N_{CP}(P))`;
* equivariance of its transported form under `N_X(P)`;
* complete central witnesses on exactly matched inertia triples.

The hypothesis `X = C N_X(P)` is the already-separated Corollary 4.3
output. -/
def assembledPPrimeEquivOfTheorem44Data
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theorem44Equiv :
      PPrimeIrreducibleCharacter (product S C) q ≃
        PPrimeIrreducibleCharacter
          (Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) q)
    (characterEquiv_smul :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI :
          (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal
          S C hgenerate
      ∀ (h : ambientNormalizer S)
        (θ :
          PPrimeIrreducibleCharacter
            (product S C) q),
        internalTheorem44CharacterEquiv
            S C theorem44Equiv (h • θ) =
          h • internalTheorem44CharacterEquiv
            S C theorem44Equiv θ)
    (centralWitness :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI :
          (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal
          S C hgenerate
      ∀ θ :
          PPrimeIrreducibleCharacter
            (product S C) q,
        CompleteCentralIsomorphismWitness
          (ofInertia (product S C) θ.1)
          (ofInertia
            (internalProductNormalizer S C)
            (internalTheorem44CharacterEquiv
              S C theorem44Equiv θ).1)) :
    PPrimeIrreducibleCharacter X q ≃
      PPrimeIrreducibleCharacter
        (ambientNormalizer S) q := by
  letI : (product S C).Normal :=
    product_normal S C hgenerate
  letI :
      (internalProductNormalizer S C).Normal :=
    internalProductNormalizer_normal
      S C hgenerate
  let assembly :
      MatchedCentralTripleCliffordAssemblyData
        (product S C)
        (ambientNormalizer S)
        (internalProductNormalizer S C) q :=
    { sup_eq_top :=
        product_sup_normalizer_eq_top
          S C hgenerate
      characterEquiv :=
        internalTheorem44CharacterEquiv
          S C theorem44Equiv
      characterEquiv_smul :=
        characterEquiv_smul
      centralWitness := centralWitness }
  exact assembly.assembledPPrimeEquiv

/-- Package the assembled ambient-to-normalizer equivalence as the second
normal-subgroup local-reduction principle.  The desired local
correspondence is a conclusion, while every missing character assertion
remains an explicit parameter above. -/
def localCorrespondenceOfTheorem44Data
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theorem44Equiv :
      PPrimeIrreducibleCharacter (product S C) q ≃
        PPrimeIrreducibleCharacter
          (Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) q)
    (characterEquiv_smul :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI :
          (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal
          S C hgenerate
      ∀ (h : ambientNormalizer S)
        (θ :
          PPrimeIrreducibleCharacter
            (product S C) q),
        internalTheorem44CharacterEquiv
            S C theorem44Equiv (h • θ) =
          h • internalTheorem44CharacterEquiv
            S C theorem44Equiv θ)
    (centralWitness :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI :
          (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal
          S C hgenerate
      ∀ θ :
          PPrimeIrreducibleCharacter
            (product S C) q,
        CompleteCentralIsomorphismWitness
          (ofInertia (product S C) θ.1)
          (ofInertia
            (internalProductNormalizer S C)
            (internalTheorem44CharacterEquiv
              S C theorem44Equiv θ).1)) :
    LocalCorrespondence S where
  intermediate := ambientNormalizer S
  normalizer_le := le_rfl
  proper_of_normalizer_ne_top := fun h =>
    lt_top_iff_ne_top.mpr h
  correspondence :=
    assembledPPrimeEquivOfTheorem44Data
      S C hgenerate theorem44Equiv
        characterEquiv_smul centralWitness

/-- Assemble the local correspondence from a bundled exact Theorem-4.4
character datum. -/
def Theorem44CharacterData.toLocalCorrespondence
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (d : Theorem44CharacterData S C hgenerate) :
    LocalCorrespondence S :=
  localCorrespondenceOfTheorem44Data
    S C hgenerate d.characterEquiv
      d.characterEquiv_smul d.centralWitness

@[simp]
theorem localCorrespondenceOfTheorem44Data_intermediate
    (hgenerate :
      C ⊔ Subgroup.normalizer (S : Set X) = ⊤)
    (theorem44Equiv :
      PPrimeIrreducibleCharacter (product S C) q ≃
        PPrimeIrreducibleCharacter
          (Subgroup.normalizer
            (productSylow S C :
              Set (product S C))) q)
    (characterEquiv_smul :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI :
          (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal
          S C hgenerate
      ∀ (h : ambientNormalizer S)
        (θ :
          PPrimeIrreducibleCharacter
            (product S C) q),
        internalTheorem44CharacterEquiv
            S C theorem44Equiv (h • θ) =
          h • internalTheorem44CharacterEquiv
            S C theorem44Equiv θ)
    (centralWitness :
      letI : (product S C).Normal :=
        product_normal S C hgenerate
      letI :
          (internalProductNormalizer S C).Normal :=
        internalProductNormalizer_normal
          S C hgenerate
      ∀ θ :
          PPrimeIrreducibleCharacter
            (product S C) q,
        CompleteCentralIsomorphismWitness
          (ofInertia (product S C) θ.1)
          (ofInertia
            (internalProductNormalizer S C)
            (internalTheorem44CharacterEquiv
              S C theorem44Equiv θ).1)) :
    (localCorrespondenceOfTheorem44Data
      S C hgenerate theorem44Equiv
        characterEquiv_smul centralWitness).intermediate =
      ambientNormalizer S :=
  rfl

end CliffordAssembly

end NormalSubgroupCentralIntersectionReduction
end InductiveMcKay
end McKayConjecture
