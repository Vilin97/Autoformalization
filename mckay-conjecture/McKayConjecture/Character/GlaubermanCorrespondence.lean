/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralScalarConstituent
import McKayConjecture.Character.PGroupQuotientClifford
import McKayConjecture.Character.PPrimeCliffordOrbit

/-!
# The ordinary Glauberman correspondence interface

Let `P` be a `p`-subgroup of a finite group and let `K` be a normal
`p′`-subgroup.  The classical Glauberman correspondence matches the
`P`-invariant irreducible characters of `K` with the irreducible characters
of `C_K(P)`.  Its defining numerical property is that the correspondent is
the unique constituent of the restriction to `C_K(P)` whose multiplicity is
prime to `p`.

`GlaubermanCorrespondence` records exactly this classical theorem.  In
particular, it is not an equivalence between ambient McKay character sets.
The central-value lemma below is then a formal consequence of the
constituent property and Schur's lemma.
-/

noncomputable section

namespace McKayConjecture

open CliffordCorrespondence
open CliffordPartition

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- The fixed-point subgroup `C_K(P)`. -/
abbrev coprimeFixedPoints
    (K P : Subgroup G) :
    Subgroup G :=
  K ⊓ Subgroup.centralizer (P : Set G)

/-- The canonical inclusion `C_K(P) ↪ K`. -/
def coprimeFixedPointsInclusion
    (K P : Subgroup G) :
    coprimeFixedPoints K P →* K :=
  Subgroup.inclusion inf_le_left

@[simp]
theorem coprimeFixedPointsInclusion_apply
    (K P : Subgroup G)
    (x : coprimeFixedPoints K P) :
    (coprimeFixedPointsInclusion K P x : G) = x :=
  rfl

/-- A prime-to-`p` irreducible character of `K` invariant under the
conjugation action of `P`. -/
abbrev PInvariantPPrimeIrreducibleCharacter
    (K P : Subgroup G) [K.Normal] (p : ℕ) :=
  {θ : PPrimeIrreducibleCharacter K p //
    P ≤ IrreducibleCharacter.inertia K θ.1}

/-- The classical Glauberman correspondence, characterized by the unique
prime-to-`p` restriction multiplicity.

The restriction to prime-to-`p` characters is harmless in the intended
application, where `K` and `C_K(P)` are `p′`-groups.  It avoids building an
unrelated divisibility theorem for all irreducible degrees into this
interface. -/
structure GlaubermanCorrespondence
    (K P : Subgroup G) [K.Normal] (p : ℕ) where
  /-- The character correspondence itself. -/
  characterEquiv :
    PInvariantPPrimeIrreducibleCharacter K P p ≃
      PPrimeIrreducibleCharacter
        (coprimeFixedPoints K P) p
  /-- The correspondent occurs with multiplicity prime to `p`. -/
  multiplicity_isPPrime :
    ∀ θ : PInvariantPPrimeIrreducibleCharacter K P p,
      ¬p ∣
        restrictionMultiplicity
          (coprimeFixedPointsInclusion K P)
          (characterEquiv θ).1 θ.1.1
  /-- The prime-to-`p` multiplicity characterizes the correspondent
  uniquely. -/
  eq_correspondent_of_multiplicity_isPPrime :
    ∀ (θ : PInvariantPPrimeIrreducibleCharacter K P p)
      (φ :
        PPrimeIrreducibleCharacter
          (coprimeFixedPoints K P) p),
      (¬p ∣
        restrictionMultiplicity
          (coprimeFixedPointsInclusion K P)
          φ.1 θ.1.1) →
        φ = characterEquiv θ

namespace GlaubermanCorrespondence

variable {K P : Subgroup G}
variable [K.Normal]

/-- The numerical relation characterizing the Glauberman correspondent:
the restriction multiplicity is prime to `p`. -/
def HasPPrimeRestrictionMultiplicity
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (φ :
      PPrimeIrreducibleCharacter
        (coprimeFixedPoints K P) p) : Prop :=
  ¬p ∣
    restrictionMultiplicity
      (coprimeFixedPointsInclusion K P)
      φ.1 θ.1.1

/-- A relation which is uniquely solvable in both variables packages into
the Glauberman equivalence.  This is the final set-theoretic assembly step
after the character-theoretic proof establishes bi-uniqueness of the
prime-to-`p` restriction multiplicity. -/
def of_biunique_multiplicity
    (hsource :
      ∀ θ : PInvariantPPrimeIrreducibleCharacter K P p,
        ∃! φ :
          PPrimeIrreducibleCharacter
            (coprimeFixedPoints K P) p,
          HasPPrimeRestrictionMultiplicity θ φ)
    (htarget :
      ∀ φ :
          PPrimeIrreducibleCharacter
            (coprimeFixedPoints K P) p,
        ∃! θ : PInvariantPPrimeIrreducibleCharacter K P p,
          HasPPrimeRestrictionMultiplicity θ φ) :
    GlaubermanCorrespondence K P p := by
  let f :
      PInvariantPPrimeIrreducibleCharacter K P p →
        PPrimeIrreducibleCharacter
          (coprimeFixedPoints K P) p :=
    fun θ ↦ Classical.choose (hsource θ)
  have hf :
      ∀ θ,
        HasPPrimeRestrictionMultiplicity θ (f θ) :=
    fun θ ↦ Classical.choose_spec (hsource θ) |>.1
  have hfinjective : Function.Injective f := by
    intro θ₁ θ₂ heq
    have hθ₁ :
        HasPPrimeRestrictionMultiplicity θ₁ (f θ₁) :=
      hf θ₁
    have hθ₂ :
        HasPPrimeRestrictionMultiplicity θ₂ (f θ₁) := by
      rw [heq]
      exact hf θ₂
    exact (htarget (f θ₁)).unique hθ₁ hθ₂
  have hfsurjective : Function.Surjective f := by
    intro φ
    let θ :
        PInvariantPPrimeIrreducibleCharacter K P p :=
      Classical.choose (htarget φ)
    have hθφ :
        HasPPrimeRestrictionMultiplicity θ φ :=
      Classical.choose_spec (htarget φ) |>.1
    refine ⟨θ, ?_⟩
    exact (hsource θ).unique (hf θ) hθφ
  let e := Equiv.ofBijective f ⟨hfinjective, hfsurjective⟩
  exact
    { characterEquiv := e
      multiplicity_isPPrime := fun θ ↦ hf θ
      eq_correspondent_of_multiplicity_isPPrime := by
        intro θ φ hφ
        exact (hsource θ).unique hφ (hf θ) }

/-- The Glauberman correspondent really is a constituent of the
restriction to `C_K(P)`. -/
theorem liesOver
    (d : GlaubermanCorrespondence K P p)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    LiesOverAlong
      (coprimeFixedPointsInclusion K P)
      (d.characterEquiv θ).1 θ.1.1 := by
  apply Nat.pos_of_ne_zero
  intro hzero
  exact
    d.multiplicity_isPPrime θ
      (hzero ▸ dvd_zero p)

omit [Finite G] [Fact p.Prime] in
/-- If `K` and `P` generate the ambient group, `P`-invariance is the same
invariance needed for a full inertia group. -/
theorem inertia_eq_top_of_generate
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    IrreducibleCharacter.inertia K θ.1.1 = ⊤ := by
  apply top_unique
  rw [← hgenerate]
  exact sup_le
    (IrreducibleCharacter.subgroup_le_inertia K θ.1.1)
    θ.2

/-- An active Clifford orbit above a `p`-group quotient supplies a
`P`-invariant prime-to-`p` kernel character. -/
def invariantCharacterOfActiveOrbit
    (hquotient : IsPGroup p (G ⧸ K))
    (q : ActiveOrbit K p) :
    PInvariantPPrimeIrreducibleCharacter K P p :=
  ⟨q.pPrimeOut K, by
    change
      P ≤ IrreducibleCharacter.inertia K q.1.out
    rw [activeOrbit_inertia_eq_top_of_quotient_isPGroup
      K hquotient q]
    exact le_top⟩

@[simp]
theorem invariantCharacterOfActiveOrbit_coe
    (hquotient : IsPGroup p (G ⧸ K))
    (q : ActiveOrbit K p) :
    (invariantCharacterOfActiveOrbit
      (K := K) (P := P) hquotient q).1 =
        q.pPrimeOut K :=
  rfl

omit [Finite G] [Fact p.Prime] in
/-- An ambient-central element of `K` belongs to `C_K(P)`. -/
def centralFixedPointElement
    (z : G)
    (hzK : z ∈ K)
    (hzcentral : z ∈ Subgroup.center G) :
    coprimeFixedPoints K P :=
  ⟨z, hzK,
    Subgroup.mem_centralizer_iff.mpr fun x _hx ↦
      Subgroup.mem_center_iff.mp hzcentral x⟩

omit [Finite G] [Fact p.Prime] in
@[simp]
theorem centralFixedPointElement_coe
    (z : G)
    (hzK : z ∈ K)
    (hzcentral : z ∈ Subgroup.center G) :
    (centralFixedPointElement
      (K := K) (P := P) z hzK hzcentral : G) =
      z :=
  rfl

/-- Glauberman correspondents have the same normalized value on every
ambient-central element lying in the coprime kernel. -/
theorem central_cross
    (d : GlaubermanCorrespondence K P p)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (z : G)
    (hzK : z ∈ K)
    (hzcentral : z ∈ Subgroup.center G) :
    θ.1.1.values ⟨z, hzK⟩ *
        ((d.characterEquiv θ).1.degree : ℂ) =
      (d.characterEquiv θ).1.values
          (centralFixedPointElement
            (K := K) (P := P) z hzK hzcentral) *
        (θ.1.1.degree : ℂ) := by
  let zC :=
    centralFixedPointElement
      (K := K) (P := P) z hzK hzcentral
  have hzCcentral :
      zC ∈ Subgroup.center (coprimeFixedPoints K P) := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact
      Subgroup.mem_center_iff.mp hzcentral (x : G)
  have hzKcentral :
      (coprimeFixedPointsInclusion K P zC) ∈
        Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact
      Subgroup.mem_center_iff.mp hzcentral (x : G)
  have hcross :=
    central_cross_of_liesOverAlong
      (coprimeFixedPointsInclusion K P)
      (d.characterEquiv θ).1 θ.1.1
      (d.liesOver θ)
      zC hzCcentral hzKcentral
  have hzIncl :
      coprimeFixedPointsInclusion K P zC =
        (⟨z, hzK⟩ : K) :=
    Subtype.ext rfl
  rw [hzIncl] at hcross
  exact hcross

end GlaubermanCorrespondence
end McKayConjecture
