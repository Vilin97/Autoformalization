/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CentralProductCharacter
import McKayConjecture.Character.Determination

/-!
# Descent of ordinary irreducible characters through a quotient

For a finite group `G` and a normal subgroup `N`, inflation identifies the
ordinary irreducible characters of `G ⧸ N` with the irreducible characters
of `G` whose chosen realization is trivial on `N`.  Triviality is independent
of the chosen simple realization: this follows from determination of simple
complex representations by their characters.

The file also records the corresponding equivalence for irreducible
characters of `p'`-degree.
-/

noncomputable section

open CategoryTheory

universe u v w z

namespace McKayConjecture

/-! ### Irreducibility and pullback along a surjection -/

namespace RepresentationTheory
namespace Representation

variable {F : Type u} [Field F]
variable {H : Type v} [Group H] {Q : Type w} [Group Q]
variable {V : Type z} [AddCommGroup V] [Module F V]

/-- Pullback along a surjective group homomorphism preserves irreducibility. -/
theorem isIrreducible_comp_of_surjective
    (σ : Representation F Q V) [Representation.IsIrreducible σ]
    (f : H →* Q) (hf : Function.Surjective f) :
    Representation.IsIrreducible (σ.comp f) := by
  have hsimple : IsSimpleOrder (Subrepresentation σ) := inferInstance
  haveI := hsimple.toNontrivial
  let extendSubrepresentation :
      Subrepresentation (σ.comp f) → Subrepresentation σ := fun R =>
    { toSubmodule := R.toSubmodule
      apply_mem_toSubmodule := fun q x hx => by
        obtain ⟨h, rfl⟩ := hf q
        exact R.apply_mem_toSubmodule h hx }
  have hbotσ : (⊥ : Subrepresentation σ).toSubmodule = ⊥ := rfl
  have htopσ : (⊤ : Subrepresentation σ).toSubmodule = ⊤ := rfl
  have hbotComp :
      (⊥ : Subrepresentation (σ.comp f)).toSubmodule = ⊥ := rfl
  have htopComp :
      (⊤ : Subrepresentation (σ.comp f)).toSubmodule = ⊤ := rfl
  have hVne : (⊥ : Submodule F V) ≠ ⊤ := fun h =>
    bot_ne_top (α := Subrepresentation σ)
      (Subrepresentation.toSubmodule_injective
        (by rw [hbotσ, htopσ]; exact h))
  haveI : Nontrivial (Subrepresentation (σ.comp f)) :=
    ⟨⟨⊥, ⊤, fun h =>
      hVne (by rw [← hbotComp, h, htopComp])⟩⟩
  exact ⟨fun S => by
    rcases hsimple.eq_bot_or_eq_top (extendSubrepresentation S) with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective
        ((congrArg Subrepresentation.toSubmodule h).trans hbotσ))
    · exact Or.inr (Subrepresentation.toSubmodule_injective
        ((congrArg Subrepresentation.toSubmodule h).trans htopσ))⟩

/-- Irreducibility is preserved and reflected by pullback along a
surjective group homomorphism. -/
theorem isIrreducible_comp_iff_of_surjective
    (σ : Representation F Q V) (f : H →* Q)
    (hf : Function.Surjective f) :
    Representation.IsIrreducible (σ.comp f) ↔
      Representation.IsIrreducible σ := by
  constructor
  · exact isIrreducible_of_isIrreducible_comp σ
  · intro hσ
    letI : Representation.IsIrreducible σ := hσ
    exact isIrreducible_comp_of_surjective σ f hf

end Representation
end RepresentationTheory

namespace FDRep

variable {H : Type v} [Group H] {Q : Type w} [Group Q]
variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]

/-- At the `FDRep.of` level, simplicity is preserved and reflected by
pullback along a surjective group homomorphism. -/
theorem simple_comp_iff_of_surjective
    (σ : Representation ℂ Q V) (f : H →* Q)
    (hf : Function.Surjective f) :
    Simple (FDRep.of (σ.comp f)) ↔ Simple (FDRep.of σ) := by
  constructor
  · intro hcomp
    letI : Simple (FDRep.of (σ.comp f)) := hcomp
    letI : Representation.IsIrreducible (σ.comp f) :=
      CliffordRestriction.isIrreducible_of_simple (FDRep.of (σ.comp f))
    letI : Representation.IsIrreducible σ :=
      RepresentationTheory.Representation.isIrreducible_of_isIrreducible_comp
        (f := f) σ inferInstance
    exact FDRep.simple_of_representation_isIrreducible σ
  · intro hσ
    letI : Simple (FDRep.of σ) := hσ
    letI : Representation.IsIrreducible σ :=
      CliffordRestriction.isIrreducible_of_simple (FDRep.of σ)
    letI : Representation.IsIrreducible (σ.comp f) :=
      RepresentationTheory.Representation.isIrreducible_comp_of_surjective
        σ f hf
    exact FDRep.simple_of_representation_isIrreducible (σ.comp f)

variable {G : Type*} [Group G]

/-- A finite-dimensional representation is trivial on `N` when every
element of `N` acts as the identity. -/
def IsTrivialOn (V : FDRep ℂ G) (N : Subgroup G) : Prop :=
  ∀ n : N, V.ρ (n : G) = LinearMap.id

/-- Triviality on a subgroup is invariant under isomorphism of
representations. -/
theorem isTrivialOn_iff_of_iso
    (N : Subgroup G) (V W : FDRep ℂ G) (i : V ≅ W) :
    FDRep.IsTrivialOn V N ↔ FDRep.IsTrivialOn W N := by
  constructor
  · intro hV n
    rw [FDRep.Iso.conj_ρ i (n : G), hV n]
    ext w
    simp [LinearEquiv.conj_apply]
  · intro hW n
    rw [FDRep.Iso.conj_ρ i.symm (n : G), hW n]
    ext v
    simp [LinearEquiv.conj_apply]

variable (N : Subgroup G) [N.Normal]

/-- Pull a quotient representation back along `G → G ⧸ N`.

This is defined at the unbundled representation level so that the
surjective-pullback irreducibility theorem applies directly. -/
def quotientPullback (V : FDRep ℂ (G ⧸ N)) : FDRep ℂ G :=
  FDRep.of (V.ρ.comp (QuotientGroup.mk' N))

@[simp]
theorem quotientPullback_ρ
    (V : FDRep ℂ (G ⧸ N)) (g : G) :
    (quotientPullback N V).ρ g =
      V.ρ (QuotientGroup.mk' N g) :=
  rfl

@[simp]
theorem quotientPullback_character
    (V : FDRep ℂ (G ⧸ N)) (g : G) :
    (quotientPullback N V).character g =
      V.character (QuotientGroup.mk' N g) :=
  rfl

@[simp]
theorem quotientPullback_finrank
    (V : FDRep ℂ (G ⧸ N)) :
    Module.finrank ℂ (quotientPullback N V) =
      Module.finrank ℂ V :=
  rfl

/-- Pullback of a simple quotient representation along the quotient map is
simple. -/
instance quotientPullbackSimple
    (V : FDRep ℂ (G ⧸ N)) [Simple V] :
    Simple (quotientPullback N V) := by
  letI : Representation.IsIrreducible V.ρ :=
    CliffordRestriction.isIrreducible_of_simple V
  letI :
      Representation.IsIrreducible
        (V.ρ.comp (QuotientGroup.mk' N)) :=
    RepresentationTheory.Representation.isIrreducible_comp_of_surjective
      V.ρ (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  exact FDRep.simple_of_representation_isIrreducible
    (V.ρ.comp (QuotientGroup.mk' N))

/-- A quotient representation pulled back to `G` is trivial on `N`. -/
theorem quotientPullback_isTrivialOn
    (V : FDRep ℂ (G ⧸ N)) :
    FDRep.IsTrivialOn (quotientPullback N V) N := by
  intro n
  change V.ρ (QuotientGroup.mk' N (n : G)) = LinearMap.id
  have hq :
      QuotientGroup.mk' N (n : G) = 1 :=
    (QuotientGroup.eq_one_iff (n : G)).2 n.property
  rw [hq]
  exact map_one V.ρ

end FDRep

/-! ### Triviality as a character-level condition -/

namespace IrreducibleCharacter

variable {G : Type*} [Group G]

/-- An irreducible character is trivial on `N` when its chosen simple
realization is trivial on `N`.  For finite groups this condition is
independent of the chosen realization. -/
def TrivialOn (N : Subgroup G) (χ : IrreducibleCharacter G) : Prop :=
  FDRep.IsTrivialOn χ.realization N

/-- Unpack character-level triviality into the pointwise identity needed by
`Representation.ofQuotient`. -/
theorem trivialOn_action
    {N : Subgroup G} {χ : IrreducibleCharacter G}
    (hχ : χ.TrivialOn N) :
    ∀ n : N, χ.realization.ρ (n : G) = LinearMap.id :=
  hχ

/-- The characters of `G` that are trivial on `N`. -/
abbrev TrivialOnCharacters (N : Subgroup G) :=
  {χ : IrreducibleCharacter G // χ.TrivialOn N}

/-- Triviality may be checked on any simple representation affording the
same character, not only on the realization selected by `χ`. -/
theorem trivialOn_iff_of_character_eq [Finite G]
    (N : Subgroup G) (χ : IrreducibleCharacter G)
    (V : FDRep ℂ G) [Simple V]
    (hchar : V.character = χ.values) :
    χ.TrivialOn N ↔ FDRep.IsTrivialOn V N := by
  have hrealization :
      χ.realization.character = V.character := by
    rw [χ.realization_character, hchar]
  obtain ⟨i⟩ :=
    FDRep.nonempty_iso_of_character_eq χ.realization V hrealization
  exact FDRep.isTrivialOn_iff_of_iso N χ.realization V i

/-- For a finite group, triviality of the character constructed from a
simple representation is equivalent to triviality of that representation. -/
theorem trivialOn_ofSimple_iff [Finite G]
    (N : Subgroup G) (V : FDRep ℂ G) [Simple V] :
    (ofSimple V).TrivialOn N ↔ FDRep.IsTrivialOn V N := by
  have hchar :
      (ofSimple V).realization.character = V.character := by
    calc
      (ofSimple V).realization.character = (ofSimple V).values :=
        (ofSimple V).realization_character
      _ = V.character := ofSimple_values V
  obtain ⟨i⟩ :=
    FDRep.nonempty_iso_of_character_eq (ofSimple V).realization V hchar
  exact FDRep.isTrivialOn_iff_of_iso N (ofSimple V).realization V i

/-! ### Inflation and descent of irreducible characters -/

variable {G : Type u} [Group G] [Finite G]
variable (N : Subgroup G) [N.Normal]

/-- Inflation of an irreducible character of `G ⧸ N` along the quotient
map. -/
def inflate (χ : IrreducibleCharacter (G ⧸ N)) :
    IrreducibleCharacter G :=
  ofSimple (FDRep.quotientPullback N χ.realization)

omit [Finite G] in
@[simp]
theorem inflate_values
    (χ : IrreducibleCharacter (G ⧸ N)) (g : G) :
    (inflate N χ).values g =
      χ.values (QuotientGroup.mk' N g) := by
  change
    χ.realization.character (QuotientGroup.mk' N g) =
      χ.values (QuotientGroup.mk' N g)
  exact congrFun χ.realization_character _

omit [Finite G] in
@[simp]
theorem inflate_degree
    (χ : IrreducibleCharacter (G ⧸ N)) :
    (inflate N χ).degree = χ.degree := by
  change Module.finrank ℂ χ.realization = χ.degree
  exact χ.realization_finrank

/-- An inflated irreducible character is trivial on the quotient kernel. -/
theorem inflate_trivialOn
    (χ : IrreducibleCharacter (G ⧸ N)) :
    (inflate N χ).TrivialOn N := by
  apply (trivialOn_ofSimple_iff N
    (FDRep.quotientPullback N χ.realization)).2
  exact FDRep.quotientPullback_isTrivialOn N χ.realization

/-- Descent of an irreducible character whose realization is trivial on
`N`.  The underlying representation is `Representation.ofQuotient`. -/
def descend (χ : TrivialOnCharacters N) :
    IrreducibleCharacter (G ⧸ N) := by
  letI :
      Simple
        (FDRep.quotient χ.1.realization N
          (trivialOn_action χ.2)) :=
    FDRep.quotient_simple χ.1.realization N
      (trivialOn_action χ.2)
  exact ofSimple
    (FDRep.quotient χ.1.realization N
      (trivialOn_action χ.2))

omit [Finite G] in
@[simp]
theorem descend_values_mk
    (χ : TrivialOnCharacters N) (g : G) :
    (descend N χ).values (QuotientGroup.mk' N g) =
      χ.1.values g := by
  unfold descend
  rw [ofSimple_values_apply, FDRep.quotient_character_mk,
    χ.1.realization_character]

omit [Finite G] in
@[simp]
theorem descend_degree
    (χ : TrivialOnCharacters N) :
    (descend N χ).degree = χ.1.degree := by
  unfold descend
  rw [ofSimple_degree]
  change Module.finrank ℂ χ.1.realization = χ.1.degree
  exact χ.1.realization_finrank

/-- Descending an inflated character recovers the quotient character. -/
theorem descend_inflate
    (χ : IrreducibleCharacter (G ⧸ N)) :
    descend N ⟨inflate N χ, inflate_trivialOn N χ⟩ = χ := by
  apply IrreducibleCharacter.ext
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  rw [descend_values_mk, inflate_values]

omit [Finite G] in
/-- Inflating a descended character recovers the original character. -/
theorem inflate_descend
    (χ : TrivialOnCharacters N) :
    inflate N (descend N χ) = χ.1 := by
  apply IrreducibleCharacter.ext
  funext g
  rw [inflate_values, descend_values_mk]

/-- Inflation along `G → G ⧸ N` is an equivalence from irreducible
characters of the quotient to irreducible characters of `G` trivial on
`N`. -/
def quotientDescentEquiv :
    IrreducibleCharacter (G ⧸ N) ≃ TrivialOnCharacters N where
  toFun χ := ⟨inflate N χ, inflate_trivialOn N χ⟩
  invFun := descend N
  left_inv := descend_inflate N
  right_inv χ := Subtype.ext (inflate_descend N χ)

@[simp]
theorem quotientDescentEquiv_apply_coe
    (χ : IrreducibleCharacter (G ⧸ N)) :
    (quotientDescentEquiv N χ).1 =
      inflate N χ :=
  rfl

@[simp]
theorem quotientDescentEquiv_values
    (χ : IrreducibleCharacter (G ⧸ N)) (g : G) :
    (quotientDescentEquiv N χ).1.values g =
      χ.values (QuotientGroup.mk' N g) :=
  inflate_values N χ g

@[simp]
theorem quotientDescentEquiv_degree
    (χ : IrreducibleCharacter (G ⧸ N)) :
    (quotientDescentEquiv N χ).1.degree = χ.degree :=
  inflate_degree N χ

@[simp]
theorem quotientDescentEquiv_symm_apply
    (χ : TrivialOnCharacters N) :
    (quotientDescentEquiv N).symm χ = descend N χ :=
  rfl

@[simp]
theorem quotientDescentEquiv_symm_values_mk
    (χ : TrivialOnCharacters N) (g : G) :
    ((quotientDescentEquiv N).symm χ).values
        (QuotientGroup.mk' N g) =
      χ.1.values g :=
  descend_values_mk N χ g

@[simp]
theorem quotientDescentEquiv_symm_degree
    (χ : TrivialOnCharacters N) :
    ((quotientDescentEquiv N).symm χ).degree = χ.1.degree :=
  descend_degree N χ

/-! ### Restriction to `p'`-degree characters -/

/-- The `p'`-degree irreducible characters of `G` that are trivial on
`N`. -/
abbrev PPrimeTrivialOnCharacters (N : Subgroup G) (p : ℕ) :=
  {χ : PPrimeIrreducibleCharacter G p // χ.1.TrivialOn N}

/-- Quotient descent restricted to irreducible characters of
`p'`-degree. -/
def pPrimeQuotientDescentEquiv (p : ℕ) :
    PPrimeIrreducibleCharacter (G ⧸ N) p ≃
      PPrimeTrivialOnCharacters N p where
  toFun χ :=
    ⟨⟨inflate N χ.1, by
        simpa [IsPPrimeDegree] using χ.2⟩,
      inflate_trivialOn N χ.1⟩
  invFun χ :=
    ⟨descend N ⟨χ.1.1, χ.2⟩, by
      simpa [IsPPrimeDegree] using χ.1.2⟩
  left_inv χ := by
    apply Subtype.ext
    exact descend_inflate N χ.1
  right_inv χ := by
    apply Subtype.ext
    apply Subtype.ext
    exact inflate_descend N ⟨χ.1.1, χ.2⟩

@[simp]
theorem pPrimeQuotientDescentEquiv_apply_coe
    (p : ℕ) (χ : PPrimeIrreducibleCharacter (G ⧸ N) p) :
    (pPrimeQuotientDescentEquiv N p χ).1.1 =
      inflate N χ.1 :=
  rfl

@[simp]
theorem pPrimeQuotientDescentEquiv_symm_apply_coe
    (p : ℕ) (χ : PPrimeTrivialOnCharacters N p) :
    ((pPrimeQuotientDescentEquiv N p).symm χ).1 =
      descend N ⟨χ.1.1, χ.2⟩ :=
  rfl

end IrreducibleCharacter

end McKayConjecture
