/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordTheorem
import McKayConjecture.Character.Determination
import McKayConjecture.Character.InductionCharacter
import McKayConjecture.Character.Inertia

/-!
# The character-level Clifford correspondence

Let `N` be a normal subgroup of a finite group `G`, let `θ ∈ Irr(N)`,
and let `I = I_G(θ)` be its inertia subgroup.  This file defines the sets

* `Irr(I | θ)`, and
* `Irr(G | G • θ)`

using positive intertwining multiplicity.  It also records the
finite-dimensional Frobenius reciprocity equivalence for the representation
model used in this project, identifies its two Hom-space dimensions, and
proves the exact degree and character formulas for induction from `I`.

The remaining step needed for the actual bijection is the Clifford--Mackey
irreducibility theorem: if an irreducible `I`-representation lies over `θ`,
then its induction to `G` is irreducible, and every irreducible
`G`-representation lying over the orbit of `θ` arises uniquely in this way.
That statement is not assumed here as data or as an axiom.  Instead,
`inducedIrreducibleCharacter` packages induction only when a genuine
`Simple` proof has been supplied.  Thus the declarations below are a
compiled interface up to, but not including, the missing Mackey argument.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture

namespace CliffordCorrespondence

variable {G H : Type} [Group G] [Group H]

/-- The multiplicity of `η` in the restriction of `χ` along `φ`, expressed
as the dimension of the corresponding intertwining space. -/
def restrictionMultiplicity (φ : H →* G)
    (η : IrreducibleCharacter H) (χ : IrreducibleCharacter G) : ℕ :=
  Module.finrank ℂ
    (η.realization ⟶ FDRep.res φ χ.realization)

/-- An irreducible character `χ` lies over `η` along `φ` when the
intertwining multiplicity from `η` to the restriction of `χ` is positive. -/
def LiesOverAlong (φ : H →* G)
    (η : IrreducibleCharacter H) (χ : IrreducibleCharacter G) : Prop :=
  0 < restrictionMultiplicity φ η χ

/-- The irreducible characters of the target group lying over `η` along
`φ`. -/
def IrreducibleCharactersOverAlong (φ : H →* G)
    (η : IrreducibleCharacter H) :=
  {χ : IrreducibleCharacter G // LiesOverAlong φ η χ}

/-- The prime-to-`p` irreducible characters of the target group lying over
`η` along `φ`. -/
def PPrimeIrreducibleCharactersOverAlong (φ : H →* G)
    (η : IrreducibleCharacter H) (p : ℕ) :=
  {χ : IrreducibleCharactersOverAlong φ η //
    χ.1.IsPPrimeDegree p}

/-- Positive restriction multiplicity is equivalent to the existence of a
nonzero intertwiner. -/
theorem liesOverAlong_iff_exists_nonzero (φ : H →* G)
    (η : IrreducibleCharacter H) (χ : IrreducibleCharacter G) :
    LiesOverAlong φ η χ ↔
      ∃ f : η.realization ⟶ FDRep.res φ χ.realization,
        f ≠ 0 := by
  rw [LiesOverAlong, restrictionMultiplicity,
    Module.finrank_pos_iff_exists_ne_zero]

/-- A nonzero morphism out of a simple finite-dimensional representation is
injective on its underlying vector space. -/
theorem fdRepHom_injective_of_nonzero_from_simple
    {V W : FDRep ℂ H} [Simple V]
    (f : V ⟶ W) (hf : f ≠ 0) :
    Function.Injective f := by
  let fRep :=
    (FDRep.forget₂HomLinearEquiv V W).symm f
  have hfRep : fRep.hom ≠ 0 := by
    dsimp [fRep]
    intro h
    apply hf
    apply
      (FDRep.forget₂HomLinearEquiv V W).symm.injective
    apply Rep.Hom.ext
    exact h
  letI :
      Representation.IsIrreducible
        (((forget₂ (FDRep ℂ H) (Rep ℂ H)).obj V).ρ) := by
    rw [FDRep.forget₂_ρ]
    exact
      CliffordRestriction.isIrreducible_of_simple V
  exact
    (Representation.IsIrreducible.injective_or_eq_zero
      fRep.hom).resolve_right hfRep

/-- The multiplicity of an irreducible target representation in an induced
representation, again expressed as a Hom-space dimension. -/
def inductionMultiplicity [Finite G] (φ : H →* G)
    (η : IrreducibleCharacter H) (χ : IrreducibleCharacter G) : ℕ :=
  Module.finrank ℂ
    (FDRep.ind φ η.realization ⟶ χ.realization)

/-- Frobenius reciprocity for finite-dimensional representations.  This is
the `FDRep` form of mathlib's representation-level equivalence. -/
def fdRepInductionRestrictionHomEquiv [Finite G] (φ : H →* G)
    (V : FDRep ℂ H) (W : FDRep ℂ G) :
    (FDRep.ind φ V ⟶ W) ≃ₗ[ℂ]
      (V ⟶ FDRep.res φ W) :=
  (FDRep.forget₂HomLinearEquiv (FDRep.ind φ V) W).symm |>.trans
    ((Rep.indResHomEquiv φ
      ((forget₂ (FDRep ℂ H) (Rep ℂ H)).obj V)
      ((forget₂ (FDRep ℂ G) (Rep ℂ G)).obj W)).trans
        (FDRep.forget₂HomLinearEquiv V (FDRep.res φ W)))

/-- Frobenius reciprocity preserves the exact Hom multiplicity. -/
theorem finrank_induction_hom_eq_restriction_hom [Finite G]
    (φ : H →* G) (V : FDRep ℂ H) (W : FDRep ℂ G) :
    Module.finrank ℂ (FDRep.ind φ V ⟶ W) =
      Module.finrank ℂ (V ⟶ FDRep.res φ W) :=
  (fdRepInductionRestrictionHomEquiv φ V W).finrank_eq

/-- Character-level Frobenius reciprocity: induction multiplicity equals
restriction multiplicity. -/
theorem inductionMultiplicity_eq_restrictionMultiplicity [Finite G]
    (φ : H →* G) (η : IrreducibleCharacter H)
    (χ : IrreducibleCharacter G) :
    inductionMultiplicity φ η χ =
      restrictionMultiplicity φ η χ :=
  finrank_induction_hom_eq_restriction_hom
    φ η.realization χ.realization

/-- An irreducible character occurs in restriction exactly when its
induction has positive Hom multiplicity into the target character. -/
theorem liesOverAlong_iff_inductionMultiplicity_pos [Finite G]
    (φ : H →* G) (η : IrreducibleCharacter H)
    (χ : IrreducibleCharacter G) :
    LiesOverAlong φ η χ ↔
      0 < inductionMultiplicity φ η χ := by
  rw [LiesOverAlong,
    inductionMultiplicity_eq_restrictionMultiplicity]

section Inertia

variable [Fintype G]
variable (N : Subgroup G) [N.Normal]
variable (θ : IrreducibleCharacter N)

/-- The canonical inclusion `N ↪ I_G(θ)`. -/
abbrev inertiaInclusion :
    N →* IrreducibleCharacter.inertia N θ :=
  Subgroup.inclusion
    (IrreducibleCharacter.subgroup_le_inertia N θ)

/-- The multiplicity of `θ` in the restriction of an irreducible
`I_G(θ)`-character. -/
abbrev inertiaRestrictionMultiplicity
    (ψ : IrreducibleCharacter (IrreducibleCharacter.inertia N θ)) : ℕ :=
  restrictionMultiplicity (inertiaInclusion N θ) θ ψ

/-- The irreducible characters of `I_G(θ)` lying over `θ`. -/
abbrev IrreducibleCharactersOverInertia :=
  IrreducibleCharactersOverAlong (inertiaInclusion N θ) θ

/-- The multiplicity of an `N`-character in the restriction of an
irreducible `G`-character. -/
abbrev normalRestrictionMultiplicity
    (η : IrreducibleCharacter N) (χ : IrreducibleCharacter G) : ℕ :=
  restrictionMultiplicity N.subtype η χ

/-- An irreducible `G`-character lies over the ambient conjugacy orbit of
`θ` if its restriction to `N` contains some conjugate of `θ`. -/
def LiesOverOrbit (χ : IrreducibleCharacter G) : Prop :=
  ∃ g : G,
    LiesOverAlong N.subtype
      (IrreducibleCharacter.conjBy N g θ) χ

/-- The irreducible characters of `G` lying over the conjugacy orbit of
`θ`. -/
def IrreducibleCharactersOverOrbit :=
  {χ : IrreducibleCharacter G // LiesOverOrbit N θ χ}

omit [Fintype G] in
/-- Lying over `θ` itself implies lying over its conjugacy orbit. -/
theorem liesOverOrbit_of_liesOver
    {χ : IrreducibleCharacter G}
    (hχ : LiesOverAlong N.subtype θ χ) :
    LiesOverOrbit N θ χ := by
  refine ⟨1, ?_⟩
  simpa using hχ

/-- Induction from the inertia subgroup, at the level of
finite-dimensional representations. -/
abbrev inertiaInduction
    (V : FDRep ℂ (IrreducibleCharacter.inertia N θ)) :
    FDRep ℂ G :=
  FDRep.indSubgroup (IrreducibleCharacter.inertia N θ) V

/-- The exact Frobenius reciprocity equivalence for induction from the
inertia subgroup. -/
abbrev inertiaInductionHomEquiv
    (V : FDRep ℂ (IrreducibleCharacter.inertia N θ))
    (W : FDRep ℂ G) :
    (inertiaInduction N θ V ⟶ W) ≃ₗ[ℂ]
      (V ⟶
        FDRep.resSubgroup
          (IrreducibleCharacter.inertia N θ) W) :=
  fdRepInductionRestrictionHomEquiv
    (IrreducibleCharacter.inertia N θ).subtype V W

/-- The adjunction unit `V ⟶ Res_I^G Ind_I^G V`, written using the explicit
Frobenius reciprocity equivalence above. -/
def inertiaInductionUnit
    (V : FDRep ℂ (IrreducibleCharacter.inertia N θ)) :
    V ⟶
      FDRep.resSubgroup
        (IrreducibleCharacter.inertia N θ)
        (inertiaInduction N θ V) :=
  inertiaInductionHomEquiv N θ V (inertiaInduction N θ V)
    (𝟙 (inertiaInduction N θ V))

omit [Fintype G] in
/-- Restricting first from `G` to the inertia group and then to `N` is the
same as restricting directly from `G` to `N`. -/
theorem res_inertia_res_eq_res_normal (W : FDRep ℂ G) :
    FDRep.res (inertiaInclusion N θ)
        (FDRep.resSubgroup
          (IrreducibleCharacter.inertia N θ) W) =
      FDRep.resSubgroup N W := by
  change
    FDRep.res
        ((IrreducibleCharacter.inertia N θ).subtype.comp
          (inertiaInclusion N θ)) W =
      FDRep.res N.subtype W
  congr 1

/-- The canonical isomorphism implementing transitivity of restriction
through the inertia group. -/
def resInertiaResIsoResNormal (W : FDRep ℂ G) :
    FDRep.res (inertiaInclusion N θ)
        (FDRep.resSubgroup
          (IrreducibleCharacter.inertia N θ) W) ≅
      FDRep.resSubgroup N W :=
  eqToIso (res_inertia_res_eq_res_normal N θ W)

/-- Frobenius reciprocity identifies the multiplicity of `W` in an
induction from `I_G(θ)` with the multiplicity of `V` in `W` restricted to
`I_G(θ)`. -/
theorem inertia_induction_hom_finrank
    (V : FDRep ℂ (IrreducibleCharacter.inertia N θ))
    (W : FDRep ℂ G) :
    Module.finrank ℂ (inertiaInduction N θ V ⟶ W) =
      Module.finrank ℂ
        (V ⟶
          FDRep.resSubgroup
            (IrreducibleCharacter.inertia N θ) W) :=
  (inertiaInductionHomEquiv N θ V W).finrank_eq

/-- The adjunction unit is nonzero whenever the induced representation has
actually been proved simple. -/
theorem inertiaInductionUnit_ne_zero
    (V : FDRep ℂ (IrreducibleCharacter.inertia N θ))
    (hsimple : Simple (inertiaInduction N θ V)) :
    inertiaInductionUnit N θ V ≠ 0 := by
  letI : Simple (inertiaInduction N θ V) := hsimple
  intro hunit
  apply id_nonzero (inertiaInduction N θ V)
  apply
    (inertiaInductionHomEquiv N θ V
      (inertiaInduction N θ V)).injective
  simpa [inertiaInductionUnit] using hunit

/-- A constituent of an inertia-group representation remains a constituent
after inducing that representation to `G`, provided the induction has been
proved simple.  This is the representation-level landing statement used by
the partial character map below. -/
theorem normal_hom_finrank_induction_pos
    (ψ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (hψ : LiesOverAlong (inertiaInclusion N θ) θ ψ)
    (hsimple : Simple (inertiaInduction N θ ψ.realization)) :
    0 <
      Module.finrank ℂ
        (θ.realization ⟶
          FDRep.resSubgroup N
            (inertiaInduction N θ ψ.realization)) := by
  rw [Module.finrank_pos_iff_exists_ne_zero]
  obtain ⟨f, hf⟩ :=
    (liesOverAlong_iff_exists_nonzero
      (inertiaInclusion N θ) θ ψ).mp hψ
  let u :=
    inertiaInductionUnit N θ ψ.realization
  have hu : u ≠ 0 :=
    inertiaInductionUnit_ne_zero N θ ψ.realization hsimple
  let uN :=
    (FDRep.resFunctor (k := ℂ)
      (inertiaInclusion N θ)).map u
  let composite :
      θ.realization ⟶
        FDRep.resSubgroup N
          (inertiaInduction N θ ψ.realization) :=
    f ≫ uN ≫
      (resInertiaResIsoResNormal N θ
        (inertiaInduction N θ ψ.realization)).hom
  haveI : Mono f :=
    mono_of_nonzero_from_simple hf
  have hu_injective : Function.Injective u :=
    fdRepHom_injective_of_nonzero_from_simple u hu
  haveI : Mono uN := by
    apply ConcreteCategory.mono_of_injective
    intro x y hxy
    apply hu_injective
    exact hxy
  haveI : Mono (f ≫ uN) :=
    mono_comp f uN
  haveI : Mono composite := by
    dsimp [composite]
    exact
      mono_comp (f ≫ uN)
        (resInertiaResIsoResNormal N θ
          (inertiaInduction N θ ψ.realization)).hom
  refine ⟨composite, ?_⟩
  intro hzero
  apply id_nonzero θ.realization
  apply (cancel_mono composite).mp
  simp [hzero]

/-- The character of representation induction from the inertia subgroup is
the classical induced class function. -/
theorem inertiaInduction_character
    (V : FDRep ℂ (IrreducibleCharacter.inertia N θ)) :
    (inertiaInduction N θ V).characterClassFunction =
      ClassFunction.induce
        (IrreducibleCharacter.inertia N θ)
        V.characterClassFunction :=
  InductionCharacter.ind_characterClassFunction_eq_induce
    (IrreducibleCharacter.inertia N θ) V

/-- Exact dimension formula for induction from the inertia subgroup. -/
theorem inertiaInduction_finrank
    (V : FDRep ℂ (IrreducibleCharacter.inertia N θ)) :
    Module.finrank ℂ (inertiaInduction N θ V) =
      (IrreducibleCharacter.inertia N θ).index *
        Module.finrank ℂ V := by
  apply Nat.cast_injective (R := ℂ)
  calc
    (Module.finrank ℂ (inertiaInduction N θ V) : ℂ) =
        (inertiaInduction N θ V).character 1 := by
      rw [FDRep.char_one]
    _ =
        ClassFunction.induce
          (IrreducibleCharacter.inertia N θ)
          V.characterClassFunction 1 :=
      InductionCharacter.ind_character_eq_induce
        (IrreducibleCharacter.inertia N θ) V 1
    _ =
        ((IrreducibleCharacter.inertia N θ).index : ℂ) *
          Module.finrank ℂ V :=
      ClassFunction.induce_character_apply_one
        (IrreducibleCharacter.inertia N θ) V
    _ =
        (((IrreducibleCharacter.inertia N θ).index *
          Module.finrank ℂ V : ℕ) : ℂ) := by
      push_cast
      rfl

/-- Package the induction of an irreducible inertia-group character as an
irreducible character of `G` once irreducibility of that particular induced
representation has actually been proved.

The `Simple` argument is precisely the local conclusion supplied by the
missing Clifford--Mackey irreducibility lemma; no global correspondence
hypothesis is stored in this construction. -/
def inducedIrreducibleCharacter
    (ψ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (hsimple : Simple (inertiaInduction N θ ψ.realization)) :
    IrreducibleCharacter G where
  values := (inertiaInduction N θ ψ.realization).character
  degree :=
    (IrreducibleCharacter.inertia N θ).index * ψ.degree
  isIrreducible := by
    refine ⟨inertiaInduction N θ ψ.realization, hsimple, rfl, ?_⟩
    rw [inertiaInduction_finrank, ψ.realization_finrank]

/-- If `ψ` lies over `θ`, then a verified-simple induction of `ψ` lies over
`θ` (and hence over its orbit).  The proof first uses the adjunction-unit
map for the concrete induced representation and then transports along
character determination to the chosen realization of the packaged
irreducible character. -/
theorem inducedIrreducibleCharacter_liesOver
    (ψ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (hψ : LiesOverAlong (inertiaInclusion N θ) θ ψ)
    (hsimple : Simple (inertiaInduction N θ ψ.realization)) :
    LiesOverAlong N.subtype θ
      (inducedIrreducibleCharacter N θ ψ hsimple) := by
  let χ :=
    inducedIrreducibleCharacter N θ ψ hsimple
  have hpositive :
      0 <
        Module.finrank ℂ
          (θ.realization ⟶
            FDRep.resSubgroup N
              (inertiaInduction N θ ψ.realization)) :=
    normal_hom_finrank_induction_pos N θ ψ hψ hsimple
  rw [Module.finrank_pos_iff_exists_ne_zero] at hpositive
  obtain ⟨f, hf⟩ := hpositive
  letI : Simple (inertiaInduction N θ ψ.realization) :=
    hsimple
  have hcharacter :
      (inertiaInduction N θ ψ.realization).character =
        χ.realization.character := by
    rw [χ.realization_character]
    rfl
  obtain ⟨e⟩ :=
    FDRep.nonempty_iso_of_character_eq
      (inertiaInduction N θ ψ.realization)
      χ.realization hcharacter
  let eN :=
    (FDRep.resSubgroupFunctor (k := ℂ) N).map e.hom
  let composite :
      θ.realization ⟶
        FDRep.resSubgroup N χ.realization :=
    f ≫ eN
  haveI : Mono f :=
    mono_of_nonzero_from_simple hf
  haveI : Mono eN := by
    dsimp [eN]
    infer_instance
  haveI : Mono composite := by
    dsimp [composite]
    exact mono_comp f eN
  rw [LiesOverAlong, restrictionMultiplicity,
    Module.finrank_pos_iff_exists_ne_zero]
  refine ⟨composite, ?_⟩
  intro hzero
  apply id_nonzero θ.realization
  apply (cancel_mono composite).mp
  simp [hzero]

@[simp]
theorem inducedIrreducibleCharacter_values
    (ψ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (hsimple : Simple (inertiaInduction N θ ψ.realization)) :
    (inducedIrreducibleCharacter N θ ψ hsimple).values =
      (inertiaInduction N θ ψ.realization).character :=
  rfl

@[simp]
theorem inducedIrreducibleCharacter_degree
    (ψ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (hsimple : Simple (inertiaInduction N θ ψ.realization)) :
    (inducedIrreducibleCharacter N θ ψ hsimple).degree =
      (IrreducibleCharacter.inertia N θ).index * ψ.degree :=
  rfl

/-- The packaged irreducible character is exactly the classical induction
of `ψ`, as a class function. -/
theorem inducedIrreducibleCharacter_toClassFunction
    (ψ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (hsimple : Simple (inertiaInduction N θ ψ.realization)) :
    (inducedIrreducibleCharacter N θ ψ hsimple).toClassFunction =
      ClassFunction.induce
        (IrreducibleCharacter.inertia N θ)
        ψ.toClassFunction := by
  calc
    (inducedIrreducibleCharacter N θ ψ hsimple).toClassFunction =
        (inertiaInduction N θ
          ψ.realization).characterClassFunction := by
      ext g
      rfl
    _ =
        ClassFunction.induce
          (IrreducibleCharacter.inertia N θ)
          ψ.realization.characterClassFunction :=
      inertiaInduction_character N θ ψ.realization
    _ =
        ClassFunction.induce
          (IrreducibleCharacter.inertia N θ)
          ψ.toClassFunction := by
      congr 1
      ext i
      change ψ.realization.character i = ψ.values i
      exact congrFun ψ.realization_character i

/-- The exact index factor in the degree of the packaged induced
irreducible character. -/
theorem induced_degree_eq_index_mul
    (ψ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (hsimple : Simple (inertiaInduction N θ ψ.realization)) :
    (inducedIrreducibleCharacter N θ ψ hsimple).degree =
      (IrreducibleCharacter.inertia N θ).index * ψ.degree :=
  rfl

/-- The part of `Irr(I_G(θ) | θ)` on which induction has already been
proved irreducible.  This subtype records a theorem about each individual
induced representation, rather than postulating a correspondence. -/
def SimpleInducibleCharactersOverInertia :=
  {ψ : IrreducibleCharactersOverInertia N θ //
    Simple
      (inertiaInduction N θ ψ.1.realization)}

/-- Induction gives an honest irreducible `G`-character on the verified
simple-induction domain. -/
def induceSimpleOverInertia
    (ψ : SimpleInducibleCharactersOverInertia N θ) :
    IrreducibleCharacter G :=
  inducedIrreducibleCharacter N θ ψ.1.1 ψ.2

/-- The verified-simple induction map with its mathematically correct
codomain `Irr(G | G • θ)`. -/
def induceSimpleOverInertiaOrbit
    (ψ : SimpleInducibleCharactersOverInertia N θ) :
    IrreducibleCharactersOverOrbit N θ :=
  ⟨induceSimpleOverInertia N θ ψ,
    liesOverOrbit_of_liesOver N θ
      (inducedIrreducibleCharacter_liesOver
        N θ ψ.1.1 ψ.1.2 ψ.2)⟩

@[simp]
theorem induceSimpleOverInertia_degree
    (ψ : SimpleInducibleCharactersOverInertia N θ) :
    (induceSimpleOverInertia N θ ψ).degree =
      (IrreducibleCharacter.inertia N θ).index *
        ψ.1.1.degree :=
  rfl

@[simp]
theorem induceSimpleOverInertiaOrbit_degree
    (ψ : SimpleInducibleCharactersOverInertia N θ) :
    (induceSimpleOverInertiaOrbit N θ ψ).1.degree =
      (IrreducibleCharacter.inertia N θ).index *
        ψ.1.1.degree :=
  rfl

/-- The character produced on the verified domain is classical character
induction. -/
theorem induceSimpleOverInertia_toClassFunction
    (ψ : SimpleInducibleCharactersOverInertia N θ) :
    (induceSimpleOverInertia N θ ψ).toClassFunction =
      ClassFunction.induce
        (IrreducibleCharacter.inertia N θ)
        ψ.1.1.toClassFunction :=
  inducedIrreducibleCharacter_toClassFunction N θ ψ.1.1 ψ.2

end Inertia

end CliffordCorrespondence

end McKayConjecture
