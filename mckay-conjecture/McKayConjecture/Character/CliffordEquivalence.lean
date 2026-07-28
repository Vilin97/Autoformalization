/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordCorrespondence
import McKayConjecture.Character.Construction
import McKayConjecture.Character.Mackey
import McKayConjecture.Character.Transport
import Mathlib.RepresentationTheory.FinGroupCharZero

/-!
# The Clifford correspondence equivalence

This file proves the irreducible-character Clifford correspondence between
the inertia subgroup of a constituent and the ambient group.  The proof is
organized around the isotypic component belonging to the fixed constituent
and the Mackey decomposition of restriction after induction.
-/

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra

namespace McKayConjecture

namespace CliffordEquivalence

open CliffordCorrespondence

universe u

variable {G K : Type} [Group G] [Group K]

/-- A product of copies of a simple module is isotypic of that simple
module. -/
theorem pi_isIsotypicOfType
    {R S ι : Type*} [Ring R]
    [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    IsIsotypicOfType R (ι → S) S := by
  classical
  intro T _
  letI : Nontrivial T := IsSimpleModule.nontrivial R T
  obtain ⟨x, hx⟩ := exists_ne (0 : T)
  have hcoord : ∃ i : ι, x.1 i ≠ 0 := by
    by_contra h
    rw [not_exists] at h
    apply hx
    apply Subtype.ext
    funext i
    exact not_ne_iff.mp (h i)
  obtain ⟨i, hi⟩ := hcoord
  let p : T →ₗ[R] S :=
    (LinearMap.proj i).comp T.subtype
  have hp : p ≠ 0 := by
    intro hp
    have happ := LinearMap.congr_fun hp x
    change x.1 i = 0 at happ
    exact hi happ
  exact
    ⟨LinearEquiv.ofBijective p
      ((LinearMap.bijective_or_eq_zero p).resolve_right hp)⟩

/-- The range of a map out of a semisimple isotypic module is isotypic of
the same type. -/
theorem isIsotypicOfType_range
    {R M P S : Type*} [Ring R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P]
    [AddCommGroup S] [Module R S]
    [IsSemisimpleModule R M]
    (hM : IsIsotypicOfType R M S)
    (f : M →ₗ[R] P) :
    IsIsotypicOfType R (LinearMap.range f) S := by
  intro T _
  obtain ⟨lift, hlift⟩ :=
    IsSemisimpleModule.lifting_property
      f.rangeRestrict
        (LinearMap.range_eq_top.mp f.range_rangeRestrict)
        T.subtype
  have hlift_injective : Function.Injective lift := by
    intro x y hxy
    apply T.subtype_injective
    calc
      T.subtype x = f.rangeRestrict (lift x) :=
        (LinearMap.congr_fun hlift x).symm
      _ = f.rangeRestrict (lift y) := congrArg f.rangeRestrict hxy
      _ = T.subtype y := LinearMap.congr_fun hlift y
  let E : T ≃ₗ[R] LinearMap.range lift :=
    LinearEquiv.ofInjective lift hlift_injective
  letI : IsSimpleModule R (LinearMap.range lift) :=
    IsSimpleModule.congr E.symm
  exact ⟨E.trans (hM (LinearMap.range lift)).some⟩

/-- There is no nonzero map between semisimple isotypic modules of
nonisomorphic simple types. -/
theorem linearMap_eq_zero_of_isotypic_types
    {R M P S T : Type*} [Ring R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P]
    [AddCommGroup S] [Module R S] [IsSimpleModule R S]
    [AddCommGroup T] [Module R T] [IsSimpleModule R T]
    [IsSemisimpleModule R M]
    (hM : IsIsotypicOfType R M S)
    (hP : IsIsotypicOfType R P T)
    (hST : ¬Nonempty (S ≃ₗ[R] T))
    (f : M →ₗ[R] P) :
    f = 0 := by
  by_contra hf
  have hrange : LinearMap.range f ≠ ⊥ := by
    exact fun h => hf (LinearMap.range_eq_bot.mp h)
  letI : Nontrivial (LinearMap.range f) :=
    Submodule.nontrivial_iff_ne_bot.mpr hrange
  letI : IsSemisimpleModule R (LinearMap.range f) :=
    IsSemisimpleModule.range f
  obtain ⟨U, hU⟩ :=
    IsSemisimpleModule.exists_simple_submodule
      R (LinearMap.range f)
  letI : IsSimpleModule R U := hU
  have hUS :
      Nonempty (U ≃ₗ[R] S) :=
    isIsotypicOfType_range hM f U
  have hUT :
      Nonempty (U ≃ₗ[R] T) :=
    (hP.of_injective (LinearMap.range f).subtype
      (LinearMap.range f).subtype_injective) U
  exact hST ⟨hUS.some.symm.trans hUT.some⟩

/-- The ordinary dependent-function representation with componentwise
action.  Unlike Mackey's finite-product carrier, this construction is used
only as a convenient target for homogeneous decompositions. -/
def functionRepresentation
    {k L ι : Type*} [Field k] [Monoid L]
    {M : ι → Type*}
    [(i : ι) → AddCommGroup (M i)]
    [(i : ι) → Module k (M i)]
    (ρ : (i : ι) → Representation k L (M i)) :
    Representation k L ((i : ι) → M i) where
  toFun g := LinearMap.pi fun i => ρ i g ∘ₗ LinearMap.proj i
  map_one' := by
    ext x i
    simp
  map_mul' g h := by
    ext x i
    change ρ i (g * h) (x i) = ρ i g (ρ i h (x i))
    rw [map_mul]
    rfl

/-- Projection from a componentwise function representation to one
component. -/
def functionRepresentationProj
    {k L ι : Type*} [Field k] [Monoid L]
    {M : ι → Type*}
    [(i : ι) → AddCommGroup (M i)]
    [(i : ι) → Module k (M i)]
    (ρ : (i : ι) → Representation k L (M i))
    (i : ι) :
    (functionRepresentation ρ).IntertwiningMap (ρ i) where
  toLinearMap := LinearMap.proj i
  isIntertwining' g := by
    ext x
    rfl

/-- A componentwise function representation made from copies of a simple
representation is isotypic of that representation at the group-algebra
module level. -/
theorem functionRepresentation_isIsotypicOfType
    {k L S ι : Type*} [Field k] [Group L]
    [AddCommGroup S] [Module k S]
    (ρ : Representation k L S)
    [IsSimpleModule k[L] ρ.asModule] :
    IsIsotypicOfType k[L]
      (functionRepresentation (fun _ : ι => ρ)).asModule
      ρ.asModule := by
  classical
  intro T hT
  letI : IsSimpleModule k[L] T := hT
  letI : Nontrivial T := IsSimpleModule.nontrivial k[L] T
  obtain ⟨x, hx⟩ := exists_ne (0 : T)
  have hcoord :
      ∃ i : ι,
        ((functionRepresentation (fun _ : ι => ρ)).asModuleEquiv
          x.1) i ≠ 0 := by
    by_contra h
    rw [not_exists] at h
    apply hx
    apply Subtype.ext
    apply
      (functionRepresentation (fun _ : ι => ρ)).asModuleEquiv.injective
    funext i
    exact not_ne_iff.mp (h i)
  obtain ⟨i, hi⟩ := hcoord
  let p₀ :
      (functionRepresentation (fun _ : ι => ρ)).asModule →ₗ[k[L]]
        ρ.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule
      (functionRepresentation (fun _ : ι => ρ))
      ρ
      (functionRepresentationProj (fun _ : ι => ρ) i)
  let p : T →ₗ[k[L]] ρ.asModule :=
    p₀.comp T.subtype
  have hp : p ≠ 0 := by
    intro hp
    have happ := LinearMap.congr_fun hp x
    change
      ((functionRepresentation (fun _ : ι => ρ)).asModuleEquiv
        x.1) i = 0 at happ
    exact hi happ
  have hρsimple :
      IsSimpleModule k[L] ρ.asModule :=
    inferInstance
  have hpbijective : Function.Bijective p :=
    @LinearMap.bijective_of_ne_zero
      k[L] inferInstance
      T inferInstance inferInstance
      ρ.asModule inferInstance inferInstance
      hT hρsimple p hp
  exact
    ⟨LinearEquiv.ofBijective p hpbijective⟩

/-- A representation equivalence induces the corresponding equivalence of
group-algebra modules. -/
def representationEquivAsModule
    {k L M P : Type*} [Field k] [Group L]
    [AddCommGroup M] [Module k M]
    [AddCommGroup P] [Module k P]
    {ρ : Representation k L M}
    {σ : Representation k L P}
    (e : ρ.Equiv σ) :
    ρ.asModule ≃ₗ[k[L]] σ.asModule :=
  LinearEquiv.ofBijective
    (Representation.IntertwiningMap.equivLinearMapAsModule
      ρ σ e.toIntertwiningMap)
    e.toLinearEquiv.bijective

/-- A group-algebra linear equivalence induces an equivalence of the
corresponding representations. -/
def representationEquivOfModuleLinearEquiv
    {k L M P : Type*} [Field k] [Group L]
    [AddCommGroup M] [Module k M]
    [AddCommGroup P] [Module k P]
    {ρ : Representation k L M}
    {σ : Representation k L P}
    (e : ρ.asModule ≃ₗ[k[L]] σ.asModule) :
    ρ.Equiv σ :=
  ((Representation.IntertwiningMap.equivLinearMapAsModule
    ρ σ).symm e.toLinearMap).ofBijective e.bijective

/-- Restrict an intertwining map along a group homomorphism. -/
def restrictIntertwiningMap
    {k A B L M : Type*} [Field k]
    [Monoid A] [Monoid B]
    [AddCommGroup L] [Module k L]
    [AddCommGroup M] [Module k M]
    {ρ : Representation k A L}
    {σ : Representation k A M}
    (φ : B →* A)
    (f : ρ.IntertwiningMap σ) :
    Representation.IntertwiningMap (ρ.comp φ) (σ.comp φ) where
  toLinearMap := f.toLinearMap
  isIntertwining' b := f.isIntertwining' (φ b)

/-- Frobenius reciprocity for coinduction, in the unbundled
`IntertwiningMap` API. -/
def homCoinductionRestrictionEquiv
    {k A B M P : Type u} [Field k]
    [Monoid A] [Monoid B]
    [AddCommGroup M] [Module k M]
    [AddCommGroup P] [Module k P]
    (φ : B →* A)
    (ρ : Representation k A M)
    (σ : Representation k B P) :
    ρ.IntertwiningMap (Representation.coind φ σ) ≃ₗ[k]
      Representation.IntertwiningMap (ρ.comp φ) σ :=
  (Rep.homLinearEquiv
      (Rep.of ρ) (Rep.of (Representation.coind φ σ))).symm |>.trans
    ((Rep.resCoindHomEquiv φ (Rep.of ρ) (Rep.of σ)).symm |>.trans
      (Rep.homLinearEquiv
        (Rep.res φ (Rep.of ρ)) (Rep.of σ)))

/-- Restriction along a homomorphism does not change the underlying vector
space. -/
def restrictionAlongCarrierLinearEquiv
    {L K : Type*} [Monoid L] [Monoid K]
    (φ : L →* K) (V : FDRep ℂ K) :
    FDRep.res φ V ≃ₗ[ℂ] V :=
  FGModuleCat.isoToLinearEquiv
    (eqToIso (FDRep.res_V φ V))

@[simp]
theorem restrictionAlongCarrierLinearEquiv_apply
    {L K : Type*} [Monoid L] [Monoid K]
    (φ : L →* K) (V : FDRep ℂ K)
    (v : FDRep.res φ V) :
    restrictionAlongCarrierLinearEquiv φ V v =
      (show V from v) :=
  rfl

@[simp]
theorem restrictionAlongCarrierLinearEquiv_symm_apply
    {L K : Type*} [Monoid L] [Monoid K]
    (φ : L →* K) (V : FDRep ℂ K)
    (v : V) :
    (restrictionAlongCarrierLinearEquiv φ V).symm v =
      (show FDRep.res φ V from v) :=
  rfl

/-- The carrier identification for restriction is an equivalence from the
bundled restricted representation to the same restricted action on the
original carrier. -/
def restrictionAlongRepresentationEquiv
    {L K : Type*} [Monoid L] [Monoid K]
    (φ : L →* K) (V : FDRep ℂ K) :
    Representation.Equiv
      (FDRep.res φ V).ρ (V.ρ.comp φ) :=
  Representation.Equiv.mk
    (restrictionAlongCarrierLinearEquiv φ V)
    (fun _ => rfl)

/-- Twisting an isotypic representation by a group automorphism twists its
simple type by the same automorphism. -/
theorem twist_isIsotypicOfType
    {L : Type*} [Group L]
    (e : L ≃* L)
    (U S : FDRep ℂ L) [Simple S]
    [IsSemisimpleModule ℂ[L] (Representation.asModule U.ρ)]
    (hU : IsIsotypicOfType ℂ[L]
      (Representation.asModule U.ρ)
      (Representation.asModule S.ρ)) :
    IsIsotypicOfType ℂ[L]
      (Representation.asModule (FDRep.res (e : L →* L) U).ρ)
      (Representation.asModule (FDRep.res (e : L →* L) S).ρ) := by
  letI : Module.Finite ℂ[L] (Representation.asModule U.ρ) :=
    Module.Finite.of_restrictScalars_finite
      ℂ ℂ[L] (Representation.asModule U.ρ)
  obtain ⟨n, ⟨E⟩⟩ := hU.linearEquiv_fun
  let sourceCarrierToModule :
      FDRep.res (e : L →* L) U ≃ₗ[ℂ]
        Representation.asModule U.ρ :=
    (restrictionAlongCarrierLinearEquiv (e : L →* L) U).trans
      (Representation.asModuleEquiv U.ρ).symm
  let coordinate :
      Representation.asModule S.ρ ≃ₗ[ℂ]
        FDRep.res (e : L →* L) S :=
    (Representation.asModuleEquiv S.ρ).trans
      (restrictionAlongCarrierLinearEquiv (e : L →* L) S).symm
  let target :=
    functionRepresentation
      (fun _ : Fin n => (FDRep.res (e : L →* L) S).ρ)
  let carrierEquiv :
      FDRep.res (e : L →* L) U ≃ₗ[ℂ]
        (Fin n → FDRep.res (e : L →* L) S) :=
    sourceCarrierToModule.trans
      ((E.restrictScalars ℂ).trans
        (LinearEquiv.piCongrRight fun _ : Fin n => coordinate))
  let repEquiv :
      Representation.Equiv
        (FDRep.res (e : L →* L) U).ρ target := by
    apply Representation.Equiv.mk carrierEquiv
    intro a
    ext v i
    let vU : U :=
      restrictionAlongCarrierLinearEquiv
        (e : L →* L) U v
    let u : Representation.asModule U.ρ :=
      (Representation.asModuleEquiv U.ρ).symm
        vU
    have hE :=
      E.map_smul (MonoidAlgebra.of ℂ L (e a)) u
    change
      (Representation.asModuleEquiv S.ρ)
          (E ((Representation.asModuleEquiv U.ρ).symm
            (U.ρ (e a) vU)) i) =
        S.ρ (e a)
          ((Representation.asModuleEquiv S.ρ)
            (E ((Representation.asModuleEquiv U.ρ).symm vU) i))
    rw [Representation.asModuleEquiv_symm_map_rho]
    calc
      (Representation.asModuleEquiv S.ρ)
          (E ((MonoidAlgebra.of ℂ L) (e a) • u) i) =
        (Representation.asModuleEquiv S.ρ)
          (((MonoidAlgebra.of ℂ L) (e a) • E u) i) :=
        congrArg
          (fun z => (Representation.asModuleEquiv S.ρ) (z i))
          hE
      _ =
        (Representation.asModuleEquiv S.ρ)
          ((MonoidAlgebra.of ℂ L) (e a) • E u i) := by
        rfl
      _ =
        S.ρ (e a)
          ((Representation.asModuleEquiv S.ρ) (E u i)) := by
        rw [Representation.asModuleEquiv_map_smul,
          Representation.asAlgebraHom_of]
  letI : Simple (FDRep.res (e : L →* L) S) :=
    FDRep.simple_res_mulEquiv e S
  haveI :
      Representation.IsIrreducible
        (FDRep.res (e : L →* L) S).ρ :=
    CliffordRestriction.isIrreducible_of_simple
      (FDRep.res (e : L →* L) S)
  haveI :
      IsSimpleModule ℂ[L]
        (Representation.asModule
          (FDRep.res (e : L →* L) S).ρ) :=
    (Representation.irreducible_iff_isSimpleModule_asModule
      (FDRep.res (e : L →* L) S).ρ).mp inferInstance
  have htarget :
      IsIsotypicOfType ℂ[L] (Representation.asModule target)
        (Representation.asModule
          (FDRep.res (e : L →* L) S).ρ) :=
    functionRepresentation_isIsotypicOfType
      (FDRep.res (e : L →* L) S).ρ
  exact
    (representationEquivAsModule repEquiv).isIsotypicOfType_iff.mpr
      htarget

/-- The group-algebra linear map underlying an intertwiner into a restricted
representation. -/
def restrictionHomAsModule
    (N : Subgroup K)
    (θ : IrreducibleCharacter N)
    (V : FDRep ℂ K)
    (f : θ.realization ⟶ FDRep.resSubgroup N V) :
    Representation.asModule θ.realization.ρ →ₗ[ℂ[N]]
      Representation.asModule (FDRep.resSubgroup N V).ρ :=
  Representation.IntertwiningMap.equivLinearMapAsModule
    θ.realization.ρ (FDRep.resSubgroup N V).ρ
    (((FDRep.forget₂HomLinearEquiv
      θ.realization (FDRep.resSubgroup N V)).symm f).hom)

/-- The simple submodule of a restriction which is the image of a nonzero
constituent map. -/
def constituentSubmodule
    (N : Subgroup K)
    (θ : IrreducibleCharacter N)
    (V : FDRep ℂ K)
    (f : θ.realization ⟶ FDRep.resSubgroup N V) :
    Submodule ℂ[N]
      (Representation.asModule (FDRep.resSubgroup N V).ρ) :=
  LinearMap.range (restrictionHomAsModule N θ V f)

/-- A nonzero constituent map is injective at the group-algebra module
level. -/
theorem restrictionHomAsModule_injective
    (N : Subgroup K)
    (θ : IrreducibleCharacter N)
    (V : FDRep ℂ K)
    (f : θ.realization ⟶ FDRep.resSubgroup N V)
    (hf : f ≠ 0) :
    Function.Injective (restrictionHomAsModule N θ V f) := by
  exact fdRepHom_injective_of_nonzero_from_simple f hf

/-- The constituent image is linearly equivalent to the chosen realization
of its irreducible character. -/
def realizationEquivConstituentSubmodule
    (N : Subgroup K)
    (θ : IrreducibleCharacter N)
    (V : FDRep ℂ K)
    (f : θ.realization ⟶ FDRep.resSubgroup N V)
    (hf : f ≠ 0) :
    Representation.asModule θ.realization.ρ ≃ₗ[ℂ[N]]
      constituentSubmodule N θ V f :=
  LinearEquiv.ofInjective
    (restrictionHomAsModule N θ V f)
    (restrictionHomAsModule_injective N θ V f hf)

/-- The constituent image of a nonzero map from an irreducible
representation is a simple group-algebra module. -/
theorem constituentSubmodule_isSimpleModule
    (N : Subgroup K)
    (θ : IrreducibleCharacter N)
    (V : FDRep ℂ K)
    (f : θ.realization ⟶ FDRep.resSubgroup N V)
    (hf : f ≠ 0) :
    IsSimpleModule ℂ[N] (constituentSubmodule N θ V f) := by
  haveI : Representation.IsIrreducible θ.realization.ρ :=
    CliffordRestriction.isIrreducible_of_simple θ.realization
  haveI :
      IsSimpleModule ℂ[N]
        (Representation.asModule θ.realization.ρ) :=
    (Representation.irreducible_iff_isSimpleModule_asModule
      θ.realization.ρ).mp inferInstance
  exact IsSimpleModule.congr
    (realizationEquivConstituentSubmodule N θ V f hf).symm

section Normal

variable [Finite K]
variable (N : Subgroup K) [N.Normal]

/-- The canonical linear identification between the carrier of a restricted
representation and the carrier of the original representation. -/
def restrictionCarrierLinearEquiv (V : FDRep ℂ K) :
    FDRep.resSubgroup N V ≃ₗ[ℂ] V :=
  restrictionAlongCarrierLinearEquiv N.subtype V

/-- The realization of `θ` twisted by conjugation with `a`. -/
abbrev conjugateRealization (a : K)
    (θ : IrreducibleCharacter N) : FDRep ℂ N :=
  FDRep.res
    ((MulAut.conjNormal (H := N) a).symm : N →* N)
    θ.realization

/-- The twisted realization has the conjugate irreducible character. -/
theorem conjugateRealization_character (a : K)
    (θ : IrreducibleCharacter N) :
    (conjugateRealization N a θ).character =
      (IrreducibleCharacter.conjBy N a θ).values := by
  funext n
  change θ.realization.character
      ((MulAut.conjNormal (H := N) a).symm n) =
    θ.values ((MulAut.conjNormal (H := N) a).symm n)
  exact congrFun θ.realization_character _

/-- The chosen realization of a conjugate character is isomorphic to the
explicitly twisted realization. -/
def conjugateCharacterRealizationIsoCore (a : K)
    (θ : IrreducibleCharacter N) :
    (IrreducibleCharacter.conjBy N a θ).realization ≅
      conjugateRealization N a θ := by
  letI : Simple (conjugateRealization N a θ) :=
    FDRep.simple_res_mulEquiv
      (MulAut.conjNormal (H := N) a).symm
      θ.realization
  apply Classical.choice
  apply FDRep.nonempty_iso_of_character_eq
  rw [(IrreducibleCharacter.conjBy N a θ).realization_character,
    conjugateRealization_character]

/-- Conjugate a constituent map back to the original character.  The
ambient action by `a⁻¹` transports a map from the `a`-conjugate constituent
to a map from the fixed constituent. -/
def deconjugatedRestrictionHom
    (θ : IrreducibleCharacter N)
    (V : FDRep ℂ K)
    (a : K)
    (f :
      (IrreducibleCharacter.conjBy N a θ).realization ⟶
        FDRep.resSubgroup N V) :
    θ.realization ⟶ FDRep.resSubgroup N V := by
  let fTwisted :
      conjugateRealization N a θ ⟶ FDRep.resSubgroup N V :=
    (conjugateCharacterRealizationIsoCore N a θ).inv ≫ f
  let sourceCarrier :
      conjugateRealization N a θ ≃ₗ[ℂ] θ.realization :=
    restrictionAlongCarrierLinearEquiv
      ((MulAut.conjNormal (H := N) a).symm : N →* N)
      θ.realization
  let targetCarrier :
      FDRep.resSubgroup N V ≃ₗ[ℂ] V :=
    restrictionCarrierLinearEquiv N V
  let fLinear :
      conjugateRealization N a θ →ₗ[ℂ] FDRep.resSubgroup N V :=
    ((forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)).map
      fTwisted.hom).hom
  let L : θ.realization →ₗ[ℂ] FDRep.resSubgroup N V :=
    targetCarrier.symm.toLinearMap.comp
      ((V.ρ a⁻¹).comp
        (targetCarrier.toLinearMap.comp
          (fLinear.comp sourceCarrier.symm.toLinearMap)))
  refine
    { hom := FGModuleCat.ofHom L
      comm := ?_ }
  intro n
  apply FGModuleCat.hom_ext
  ext v
  change
    targetCarrier.symm
        (V.ρ a⁻¹
          (targetCarrier
            (fLinear
              (sourceCarrier.symm
                (θ.realization.ρ n v))))) =
      V.ρ (n : N)
        (targetCarrier.symm
          (V.ρ a⁻¹
            (targetCarrier
              (fLinear (sourceCarrier.symm v)))))
  let m : N := MulAut.conjNormal (H := N) a n
  have hsource :
      sourceCarrier.symm (θ.realization.ρ n v) =
        (conjugateRealization N a θ).ρ m
          (sourceCarrier.symm v) := by
    apply sourceCarrier.injective
    change
      θ.realization.ρ n v =
        θ.realization.ρ
          ((MulAut.conjNormal (H := N) a).symm m) v
    simp [m]
  have hf :
      targetCarrier
          (fLinear
            ((conjugateRealization N a θ).ρ m
              (sourceCarrier.symm v))) =
        V.ρ (m : N)
          (targetCarrier
            (fLinear (sourceCarrier.symm v))) := by
    change
      (show V from
        fTwisted
          ((conjugateRealization N a θ).ρ m
            (sourceCarrier.symm v))) =
        V.ρ ((m : N) : K)
          (show V from
            fTwisted (sourceCarrier.symm v))
    exact ConcreteCategory.congr_hom
      (fTwisted.comm m) (sourceCarrier.symm v)
  rw [hsource, hf]
  apply targetCarrier.symm.injective
  change
    V.ρ a⁻¹
        (V.ρ (m : K)
          (targetCarrier (fLinear (sourceCarrier.symm v)))) =
      V.ρ (n : K)
        (V.ρ a⁻¹
          (targetCarrier (fLinear (sourceCarrier.symm v))))
  rw [← Module.End.mul_apply, ← Module.End.mul_apply,
    ← map_mul, ← map_mul]
  have hgroup : a⁻¹ * (m : K) = (n : K) * a⁻¹ := by
    change a⁻¹ * (a * (n : K) * a⁻¹) = (n : K) * a⁻¹
    group
  rw [hgroup]

/-- Conjugating a nonzero constituent map back to the fixed constituent
preserves nonzeroness. -/
theorem deconjugatedRestrictionHom_ne_zero
    (θ : IrreducibleCharacter N)
    (V : FDRep ℂ K)
    (a : K)
    (f :
      (IrreducibleCharacter.conjBy N a θ).realization ⟶
        FDRep.resSubgroup N V)
    (hf : f ≠ 0) :
    deconjugatedRestrictionHom N θ V a f ≠ 0 := by
  let fTwisted :
      conjugateRealization N a θ ⟶ FDRep.resSubgroup N V :=
    (conjugateCharacterRealizationIsoCore N a θ).inv ≫ f
  have hfTwisted : fTwisted ≠ 0 := by
    intro hzero
    apply hf
    have hrecover :
        (conjugateCharacterRealizationIsoCore N a θ).hom ≫
            fTwisted =
          f := by
      simp [fTwisted]
    rw [← hrecover, hzero]
    simp
  letI : Simple (conjugateRealization N a θ) :=
    FDRep.simple_res_mulEquiv
      (MulAut.conjNormal (H := N) a).symm
      θ.realization
  have hf_injective : Function.Injective fTwisted :=
    fdRepHom_injective_of_nonzero_from_simple
      fTwisted hfTwisted
  let sourceCarrier :
      conjugateRealization N a θ ≃ₗ[ℂ] θ.realization :=
    restrictionAlongCarrierLinearEquiv
      ((MulAut.conjNormal (H := N) a).symm : N →* N)
      θ.realization
  let targetCarrier :
      FDRep.resSubgroup N V ≃ₗ[ℂ] V :=
    restrictionCarrierLinearEquiv N V
  have hmap_injective :
      Function.Injective
        (deconjugatedRestrictionHom N θ V a f) := by
    intro x y hxy
    dsimp [deconjugatedRestrictionHom] at hxy
    change
      targetCarrier.symm
          (V.ρ a⁻¹
            (targetCarrier
              (fTwisted (sourceCarrier.symm x)))) =
        targetCarrier.symm
          (V.ρ a⁻¹
            (targetCarrier
              (fTwisted (sourceCarrier.symm y)))) at hxy
    apply sourceCarrier.symm.injective
    apply hf_injective
    apply targetCarrier.injective
    apply (Representation.apply_bijective V.ρ a⁻¹).1
    apply targetCarrier.symm.injective
    exact hxy
  letI : Nontrivial θ.realization :=
    CliffordRestriction.nontrivial_of_simple θ.realization
  obtain ⟨v, hv⟩ := exists_ne (0 : θ.realization)
  intro hzero
  apply hv
  apply hmap_injective
  rw [hzero]
  change (0 : FDRep.resSubgroup N V) = 0
  rfl

/-- If `a` fixes `θ`, its realization is isomorphic to the corresponding
conjugation twist. -/
def invariantRealizationIso (a : K)
    (θ : IrreducibleCharacter N)
    (ha : IrreducibleCharacter.conjBy N a θ = θ) :
    θ.realization ≅ conjugateRealization N a θ := by
  letI : Simple (conjugateRealization N a θ) :=
    FDRep.simple_res_mulEquiv
      (MulAut.conjNormal (H := N) a).symm
      θ.realization
  apply Classical.choice
  apply FDRep.nonempty_iso_of_character_eq
  rw [conjugateRealization_character, ha,
    θ.realization_character]

/-- The underlying linear automorphism supplied by invariance of `θ`.
The codomain of `invariantRealizationIso` is a twist with the same carrier,
so this forgets that twisted action while retaining the intertwining law. -/
def invariantConjugationLinearEquiv (a : K)
    (θ : IrreducibleCharacter N)
    (ha : IrreducibleCharacter.conjBy N a θ = θ) :
    θ.realization ≃ₗ[ℂ] θ.realization where
  toFun v :=
    show θ.realization from
      FDRep.isoToLinearEquiv
        (invariantRealizationIso N a θ ha) v
  invFun v :=
    (FDRep.isoToLinearEquiv
      (invariantRealizationIso N a θ ha)).symm
      (show conjugateRealization N a θ from v)
  map_add' x y := by
    exact map_add
      (FDRep.isoToLinearEquiv
        (invariantRealizationIso N a θ ha)) x y
  map_smul' c x := by
    exact map_smul
      (FDRep.isoToLinearEquiv
        (invariantRealizationIso N a θ ha)) c x
  left_inv x := by
    exact
      (FDRep.isoToLinearEquiv
        (invariantRealizationIso N a θ ha)).left_inv x
  right_inv x := by
    exact
      (FDRep.isoToLinearEquiv
        (invariantRealizationIso N a θ ha)).right_inv
      (show conjugateRealization N a θ from x)

/-- Intertwining law for the invariant-conjugation linear automorphism. -/
theorem invariantConjugationLinearEquiv_map
    (a : K)
    (θ : IrreducibleCharacter N)
    (ha : IrreducibleCharacter.conjBy N a θ = θ)
    (n : N) (v : θ.realization) :
    invariantConjugationLinearEquiv N a θ ha
        (θ.realization.ρ n v) =
      θ.realization.ρ
        ((MulAut.conjNormal (H := N) a).symm n)
        (invariantConjugationLinearEquiv N a θ ha v) := by
  exact
    ConcreteCategory.congr_hom
      ((invariantRealizationIso N a θ ha).hom.comm n) v

/-- Conjugate a constituent map by an element which fixes its character. -/
def conjugatedRestrictionHom
    (θ : IrreducibleCharacter N)
    (V : FDRep ℂ K)
    (f : θ.realization ⟶ FDRep.resSubgroup N V)
    (a : K)
    (ha : IrreducibleCharacter.conjBy N a θ = θ) :
    θ.realization ⟶ FDRep.resSubgroup N V := by
  let t := invariantConjugationLinearEquiv N a θ ha
  let fL : θ.realization →ₗ[ℂ] FDRep.resSubgroup N V :=
    ((forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)).map f.hom).hom
  let e := restrictionCarrierLinearEquiv N V
  let L : θ.realization →ₗ[ℂ] FDRep.resSubgroup N V :=
    e.symm.toLinearMap.comp
      ((V.ρ a).comp
        (e.toLinearMap.comp
          (fL.comp t.toLinearMap)))
  refine
    { hom := FGModuleCat.ofHom L
      comm := ?_ }
  intro n
  apply FGModuleCat.hom_ext
  ext v
  change
    e.symm
        (V.ρ a
          (e (fL (t (θ.realization.ρ n v))))) =
      V.ρ (n : N)
        (e.symm
          (V.ρ a (e (fL (t v)))))
  have ht :
      t (θ.realization.ρ n v) =
        θ.realization.ρ
          ((MulAut.conjNormal (H := N) a).symm n)
          (t v) :=
    invariantConjugationLinearEquiv_map N a θ ha n v
  have hf' :
      e
        (fL
          (θ.realization.ρ
            ((MulAut.conjNormal (H := N) a).symm n)
            (t v))) =
        V.ρ
          (((MulAut.conjNormal (H := N) a).symm n : N) : K)
          (e (fL (t v))) := by
    change
      (show V from
        fL
          (θ.realization.ρ
            ((MulAut.conjNormal (H := N) a).symm n)
            (t v))) =
        V.ρ
          (((MulAut.conjNormal (H := N) a).symm n : N) : K)
          (show V from fL (t v))
    exact ConcreteCategory.congr_hom
      (f.comm ((MulAut.conjNormal (H := N) a).symm n)) (t v)
  rw [ht, hf']
  apply e.symm.injective
  change
    V.ρ a
        (V.ρ
          (((MulAut.conjNormal (H := N) a).symm n : N) : K)
          (e (fL (t v)))) =
      V.ρ (n : K)
        (V.ρ a (e (fL (t v))))
  rw [← Module.End.mul_apply, ← Module.End.mul_apply,
    ← map_mul, ← map_mul]
  congr 1
  simp only [MulAut.conjNormal_symm_apply]
  group

/-- Pointwise formula for the conjugated constituent map. -/
theorem conjugatedRestrictionHom_apply
    (θ : IrreducibleCharacter N)
    (V : FDRep ℂ K)
    (f : θ.realization ⟶ FDRep.resSubgroup N V)
    (a : K)
    (ha : IrreducibleCharacter.conjBy N a θ = θ)
    (v : θ.realization) :
    conjugatedRestrictionHom N θ V f a ha v =
      V.ρ a
        (f (invariantConjugationLinearEquiv N a θ ha v)) :=
  rfl

/-- Conjugating a nonzero constituent map preserves nonzeroness. -/
theorem conjugatedRestrictionHom_ne_zero
    (θ : IrreducibleCharacter N)
    (V : FDRep ℂ K)
    (f : θ.realization ⟶ FDRep.resSubgroup N V)
    (hf : f ≠ 0)
    (a : K)
    (ha : IrreducibleCharacter.conjBy N a θ = θ) :
    conjugatedRestrictionHom N θ V f a ha ≠ 0 := by
  let t := invariantConjugationLinearEquiv N a θ ha
  have hf_injective : Function.Injective f :=
    fdRepHom_injective_of_nonzero_from_simple f hf
  have ht_injective : Function.Injective t :=
    t.injective
  have ha_injective : Function.Injective (V.ρ a) :=
    (Representation.apply_bijective V.ρ a).1
  have hconj_injective :
      Function.Injective
        (conjugatedRestrictionHom N θ V f a ha) := by
    intro x y hxy
    apply ht_injective
    apply hf_injective
    apply (restrictionCarrierLinearEquiv N V).injective
    apply ha_injective
    have hxy' :=
      congrArg (restrictionCarrierLinearEquiv N V) hxy
    change
      V.ρ a
          (restrictionCarrierLinearEquiv N V
            (f (t x))) =
        V.ρ a
          (restrictionCarrierLinearEquiv N V
            (f (t y))) at hxy'
    exact hxy'
  letI : Nontrivial θ.realization :=
    CliffordRestriction.nontrivial_of_simple θ.realization
  obtain ⟨v, hv⟩ := exists_ne (0 : θ.realization)
  intro hzero
  apply hv
  apply hconj_injective
  have happ :=
    ConcreteCategory.congr_hom hzero v
  change
    (conjugatedRestrictionHom N θ V f a ha) v = 0 at happ
  change
    (conjugatedRestrictionHom N θ V f a ha) v =
      (conjugatedRestrictionHom N θ V f a ha) 0
  calc
    (conjugatedRestrictionHom N θ V f a ha) v = 0 :=
      happ
    _ = (conjugatedRestrictionHom N θ V f a ha) 0 := by
      exact
        (map_zero
          (((forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)).map
            (conjugatedRestrictionHom N θ V f a ha).hom).hom)).symm

/-- The image of the conjugated constituent map is exactly the conjugate
of the original constituent submodule. -/
theorem map_constituentSubmodule
    (θ : IrreducibleCharacter N)
    (V : FDRep ℂ K)
    (f : θ.realization ⟶ FDRep.resSubgroup N V)
    (a : K)
    (ha : IrreducibleCharacter.conjBy N a θ = θ) :
    (constituentSubmodule N θ V f).map
        (CliffordModule.conjSemilinearEnd (H := N) V.ρ a) =
      constituentSubmodule N θ V
        (conjugatedRestrictionHom N θ V f a ha) := by
  ext x
  constructor
  · rintro ⟨y, ⟨v, rfl⟩, rfl⟩
    obtain ⟨u, rfl⟩ :=
      (invariantConjugationLinearEquiv N a θ ha).surjective v
    exact ⟨u, rfl⟩
  · rintro ⟨v, rfl⟩
    refine
      ⟨restrictionHomAsModule N θ V f
          (invariantConjugationLinearEquiv N a θ ha v),
        ⟨_, rfl⟩, ?_⟩
    rfl

/-- If every element of the ambient group fixes `θ`, then the restriction
of a simple representation containing `θ` is `θ`-isotypic. -/
theorem restriction_isIsotypicOfType_of_invariant
    (θ : IrreducibleCharacter N)
    (V : FDRep ℂ K) [Simple V]
    (f : θ.realization ⟶ FDRep.resSubgroup N V)
    (hf : f ≠ 0)
    (hinvariant :
      ∀ a : K, IrreducibleCharacter.conjBy N a θ = θ) :
    IsIsotypicOfType ℂ[N]
      (Representation.asModule (FDRep.resSubgroup N V).ρ)
      (constituentSubmodule N θ V f) := by
  haveI : Representation.IsIrreducible V.ρ :=
    CliffordRestriction.isIrreducible_of_simple V
  let W :
      Submodule ℂ[N] (CliffordModule.resRep V.ρ N).asModule :=
    constituentSubmodule N θ V f
  letI : IsSimpleModule ℂ[N] W := by
    dsimp [W]
    exact constituentSubmodule_isSimpleModule N θ V f hf
  change
    IsIsotypicOfType ℂ[N]
      (CliffordModule.resRep V.ρ N).asModule W
  apply CliffordModule.isIsotypicOfType_of_conjugates
    (H := N) V.ρ W
  · exact fun hrange => (show restrictionHomAsModule N θ V f ≠ 0 by
        intro hzero
        apply hf
        apply
          (FDRep.forget₂HomLinearEquiv
            θ.realization (FDRep.resSubgroup N V)).symm.injective
        apply Rep.Hom.ext
        apply
          (Representation.IntertwiningMap.equivLinearMapAsModule
            θ.realization.ρ
            (FDRep.resSubgroup N V).ρ).injective
        exact hzero) (LinearMap.range_eq_bot.mp hrange)
  · intro a
    let f' :=
      conjugatedRestrictionHom N θ V f a (hinvariant a)
    let W' :
        Submodule ℂ[N] (CliffordModule.resRep V.ρ N).asModule :=
      constituentSubmodule N θ V f'
    let E :
        constituentSubmodule N θ V f ≃ₗ[ℂ[N]]
          constituentSubmodule N θ V f' :=
      (realizationEquivConstituentSubmodule N θ V f hf).symm.trans
        (realizationEquivConstituentSubmodule N θ V f'
          (conjugatedRestrictionHom_ne_zero N θ V f hf a
            (hinvariant a)))
    change Nonempty
      ((constituentSubmodule N θ V f) ≃ₗ[ℂ[N]]
        (constituentSubmodule N θ V f).map
          (CliffordModule.conjSemilinearEnd (H := N) V.ρ a))
    rw [map_constituentSubmodule N θ V f a (hinvariant a)]
    exact ⟨E⟩

/-- The preceding isotypy statement, with the chosen realization of `θ`
itself as the simple type. -/
theorem restriction_isIsotypic_realization_of_invariant
    (θ : IrreducibleCharacter N)
    (V : FDRep ℂ K) [Simple V]
    (f : θ.realization ⟶ FDRep.resSubgroup N V)
    (hf : f ≠ 0)
    (hinvariant :
      ∀ a : K, IrreducibleCharacter.conjBy N a θ = θ) :
    IsIsotypicOfType ℂ[N]
      (Representation.asModule (FDRep.resSubgroup N V).ρ)
      (Representation.asModule θ.realization.ρ) := by
  exact
    (restriction_isIsotypicOfType_of_invariant
      N θ V f hf hinvariant).of_linearEquiv_type
        (realizationEquivConstituentSubmodule N θ V f hf).symm

end Normal

section Inertia

variable [Fintype G]
variable (N : Subgroup G) [N.Normal]
variable (θ : IrreducibleCharacter N)

/-- For a normal-subgroup restriction, containing one conjugate of `θ`
implies containing `θ` itself. -/
theorem liesOver_of_liesOverOrbit
    (χ : IrreducibleCharacter G)
    (hχ : LiesOverOrbit N θ χ) :
    LiesOverAlong N.subtype θ χ := by
  obtain ⟨g, hg⟩ := hχ
  obtain ⟨f, hf⟩ :=
    (liesOverAlong_iff_exists_nonzero N.subtype
      (IrreducibleCharacter.conjBy N g θ) χ).mp hg
  apply
    (liesOverAlong_iff_exists_nonzero N.subtype θ χ).mpr
  exact
    ⟨deconjugatedRestrictionHom N θ χ.realization g f,
      deconjugatedRestrictionHom_ne_zero
        N θ χ.realization g f hf⟩

/-- The canonical copy of `N` as a subgroup of its inertia group. -/
abbrev inertiaNormalCopy :
    Subgroup (IrreducibleCharacter.inertia N θ) :=
  N.subgroupOf (IrreducibleCharacter.inertia N θ)

/-- The canonical group equivalence from the copy of `N` inside its inertia
group back to `N`. -/
abbrev inertiaNormalCopyEquiv :
    inertiaNormalCopy N θ ≃* N :=
  Subgroup.subgroupOfEquivOfLe
    (IrreducibleCharacter.subgroup_le_inertia N θ)

/-- The character `θ`, transported to the canonical copy of `N` inside its
inertia group. -/
def inertiaCopyCharacter :
    IrreducibleCharacter (inertiaNormalCopy N θ) :=
  θ.comap (inertiaNormalCopyEquiv N θ)

omit [Fintype G] in
/-- Restriction through the transported copy of `N` agrees with restriction
along the canonical inertia inclusion. -/
theorem res_copy_res_inertia_eq_res_copy
    (V : FDRep ℂ (IrreducibleCharacter.inertia N θ)) :
    FDRep.res (inertiaNormalCopyEquiv N θ : inertiaNormalCopy N θ →* N)
        (FDRep.res (inertiaInclusion N θ) V) =
      FDRep.resSubgroup (inertiaNormalCopy N θ) V := by
  change
    FDRep.res
        ((inertiaInclusion N θ).comp
          (inertiaNormalCopyEquiv N θ :
            inertiaNormalCopy N θ →* N)) V =
      FDRep.res (inertiaNormalCopy N θ).subtype V
  congr 1

/-- The chosen realization of the transported character is isomorphic to
the transported chosen realization of `θ`. -/
def inertiaCopyRealizationIso :
    (inertiaCopyCharacter N θ).realization ≅
      FDRep.res (inertiaNormalCopyEquiv N θ :
        inertiaNormalCopy N θ →* N) θ.realization := by
  letI :
      Simple
        (FDRep.res (inertiaNormalCopyEquiv N θ :
          inertiaNormalCopy N θ →* N) θ.realization) :=
    FDRep.simple_res_mulEquiv
      (inertiaNormalCopyEquiv N θ) θ.realization
  apply Classical.choice
  apply FDRep.nonempty_iso_of_character_eq
  funext n
  rw [(inertiaCopyCharacter N θ).realization_character]
  change
    θ.values (inertiaNormalCopyEquiv N θ n) =
      θ.realization.character (inertiaNormalCopyEquiv N θ n)
  exact (congrFun θ.realization_character _).symm

/-- Transport a constituent map from `N` to its canonical copy in the
inertia group. -/
def inertiaCopyConstituentHom
    (ψ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (f : θ.realization ⟶
      FDRep.res (inertiaInclusion N θ) ψ.realization) :
    (inertiaCopyCharacter N θ).realization ⟶
      FDRep.resSubgroup (inertiaNormalCopy N θ) ψ.realization :=
  (inertiaCopyRealizationIso N θ).hom ≫
    (FDRep.resFunctor (k := ℂ)
      (inertiaNormalCopyEquiv N θ :
        inertiaNormalCopy N θ →* N)).map f ≫
    (eqToIso
      (res_copy_res_inertia_eq_res_copy N θ ψ.realization)).hom

/-- Transporting a nonzero constituent map to the inertia copy preserves
nonzeroness. -/
theorem inertiaCopyConstituentHom_ne_zero
    (ψ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (f : θ.realization ⟶
      FDRep.res (inertiaInclusion N θ) ψ.realization)
    (hf : f ≠ 0) :
    inertiaCopyConstituentHom N θ ψ f ≠ 0 := by
  let f' :=
    (FDRep.resFunctor (k := ℂ)
      (inertiaNormalCopyEquiv N θ :
        inertiaNormalCopy N θ →* N)).map f
  have hf_injective : Function.Injective f :=
    fdRepHom_injective_of_nonzero_from_simple f hf
  have hf'_injective : Function.Injective f' := by
    intro x y hxy
    exact hf_injective hxy
  haveI : Mono f' :=
    ConcreteCategory.mono_of_injective f' hf'_injective
  haveI :
      Mono (inertiaCopyRealizationIso N θ).hom :=
    inferInstance
  haveI :
      Mono
        (eqToIso
          (res_copy_res_inertia_eq_res_copy
            N θ ψ.realization)).hom :=
    inferInstance
  haveI :
      Mono ((inertiaCopyRealizationIso N θ).hom ≫ f') :=
    mono_comp (inertiaCopyRealizationIso N θ).hom f'
  haveI : Mono (inertiaCopyConstituentHom N θ ψ f) := by
    change
      Mono
        (((inertiaCopyRealizationIso N θ).hom ≫ f') ≫
          (eqToIso
            (res_copy_res_inertia_eq_res_copy
              N θ ψ.realization)).hom)
    exact
      mono_comp
        ((inertiaCopyRealizationIso N θ).hom ≫ f')
        (eqToIso
          (res_copy_res_inertia_eq_res_copy
            N θ ψ.realization)).hom
  intro hzero
  apply id_nonzero (inertiaCopyCharacter N θ).realization
  apply (cancel_mono (inertiaCopyConstituentHom N θ ψ f)).mp
  simp [hzero]

omit [Fintype G] in
/-- Every element of the inertia group fixes the transported copy of
`θ`. -/
theorem inertiaCopyCharacter_invariant
    (a : IrreducibleCharacter.inertia N θ) :
    IrreducibleCharacter.conjBy (inertiaNormalCopy N θ) a
        (inertiaCopyCharacter N θ) =
      inertiaCopyCharacter N θ := by
  apply IrreducibleCharacter.ext
  funext n
  rw [IrreducibleCharacter.conjBy_values]
  change
    θ.values
        (inertiaNormalCopyEquiv N θ
          ((MulAut.conjNormal (H := inertiaNormalCopy N θ) a).symm n)) =
      θ.values (inertiaNormalCopyEquiv N θ n)
  have hfix :
      IrreducibleCharacter.conjBy N (a : G) θ = θ :=
    (IrreducibleCharacter.mem_inertia_iff N θ (a : G)).mp a.property
  have hvalue :=
    congrArg
      (fun η : IrreducibleCharacter N =>
        η.values (inertiaNormalCopyEquiv N θ n))
      hfix
  rw [IrreducibleCharacter.conjBy_values] at hvalue
  convert hvalue using 1
  apply congrArg θ.values
  apply Subtype.ext
  rfl

/-- Conjugation by an ambient element, transported to the canonical copy
of `N` inside the inertia group. -/
def inertiaCopyConjugation (x : G) :
    inertiaNormalCopy N θ ≃* inertiaNormalCopy N θ :=
  ((inertiaNormalCopyEquiv N θ).trans
    (MulAut.conjNormal (H := N) x)).trans
      (inertiaNormalCopyEquiv N θ).symm

omit [Fintype G] in
@[simp]
theorem inertiaCopyConjugation_coe
    (x : G) (n : inertiaNormalCopy N θ) :
    ((((inertiaCopyConjugation N θ x) n :
        inertiaNormalCopy N θ) :
      IrreducibleCharacter.inertia N θ) : G) =
      x * (((n : inertiaNormalCopy N θ) :
        IrreducibleCharacter.inertia N θ) : G) * x⁻¹ := by
  rfl

/-- The canonical copy of `N` lies in every Mackey intersection for the
inertia subgroup, because `N` is normal in `G`. -/
def inertiaCopyToIntersection (x : G) :
    inertiaNormalCopy N θ →*
      Mackey.intersection
        (IrreducibleCharacter.inertia N θ)
        (IrreducibleCharacter.inertia N θ) x where
  toFun n :=
    ⟨(n : IrreducibleCharacter.inertia N θ), by
      change
        x * ((((n : inertiaNormalCopy N θ) :
          IrreducibleCharacter.inertia N θ) : G)) * x⁻¹ ∈
            IrreducibleCharacter.inertia N θ
      apply IrreducibleCharacter.subgroup_le_inertia N θ
      exact
        (inferInstance : N.Normal).conj_mem _ n.property x⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' a b := by
    apply Subtype.ext
    rfl

omit [Fintype G] in
/-- Restricting through the Mackey intersection and then through the copy
of `N` is ordinary restriction to that copy. -/
theorem intersectionRestriction_copy
    (x : G)
    (V : FDRep ℂ (IrreducibleCharacter.inertia N θ)) :
    (V.ρ.comp
      (Mackey.intersection
        (IrreducibleCharacter.inertia N θ)
        (IrreducibleCharacter.inertia N θ) x).subtype).comp
          (inertiaCopyToIntersection N θ x) =
      V.ρ.comp (inertiaNormalCopy N θ).subtype := by
  rfl

omit [Fintype G] in
/-- On the canonical copy of `N`, a Mackey conjugate restriction is exactly
restriction twisted by ambient conjugation. -/
theorem conjugateRestriction_copy
    (x : G)
    (V : FDRep ℂ (IrreducibleCharacter.inertia N θ)) :
    (Mackey.conjugateRestriction
      (IrreducibleCharacter.inertia N θ)
      (IrreducibleCharacter.inertia N θ) x V.ρ).comp
        (inertiaCopyToIntersection N θ x) =
      (V.ρ.comp (inertiaNormalCopy N θ).subtype).comp
        (inertiaCopyConjugation N θ x :
          inertiaNormalCopy N θ →*
            inertiaNormalCopy N θ) := by
  apply MonoidHom.ext
  intro n
  congr 1

/-- If the transported realization of `θ` were isomorphic to its twist by
`x`, then `x` would belong to the inertia subgroup. -/
theorem not_nonempty_inertiaCopyRealization_equiv_twist
    (x : G)
    (hx : x ∉ IrreducibleCharacter.inertia N θ) :
    ¬Nonempty
      (Representation.asModule
          (inertiaCopyCharacter N θ).realization.ρ ≃ₗ[
            ℂ[inertiaNormalCopy N θ]]
        Representation.asModule
          (FDRep.res
            (inertiaCopyConjugation N θ x :
              inertiaNormalCopy N θ →*
                inertiaNormalCopy N θ)
            (inertiaCopyCharacter N θ).realization).ρ) := by
  rintro ⟨E⟩
  let repEquiv :=
    representationEquivOfModuleLinearEquiv E
  have hchar :=
    Representation.char_iso repEquiv
  have hfix_inv :
      IrreducibleCharacter.conjBy N x⁻¹ θ = θ := by
    apply IrreducibleCharacter.ext
    funext n
    let nCopy : inertiaNormalCopy N θ :=
      (inertiaNormalCopyEquiv N θ).symm n
    have hn := congrFun hchar nCopy
    change
      (inertiaCopyCharacter N θ).realization.character nCopy =
        (FDRep.res
          (inertiaCopyConjugation N θ x :
            inertiaNormalCopy N θ →*
              inertiaNormalCopy N θ)
          (inertiaCopyCharacter N θ).realization).character nCopy at hn
    rw [(inertiaCopyCharacter N θ).realization_character,
      FDRep.res_character_apply,
      (inertiaCopyCharacter N θ).realization_character] at hn
    rw [IrreducibleCharacter.conjBy_values]
    change
      θ.values
          ((MulAut.conjNormal (H := N) x⁻¹).symm n) =
        θ.values n
    convert hn.symm using 1
    · apply congrArg θ.values
      apply Subtype.ext
      simp only [MulAut.conjNormal_symm_apply, inv_inv]
      rfl
    · apply congrArg θ.values
      exact (inertiaNormalCopyEquiv N θ).apply_symm_apply n
  have hxinv :
      x⁻¹ ∈ IrreducibleCharacter.inertia N θ :=
    (IrreducibleCharacter.mem_inertia_iff N θ x⁻¹).mpr hfix_inv
  apply hx
  have := (IrreducibleCharacter.inertia N θ).inv_mem hxinv
  simpa using this

/-- The restriction of an irreducible inertia-group representation lying
over `θ` is homogeneous of type `θ` on the canonical copy of `N`. -/
theorem inertiaRestriction_isIsotypic
    (ψ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (hψ : LiesOverAlong (inertiaInclusion N θ) θ ψ) :
    IsIsotypicOfType
      ℂ[inertiaNormalCopy N θ]
      (Representation.asModule
        (FDRep.resSubgroup
          (inertiaNormalCopy N θ) ψ.realization).ρ)
      (Representation.asModule
        (inertiaCopyCharacter N θ).realization.ρ) := by
  obtain ⟨f, hf⟩ :=
    (liesOverAlong_iff_exists_nonzero
      (inertiaInclusion N θ) θ ψ).mp hψ
  exact
    restriction_isIsotypic_realization_of_invariant
      (inertiaNormalCopy N θ)
      (inertiaCopyCharacter N θ)
      ψ.realization
      (inertiaCopyConstituentHom N θ ψ f)
      (inertiaCopyConstituentHom_ne_zero N θ ψ f hf)
      (inertiaCopyCharacter_invariant N θ)

/-- A non-inertial mixed Mackey double-coset component admits no map
between two irreducible inertia representations lying over `θ`. -/
theorem mixedMackeyComponent_eq_zero_of_out_not_mem
    (ψ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (hψ : LiesOverAlong (inertiaInclusion N θ) θ ψ)
    (φ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (hφ : LiesOverAlong (inertiaInclusion N θ) θ φ)
    (q : DoubleCoset.Quotient
      (IrreducibleCharacter.inertia N θ : Set G)
      (IrreducibleCharacter.inertia N θ))
    (hq :
      q.out ∉ IrreducibleCharacter.inertia N θ)
    (F :
      Representation.IntertwiningMap ψ.realization.ρ
        (Mackey.coinducedSummand
          (IrreducibleCharacter.inertia N θ)
          (IrreducibleCharacter.inertia N θ)
          φ.realization.ρ q)) :
    F = 0 := by
  let I := IrreducibleCharacter.inertia N θ
  let J := Mackey.intersection I I q.out
  let component :
      Representation.IntertwiningMap
        (ψ.realization.ρ.comp J.subtype)
        (Mackey.conjugateRestriction I I q.out
          φ.realization.ρ) :=
    homCoinductionRestrictionEquiv J.subtype
      ψ.realization.ρ
      (Mackey.conjugateRestriction I I q.out
        φ.realization.ρ) F
  let componentOnCopy :=
    restrictIntertwiningMap
      (inertiaCopyToIntersection N θ q.out) component
  have hsourceRestricted :
      IsIsotypicOfType ℂ[inertiaNormalCopy N θ]
        (Representation.asModule
          (FDRep.resSubgroup
            (inertiaNormalCopy N θ) ψ.realization).ρ)
        (Representation.asModule
          (inertiaCopyCharacter N θ).realization.ρ) :=
    inertiaRestriction_isIsotypic N θ ψ hψ
  letI :
      IsSemisimpleModule ℂ[inertiaNormalCopy N θ]
        (Representation.asModule
          (FDRep.resSubgroup
            (inertiaNormalCopy N θ) ψ.realization).ρ) :=
    CliffordRestriction.isSemisimpleModule_resSubgroup
      ψ.realization (inertiaNormalCopy N θ)
  let sourceEquiv :
      Representation.Equiv
        (FDRep.resSubgroup
          (inertiaNormalCopy N θ) ψ.realization).ρ
        ((ψ.realization.ρ.comp J.subtype).comp
          (inertiaCopyToIntersection N θ q.out)) := by
    simpa only [I, J, intersectionRestriction_copy] using
      (restrictionAlongRepresentationEquiv
        (inertiaNormalCopy N θ).subtype ψ.realization)
  have hsource :
      IsIsotypicOfType ℂ[inertiaNormalCopy N θ]
        (Representation.asModule
          ((ψ.realization.ρ.comp J.subtype).comp
            (inertiaCopyToIntersection N θ q.out)))
        (Representation.asModule
          (inertiaCopyCharacter N θ).realization.ρ) :=
    (representationEquivAsModule sourceEquiv).isIsotypicOfType_iff.mp
      hsourceRestricted
  letI :
      IsSemisimpleModule ℂ[inertiaNormalCopy N θ]
        (Representation.asModule
          ((ψ.realization.ρ.comp J.subtype).comp
            (inertiaCopyToIntersection N θ q.out))) :=
    IsSemisimpleModule.congr
      (representationEquivAsModule sourceEquiv).symm
  have htargetRestricted :
      IsIsotypicOfType ℂ[inertiaNormalCopy N θ]
        (Representation.asModule
          (FDRep.res
            (inertiaCopyConjugation N θ q.out :
              inertiaNormalCopy N θ →*
                inertiaNormalCopy N θ)
            (FDRep.resSubgroup
              (inertiaNormalCopy N θ) φ.realization)).ρ)
        (Representation.asModule
          (FDRep.res
            (inertiaCopyConjugation N θ q.out :
              inertiaNormalCopy N θ →*
                inertiaNormalCopy N θ)
            (inertiaCopyCharacter N θ).realization).ρ) :=
    twist_isIsotypicOfType
      (inertiaCopyConjugation N θ q.out)
      (FDRep.resSubgroup
        (inertiaNormalCopy N θ) φ.realization)
      (inertiaCopyCharacter N θ).realization
      (inertiaRestriction_isIsotypic N θ φ hφ)
  let targetEquiv :
      Representation.Equiv
        (FDRep.res
          (inertiaCopyConjugation N θ q.out :
            inertiaNormalCopy N θ →*
              inertiaNormalCopy N θ)
          (FDRep.resSubgroup
            (inertiaNormalCopy N θ) φ.realization)).ρ
        ((Mackey.conjugateRestriction I I q.out
          φ.realization.ρ).comp
            (inertiaCopyToIntersection N θ q.out)) := by
    let first :=
      restrictionAlongRepresentationEquiv
        (inertiaCopyConjugation N θ q.out :
          inertiaNormalCopy N θ →*
            inertiaNormalCopy N θ)
        (FDRep.resSubgroup
          (inertiaNormalCopy N θ) φ.realization)
    let second :=
      Mackey.compEquiv
        (inertiaCopyConjugation N θ q.out :
          inertiaNormalCopy N θ →*
            inertiaNormalCopy N θ)
        (restrictionAlongRepresentationEquiv
          (inertiaNormalCopy N θ).subtype φ.realization)
    simpa only [I, conjugateRestriction_copy] using
      first.trans second
  have htarget :
      IsIsotypicOfType ℂ[inertiaNormalCopy N θ]
        (Representation.asModule
          ((Mackey.conjugateRestriction I I q.out
            φ.realization.ρ).comp
              (inertiaCopyToIntersection N θ q.out)))
        (Representation.asModule
          (FDRep.res
            (inertiaCopyConjugation N θ q.out :
              inertiaNormalCopy N θ →*
                inertiaNormalCopy N θ)
            (inertiaCopyCharacter N θ).realization).ρ) :=
    (representationEquivAsModule targetEquiv).isIsotypicOfType_iff.mp
      htargetRestricted
  haveI :
      Representation.IsIrreducible
        (inertiaCopyCharacter N θ).realization.ρ :=
    CliffordRestriction.isIrreducible_of_simple
      (inertiaCopyCharacter N θ).realization
  haveI :
      IsSimpleModule ℂ[inertiaNormalCopy N θ]
        (Representation.asModule
          (inertiaCopyCharacter N θ).realization.ρ) :=
    (Representation.irreducible_iff_isSimpleModule_asModule
      (inertiaCopyCharacter N θ).realization.ρ).mp inferInstance
  letI :
      Simple
        (FDRep.res
          (inertiaCopyConjugation N θ q.out :
            inertiaNormalCopy N θ →*
              inertiaNormalCopy N θ)
          (inertiaCopyCharacter N θ).realization) :=
    FDRep.simple_res_mulEquiv
      (inertiaCopyConjugation N θ q.out)
      (inertiaCopyCharacter N θ).realization
  haveI :
      Representation.IsIrreducible
        (FDRep.res
          (inertiaCopyConjugation N θ q.out :
            inertiaNormalCopy N θ →*
              inertiaNormalCopy N θ)
          (inertiaCopyCharacter N θ).realization).ρ :=
    CliffordRestriction.isIrreducible_of_simple _
  haveI :
      IsSimpleModule ℂ[inertiaNormalCopy N θ]
        (Representation.asModule
          (FDRep.res
            (inertiaCopyConjugation N θ q.out :
              inertiaNormalCopy N θ →*
                inertiaNormalCopy N θ)
            (inertiaCopyCharacter N θ).realization).ρ) :=
    (Representation.irreducible_iff_isSimpleModule_asModule
      (FDRep.res
        (inertiaCopyConjugation N θ q.out :
          inertiaNormalCopy N θ →*
            inertiaNormalCopy N θ)
        (inertiaCopyCharacter N θ).realization).ρ).mp inferInstance
  let componentAsModule :
      Representation.asModule
          ((ψ.realization.ρ.comp J.subtype).comp
            (inertiaCopyToIntersection N θ q.out)) →ₗ[
          ℂ[inertiaNormalCopy N θ]]
        Representation.asModule
          ((Mackey.conjugateRestriction I I q.out
            φ.realization.ρ).comp
              (inertiaCopyToIntersection N θ q.out)) :=
    Representation.IntertwiningMap.equivLinearMapAsModule
      ((ψ.realization.ρ.comp J.subtype).comp
        (inertiaCopyToIntersection N θ q.out))
      ((Mackey.conjugateRestriction I I q.out
        φ.realization.ρ).comp
          (inertiaCopyToIntersection N θ q.out))
      componentOnCopy
  have hmodule : componentAsModule = 0 :=
    linearMap_eq_zero_of_isotypic_types
      hsource htarget
      (not_nonempty_inertiaCopyRealization_equiv_twist
        N θ q.out hq)
      componentAsModule
  have hcopy : componentOnCopy = 0 := by
    apply
      (Representation.IntertwiningMap.equivLinearMapAsModule
        ((ψ.realization.ρ.comp J.subtype).comp
          (inertiaCopyToIntersection N θ q.out))
        ((Mackey.conjugateRestriction I I q.out
          φ.realization.ρ).comp
            (inertiaCopyToIntersection N θ q.out))).injective
    exact hmodule
  have hcomponent : component = 0 := by
    apply Representation.IntertwiningMap.ext
    have hlinear :=
      congrArg
        Representation.IntertwiningMap.toLinearMap hcopy
    change component.toLinearMap = 0 at hlinear
    exact hlinear
  apply
    (homCoinductionRestrictionEquiv J.subtype
      ψ.realization.ρ
      (Mackey.conjugateRestriction I I q.out
        φ.realization.ρ)).injective
  exact hcomponent

/-- The diagonal specialization of the mixed non-inertial component
vanishing theorem. -/
theorem mackeyComponent_eq_zero_of_out_not_mem
    (ψ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (hψ : LiesOverAlong (inertiaInclusion N θ) θ ψ)
    (q : DoubleCoset.Quotient
      (IrreducibleCharacter.inertia N θ : Set G)
      (IrreducibleCharacter.inertia N θ))
    (hq :
      q.out ∉ IrreducibleCharacter.inertia N θ)
    (F :
      Representation.IntertwiningMap ψ.realization.ρ
        (Mackey.coinducedSummand
          (IrreducibleCharacter.inertia N θ)
          (IrreducibleCharacter.inertia N θ)
          ψ.realization.ρ q)) :
    F = 0 :=
  mixedMackeyComponent_eq_zero_of_out_not_mem
    N θ ψ hψ ψ hψ q hq F

/-- When `x` belongs to the inertia subgroup, its Mackey intersection with
that subgroup is canonically the whole inertia subgroup. -/
def inertiaIntersectionEquiv
    (x : G)
    (hx : x ∈ IrreducibleCharacter.inertia N θ) :
    Mackey.intersection
        (IrreducibleCharacter.inertia N θ)
        (IrreducibleCharacter.inertia N θ) x ≃*
      IrreducibleCharacter.inertia N θ where
  toFun := (Mackey.intersection
    (IrreducibleCharacter.inertia N θ)
    (IrreducibleCharacter.inertia N θ) x).subtype
  invFun a :=
    ⟨a, by
      change
        x * (a : G) * x⁻¹ ∈
          IrreducibleCharacter.inertia N θ
      exact
        (IrreducibleCharacter.inertia N θ).mul_mem
          ((IrreducibleCharacter.inertia N θ).mul_mem hx a.property)
          ((IrreducibleCharacter.inertia N θ).inv_mem hx)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- For an inertial representative `x`, multiplication by the action of
`x` identifies ordinary restriction with the Mackey conjugate
restriction. -/
def inertiaIntersectionConjugationEquiv
    (V : FDRep ℂ (IrreducibleCharacter.inertia N θ))
    (x : G)
    (hx : x ∈ IrreducibleCharacter.inertia N θ) :
    Representation.Equiv
      (V.ρ.comp
        (Mackey.intersection
          (IrreducibleCharacter.inertia N θ)
          (IrreducibleCharacter.inertia N θ) x).subtype)
      (Mackey.conjugateRestriction
        (IrreducibleCharacter.inertia N θ)
        (IrreducibleCharacter.inertia N θ) x V.ρ) := by
  let xI : IrreducibleCharacter.inertia N θ := ⟨x, hx⟩
  let L : V ≃ₗ[ℂ] V :=
    LinearEquiv.ofBijective (V.ρ xI)
      (Representation.apply_bijective V.ρ xI)
  apply Representation.Equiv.mk L
  intro a
  ext v
  change
    V.ρ xI
        (V.ρ
          ((Mackey.intersection
            (IrreducibleCharacter.inertia N θ)
            (IrreducibleCharacter.inertia N θ) x).subtype a) v) =
      V.ρ (Mackey.conjugationHom
        (IrreducibleCharacter.inertia N θ)
        (IrreducibleCharacter.inertia N θ) x a)
        (V.ρ xI v)
  rw [← Module.End.mul_apply, ← Module.End.mul_apply,
    ← map_mul, ← map_mul]
  have hgroup :
      xI *
          (Mackey.intersection
            (IrreducibleCharacter.inertia N θ)
            (IrreducibleCharacter.inertia N θ) x).subtype a =
        Mackey.conjugationHom
            (IrreducibleCharacter.inertia N θ)
            (IrreducibleCharacter.inertia N θ) x a *
          xI := by
    apply Subtype.ext
    change x * (a : IrreducibleCharacter.inertia N θ) =
      (x * (a : IrreducibleCharacter.inertia N θ) * x⁻¹) * x
    group
  rw [hgroup]

/-- An identity-double-coset Mackey component has dimension one. -/
theorem finrank_mackeyComponent_of_out_mem
    (ψ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (q : DoubleCoset.Quotient
      (IrreducibleCharacter.inertia N θ : Set G)
      (IrreducibleCharacter.inertia N θ))
    (hq :
      q.out ∈ IrreducibleCharacter.inertia N θ) :
    Module.finrank ℂ
      (Representation.IntertwiningMap ψ.realization.ρ
        (Mackey.coinducedSummand
          (IrreducibleCharacter.inertia N θ)
          (IrreducibleCharacter.inertia N θ)
          ψ.realization.ρ q)) = 1 := by
  let I := IrreducibleCharacter.inertia N θ
  let J := Mackey.intersection I I q.out
  let source := ψ.realization.ρ.comp J.subtype
  let target :=
    Mackey.conjugateRestriction I I q.out ψ.realization.ρ
  let eJ : J ≃* I :=
    inertiaIntersectionEquiv N θ q.out hq
  letI : Simple (FDRep.res (eJ : J →* I) ψ.realization) :=
    FDRep.simple_res_mulEquiv eJ ψ.realization
  haveI :
      Representation.IsIrreducible
        (FDRep.res (eJ : J →* I) ψ.realization).ρ :=
    CliffordRestriction.isIrreducible_of_simple
      (FDRep.res (eJ : J →* I) ψ.realization)
  haveI :
      IsSimpleModule ℂ[J]
        (Representation.asModule
          (FDRep.res (eJ : J →* I) ψ.realization).ρ) :=
    (Representation.irreducible_iff_isSimpleModule_asModule
      (FDRep.res (eJ : J →* I) ψ.realization).ρ).mp inferInstance
  have heJ : (eJ : J →* I) = J.subtype := by
    ext a
    rfl
  let sourceEquiv :
      Representation.Equiv
        (FDRep.res (eJ : J →* I) ψ.realization).ρ source := by
    change
      Representation.Equiv
        (FDRep.res (eJ : J →* I) ψ.realization).ρ
        (ψ.realization.ρ.comp J.subtype)
    rw [← heJ]
    exact
      (restrictionAlongRepresentationEquiv
        (eJ : J →* I) ψ.realization)
  haveI :
      IsSimpleModule ℂ[J] (Representation.asModule source) :=
    IsSimpleModule.congr
      (representationEquivAsModule sourceEquiv).symm
  haveI : Representation.IsIrreducible source :=
    (Representation.irreducible_iff_isSimpleModule_asModule
      source).mpr inferInstance
  let conjugationEquiv :
      Representation.Equiv source target :=
    inertiaIntersectionConjugationEquiv
      N θ ψ.realization q.out hq
  calc
    Module.finrank ℂ
        (Representation.IntertwiningMap ψ.realization.ρ
          (Mackey.coinducedSummand I I
            ψ.realization.ρ q)) =
      Module.finrank ℂ
        (Representation.IntertwiningMap source target) :=
      (homCoinductionRestrictionEquiv J.subtype
        ψ.realization.ρ target).finrank_eq
    _ =
      Module.finrank ℂ
        (Representation.IntertwiningMap source source) :=
      (Mackey.postcomposeEquiv source conjugationEquiv).finrank_eq.symm
    _ = 1 :=
      Representation.IsIrreducible.finrank_intertwiningMap_self source

/-- A double coset of the inertia subgroup has an inertial representative
exactly when it is the identity double coset. -/
theorem out_mem_inertia_iff_eq_identityDoubleCoset
    (q : DoubleCoset.Quotient
      (IrreducibleCharacter.inertia N θ : Set G)
      (IrreducibleCharacter.inertia N θ)) :
    q.out ∈ IrreducibleCharacter.inertia N θ ↔
      q = DoubleCoset.mk
        (IrreducibleCharacter.inertia N θ)
        (IrreducibleCharacter.inertia N θ) 1 := by
  let I := IrreducibleCharacter.inertia N θ
  constructor
  · intro hq
    rw [← DoubleCoset.out_eq' I I q]
    apply (DoubleCoset.eq I I q.out 1).2
    exact
      ⟨q.out⁻¹, I.inv_mem hq, 1, I.one_mem, by simp⟩
  · intro hq
    subst q
    obtain ⟨a, b, ha, hb, hab⟩ :=
      DoubleCoset.mk_out_eq_mul I I (1 : G)
    rw [hab]
    exact I.mul_mem (I.mul_mem ha I.one_mem) hb

/-- A nonzero identity-double-coset component forces the two inertia
characters to agree. -/
theorem eq_of_nonzero_mackeyComponent_of_out_mem
    (ψ φ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (q : DoubleCoset.Quotient
      (IrreducibleCharacter.inertia N θ : Set G)
      (IrreducibleCharacter.inertia N θ))
    (hq : q.out ∈ IrreducibleCharacter.inertia N θ)
    (F :
      Representation.IntertwiningMap ψ.realization.ρ
        (Mackey.coinducedSummand
          (IrreducibleCharacter.inertia N θ)
          (IrreducibleCharacter.inertia N θ)
          φ.realization.ρ q))
    (hF : F ≠ 0) :
    ψ = φ := by
  let I := IrreducibleCharacter.inertia N θ
  let J := Mackey.intersection I I q.out
  let source := ψ.realization.ρ.comp J.subtype
  let ordinaryTarget := φ.realization.ρ.comp J.subtype
  let conjugateTarget :=
    Mackey.conjugateRestriction I I q.out φ.realization.ρ
  let component :
      Representation.IntertwiningMap source conjugateTarget :=
    homCoinductionRestrictionEquiv J.subtype
      ψ.realization.ρ conjugateTarget F
  have hcomponent : component ≠ 0 := by
    intro hzero
    apply hF
    apply
      (homCoinductionRestrictionEquiv J.subtype
        ψ.realization.ρ conjugateTarget).injective
    simpa [component, hzero]
  let conjugationEquiv :
      Representation.Equiv ordinaryTarget conjugateTarget :=
    inertiaIntersectionConjugationEquiv
      N θ φ.realization q.out hq
  let ordinaryComponent :
      Representation.IntertwiningMap source ordinaryTarget :=
    Mackey.postcomposeEquiv source conjugationEquiv.symm component
  have hordinaryComponent : ordinaryComponent ≠ 0 := by
    intro hzero
    apply hcomponent
    apply
      (Mackey.postcomposeEquiv
        source conjugationEquiv.symm).injective
    simpa [ordinaryComponent, hzero]
  let eJ : J ≃* I :=
    inertiaIntersectionEquiv N θ q.out hq
  have heJ : (eJ : J →* I) = J.subtype := by
    ext a
    rfl
  letI : Simple (FDRep.res (eJ : J →* I) ψ.realization) :=
    FDRep.simple_res_mulEquiv eJ ψ.realization
  letI : Simple (FDRep.res (eJ : J →* I) φ.realization) :=
    FDRep.simple_res_mulEquiv eJ φ.realization
  haveI : Representation.IsIrreducible source := by
    change
      Representation.IsIrreducible
        (ψ.realization.ρ.comp J.subtype)
    rw [← heJ]
    exact
      CliffordRestriction.isIrreducible_of_simple
        (FDRep.res (eJ : J →* I) ψ.realization)
  haveI : Representation.IsIrreducible ordinaryTarget := by
    change
      Representation.IsIrreducible
        (φ.realization.ρ.comp J.subtype)
    rw [← heJ]
    exact
      CliffordRestriction.isIrreducible_of_simple
        (FDRep.res (eJ : J →* I) φ.realization)
  have hbijective : Function.Bijective ordinaryComponent :=
    (Representation.IsIrreducible.bijective_or_eq_zero
      ordinaryComponent).resolve_right hordinaryComponent
  let representationEquiv :
      Representation.Equiv source ordinaryTarget :=
    ordinaryComponent.ofBijective hbijective
  apply IrreducibleCharacter.ext
  funext a
  rw [← ψ.realization_character, ← φ.realization_character]
  have hchar :=
    congrFun (Representation.char_iso representationEquiv) (eJ.symm a)
  have hvalue :
      J.subtype (eJ.symm a) = a := by
    rw [← heJ]
    exact eJ.apply_symm_apply a
  change
    ψ.realization.character (J.subtype (eJ.symm a)) =
      φ.realization.character (J.subtype (eJ.symm a)) at hchar
  simpa [hvalue] using hchar

/-- A nonzero map from `ψ` into the restriction of the induction of `φ`
forces equality of inertia characters, provided both lie over `θ`. -/
theorem eq_of_nonzero_intertwining_restricted_inertiaInduction
    (ψ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (hψ : LiesOverAlong (inertiaInclusion N θ) θ ψ)
    (φ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (hφ : LiesOverAlong (inertiaInclusion N θ) θ φ)
    (F :
      Representation.IntertwiningMap ψ.realization.ρ
        ((Representation.ind
          (IrreducibleCharacter.inertia N θ).subtype
          φ.realization.ρ).comp
            (IrreducibleCharacter.inertia N θ).subtype))
    (hF : F ≠ 0) :
    ψ = φ := by
  classical
  let I := IrreducibleCharacter.inertia N θ
  let q₀ : DoubleCoset.Quotient (I : Set G) I :=
    DoubleCoset.mk I I 1
  let components :=
    Mackey.homIntoRestrictedInductionEquiv
      I I φ.realization.ρ ψ.realization.ρ F
  have hq₀component : components q₀ ≠ 0 := by
    intro hzero
    apply hF
    apply
      (Mackey.homIntoRestrictedInductionEquiv
        I I φ.realization.ρ ψ.realization.ρ).injective
    rw [map_zero]
    funext q
    by_cases hq : q = q₀
    · subst q
      exact hzero
    · have hqout : q.out ∉ I := by
        intro hmem
        exact hq
          ((out_mem_inertia_iff_eq_identityDoubleCoset
            N θ q).mp hmem)
      exact
        mixedMackeyComponent_eq_zero_of_out_not_mem
          N θ ψ hψ φ hφ q hqout (components q)
  have hq₀ : q₀.out ∈ I :=
    (out_mem_inertia_iff_eq_identityDoubleCoset
      N θ q₀).2 rfl
  exact
    eq_of_nonzero_mackeyComponent_of_out_mem
      N θ ψ φ q₀ hq₀ (components q₀) hq₀component

/-- Mackey's decomposition shows that only the identity double coset
contributes to the endomorphism calculation for an inertia character lying
over `θ`. -/
theorem finrank_intertwining_restricted_inertiaInduction_eq_one
    (ψ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (hψ : LiesOverAlong (inertiaInclusion N θ) θ ψ) :
    Module.finrank ℂ
      (Representation.IntertwiningMap ψ.realization.ρ
        ((Representation.ind
          (IrreducibleCharacter.inertia N θ).subtype
          ψ.realization.ρ).comp
            (IrreducibleCharacter.inertia N θ).subtype)) = 1 := by
  classical
  let I := IrreducibleCharacter.inertia N θ
  let q₀ : DoubleCoset.Quotient (I : Set G) I :=
    DoubleCoset.mk I I 1
  let projection :
      ((q : DoubleCoset.Quotient (I : Set G) I) →
        Representation.IntertwiningMap ψ.realization.ρ
          (Mackey.coinducedSummand I I ψ.realization.ρ q)) →ₗ[ℂ]
        Representation.IntertwiningMap ψ.realization.ρ
          (Mackey.coinducedSummand I I ψ.realization.ρ q₀) :=
    LinearMap.proj q₀
  have projection_bijective : Function.Bijective projection := by
    constructor
    · intro F₁ F₂ hF
      change F₁ q₀ = F₂ q₀ at hF
      funext q
      by_cases hq : q = q₀
      · subst q
        exact hF
      · have hqout : q.out ∉ I := by
          intro hmem
          exact hq
            ((out_mem_inertia_iff_eq_identityDoubleCoset
              N θ q).mp hmem)
        exact
          (mackeyComponent_eq_zero_of_out_not_mem
            N θ ψ hψ q hqout (F₁ q)).trans
          (mackeyComponent_eq_zero_of_out_not_mem
            N θ ψ hψ q hqout (F₂ q)).symm
    · intro F
      let family :
          (q : DoubleCoset.Quotient (I : Set G) I) →
            Representation.IntertwiningMap ψ.realization.ρ
              (Mackey.coinducedSummand I I ψ.realization.ρ q) :=
        fun q =>
          if hq : q = q₀ then hq.symm ▸ F else 0
      refine ⟨family, ?_⟩
      simp [projection, family]
  let projectionEquiv :=
    LinearEquiv.ofBijective projection projection_bijective
  calc
    Module.finrank ℂ
        (Representation.IntertwiningMap ψ.realization.ρ
          ((Representation.ind I.subtype ψ.realization.ρ).comp
            I.subtype)) =
      Module.finrank ℂ
        ((q : DoubleCoset.Quotient (I : Set G) I) →
          Representation.IntertwiningMap ψ.realization.ρ
            (Mackey.coinducedSummand I I ψ.realization.ρ q)) :=
      (Mackey.homIntoRestrictedInductionEquiv
        I I ψ.realization.ρ ψ.realization.ρ).finrank_eq
    _ =
      Module.finrank ℂ
        (Representation.IntertwiningMap ψ.realization.ρ
          (Mackey.coinducedSummand I I
            ψ.realization.ρ q₀)) :=
      projectionEquiv.finrank_eq
    _ = 1 := by
      have hq₀ : q₀.out ∈ I :=
        (out_mem_inertia_iff_eq_identityDoubleCoset
          N θ q₀).2 rfl
      exact finrank_mackeyComponent_of_out_mem N θ ψ q₀ hq₀

/-- The induced representation has a one-dimensional endomorphism
algebra. -/
theorem inertiaInduction_end_finrank_eq_one
    (ψ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (hψ : LiesOverAlong (inertiaInclusion N θ) θ ψ) :
    Module.finrank ℂ
      (inertiaInduction N θ ψ.realization ⟶
        inertiaInduction N θ ψ.realization) = 1 := by
  calc
    Module.finrank ℂ
        (inertiaInduction N θ ψ.realization ⟶
          inertiaInduction N θ ψ.realization) =
      Module.finrank ℂ
        (ψ.realization ⟶
          FDRep.resSubgroup
            (IrreducibleCharacter.inertia N θ)
            (inertiaInduction N θ ψ.realization)) :=
      inertia_induction_hom_finrank N θ ψ.realization
        (inertiaInduction N θ ψ.realization)
    _ =
      Module.finrank ℂ
        (Representation.IntertwiningMap ψ.realization.ρ
          (FDRep.resSubgroup
            (IrreducibleCharacter.inertia N θ)
            (inertiaInduction N θ ψ.realization)).ρ) :=
      (((FDRep.forget₂HomLinearEquiv
          ψ.realization
          (FDRep.resSubgroup
            (IrreducibleCharacter.inertia N θ)
            (inertiaInduction N θ ψ.realization))).symm).trans
        (Rep.homLinearEquiv _ _)).finrank_eq
    _ = 1 := by
      exact
        finrank_intertwining_restricted_inertiaInduction_eq_one
          N θ ψ hψ

/-- Clifford--Mackey irreducibility: induction to `G` of every irreducible
inertia character lying over `θ` is irreducible. -/
theorem inertiaInduction_simple
    (ψ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (hψ : LiesOverAlong (inertiaInclusion N θ) θ ψ) :
    Simple (inertiaInduction N θ ψ.realization) :=
  (FDRep.simple_iff_end_is_rank_one
    (inertiaInduction N θ ψ.realization)).2
      (inertiaInduction_end_finrank_eq_one N θ ψ hψ)

/-- A nonzero morphism between two inertia inductions determines equality
of their inducing characters. -/
theorem eq_of_nonzero_inertiaInductionHom
    (ψ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (hψ : LiesOverAlong (inertiaInclusion N θ) θ ψ)
    (φ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (hφ : LiesOverAlong (inertiaInclusion N θ) θ φ)
    (f :
      inertiaInduction N θ ψ.realization ⟶
        inertiaInduction N θ φ.realization)
    (hf : f ≠ 0) :
    ψ = φ := by
  let restrictedTarget :=
    FDRep.resSubgroup
      (IrreducibleCharacter.inertia N θ)
      (inertiaInduction N θ φ.realization)
  let homEquiv :
      (inertiaInduction N θ ψ.realization ⟶
          inertiaInduction N θ φ.realization) ≃ₗ[ℂ]
        Representation.IntertwiningMap ψ.realization.ρ
          restrictedTarget.ρ :=
    (inertiaInductionHomEquiv N θ ψ.realization
      (inertiaInduction N θ φ.realization)).trans
      (((FDRep.forget₂HomLinearEquiv
        ψ.realization restrictedTarget).symm).trans
          (Rep.homLinearEquiv _ _))
  let F := homEquiv f
  have hF : F ≠ 0 := by
    intro hzero
    apply hf
    apply homEquiv.injective
    simpa [F, hzero]
  exact
    eq_of_nonzero_intertwining_restricted_inertiaInduction
      N θ ψ hψ φ hφ F hF

/-- Clifford induction, now defined on every irreducible inertia character
lying over `θ`. -/
def induceOverInertiaOrbit
    (ψ : IrreducibleCharactersOverInertia N θ) :
    IrreducibleCharactersOverOrbit N θ :=
  induceSimpleOverInertiaOrbit N θ
    ⟨ψ, inertiaInduction_simple N θ ψ.1 ψ.2⟩

/-- Clifford induction separates irreducible inertia characters lying over
the fixed constituent. -/
theorem induceOverInertiaOrbit_injective :
    Function.Injective (induceOverInertiaOrbit N θ) := by
  intro ψ φ h
  let hsimpleψ :=
    inertiaInduction_simple N θ ψ.1 ψ.2
  let hsimpleφ :=
    inertiaInduction_simple N θ φ.1 φ.2
  letI : Simple (inertiaInduction N θ ψ.1.realization) :=
    hsimpleψ
  letI : Simple (inertiaInduction N θ φ.1.realization) :=
    hsimpleφ
  have hcharacter :
      (inertiaInduction N θ ψ.1.realization).character =
        (inertiaInduction N θ φ.1.realization).character := by
    funext g
    have hg :=
      congrArg
        (fun χ : IrreducibleCharactersOverOrbit N θ =>
          χ.1.values g) h
    change
      (inertiaInduction N θ ψ.1.realization).character g =
        (inertiaInduction N θ φ.1.realization).character g at hg
    exact hg
  obtain ⟨i⟩ :=
    FDRep.nonempty_iso_of_character_eq
      (inertiaInduction N θ ψ.1.realization)
      (inertiaInduction N θ φ.1.realization)
      hcharacter
  have hi : i.hom ≠ 0 := by
    intro hzero
    apply id_nonzero (inertiaInduction N θ ψ.1.realization)
    have hid := i.hom_inv_id
    simpa [hzero] using hid.symm
  apply Subtype.ext
  exact
    eq_of_nonzero_inertiaInductionHom
      N θ ψ.1 ψ.2 φ.1 φ.2 i.hom hi

end Inertia

end CliffordEquivalence

end McKayConjecture
