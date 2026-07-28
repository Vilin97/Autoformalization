/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordModule
import McKayConjecture.Character.CliffordRestriction

/-!
# Clifford's theorem for a normal-subgroup restriction

Let `V` be a simple finite-dimensional representation of `G` over a field
`k`, and let `N` be normal in `G`.  This file chooses a simple constituent
`W` of the restriction to `N` and proves the orbit and homogeneous-component
forms of Clifford's theorem:

* every conjugate of `W` is simple;
* the conjugates of `W` span the restricted module;
* every simple constituent is isomorphic to a conjugate of `W`;
* the isotypic components are precisely the homogeneous components generated
  by these conjugates;
* those homogeneous components are independent and span the whole module.

Each homogeneous component is also exhibited as a finite direct sum of copies
of its simple type, and the resulting multiplicities are proved equal across
the conjugation orbit.
-/

open CategoryTheory
open scoped MonoidAlgebra

universe u v w

namespace McKayConjecture.CliffordTheorem

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]

/-- The group-algebra module underlying the restriction of `V` to `N`. -/
abbrev restrictedModule (V : FDRep k G) (N : Subgroup G) :=
  (CliffordModule.resRep V.ρ N).asModule

section ConjugationTransport

variable {M : Type w} [AddCommGroup M] [Module k M]
variable (ρ : Representation k G M) (N : Subgroup G) [N.Normal]

/-- The group-algebra ring equivalence induced by conjugation by `g`. -/
noncomputable def conjugationRingEquiv (g : G) : k[N] ≃+* k[N] :=
  MonoidAlgebra.mapDomainRingEquiv k
    (CliffordModule.conjNormalMulAut N g)

/-- Conjugation by `g`, upgraded from a bijective semilinear map to a
semilinear equivalence. -/
noncomputable def conjugationSemilinearEquiv (g : G) :
    @LinearEquiv k[N] k[N] _ _
      (conjugationRingEquiv (k := k) N g).toRingHom
      (conjugationRingEquiv (k := k) N g).symm.toRingHom
      (RingHomInvPair.of_ringEquiv
        (conjugationRingEquiv (k := k) N g))
      ((RingHomInvPair.of_ringEquiv
        (conjugationRingEquiv (k := k) N g)).symm)
      (CliffordModule.resRep ρ N).asModule
      (CliffordModule.resRep ρ N).asModule _ _ _ _ := by
  letI hpair : RingHomInvPair
      (conjugationRingEquiv (k := k) N g).toRingHom
      (conjugationRingEquiv (k := k) N g).symm.toRingHom :=
    RingHomInvPair.of_ringEquiv
      (conjugationRingEquiv (k := k) N g)
  letI : RingHomInvPair
      (conjugationRingEquiv (k := k) N g).symm.toRingHom
      (conjugationRingEquiv (k := k) N g).toRingHom :=
    hpair.symm
  exact
    LinearEquiv.ofBijective
      (show (CliffordModule.resRep ρ N).asModule →ₛₗ[
          (conjugationRingEquiv (k := k) N g).toRingHom]
          (CliffordModule.resRep ρ N).asModule from
        CliffordModule.conjSemilinearEnd (H := N) ρ g)
      (CliffordModule.conjSemilinearEnd_bijective (H := N) ρ g)

/-- Applying the same conjugation twist to two isomorphic submodules
preserves their isomorphism type. -/
noncomputable def conjugateLinearEquiv
    (g : G)
    (S T : Submodule k[N] (CliffordModule.resRep ρ N).asModule)
    (e : S ≃ₗ[k[N]] T) :
    S.map (CliffordModule.conjSemilinearEnd (H := N) ρ g) ≃ₗ[k[N]]
      T.map (CliffordModule.conjSemilinearEnd (H := N) ρ g) := by
  let E := conjugationSemilinearEquiv ρ N g
  letI hpair : RingHomInvPair
      (conjugationRingEquiv (k := k) N g).toRingHom
      (conjugationRingEquiv (k := k) N g).symm.toRingHom :=
    RingHomInvPair.of_ringEquiv
      (conjugationRingEquiv (k := k) N g)
  letI : RingHomInvPair
      (conjugationRingEquiv (k := k) N g).symm.toRingHom
      (conjugationRingEquiv (k := k) N g).toRingHom :=
    hpair.symm
  exact
    (E.submoduleMap S).symm.trans
      (e.trans (E.submoduleMap T))

/-- Conjugation restricts to a `k`-linear equivalence from a submodule to
its conjugate. -/
noncomputable def conjugateSubmoduleLinearEquiv
    (g : G)
    (S : Submodule k[N] (CliffordModule.resRep ρ N).asModule) :
    S ≃ₗ[k]
      S.map (CliffordModule.conjSemilinearEnd (H := N) ρ g) := by
  let f :
      S →ₗ[k]
        S.map (CliffordModule.conjSemilinearEnd (H := N) ρ g) :=
    { toFun := fun x =>
        ⟨(show (CliffordModule.resRep ρ N).asModule from
            ρ g (show M from x.1)),
          Submodule.mem_map_of_mem x.property⟩
      map_add' := fun x y => by
        apply Subtype.ext
        exact map_add (ρ g) (show M from x.1) (show M from y.1)
      map_smul' := fun c x => by
        apply Subtype.ext
        exact map_smul (ρ g) c (show M from x.1) }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply (Representation.apply_bijective ρ g).1
    exact congrArg Subtype.val hxy
  · intro x
    obtain ⟨y, hy, hyx⟩ :=
      (CliffordModule.mem_map_conjSemilinearEnd
        ρ g S x.1).mp x.property
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩

/-- Conjugation maps an isotypic component into the isotypic component of
the conjugate simple type. -/
theorem map_isotypicComponent_le (g : G)
    (S : Submodule k[N] (CliffordModule.resRep ρ N).asModule) :
    (isotypicComponent k[N]
        (CliffordModule.resRep ρ N).asModule S).map
        (CliffordModule.conjSemilinearEnd (H := N) ρ g) ≤
      isotypicComponent k[N] (CliffordModule.resRep ρ N).asModule
        (S.map (CliffordModule.conjSemilinearEnd (H := N) ρ g)) := by
  rw [Submodule.map_le_iff_le_comap]
  exact
    sSup_le fun T hT =>
      Submodule.map_le_iff_le_comap.mp
        (le_sSup ⟨conjugateLinearEquiv ρ N g T S hT.some⟩)

/-- Conjugation carries an isotypic component exactly onto the component
of the conjugate simple type. -/
theorem map_isotypicComponent (g : G)
    (S : Submodule k[N] (CliffordModule.resRep ρ N).asModule) :
    (isotypicComponent k[N]
        (CliffordModule.resRep ρ N).asModule S).map
        (CliffordModule.conjSemilinearEnd (H := N) ρ g) =
      isotypicComponent k[N] (CliffordModule.resRep ρ N).asModule
        (S.map (CliffordModule.conjSemilinearEnd (H := N) ρ g)) := by
  apply le_antisymm (map_isotypicComponent_le ρ N g S)
  have h :=
    map_isotypicComponent_le ρ N (g⁻¹)
      (S.map (CliffordModule.conjSemilinearEnd (H := N) ρ g))
  have h' :=
    Submodule.map_mono
      (f := CliffordModule.conjSemilinearEnd (H := N) ρ g) h
  rw [CliffordModule.map_map_conjSemilinearEnd] at h'
  rw [CliffordModule.map_map_conjSemilinearEnd] at h'
  rw [mul_inv_cancel g, inv_mul_cancel g] at h'
  rw [CliffordModule.map_conjSemilinearEnd_one] at h'
  rw [CliffordModule.map_conjSemilinearEnd_one] at h'
  exact h'

end ConjugationTransport

variable (V : FDRep k G) [Simple V]
variable (N : Subgroup G) [N.Normal]

instance restrictedModuleIsSemisimple :
    IsSemisimpleModule k[N] (restrictedModule V N) :=
  CliffordRestriction.isSemisimpleModule_resSubgroup V N

instance representationIsIrreducible :
    Representation.IsIrreducible V.ρ :=
  CliffordRestriction.isIrreducible_of_simple V

/-- A chosen nonzero simple constituent of the restriction to `N`. -/
noncomputable def simpleConstituent :
    Submodule k[N] (restrictedModule V N) :=
  Classical.choose
    (CliffordRestriction.exists_simple_constituent_resSubgroup V N)

theorem simpleConstituent_ne_bot :
    simpleConstituent V N ≠ ⊥ :=
  (Classical.choose_spec
    (CliffordRestriction.exists_simple_constituent_resSubgroup V N)).1

instance simpleConstituentIsSimple :
    IsSimpleModule k[N] (simpleConstituent V N) :=
  (Classical.choose_spec
    (CliffordRestriction.exists_simple_constituent_resSubgroup V N)).2

/-- The constituent obtained from `W` by conjugation with `g`. -/
noncomputable def conjugateConstituent (g : G) :
    Submodule k[N] (restrictedModule V N) :=
  (simpleConstituent V N).map
    (CliffordModule.conjSemilinearEnd (H := N) V.ρ g)

instance conjugateConstituentIsSimple (g : G) :
    IsSimpleModule k[N] (conjugateConstituent V N g) := by
  let W :
      Submodule k[N] (CliffordModule.resRep V.ρ N).asModule :=
    simpleConstituent V N
  letI : IsSimpleModule k[N] W := by
    change IsSimpleModule k[N] (simpleConstituent V N)
    exact simpleConstituentIsSimple V N
  change IsSimpleModule k[N]
    (W.map (CliffordModule.conjSemilinearEnd (H := N) V.ρ g))
  exact CliffordModule.isSimpleModule_map_conjSemilinearEnd V.ρ g W

theorem conjugateConstituent_ne_bot (g : G) :
    conjugateConstituent V N g ≠ ⊥ :=
  (isSimpleModule_iff_isAtom.mp
    (conjugateConstituentIsSimple V N g)).1

@[simp]
theorem conjugateConstituent_one :
    conjugateConstituent V N 1 = simpleConstituent V N :=
  CliffordModule.map_conjSemilinearEnd_one
    V.ρ (simpleConstituent V N)

/-- Conjugation of constituents follows the multiplication law in `G`. -/
theorem map_conjugateConstituent (g₁ g₂ : G) :
    (conjugateConstituent V N g₂).map
        (CliffordModule.conjSemilinearEnd (H := N) V.ρ g₁) =
      conjugateConstituent V N (g₁ * g₂) :=
  CliffordModule.map_map_conjSemilinearEnd
    V.ρ (simpleConstituent V N) g₁ g₂

/-- The orbit of the chosen simple constituent under `G`. -/
noncomputable def constituentOrbit :
    Set (Submodule k[N] (restrictedModule V N)) :=
  Set.range (conjugateConstituent V N)

theorem mem_constituentOrbit_isSimpleModule
    {W : Submodule k[N] (restrictedModule V N)}
    (hW : W ∈ constituentOrbit V N) :
    IsSimpleModule k[N] W := by
  obtain ⟨g, rfl⟩ := hW
  infer_instance

/-- The actual orbit of submodules is transitive under conjugation. -/
theorem constituentOrbit_transitive
    {W₁ W₂ : Submodule k[N] (restrictedModule V N)}
    (hW₁ : W₁ ∈ constituentOrbit V N)
    (hW₂ : W₂ ∈ constituentOrbit V N) :
    ∃ g : G,
      W₁.map (CliffordModule.conjSemilinearEnd (H := N) V.ρ g) = W₂ := by
  obtain ⟨g₁, rfl⟩ := hW₁
  obtain ⟨g₂, rfl⟩ := hW₂
  refine ⟨g₂ * g₁⁻¹, ?_⟩
  rw [map_conjugateConstituent]
  congr 1
  group

/-- The conjugates of the chosen constituent span the restricted module. -/
theorem iSup_conjugateConstituent_eq_top :
    ⨆ g : G, conjugateConstituent V N g = ⊤ :=
  CliffordModule.iSup_map_conjSemilinearEnd_eq_top
    V.ρ (simpleConstituent V N) (simpleConstituent_ne_bot V N)

theorem sSup_constituentOrbit_eq_top :
    sSup (constituentOrbit V N) = ⊤ := by
  rw [constituentOrbit, sSup_range]
  exact iSup_conjugateConstituent_eq_top V N

/-- Every simple constituent of the restriction is isomorphic to a conjugate
of the chosen constituent.  Thus the irreducible constituent types form one
`G`-orbit. -/
theorem simpleConstituent_linearEquiv_conjugate
    (S : Submodule k[N] (restrictedModule V N))
    [IsSimpleModule k[N] S] :
    ∃ g : G, Nonempty (S ≃ₗ[k[N]] conjugateConstituent V N g) := by
  haveI : ∀ W : constituentOrbit V N,
      IsSimpleModule k[N]
        (W : Submodule k[N] (restrictedModule V N)) :=
    fun W => mem_constituentOrbit_isSimpleModule V N W.property
  obtain ⟨W, hW, e⟩ :=
    Submodule.linearEquiv_of_sSup_eq_top S
      (constituentOrbit V N) (sSup_constituentOrbit_eq_top V N)
  obtain ⟨g, rfl⟩ := hW
  exact ⟨g, e⟩

/-- Conjugation preserves the vector-space dimension of a simple
constituent. -/
noncomputable def simpleConstituentLinearEquivConjugate (g : G) :
    simpleConstituent V N ≃ₗ[k] conjugateConstituent V N g := by
  let f :
      simpleConstituent V N →ₗ[k] conjugateConstituent V N g :=
    { toFun := fun w =>
        ⟨(show restrictedModule V N from
            V.ρ g (show V from w.1)),
          Submodule.mem_map_of_mem w.property⟩
      map_add' := fun x y => by
        apply Subtype.ext
        exact map_add (V.ρ g) (show V from x.1) (show V from y.1)
      map_smul' := fun c x => by
        apply Subtype.ext
        exact map_smul (V.ρ g) c (show V from x.1) }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply (Representation.apply_bijective V.ρ g).1
    exact congrArg Subtype.val hxy
  · intro x
    obtain ⟨w, hw, hwx⟩ :=
      (CliffordModule.mem_map_conjSemilinearEnd
        V.ρ g (simpleConstituent V N)
          (show (CliffordModule.resRep V.ρ N).asModule from x.1)).mp
        x.property
    exact ⟨⟨w, hw⟩, Subtype.ext hwx⟩

theorem finrank_conjugateConstituent (g : G) :
    Module.finrank k (conjugateConstituent V N g) =
      Module.finrank k (simpleConstituent V N) :=
  (simpleConstituentLinearEquivConjugate V N g).finrank_eq.symm

/-- All irreducible constituents of the restriction have the same
vector-space dimension. -/
theorem finrank_simple_constituent_eq
    (S : Submodule k[N] (restrictedModule V N))
    [IsSimpleModule k[N] S] :
    Module.finrank k S = Module.finrank k (simpleConstituent V N) := by
  obtain ⟨g, ⟨e⟩⟩ := simpleConstituent_linearEquiv_conjugate V N S
  calc
    Module.finrank k S =
        Module.finrank k (conjugateConstituent V N g) :=
      (e.restrictScalars k).finrank_eq
    _ = Module.finrank k (simpleConstituent V N) :=
      finrank_conjugateConstituent V N g

/-- The homogeneous component belonging to the conjugate indexed by `g`. -/
noncomputable def homogeneousComponent (g : G) :
    Submodule k[N] (restrictedModule V N) :=
  isotypicComponent k[N] (restrictedModule V N)
    (conjugateConstituent V N g)

theorem homogeneousComponent_mem_isotypicComponents (g : G) :
    homogeneousComponent V N g ∈
      isotypicComponents k[N] (restrictedModule V N) :=
  ⟨conjugateConstituent V N g, inferInstance, rfl⟩

theorem homogeneousComponent_ne_bot (g : G) :
    homogeneousComponent V N g ≠ ⊥ :=
  (bot_lt_isotypicComponent (conjugateConstituent V N g)).ne'

/-- Each homogeneous component is isotypic of the corresponding conjugate
simple type. -/
theorem homogeneousComponent_isIsotypicOfType (g : G) :
    IsIsotypicOfType k[N] (homogeneousComponent V N g)
      (conjugateConstituent V N g) :=
  IsIsotypicOfType.isotypicComponent k[N] (restrictedModule V N)
    (conjugateConstituent V N g)

/-- Conjugation carries homogeneous components according to the same
multiplication law as their simple types. -/
theorem map_homogeneousComponent (g₁ g₂ : G) :
    (homogeneousComponent V N g₂).map
        (CliffordModule.conjSemilinearEnd (H := N) V.ρ g₁) =
      homogeneousComponent V N (g₁ * g₂) := by
  rw [homogeneousComponent, map_isotypicComponent,
    map_conjugateConstituent]
  rfl

/-- Conjugation preserves the base-field dimension of a homogeneous
component. -/
theorem finrank_map_homogeneousComponent (g₁ g₂ : G) :
    Module.finrank k (homogeneousComponent V N g₂) =
      Module.finrank k (homogeneousComponent V N (g₁ * g₂)) := by
  calc
    Module.finrank k (homogeneousComponent V N g₂) =
        Module.finrank k
          ((homogeneousComponent V N g₂).map
            (CliffordModule.conjSemilinearEnd (H := N) V.ρ g₁)) :=
      (conjugateSubmoduleLinearEquiv V.ρ N g₁
        (homogeneousComponent V N g₂)).finrank_eq
    _ = Module.finrank k (homogeneousComponent V N (g₁ * g₂)) := by
      rw [map_homogeneousComponent]

/-- All homogeneous components have the same base-field dimension. -/
theorem finrank_homogeneousComponents_eq (g₁ g₂ : G) :
    Module.finrank k (homogeneousComponent V N g₁) =
      Module.finrank k (homogeneousComponent V N g₂) :=
  by
    have h :=
      finrank_map_homogeneousComponent V N (g₂ * g₁⁻¹) g₁
    have hg : (g₂ * g₁⁻¹) * g₁ = g₂ := by group
    rw [hg] at h
    exact h

/-- Every isotypic component of the restriction is one of the homogeneous
components indexed by a conjugate of the chosen constituent. -/
theorem range_homogeneousComponent_eq_isotypicComponents :
    Set.range (homogeneousComponent V N) =
      isotypicComponents k[N] (restrictedModule V N) := by
  ext C
  constructor
  · rintro ⟨g, rfl⟩
    exact homogeneousComponent_mem_isotypicComponents V N g
  · rintro ⟨S, hS, rfl⟩
    letI : IsSimpleModule k[N] S := hS
    obtain ⟨g, ⟨e⟩⟩ :=
      simpleConstituent_linearEquiv_conjugate V N S
    refine ⟨g, ?_⟩
    exact e.isotypicComponent_eq.symm

/-- The distinct homogeneous components are independent. -/
theorem sSupIndep_range_homogeneousComponent :
    sSupIndep (Set.range (homogeneousComponent V N)) := by
  rw [range_homogeneousComponent_eq_isotypicComponents]
  exact sSupIndep_isotypicComponents k[N] (restrictedModule V N)

/-- The homogeneous components span the whole restricted module. -/
theorem sSup_range_homogeneousComponent_eq_top :
    sSup (Set.range (homogeneousComponent V N)) = ⊤ := by
  rw [range_homogeneousComponent_eq_isotypicComponents]
  exact sSup_isotypicComponents k[N] (restrictedModule V N)

/-- Each homogeneous component is a finite direct sum of copies of its
simple constituent type. -/
theorem homogeneousComponent_linearEquiv_pi (g : G) :
    ∃ n : ℕ,
      n ≠ 0 ∧
        Nonempty
          (homogeneousComponent V N g ≃ₗ[k[N]]
            Fin n → conjugateConstituent V N g) := by
  letI : Module.Finite k (homogeneousComponent V N g) :=
    Module.Finite.of_injective
      ((homogeneousComponent V N g).subtype.restrictScalars k)
      (homogeneousComponent V N g).subtype_injective
  letI : Module.Finite k[N] (homogeneousComponent V N g) :=
    Module.Finite.of_restrictScalars_finite
      k k[N] (homogeneousComponent V N g)
  letI : Nontrivial (homogeneousComponent V N g) :=
    Submodule.nontrivial_iff_ne_bot.mpr
      (homogeneousComponent_ne_bot V N g)
  obtain ⟨n, e⟩ :=
    (homogeneousComponent_isIsotypicOfType V N g).linearEquiv_fun
  refine ⟨n, ?_, e⟩
  rintro rfl
  exact not_subsingleton (homogeneousComponent V N g) e.some.subsingleton

/-- The multiplicity of the simple type in the chosen finite homogeneous
decomposition. -/
noncomputable def homogeneousMultiplicity (g : G) : ℕ :=
  Classical.choose (homogeneousComponent_linearEquiv_pi V N g)

theorem homogeneousMultiplicity_ne_zero (g : G) :
    homogeneousMultiplicity V N g ≠ 0 :=
  (Classical.choose_spec
    (homogeneousComponent_linearEquiv_pi V N g)).1

/-- The chosen homogeneous decomposition realizing
`homogeneousMultiplicity`. -/
noncomputable def homogeneousMultiplicityEquiv (g : G) :
    homogeneousComponent V N g ≃ₗ[k[N]]
      Fin (homogeneousMultiplicity V N g) →
        conjugateConstituent V N g :=
  (Classical.choose_spec
    (homogeneousComponent_linearEquiv_pi V N g)).2.some

theorem finrank_homogeneousComponent_eq_multiplicity_mul (g : G) :
    Module.finrank k (homogeneousComponent V N g) =
      homogeneousMultiplicity V N g *
        Module.finrank k (conjugateConstituent V N g) := by
  letI : Module.Finite k (homogeneousComponent V N g) :=
    Module.Finite.of_injective
      ((homogeneousComponent V N g).subtype.restrictScalars k)
      (homogeneousComponent V N g).subtype_injective
  letI : Module.Finite k (conjugateConstituent V N g) :=
    Module.Finite.of_injective
      ((conjugateConstituent V N g).subtype.restrictScalars k)
      (conjugateConstituent V N g).subtype_injective
  calc
    Module.finrank k (homogeneousComponent V N g) =
        Module.finrank k
          (Fin (homogeneousMultiplicity V N g) →
            conjugateConstituent V N g) :=
      ((homogeneousMultiplicityEquiv V N g).restrictScalars k).finrank_eq
    _ = ∑ _ : Fin (homogeneousMultiplicity V N g),
          Module.finrank k (conjugateConstituent V N g) :=
      Module.finrank_pi_fintype k
    _ = homogeneousMultiplicity V N g *
          Module.finrank k (conjugateConstituent V N g) := by
      simp

/-- **Equal multiplicities in Clifford's theorem.** Every irreducible type
in the conjugation orbit occurs with the same multiplicity in the restricted
representation. -/
theorem homogeneousMultiplicity_eq (g₁ g₂ : G) :
    homogeneousMultiplicity V N g₁ =
      homogeneousMultiplicity V N g₂ := by
  letI : Module.Finite k (simpleConstituent V N) :=
    Module.Finite.of_injective
      ((simpleConstituent V N).subtype.restrictScalars k)
      (simpleConstituent V N).subtype_injective
  apply Nat.eq_of_mul_eq_mul_right
    ((Module.finrank_pos_iff
      (R := k) (M := simpleConstituent V N)).mpr
        (Submodule.nontrivial_iff_ne_bot.mpr
          (simpleConstituent_ne_bot V N)))
  calc
    homogeneousMultiplicity V N g₁ *
        Module.finrank k (simpleConstituent V N) =
      homogeneousMultiplicity V N g₁ *
        Module.finrank k (conjugateConstituent V N g₁) := by
          rw [finrank_conjugateConstituent]
    _ = Module.finrank k (homogeneousComponent V N g₁) :=
      (finrank_homogeneousComponent_eq_multiplicity_mul V N g₁).symm
    _ = Module.finrank k (homogeneousComponent V N g₂) :=
      finrank_homogeneousComponents_eq V N g₁ g₂
    _ = homogeneousMultiplicity V N g₂ *
        Module.finrank k (conjugateConstituent V N g₂) :=
      finrank_homogeneousComponent_eq_multiplicity_mul V N g₂
    _ = homogeneousMultiplicity V N g₂ *
        Module.finrank k (simpleConstituent V N) := by
          rw [finrank_conjugateConstituent]

end McKayConjecture.CliffordTheorem
