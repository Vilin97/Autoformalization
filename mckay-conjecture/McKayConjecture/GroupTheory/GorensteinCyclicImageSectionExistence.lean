/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.GorensteinCyclicQuotientReduction
import McKayConjecture.GroupTheory.MinimalNormalModule
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.LittleWedderburn

/-!
# Existence of the cyclic-image section in Gorenstein's reduction

This file proves the representation-theoretic input isolated in
`GorensteinCyclicQuotientReduction`.

The proof has two independent parts.

* An irreducible representation of an abelian group over a finite field has
  cyclic image.  Indeed, every action operator is an endomorphism of the
  simple group-algebra module.  Schur's lemma makes the endomorphism ring a
  finite division ring, hence a finite field, whose unit group is cyclic.
* A minimal normal subgroup of the action semidirect product contained in
  the abelianization supplies a nonzero invariant elementary abelian
  section.  Minimal normality is exactly irreducibility of the restricted
  action.
-/

noncomputable section

universe u v w

namespace McKayConjecture
namespace GroupTheory

open scoped IsMulCommutative MonoidAlgebra

namespace GorensteinCyclicImageSectionExistence

section AbelianIrreducibleImage

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Finite k]
variable [Group G]
variable [AddCommGroup V] [Module k V] [Finite V]

/-- Pairwise commuting representation operators are intertwining
endomorphisms. -/
def commutingIntertwiningActionHom
    (ρ : Representation k G V)
    (hcomm : ∀ g h : G, ρ g * ρ h = ρ h * ρ g) :
    G →* ρ.IntertwiningMap ρ where
  toFun g :=
    { toLinearMap := ρ g
      isIntertwining' h := by
        simpa only [Module.End.mul_eq_comp] using hcomm g h }
  map_one' := by
    apply Representation.IntertwiningMap.ext
    exact ρ.map_one
  map_mul' g h := by
    apply Representation.IntertwiningMap.ext
    exact ρ.map_mul g h

@[simp]
theorem commutingIntertwiningActionHom_toLinearMap
    (ρ : Representation k G V)
    (hcomm : ∀ g h : G, ρ g * ρ h = ρ h * ρ g)
    (g : G) :
    (commutingIntertwiningActionHom ρ hcomm g).toLinearMap =
      ρ g :=
  rfl

/-- For an abelian acting group, every representation operator is an
intertwining endomorphism. -/
def abelianIntertwiningActionHom
    [IsMulCommutative G]
    (ρ : Representation k G V) :
    G →* ρ.IntertwiningMap ρ :=
  commutingIntertwiningActionHom ρ (fun g h ↦ by
    rw [← ρ.map_mul, ← ρ.map_mul, mul_comm])

@[simp]
theorem abelianIntertwiningActionHom_toLinearMap
    [IsMulCommutative G]
    (ρ : Representation k G V) (g : G) :
    (abelianIntertwiningActionHom ρ g).toLinearMap = ρ g :=
  rfl

/-- The image of an irreducible finite-field representation is cyclic when
its action image is commutative.

This is the precise algebraic statement used in Gorenstein's construction.
The proof is Schur's lemma followed by Wedderburn's little theorem and
cyclicity of the unit group of a finite field. -/
theorem irreducible_commutative_actionImage_isCyclic
    (ρ : Representation k G V)
    (hρ : Representation.IsIrreducible ρ)
    (hcomm : IsMulCommutative ρ.asGroupHom.range) :
    IsCyclic ρ.asGroupHom.range := by
  classical
  letI : Representation.IsIrreducible ρ := hρ
  letI : IsMulCommutative ρ.asGroupHom.range := hcomm
  have hoperators :
      ∀ g h : G, ρ g * ρ h = ρ h * ρ g := by
    intro g h
    let x : ρ.asGroupHom.range :=
      ⟨ρ.asGroupHom g, ⟨g, rfl⟩⟩
    let y : ρ.asGroupHom.range :=
      ⟨ρ.asGroupHom h, ⟨h, rfl⟩⟩
    have hxy := mul_comm x y
    have hxy' := congrArg
      (fun z : ρ.asGroupHom.range ↦
        ((z.1 : Units (Module.End k V)) :
          Module.End k V)) hxy
    exact hxy'
  letI : Finite ρ.asModule :=
    Finite.of_injective
      ρ.asModuleEquiv
      ρ.asModuleEquiv.injective
  let D := Module.End k[G] ρ.asModule
  letI : DecidableEq D := Classical.decEq D
  letI : Finite D :=
    Finite.of_injective
      (fun d : D ↦ (d : V → V))
      DFunLike.coe_injective
  letI : Field D := Finite.divisionRing_to_field D
  let f : G →* D :=
    (Representation.IntertwiningMap.equivAlgEnd
      (ρ := ρ)).toMonoidHom.comp
        (commutingIntertwiningActionHom ρ hoperators)
  letI : Finite Dˣ :=
    Finite.of_injective Units.val Units.val_injective
  letI : Finite f.toHomUnits.range :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hker :
      f.toHomUnits.ker = ρ.asGroupHom.ker := by
    ext g
    simp only [MonoidHom.mem_ker]
    constructor
    · intro hg
      have hgval := congrArg Units.val hg
      apply Units.ext
      change ρ g = 1
      change f g = 1 at hgval
      dsimp only [f, MonoidHom.comp_apply] at hgval
      have hg' :
          (Representation.IntertwiningMap.equivAlgEnd
            (ρ := ρ))
              (commutingIntertwiningActionHom
                ρ hoperators g) = 1 :=
        hgval
      have hi :
          commutingIntertwiningActionHom ρ hoperators g = 1 := by
        apply
          (Representation.IntertwiningMap.equivAlgEnd
            (ρ := ρ)).injective
        simpa using hg'
      apply LinearMap.ext
      intro v
      have hiv :=
        congrArg
          (fun x : ρ.IntertwiningMap ρ ↦ x v) hi
      change
        (commutingIntertwiningActionHom
          ρ hoperators g).toLinearMap v =
          v at hiv
      rw [commutingIntertwiningActionHom_toLinearMap] at hiv
      exact hiv
    · intro hg
      apply Units.ext
      change f g = 1
      dsimp only [f, MonoidHom.comp_apply]
      have hg' :
          (commutingIntertwiningActionHom
            ρ hoperators g) = 1 := by
        apply Representation.IntertwiningMap.ext
        exact congrArg Units.val hg
      simpa using congrArg
        (Representation.IntertwiningMap.equivAlgEnd
          (ρ := ρ))
        hg'
  have hquot :
      IsCyclic (G ⧸ ρ.asGroupHom.ker) := by
    have hfquot :
      IsCyclic (G ⧸ f.toHomUnits.ker) :=
      (QuotientGroup.quotientKerEquivRange
        f.toHomUnits).isCyclic.mpr
          (isCyclic_subgroup_units f.toHomUnits.range)
    exact
      (QuotientGroup.quotientMulEquivOfEq
        hker).isCyclic.mp hfquot
  exact
    (QuotientGroup.quotientKerEquivRange
      ρ.asGroupHom).isCyclic.mp hquot

/-- The familiar abelian-source form of
`irreducible_commutative_actionImage_isCyclic`. -/
theorem irreducible_abelian_actionImage_isCyclic
    [IsMulCommutative G]
    (ρ : Representation k G V)
    (hρ : Representation.IsIrreducible ρ) :
    IsCyclic ρ.asGroupHom.range := by
  apply irreducible_commutative_actionImage_isCyclic ρ hρ
  infer_instance

end AbelianIrreducibleImage

section MinimalInvariantSection

variable {M : Type u} {P : Type v}
variable [Group M] [Group P]
variable [MulDistribMulAction M P]
variable {p : ℕ} [Fact p.Prime]
variable [Finite M] [Finite P] [Nontrivial P]

/-- The abelianization of a nontrivial finite `p`-group is nontrivial. -/
theorem abelianization_nontrivial_of_isPGroup
    (hP : IsPGroup p P) :
    Nontrivial (Abelianization P) := by
  letI : Group.IsNilpotent P := hP.isNilpotent
  exact
    QuotientGroup.nontrivial_iff.mpr
      (Group.IsSolvable.commutator_lt_top_of_nontrivial P).ne

/-- The abelianization of a `p`-group is again a `p`-group. -/
theorem abelianization_isPGroup
    (hP : IsPGroup p P) :
    IsPGroup p (Abelianization P) :=
  hP.to_quotient (_root_.commutator P)

/-- The canonical copy of the abelianization in its action semidirect
product is nonzero. -/
theorem abelianizationActionKernel_ne_bot
    (hP : IsPGroup p P) :
    actionKernel M (Abelianization P) ≠ ⊥ := by
  letI : Nontrivial (Abelianization P) :=
    abelianization_nontrivial_of_isPGroup hP
  letI : Nontrivial (actionKernel M (Abelianization P)) :=
    (actionKernelEquiv M
      (Abelianization P)).symm.injective.nontrivial
  exact
    (Subgroup.nontrivial_iff_ne_bot
      (actionKernel M (Abelianization P))).mp inferInstance

/-- A chosen minimal normal subgroup of the action semidirect product
lying in the canonical abelianization subgroup. -/
def minimalAbelianizationNormal
    (hP : IsPGroup p P) :
    Subgroup
      (actionSemidirectProduct M (Abelianization P)) :=
  Classical.choose
    (exists_minimalNormal_le
      (G := actionSemidirectProduct M (Abelianization P))
      (N := actionKernel M (Abelianization P))
      inferInstance
      (abelianizationActionKernel_ne_bot
        (M := M) hP))

/-- The chosen subgroup is minimal normal. -/
theorem minimalAbelianizationNormal_isMinimalNormal
    (hP : IsPGroup p P) :
    IsMinimalNormal
      (minimalAbelianizationNormal (M := M) hP) :=
  (Classical.choose_spec
    (exists_minimalNormal_le
      (G := actionSemidirectProduct M (Abelianization P))
      (N := actionKernel M (Abelianization P))
      inferInstance
      (abelianizationActionKernel_ne_bot
        (M := M) hP))).1

/-- The chosen minimal normal subgroup lies in the canonical
abelianization subgroup. -/
theorem minimalAbelianizationNormal_le_actionKernel
    (hP : IsPGroup p P) :
    minimalAbelianizationNormal (M := M) hP ≤
      actionKernel M (Abelianization P) :=
  (Classical.choose_spec
    (exists_minimalNormal_le
      (G := actionSemidirectProduct M (Abelianization P))
      (N := actionKernel M (Abelianization P))
      inferInstance
      (abelianizationActionKernel_ne_bot
        (M := M) hP))).2

/-- The minimal normal subgroup, pulled back along the canonical embedding
of the abelianization. -/
def minimalInvariantAbelianizationSection
    (hP : IsPGroup p P) :
    Subgroup (Abelianization P) :=
  (minimalAbelianizationNormal (M := M) hP).comap
    (SemidirectProduct.inl :
      Abelianization P →*
        actionSemidirectProduct M (Abelianization P))

/-- Mapping the pulled-back section into the semidirect product recovers
the chosen minimal normal subgroup. -/
theorem minimalInvariantAbelianizationSection_map_inl
    (hP : IsPGroup p P) :
    (minimalInvariantAbelianizationSection
      (M := M) hP).map
        (SemidirectProduct.inl :
          Abelianization P →*
            actionSemidirectProduct M (Abelianization P)) =
      minimalAbelianizationNormal (M := M) hP :=
  Subgroup.map_comap_eq_self
    (minimalAbelianizationNormal_le_actionKernel
      (M := M) hP)

/-- The pulled-back section is nonzero. -/
theorem minimalInvariantAbelianizationSection_ne_bot
    (hP : IsPGroup p P) :
    minimalInvariantAbelianizationSection
      (M := M) hP ≠ ⊥ := by
  intro hbot
  exact
    (minimalAbelianizationNormal_isMinimalNormal
      (M := M) hP).ne_bot
      (by
        rw [←
          minimalInvariantAbelianizationSection_map_inl
            (M := M) hP,
          hbot, Subgroup.map_bot])

/-- The pulled-back section is invariant under the original action of
`M`. -/
theorem smul_mem_minimalInvariantAbelianizationSection
    (hP : IsPGroup p P)
    (m : M) {a : Abelianization P}
    (ha : a ∈ minimalInvariantAbelianizationSection
      (M := M) hP) :
    m • a ∈ minimalInvariantAbelianizationSection
      (M := M) hP := by
  change
    SemidirectProduct.inl
        ((actionHom M (Abelianization P)) m a) ∈
      minimalAbelianizationNormal (M := M) hP
  rw [SemidirectProduct.inl_aut]
  simpa only [map_inv] using
    (minimalAbelianizationNormal_isMinimalNormal
      (M := M) hP).normal.conj_mem
      (SemidirectProduct.inl a) ha
      (SemidirectProduct.inr m)

/-- The canonical isomorphism from the invariant section to the chosen
minimal normal subgroup. -/
def minimalInvariantSectionEquivNormal
    (hP : IsPGroup p P) :
    minimalInvariantAbelianizationSection
        (M := M) hP ≃*
      minimalAbelianizationNormal (M := M) hP :=
  (Subgroup.equivMapOfInjective
      (minimalInvariantAbelianizationSection
        (M := M) hP)
      (SemidirectProduct.inl :
        Abelianization P →*
          actionSemidirectProduct M (Abelianization P))
      SemidirectProduct.inl_injective).trans
    (MulEquiv.subgroupCongr
      (minimalInvariantAbelianizationSection_map_inl
        (M := M) hP))

/-- The invariant section is a `p`-group. -/
theorem minimalInvariantAbelianizationSection_isPGroup
    (hP : IsPGroup p P) :
    IsPGroup p (minimalInvariantAbelianizationSection
      (M := M) hP) :=
  (abelianization_isPGroup hP).to_subgroup
    (minimalInvariantAbelianizationSection
      (M := M) hP)

/-- The minimal invariant section has exponent `p`. -/
theorem minimalInvariantAbelianizationSection_pow_prime_eq_one
    (hP : IsPGroup p P) :
    ∀ a : minimalInvariantAbelianizationSection
        (M := M) hP,
      a ^ p = 1 := by
  let N := minimalAbelianizationNormal (M := M) hP
  let e :=
    minimalInvariantSectionEquivNormal
      (M := M) hP
  have hNp : IsPGroup p N :=
    (minimalInvariantAbelianizationSection_isPGroup
      (M := M) hP).of_equiv e
  letI : Nontrivial N :=
    N.nontrivial_iff_ne_bot.mpr
      (minimalAbelianizationNormal_isMinimalNormal
        (M := M) hP).ne_bot
  letI : IsMulCommutative N :=
    ⟨⟨fun x y ↦ by
      obtain ⟨a, rfl⟩ := e.surjective x
      obtain ⟨b, rfl⟩ := e.surjective y
      rw [← map_mul, mul_comm, map_mul]⟩⟩
  obtain ⟨x, hx⟩ := exists_ne (1 : N)
  have hpCard : p ∣ Nat.card N :=
    (hNp.dvd_orderOf hx).trans
      (orderOf_dvd_natCard x)
  have hpowN :
      ∀ x : N, x ^ p = 1 :=
    (minimalAbelianizationNormal_isMinimalNormal
      (M := M) hP).pow_prime_eq_one hpCard
  intro a
  apply e.injective
  rw [map_pow, hpowN, map_one]

/-- The linear representation on an invariant prime-exponent subgroup of
the abelianization. -/
def invariantAbelianizationLinearRepresentation
    (A : Subgroup (Abelianization P))
    (hA : ∀ (m : M) {a : Abelianization P},
      a ∈ A → m • a ∈ A)
    [Module (ZMod p) (Additive A)] :
    Representation (ZMod p) M (Additive A) := by
  let α := invariantAbelianizationAction M P A hA
  exact
    { toFun := fun m ↦
        AddMonoidHom.toZModLinearMap p
          (MulEquiv.toAdditive (α m)).toAddMonoidHom
      map_one' := by
        apply LinearMap.ext
        intro x
        apply Additive.toMul.injective
        simp [α, MulEquiv.toAdditive]
      map_mul' := by
        intro m n
        apply LinearMap.ext
        intro x
        apply Additive.toMul.injective
        simp [α, MulEquiv.toAdditive] }

@[simp]
theorem invariantAbelianizationLinearRepresentation_apply
    (A : Subgroup (Abelianization P))
    (hA : ∀ (m : M) {a : Abelianization P},
      a ∈ A → m • a ∈ A)
    [Module (ZMod p) (Additive A)]
    (m : M) (a : Additive A) :
    invariantAbelianizationLinearRepresentation
        (p := p) A hA m a =
      Additive.ofMul
        (invariantAbelianizationAction
          M P A hA m a.toMul) := by
  rfl

/-- The linear representation on the chosen minimal invariant section. -/
def minimalInvariantAbelianizationRepresentation
    (hP : IsPGroup p P) :
    letI : Module (ZMod p)
        (Additive
          (minimalInvariantAbelianizationSection
            (M := M) hP)) :=
      primeExponentZModModule p
        (minimalInvariantAbelianizationSection_pow_prime_eq_one
          (M := M) hP)
    Representation (ZMod p) M
      (Additive
        (minimalInvariantAbelianizationSection
          (M := M) hP)) := by
  letI : Module (ZMod p)
      (Additive
        (minimalInvariantAbelianizationSection
          (M := M) hP)) :=
    primeExponentZModModule p
      (minimalInvariantAbelianizationSection_pow_prime_eq_one
        (M := M) hP)
  exact
    invariantAbelianizationLinearRepresentation
      (p := p)
      (minimalInvariantAbelianizationSection
        (M := M) hP)
      (smul_mem_minimalInvariantAbelianizationSection
        (M := M) hP)

/-- Minimality of the normal subgroup in the semidirect product says that
the chosen section is irreducible under `M`. -/
theorem minimalInvariantAbelianizationRepresentation_isIrreducible
    (hP : IsPGroup p P) :
    letI : Module (ZMod p)
        (Additive
          (minimalInvariantAbelianizationSection
            (M := M) hP)) :=
      primeExponentZModModule p
        (minimalInvariantAbelianizationSection_pow_prime_eq_one
          (M := M) hP)
    Representation.IsIrreducible
      (minimalInvariantAbelianizationRepresentation
        (M := M) hP) := by
  let A :=
    minimalInvariantAbelianizationSection
      (M := M) hP
  letI : Module (ZMod p) (Additive A) :=
    primeExponentZModModule p
      (minimalInvariantAbelianizationSection_pow_prime_eq_one
        (M := M) hP)
  let ρ :=
    minimalInvariantAbelianizationRepresentation
      (M := M) hP
  refine
    { exists_pair_ne := ⟨⊥, ⊤, ?_⟩
      eq_bot_or_eq_top := fun S ↦ ?_ }
  · intro h
    haveI : Nontrivial A :=
      A.nontrivial_iff_ne_bot.mpr
        (minimalInvariantAbelianizationSection_ne_bot
          (M := M) hP)
    obtain ⟨x, hx⟩ := exists_ne (0 : Additive A)
    apply hx
    have hxbot : x ∈ (⊥ : Subrepresentation ρ) := by
      rw [h]
      exact Submodule.mem_top
    change x = 0 at hxbot
    exact hxbot
  let B : Subgroup A :=
    AddSubgroup.toSubgroup'
      S.toSubmodule.toAddSubgroup
  let B₀ : Subgroup (Abelianization P) :=
    B.map A.subtype
  let Bsemi : Subgroup
      (actionSemidirectProduct M (Abelianization P)) :=
    B₀.map
      (SemidirectProduct.inl :
        Abelianization P →*
          actionSemidirectProduct M (Abelianization P))
  have hB₀inv :
      ∀ (m : M) {a : Abelianization P},
        a ∈ B₀ → m • a ∈ B₀ := by
    intro m a ha
    obtain ⟨b, hbB, rfl⟩ := ha
    let mb : A :=
      ⟨m • (b : Abelianization P),
        smul_mem_minimalInvariantAbelianizationSection
          (M := M) hP m b.property⟩
    refine ⟨mb, ?_, rfl⟩
    have hbS :
        Additive.ofMul b ∈ S.toSubmodule :=
      hbB
    have hmbS :=
      S.apply_mem_toSubmodule m hbS
    change
      invariantAbelianizationLinearRepresentation
          (p := p) A
            (smul_mem_minimalInvariantAbelianizationSection
              (M := M) hP)
          m (Additive.ofMul b) ∈
        S.toSubmodule at hmbS
    rw [invariantAbelianizationLinearRepresentation_apply]
      at hmbS
    exact hmbS
  have hBsemiNormal : Bsemi.Normal := by
    letI : B₀.Normal := inferInstance
    refine ⟨?_⟩
    rintro _ ⟨b, hb, rfl⟩ g
    refine
      ⟨g.left * (g.right • b) * g.left⁻¹,
        ?_, ?_⟩
    · exact
        (inferInstance : B₀.Normal).conj_mem
          (g.right • b) (hB₀inv g.right hb)
          g.left
    · apply SemidirectProduct.ext
      · simp
      · simp
  have hBsemiLe :
      Bsemi ≤ minimalAbelianizationNormal
        (M := M) hP := by
    intro x hx
    obtain ⟨a, haB₀, rfl⟩ := hx
    obtain ⟨b, hbB, rfl⟩ := haB₀
    exact b.property
  rcases
      (minimalAbelianizationNormal_isMinimalNormal
        (M := M) hP).eq_bot_or_eq
          hBsemiNormal hBsemiLe with
    hBsemiBot | hBsemiTop
  · left
    have hBbot : B = ⊥ := by
      rw [eq_bot_iff]
      intro b hb
      have hbB₀ : (b : Abelianization P) ∈ B₀ :=
        ⟨b, hb, rfl⟩
      have hbBsemi :
          SemidirectProduct.inl
              (b : Abelianization P) ∈ Bsemi :=
        ⟨(b : Abelianization P), hbB₀, rfl⟩
      rw [hBsemiBot] at hbBsemi
      have hbinl :
          (SemidirectProduct.inl :
              Abelianization P →*
                actionSemidirectProduct M
                  (Abelianization P))
              (b : Abelianization P) = 1 := by
        simpa using hbBsemi
      apply Subtype.ext
      exact
        SemidirectProduct.inl_injective
          (by simpa using hbinl)
    apply Subrepresentation.ext
    apply Submodule.ext
    intro x
    constructor
    · intro hx
      have hxB : x.toMul ∈ B := hx
      rw [hBbot] at hxB
      exact hxB
    · intro hx
      have hxzero : x = 0 := by
        change x = 0 at hx
        exact hx
      subst x
      exact S.toSubmodule.zero_mem
  · right
    have hBtop : B = ⊤ := by
      rw [eq_top_iff]
      intro a _
      have haN :
          SemidirectProduct.inl
              (a : Abelianization P) ∈
            minimalAbelianizationNormal
              (M := M) hP :=
        a.property
      have haBsemi :
          SemidirectProduct.inl
              (a : Abelianization P) ∈ Bsemi := by
        rw [hBsemiTop]
        exact haN
      obtain ⟨z, hzB₀, hz⟩ := haBsemi
      obtain ⟨b, hbB, hb⟩ := hzB₀
      have hza :
          z = (a : Abelianization P) :=
        SemidirectProduct.inl_injective hz
      have hba : b = a := by
        apply Subtype.ext
        exact hb.trans hza
      simpa [hba] using hbB
    apply Subrepresentation.ext
    apply Submodule.ext
    intro x
    constructor
    · intro _
      exact Submodule.mem_top
    · intro _
      have hxB : x.toMul ∈ B := by
        rw [hBtop]
        exact Subgroup.mem_top x.toMul
      exact hxB

/-- If a homomorphism descends through an abelian quotient, then its image
is abelian. -/
theorem range_isMulCommutative_of_quotient
    {H : Type w} [Group H]
    (f : M →* H)
    (L : Subgroup M) [L.Normal]
    (hL : L ≤ f.ker)
    (hcomm : IsMulCommutative (M ⧸ L)) :
    IsMulCommutative f.range := by
  letI : IsMulCommutative (M ⧸ L) := hcomm
  let fbar : M ⧸ L →* H :=
    QuotientGroup.lift L f hL
  refine ⟨⟨?_⟩⟩
  rintro ⟨_, ⟨m, rfl⟩⟩ ⟨_, ⟨n, rfl⟩⟩
  apply Subtype.ext
  change f m * f n = f n * f m
  have hmn :
      QuotientGroup.mk' L m *
          QuotientGroup.mk' L n =
        QuotientGroup.mk' L n *
          QuotientGroup.mk' L m :=
    mul_comm _ _
  have hmn' := congrArg fbar hmn
  have hm :
      fbar (QuotientGroup.mk' L m) = f m :=
    QuotientGroup.lift_mk L hL m
  have hn :
      fbar (QuotientGroup.mk' L n) = f n :=
    QuotientGroup.lift_mk L hL n
  rw [map_mul, map_mul, hm, hn] at hmn'
  exact hmn'

/-- The kernel of the original action on `P` acts trivially on the
restriction to every invariant subgroup of the abelianization. -/
theorem okuyamaWajimaActionKernel_le_invariantAction_ker
    (A : Subgroup (Abelianization P))
    (hA : ∀ (m : M) {a : Abelianization P},
      a ∈ A → m • a ∈ A) :
    okuyamaWajimaActionKernel M P ≤
      (invariantAbelianizationAction M P A hA).ker := by
  intro m hm
  rw [MonoidHom.mem_ker]
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  change m • (a : Abelianization P) =
    (a : Abelianization P)
  obtain ⟨x, hx⟩ :=
    QuotientGroup.mk'_surjective
      (_root_.commutator P) (a : Abelianization P)
  have hmP :
      (MulDistribMulAction.toMulAut M P) m = 1 :=
    MonoidHom.mem_ker.mp hm
  have hmx : m • x = x := by
    have h :=
      DFunLike.congr_fun hmP x
    simpa using h
  rw [← hx]
  change
    m • Abelianization.of x =
      Abelianization.of x
  rw [smul_abelianization_of, hmx]

/-- The linearization of a prime-exponent invariant section has exactly
the same action kernel as the underlying multiplicative action. -/
theorem invariantAbelianizationLinearRepresentation_ker
    (A : Subgroup (Abelianization P))
    (hA : ∀ (m : M) {a : Abelianization P},
      a ∈ A → m • a ∈ A)
    [Module (ZMod p) (Additive A)] :
    (invariantAbelianizationLinearRepresentation
        (p := p) A hA).asGroupHom.ker =
      (invariantAbelianizationAction M P A hA).ker := by
  ext m
  simp only [MonoidHom.mem_ker]
  constructor
  · intro hm
    apply MulEquiv.ext
    intro a
    change
      invariantAbelianizationAction M P A hA m a = a
    apply Additive.ofMul.injective
    have hmval := congrArg Units.val hm
    have hma :=
      DFunLike.congr_fun hmval
        (Additive.ofMul a)
    change
      invariantAbelianizationLinearRepresentation
          (p := p) A hA m (Additive.ofMul a) =
        (1 : Module.End (ZMod p) (Additive A))
          (Additive.ofMul a) at hma
    rw [invariantAbelianizationLinearRepresentation_apply]
      at hma
    simpa using hma
  · intro hm
    apply Units.ext
    change
      invariantAbelianizationLinearRepresentation
          (p := p) A hA m = 1
    apply LinearMap.ext
    intro a
    have hma :=
      DFunLike.congr_fun hm a.toMul
    change
      invariantAbelianizationAction M P A hA m a.toMul =
        a.toMul at hma
    change
      invariantAbelianizationLinearRepresentation
          (p := p) A hA m a = a
    rw [invariantAbelianizationLinearRepresentation_apply]
    apply Additive.toMul.injective
    exact hma

/-- The restricted action on the chosen minimal invariant section has
cyclic image. -/
theorem minimalInvariantAbelianizationSection_actionImage_isCyclic
    (hP : IsPGroup p P)
    (L : Subgroup M) [L.Normal]
    (hL : L = okuyamaWajimaActionKernel M P)
    (hML : IsMulCommutative (M ⧸ L)) :
    IsCyclic
      (invariantAbelianizationAction
        M P
        (minimalInvariantAbelianizationSection
          (M := M) hP)
        (smul_mem_minimalInvariantAbelianizationSection
          (M := M) hP)).range := by
  let A :=
    minimalInvariantAbelianizationSection
      (M := M) hP
  let hA :
      ∀ (m : M) {a : Abelianization P},
        a ∈ A → m • a ∈ A :=
    smul_mem_minimalInvariantAbelianizationSection
      (M := M) hP
  letI : Module (ZMod p) (Additive A) :=
    primeExponentZModModule p
      (minimalInvariantAbelianizationSection_pow_prime_eq_one
        (M := M) hP)
  let ρ : Representation (ZMod p) M (Additive A) :=
    minimalInvariantAbelianizationRepresentation
      (M := M) hP
  let α : M →* MulAut A :=
    invariantAbelianizationAction M P A hA
  have hLα : L ≤ α.ker := by
    rw [hL]
    exact
      okuyamaWajimaActionKernel_le_invariantAction_ker
        A hA
  have hker :
      ρ.asGroupHom.ker = α.ker := by
    exact
      invariantAbelianizationLinearRepresentation_ker
        (p := p) A hA
  have hLρ : L ≤ ρ.asGroupHom.ker := by
    rw [hker]
    exact hLα
  have hcommρ :
      IsMulCommutative ρ.asGroupHom.range :=
    range_isMulCommutative_of_quotient
      ρ.asGroupHom L hLρ hML
  have hcyclicρ :
      IsCyclic ρ.asGroupHom.range :=
    irreducible_commutative_actionImage_isCyclic
      ρ
      (minimalInvariantAbelianizationRepresentation_isIrreducible
        (M := M) hP)
      hcommρ
  have hquotρ :
      IsCyclic (M ⧸ ρ.asGroupHom.ker) :=
    (QuotientGroup.quotientKerEquivRange
      ρ.asGroupHom).isCyclic.mpr hcyclicρ
  have hquotα :
      IsCyclic (M ⧸ α.ker) :=
    (QuotientGroup.quotientMulEquivOfEq
      hker).isCyclic.mp hquotρ
  exact
    (QuotientGroup.quotientKerEquivRange
      α).isCyclic.mp hquotα

/-- The cyclic-image section constructed from the original Gorenstein
hypotheses. -/
def gorensteinCyclicImageSection
    (hP : IsPGroup p P)
    (L : Subgroup M) [L.Normal]
    (hL : L = okuyamaWajimaActionKernel M P)
    (hML : IsMulCommutative (M ⧸ L)) :
    GorensteinCyclicImageSection M P where
  toSubgroup :=
    minimalInvariantAbelianizationSection
      (M := M) hP
  smul_mem :=
    smul_mem_minimalInvariantAbelianizationSection
      (M := M) hP
  nontrivial :=
    bot_lt_iff_ne_bot.mpr
      (minimalInvariantAbelianizationSection_ne_bot
        (M := M) hP)
  actionImage_isCyclic :=
    minimalInvariantAbelianizationSection_actionImage_isCyclic
      (M := M) hP L hL hML

/-- The canonical bundled cyclic-quotient subgroup produced by the
minimal invariant section.  This data-level form is convenient for the
two branches of the Okuyama--Wajima induction. -/
def gorensteinCyclicQuotientSubgroup
    (hP : IsPGroup p P)
    (L : Subgroup M) [L.Normal]
    (hL : L = okuyamaWajimaActionKernel M P)
    (hML : IsMulCommutative (M ⧸ L)) :
    OkuyamaWajimaCyclicQuotientSubgroup M P L :=
  (gorensteinCyclicImageSection
    (M := M) hP L hL hML).toOkuyamaWajimaCyclicQuotientSubgroup
      L hL

/-- Gorenstein's original hypotheses imply the cyclic-image section input
isolated in `GorensteinCyclicQuotientReduction`. -/
theorem gorensteinCyclicImageSectionExistenceInput
    (hP : IsPGroup p P)
    (_hM : IsPPrimeGroup p M)
    (L : Subgroup M) [L.Normal]
    (hL : L = okuyamaWajimaActionKernel M P)
    (hML : IsMulCommutative (M ⧸ L)) :
    GorensteinCyclicImageSectionExistenceInput M P := by
  exact
    ⟨gorensteinCyclicImageSection
      (M := M) hP L hL hML⟩

/-- Consequently the full cyclic-quotient subgroup input used by the
Okuyama--Wajima induction follows from Gorenstein's hypotheses. -/
theorem gorensteinCyclicQuotientSubgroupExistenceInput
    (hP : IsPGroup p P)
    (hM : IsPPrimeGroup p M)
    (L : Subgroup M) [L.Normal]
    (hL : L = okuyamaWajimaActionKernel M P)
    (hML : IsMulCommutative (M ⧸ L)) :
    GorensteinCyclicQuotientSubgroupExistenceInput
      M P p L hP hM hL hML :=
  ⟨gorensteinCyclicQuotientSubgroup
    (M := M) hP L hL hML⟩

end MinimalInvariantSection

end GorensteinCyclicImageSectionExistence

end GroupTheory
end McKayConjecture
