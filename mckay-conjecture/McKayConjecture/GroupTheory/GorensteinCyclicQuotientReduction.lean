/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.OkuyamaWajimaCyclicQuotientSubgroup

/-!
# Reduction of the Gorenstein cyclic-quotient input

The group-theoretic input used by the Okuyama--Wajima induction asks for
`U ◁ M` such that `M / U` is cyclic and `U` has nonidentity fixed points
on `P / P'`.  This file reduces that output to a smaller
representation-theoretic statement.

It is enough to find a nontrivial `M`-invariant subgroup `A` of the
abelianization `P / P'` for which the image of the restricted action

`M → Aut(A)`

is cyclic.  Taking `U` to be the kernel of this restricted action gives
all the required conclusions:

* the original action kernel `L` lies in `U`;
* `U` is normal;
* the first isomorphism theorem identifies `M / U` with the cyclic
  action image; and
* every element of `A` is fixed by `U`, so the nontriviality of `A`
  supplies the required nonidentity fixed point.

The proof of the section-existence statement is to
choose a minimal nonzero invariant elementary abelian `p`-section.  The
abelian group `M / L` acts irreducibly on that section; its faithful
image embeds in the multiplicative group of a finite division field
and is therefore cyclic.  The representation-theoretic interface is
isolated below as `GorensteinCyclicImageSectionExistenceInput` and proved
in `GorensteinCyclicImageSectionExistence.lean`.

No axiom is introduced.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace GroupTheory

variable (M : Type u) (P : Type v)
variable [Group M] [Group P]
variable [MulDistribMulAction M P]

/-- The action of `M` restricted to an invariant subgroup of the
abelianization of `P`. -/
def invariantAbelianizationAction
    (A : Subgroup (Abelianization P))
    (hA : ∀ (m : M) {a : Abelianization P},
      a ∈ A → m • a ∈ A) :
    M →* MulAut A where
  toFun m :=
    { toFun := fun a ↦ ⟨m • (a : Abelianization P), hA m a.2⟩
      invFun := fun a ↦
        ⟨m⁻¹ • (a : Abelianization P), hA m⁻¹ a.2⟩
      left_inv := fun a ↦ by
        apply Subtype.ext
        simp
      right_inv := fun a ↦ by
        apply Subtype.ext
        simp
      map_mul' := fun a b ↦ by
        apply Subtype.ext
        exact smul_mul' m (a : Abelianization P)
          (b : Abelianization P) }
  map_one' := by
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    simp
  map_mul' m n := by
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    exact mul_smul m n (a : Abelianization P)

@[simp]
theorem invariantAbelianizationAction_apply_coe
    (A : Subgroup (Abelianization P))
    (hA : ∀ (m : M) {a : Abelianization P},
      a ∈ A → m • a ∈ A)
    (m : M) (a : A) :
    ((invariantAbelianizationAction M P A hA m a : A) :
        Abelianization P) =
      m • (a : Abelianization P) :=
  rfl

/-- The strictly smaller representation-theoretic datum from which the
cyclic-quotient subgroup required by Gorenstein's theorem is recovered.

All quotient, kernel, normality, and fixed-point arguments are
formalized below; existence is proved in
`GorensteinCyclicImageSectionExistence.lean`. -/
structure GorensteinCyclicImageSection where
  /-- A nonzero subgroup of `P / P'` on which to restrict the action. -/
  toSubgroup : Subgroup (Abelianization P)
  /-- Invariance under the action of `M`. -/
  smul_mem :
    ∀ (m : M) {a : Abelianization P},
      a ∈ toSubgroup → m • a ∈ toSubgroup
  /-- The section contains a nonidentity element. -/
  nontrivial :
    (⊥ : Subgroup (Abelianization P)) < toSubgroup
  /-- The faithful image of the restricted action is cyclic. -/
  actionImage_isCyclic :
    IsCyclic
      (invariantAbelianizationAction
        M P toSubgroup smul_mem).range

namespace GorensteinCyclicImageSection

variable {M P}

/-- The restricted action associated to a cyclic-image section. -/
abbrev action
    (s : GorensteinCyclicImageSection M P) :
    M →* MulAut s.toSubgroup :=
  invariantAbelianizationAction
    M P s.toSubgroup s.smul_mem

/-- The kernel of the original action on `P` acts trivially on every
invariant subgroup of `P / P'`. -/
theorem okuyamaWajimaActionKernel_le_action_ker
    (s : GorensteinCyclicImageSection M P) :
    okuyamaWajimaActionKernel M P ≤ s.action.ker := by
  intro m hm
  rw [MonoidHom.mem_ker]
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  change m • (a : Abelianization P) = (a : Abelianization P)
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

/-- Consequently the displayed subgroup `L`, once identified with the
original action kernel, lies in the kernel of the section action. -/
theorem subgroup_le_action_ker
    (s : GorensteinCyclicImageSection M P)
    (L : Subgroup M)
    (hL : L = okuyamaWajimaActionKernel M P) :
    L ≤ s.action.ker := by
  rw [hL]
  exact s.okuyamaWajimaActionKernel_le_action_ker

/-- The action on the invariant section descends through `M / L`. -/
def quotientAction
    (s : GorensteinCyclicImageSection M P)
    (L : Subgroup M) [L.Normal]
    (hL : L = okuyamaWajimaActionKernel M P) :
    M ⧸ L →* MulAut s.toSubgroup :=
  QuotientGroup.lift L s.action
    (s.subgroup_le_action_ker L hL)

@[simp]
theorem quotientAction_mk
    (s : GorensteinCyclicImageSection M P)
    (L : Subgroup M) [L.Normal]
    (hL : L = okuyamaWajimaActionKernel M P)
    (m : M) :
    s.quotientAction L hL (QuotientGroup.mk' L m) =
      s.action m :=
  rfl

/-- Descending through `M / L` does not change the action image. -/
theorem quotientAction_range_eq
    (s : GorensteinCyclicImageSection M P)
    (L : Subgroup M) [L.Normal]
    (hL : L = okuyamaWajimaActionKernel M P) :
    (s.quotientAction L hL).range = s.action.range := by
  apply le_antisymm
  · rintro y ⟨q, rfl⟩
    refine Quotient.inductionOn' q ?_
    intro m
    exact ⟨m, rfl⟩
  · rintro y ⟨m, rfl⟩
    exact ⟨QuotientGroup.mk' L m, rfl⟩

/-- The quotient action therefore also has cyclic image. -/
theorem quotientAction_range_isCyclic
    (s : GorensteinCyclicImageSection M P)
    (L : Subgroup M) [L.Normal]
    (hL : L = okuyamaWajimaActionKernel M P) :
    IsCyclic (s.quotientAction L hL).range := by
  rw [s.quotientAction_range_eq L hL]
  exact s.actionImage_isCyclic

/-- The pullback kernel in `M`, bundled with its automatic normality. -/
def actionKernelData
    (s : GorensteinCyclicImageSection M P) :
    NormalSubgroupData M where
  toSubgroup := s.action.ker
  normal := inferInstance

@[simp]
theorem actionKernelData_toSubgroup
    (s : GorensteinCyclicImageSection M P) :
    s.actionKernelData.toSubgroup = s.action.ker :=
  rfl

/-- The first isomorphism theorem identifies the quotient by the
pullback kernel with the action image. -/
def quotientActionKernelEquivRange
    (s : GorensteinCyclicImageSection M P) :
    M ⧸ s.actionKernelData.toSubgroup ≃*
      s.action.range :=
  QuotientGroup.quotientKerEquivRange s.action

/-- Hence the quotient by the pullback kernel is cyclic. -/
theorem quotient_actionKernel_isCyclic
    (s : GorensteinCyclicImageSection M P) :
    IsCyclic (M ⧸ s.actionKernelData.toSubgroup) :=
  s.quotientActionKernelEquivRange.isCyclic.mpr
    s.actionImage_isCyclic

/-- Every point of the invariant section is fixed by the pullback
kernel. -/
theorem coe_mem_fixedPoints_actionKernel
    (s : GorensteinCyclicImageSection M P)
    (a : s.toSubgroup) :
    (a : Abelianization P) ∈
      FixedPoints.subgroup
        s.actionKernelData.toSubgroup
        (Abelianization P) := by
  intro u
  change
    (u : M) • (a : Abelianization P) =
      (a : Abelianization P)
  have hu :
      s.action (u : M) = 1 :=
    MonoidHom.mem_ker.mp u.2
  have hua :=
    DFunLike.congr_fun hu a
  have hua_coe :=
    congrArg
      (fun z : s.toSubgroup ↦
        (z : Abelianization P)) hua
  simpa using hua_coe

/-- The nonzero invariant section supplies a nonidentity fixed point
for the pullback kernel. -/
theorem fixedPoints_actionKernel_nontrivial
    (s : GorensteinCyclicImageSection M P) :
    (⊥ : Subgroup (Abelianization P)) <
      FixedPoints.subgroup
        s.actionKernelData.toSubgroup
        (Abelianization P) := by
  obtain ⟨a, haA, ha1⟩ :=
    (Subgroup.nontrivial_iff_exists_ne_one s.toSubgroup).mp
      ((Subgroup.nontrivial_iff_ne_bot s.toSubgroup).mpr
        (bot_lt_iff_ne_bot.mp s.nontrivial))
  rw [bot_lt_iff_ne_bot]
  intro hbot
  have haFixed :
      a ∈ FixedPoints.subgroup
        s.actionKernelData.toSubgroup
        (Abelianization P) :=
    s.coe_mem_fixedPoints_actionKernel ⟨a, haA⟩
  have :
      a = 1 := by
    have := haFixed
    rw [hbot] at this
    simpa using this
  exact ha1 this

/-- A cyclic-image invariant section gives the complete bundled output
required by the Okuyama--Wajima proof. -/
def toOkuyamaWajimaCyclicQuotientSubgroup
    (s : GorensteinCyclicImageSection M P)
    (L : Subgroup M)
    (hL : L = okuyamaWajimaActionKernel M P) :
    OkuyamaWajimaCyclicQuotientSubgroup M P L where
  U := s.actionKernelData
  L_le_U := s.subgroup_le_action_ker L hL
  quotient_isCyclic := s.quotient_actionKernel_isCyclic
  fixedPoints_nontrivial :=
    s.fixedPoints_actionKernel_nontrivial

end GorensteinCyclicImageSection

/-- The reduced representation-theoretic existence interface.

This is strictly smaller than
`GorensteinCyclicQuotientSubgroupExistenceInput`: it only asks for a
nonzero invariant section with cyclic restricted action image.  The
normal subgroup `U`, its containment relation, its cyclic quotient, and
its fixed point are then constructed rather than assumed.  The interface
is proved in `GorensteinCyclicImageSectionExistence.lean`. -/
def GorensteinCyclicImageSectionExistenceInput :
    Prop :=
  Nonempty (GorensteinCyclicImageSection M P)

variable {M P}

/-- The cyclic-image section input implies the original isolated
Gorenstein input.  The coprimality and `p`-group hypotheses belong to
the expected proof that the section exists; the reduction itself uses
only the section and the identification of `L` with the action kernel. -/
theorem gorensteinCyclicQuotientSubgroupExistenceInput_of_section
    (p : ℕ)
    [Fact p.Prime]
    [Finite M] [Finite P]
    [Nontrivial P]
    (L : Subgroup M) [L.Normal]
    (hP : IsPGroup p P)
    (hM : IsPPrimeGroup p M)
    (hL : L = okuyamaWajimaActionKernel M P)
    (hML : IsMulCommutative (M ⧸ L))
    (hSection :
      GorensteinCyclicImageSectionExistenceInput M P) :
    GorensteinCyclicQuotientSubgroupExistenceInput
      M P p L hP hM hL hML := by
  obtain ⟨s⟩ := hSection
  exact ⟨s.toOkuyamaWajimaCyclicQuotientSubgroup L hL⟩

end GroupTheory
end McKayConjecture
