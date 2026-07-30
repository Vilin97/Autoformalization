/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.QuotientGroup.Basic
import McKayConjecture.Character.InnerAutomorphism
import McKayConjecture.GroupTheory.InnerAutomorphismKernel
import McKayConjecture.InductiveMcKay.AutomorphismStabilizer

/-!
# Adjusting automorphisms to stabilize a fixed Sylow subgroup

Every automorphism sends a fixed Sylow subgroup to a conjugate Sylow
subgroup.  Multiplication by a suitable inner automorphism therefore gives
a representative of the same outer class which stabilizes the fixed Sylow
subgroup.

This file packages that observation, identifies the inner part of the Sylow
automorphism stabilizer with the image of the exact Sylow normalizer, and
states the exact quotient-generation condition needed to reduce a
full-stabilizer calculation to finitely many outer representatives.
-/

noncomputable section

open scoped Pointwise

universe u v

namespace McKayConjecture
namespace InductiveMcKay

variable {G : Type u} [Group G] {p : ℕ}

/-! ### Inner automorphisms and the outer quotient -/

/-- The subgroup of inner automorphisms of a group. -/
abbrev InnerAutomorphismSubgroup (G : Type u) [Group G] :
    Subgroup (MulAut G) :=
  (MulAut.conj : G →* MulAut G).range

/-- The inner automorphism subgroup has the cardinality of the quotient by
the center. -/
theorem natCard_innerAutomorphismSubgroup_eq_quotient_center :
    Nat.card (InnerAutomorphismSubgroup G) =
      Nat.card (G ⧸ Subgroup.center G) := by
  change
    Nat.card ((MulAut.conj : G →* MulAut G).range) =
      Nat.card (G ⧸ Subgroup.center G)
  calc
    Nat.card ((MulAut.conj : G →* MulAut G).range) =
        Nat.card
          (G ⧸ (MulAut.conj : G →* MulAut G).ker) :=
      Nat.card_congr
        (QuotientGroup.quotientKerEquivRange
          (MulAut.conj : G →* MulAut G)).toEquiv.symm
    _ = Nat.card (G ⧸ Subgroup.center G) := by
      rw [GroupTheory.mulAutConj_ker_eq_center]

/-- Inner automorphisms form a normal subgroup of the full automorphism
group. -/
instance innerAutomorphismSubgroup_normal :
    (InnerAutomorphismSubgroup G).Normal where
  conj_mem := by
    intro b hb a
    obtain ⟨g, rfl⟩ := hb
    refine ⟨a g, ?_⟩
    apply MulEquiv.ext
    intro x
    simp [MulAut.mul_apply, MulAut.conj_apply]

/-- The outer automorphism group, defined as automorphisms modulo inner
automorphisms. -/
abbrev OuterAutomorphismQuotient (G : Type u) [Group G] :=
  MulAut G ⧸ InnerAutomorphismSubgroup G

/-! ### The normalizer realizes the inner part of the stabilizer -/

/-- Conjugation by an element of the exact Sylow normalizer, bundled as an
element of the Sylow automorphism stabilizer. -/
def normalizerInnerSylowAutStabilizerHom
    (P : Sylow p G) :
    SylowNormalizer P →* SylowAutStabilizer P where
  toFun g :=
    ⟨MulAut.conj g.1, by
      rw [SylowAutStabilizer.mem_iff]
      apply Sylow.ext
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp g.2⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (MulAut.conj : G →* MulAut G)
  map_mul' g h := by
    apply Subtype.ext
    exact map_mul (MulAut.conj : G →* MulAut G) g.1 h.1

@[simp]
theorem normalizerInnerSylowAutStabilizerHom_coe
    (P : Sylow p G) (g : SylowNormalizer P) :
    (normalizerInnerSylowAutStabilizerHom P g).1 =
      MulAut.conj g.1 :=
  rfl

/-- The inner automorphisms which stabilize `P`. -/
abbrev SylowInnerAutomorphismStabilizer
    (P : Sylow p G) :
    Subgroup (SylowAutStabilizer P) :=
  (InnerAutomorphismSubgroup G).comap
    (SylowAutStabilizer P).subtype

/-- A conjugating element for an inner automorphism in the Sylow
stabilizer lies in the exact Sylow normalizer. -/
theorem mem_normalizer_of_inner_eq_sylowAutStabilizer
    (P : Sylow p G)
    (a : SylowAutStabilizer P)
    (g : G)
    (ha : a.1 = MulAut.conj g) :
    g ∈ Subgroup.normalizer (P : Set G) := by
  apply
    (Subgroup.mem_normalizer_iff_map_conj_eq
      (H := (P : Subgroup G))).2
  have hstabilizes :=
    congrArg
      (fun Q : Sylow p G ↦ (Q : Subgroup G))
      a.2
  rw [ha] at hstabilizes
  exact hstabilizes

/-- The image of the exact Sylow normalizer is exactly the inner part of
the Sylow automorphism stabilizer. -/
theorem normalizerInnerSylowAutStabilizerHom_range
    (P : Sylow p G) :
    (normalizerInnerSylowAutStabilizerHom P).range =
      SylowInnerAutomorphismStabilizer P := by
  ext a
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.1, rfl⟩
  · intro ha
    obtain ⟨g, hg⟩ := ha
    let n : SylowNormalizer P :=
      ⟨g,
        mem_normalizer_of_inner_eq_sylowAutStabilizer
          P a g hg.symm⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    exact hg

/-! ### Inner adjustment of arbitrary automorphisms -/

variable [Finite G] [Fact p.Prime]

/-- Every automorphism can be multiplied on the left by an inner
automorphism so that it stabilizes the fixed Sylow subgroup. -/
theorem exists_inner_mul_mem_sylowAutStabilizer
    (P : Sylow p G)
    (a : MulAut G) :
    ∃ g : G,
      MulAut.conj g * a ∈ SylowAutStabilizer P := by
  obtain ⟨g, hg⟩ :=
    MulAction.exists_smul_eq G (a • P) P
  refine ⟨g, ?_⟩
  rw [SylowAutStabilizer.mem_iff, mul_smul]
  exact hg

/-- A selected inner correction which makes `a` stabilize `P`. -/
def sylowAutomorphismInnerAdjustment
    (P : Sylow p G)
    (a : MulAut G) :
    G :=
  Classical.choose
    (exists_inner_mul_mem_sylowAutStabilizer P a)

/-- The selected correction has the required stabilizing property. -/
theorem sylowAutomorphismInnerAdjustment_spec
    (P : Sylow p G)
    (a : MulAut G) :
    MulAut.conj (sylowAutomorphismInnerAdjustment P a) * a ∈
      SylowAutStabilizer P :=
  Classical.choose_spec
    (exists_inner_mul_mem_sylowAutStabilizer P a)

/-- The selected representative of the outer class of `a` which
stabilizes `P`. -/
def sylowAdjustedAutomorphism
    (P : Sylow p G)
    (a : MulAut G) :
    SylowAutStabilizer P :=
  ⟨MulAut.conj (sylowAutomorphismInnerAdjustment P a) * a,
    sylowAutomorphismInnerAdjustment_spec P a⟩

@[simp]
theorem sylowAdjustedAutomorphism_coe
    (P : Sylow p G)
    (a : MulAut G) :
    (sylowAdjustedAutomorphism P a).1 =
      MulAut.conj (sylowAutomorphismInnerAdjustment P a) * a :=
  rfl

/-- The original automorphism differs from its adjusted representative by
an inner automorphism. -/
theorem original_eq_inner_mul_sylowAdjustedAutomorphism
    (P : Sylow p G)
    (a : MulAut G) :
    a =
      MulAut.conj (sylowAutomorphismInnerAdjustment P a)⁻¹ *
        (sylowAdjustedAutomorphism P a).1 := by
  rw [sylowAdjustedAutomorphism_coe]
  rw [map_inv]
  simp

/-- Inner adjustment does not change the action of an automorphism on an
ordinary irreducible character. -/
@[simp]
theorem sylowAdjustedAutomorphism_smul_irreducibleCharacter
    (P : Sylow p G)
    (a : MulAut G)
    (χ : IrreducibleCharacter G) :
    sylowAdjustedAutomorphism P a • χ =
      a • χ := by
  change
    (sylowAdjustedAutomorphism P a).1 • χ =
      a • χ
  rw [sylowAdjustedAutomorphism_coe, mul_smul,
    IrreducibleCharacter.conj_smul]

/-- Inner adjustment does not change the action of an automorphism on a
prime-to-`q` irreducible character. -/
@[simp]
theorem sylowAdjustedAutomorphism_smul_pPrime
    (P : Sylow p G)
    (a : MulAut G)
    (q : Nat)
    (χ : PPrimeIrreducibleCharacter G q) :
    sylowAdjustedAutomorphism P a • χ =
      a • χ := by
  change
    (sylowAdjustedAutomorphism P a).1 • χ =
      a • χ
  rw [sylowAdjustedAutomorphism_coe, mul_smul,
    pPrime_conj_smul]

/-! ### The quotient map and its generation boundary -/

/-- The natural map from the Sylow automorphism stabilizer to the outer
automorphism group. -/
def sylowAutStabilizerOuterHom
    (P : Sylow p G) :
    SylowAutStabilizer P →* OuterAutomorphismQuotient G :=
  (QuotientGroup.mk' (InnerAutomorphismSubgroup G)).comp
    (SylowAutStabilizer P).subtype

/-- Inner adjustment does not change the image in the outer quotient. -/
@[simp]
theorem sylowAutStabilizerOuterHom_adjusted
    (P : Sylow p G)
    (a : MulAut G) :
    sylowAutStabilizerOuterHom P
        (sylowAdjustedAutomorphism P a) =
      QuotientGroup.mk' (InnerAutomorphismSubgroup G) a := by
  change
    QuotientGroup.mk' (InnerAutomorphismSubgroup G)
        (MulAut.conj (sylowAutomorphismInnerAdjustment P a) * a) =
      QuotientGroup.mk' (InnerAutomorphismSubgroup G) a
  rw [map_mul]
  have hinner :
      QuotientGroup.mk' (InnerAutomorphismSubgroup G)
          (MulAut.conj (sylowAutomorphismInnerAdjustment P a)) =
        1 := by
    apply (QuotientGroup.eq_one_iff _).2
    exact ⟨sylowAutomorphismInnerAdjustment P a, rfl⟩
  rw [hinner, one_mul]

/-- Restriction to the Sylow stabilizer is still onto the full outer
automorphism group. -/
theorem sylowAutStabilizerOuterHom_surjective
    (P : Sylow p G) :
    Function.Surjective (sylowAutStabilizerOuterHom P) := by
  intro q
  obtain ⟨a, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (InnerAutomorphismSubgroup G) q
  exact
    ⟨sylowAdjustedAutomorphism P a,
      sylowAutStabilizerOuterHom_adjusted P a⟩

omit [Finite G] [Fact p.Prime] in
/-- The kernel of the outer-quotient map is precisely the stabilizing
inner automorphisms. -/
theorem sylowAutStabilizerOuterHom_ker
    (P : Sylow p G) :
    (sylowAutStabilizerOuterHom P).ker =
      SylowInnerAutomorphismStabilizer P := by
  ext a
  change
    QuotientGroup.mk' (InnerAutomorphismSubgroup G) a.1 = 1 ↔
      a.1 ∈ InnerAutomorphismSubgroup G
  exact QuotientGroup.eq_one_iff a.1

omit [Finite G] [Fact p.Prime] in
/-- Equivalently, the kernel is the image of the exact Sylow normalizer
acting by inner automorphisms. -/
theorem sylowAutStabilizerOuterHom_ker_eq_normalizerInner_range
    (P : Sylow p G) :
    (sylowAutStabilizerOuterHom P).ker =
      (normalizerInnerSylowAutStabilizerHom P).range := by
  rw [sylowAutStabilizerOuterHom_ker,
    normalizerInnerSylowAutStabilizerHom_range]

/-- The quotient of the Sylow automorphism stabilizer by its inner part is
canonically the full outer automorphism group. -/
def sylowAutStabilizerQuotientInnerEquiv
    (P : Sylow p G) :
    SylowAutStabilizer P ⧸
        SylowInnerAutomorphismStabilizer P ≃*
      OuterAutomorphismQuotient G :=
  (QuotientGroup.quotientMulEquivOfEq
      (sylowAutStabilizerOuterHom_ker P).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (sylowAutStabilizerOuterHom P)
      (sylowAutStabilizerOuterHom_surjective P))

/-- For a homomorphism, generators of the target lift to generators of
the source after adjoining the kernel. -/
theorem closure_union_ker_eq_top_of_image_closure_eq_top
    {A : Type u} {B : Type v}
    [Group A] [Group B]
    (f : A →* B)
    (generators : Set A)
    (hgenerates :
      Subgroup.closure (f '' generators) = ⊤) :
    Subgroup.closure
        (generators ∪ (f.ker : Set A)) =
      ⊤ := by
  let H : Subgroup A :=
    Subgroup.closure
      (generators ∪ (f.ker : Set A))
  have hker : f.ker ≤ H := by
    intro x hx
    exact Subgroup.subset_closure (Or.inr hx)
  have hmap : H.map f = ⊤ := by
    apply top_unique
    rw [← hgenerates, Subgroup.closure_le]
    rintro y ⟨x, hx, rfl⟩
    exact
      ⟨x, Subgroup.subset_closure (Or.inl hx), rfl⟩
  calc
    H = (H.map f).comap f := by
      symm
      rw [Subgroup.comap_map_eq, sup_eq_left.mpr hker]
    _ = ⊤ := by rw [hmap, Subgroup.comap_top]

/-- A set of stabilizer elements generates the outer quotient when its
images generate that quotient. -/
def GeneratesSylowOuterQuotient
    (P : Sylow p G)
    (generators : Set (SylowAutStabilizer P)) :
    Prop :=
  Subgroup.closure
      (sylowAutStabilizerOuterHom P '' generators) =
    ⊤

/-- A set of stabilizer elements generates modulo inner automorphisms when
it, together with the inner part of the stabilizer, generates the whole
stabilizer. -/
def GeneratesSylowAutStabilizerModuloInner
    (P : Sylow p G)
    (generators : Set (SylowAutStabilizer P)) :
    Prop :=
  Subgroup.closure
      (generators ∪
        (SylowInnerAutomorphismStabilizer P :
          Set (SylowAutStabilizer P))) =
    ⊤

omit [Finite G] [Fact p.Prime] in
/-- Generation of the outer quotient is exactly the sufficient input for
generation of the Sylow stabilizer after adjoining its inner part. -/
theorem generatesSylowAutStabilizerModuloInner_of_generatesOuter
    (P : Sylow p G)
    (generators : Set (SylowAutStabilizer P))
    (hgenerates :
      GeneratesSylowOuterQuotient P generators) :
    GeneratesSylowAutStabilizerModuloInner P generators := by
  rw [GeneratesSylowAutStabilizerModuloInner,
    ← sylowAutStabilizerOuterHom_ker P]
  exact
    closure_union_ker_eq_top_of_image_closure_eq_top
      (sylowAutStabilizerOuterHom P)
      generators hgenerates

omit [Finite G] [Fact p.Prime] in
/-- Equivalently, generators of the outer quotient together with the
image of the exact Sylow normalizer generate the full stabilizer. -/
theorem closure_union_normalizerInner_range_eq_top_of_generatesOuter
    (P : Sylow p G)
    (generators : Set (SylowAutStabilizer P))
    (hgenerates :
      GeneratesSylowOuterQuotient P generators) :
    Subgroup.closure
        (generators ∪
          ((normalizerInnerSylowAutStabilizerHom P).range :
            Set (SylowAutStabilizer P))) =
      ⊤ := by
  rw [normalizerInnerSylowAutStabilizerHom_range]
  exact
    generatesSylowAutStabilizerModuloInner_of_generatesOuter
      P generators hgenerates

end InductiveMcKay
end McKayConjecture
