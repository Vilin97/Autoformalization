/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.CoprimeActionSemidirect
import McKayConjecture.GroupTheory.PGroupMaximalCyclicQuotient
import Mathlib.GroupTheory.Abelianization.Finite

/-!
# The cyclic-quotient subgroup in the Okuyama--Wajima proof

In the proof of Okuyama--Wajima's extension theorem, a finite `p'`-group
`M` acts on a nontrivial finite `p`-group `P`.  If `L` is the kernel of
the action and `M / L` is abelian, Gorenstein's coprime-action theorem
produces a subgroup `U` such that

* `L ≤ U`;
* `U` is normal in `M`;
* `M / U` is cyclic; and
* `U` has a nonidentity fixed point on `P / P'`.

This file isolates the exact source interface as
`GorensteinCyclicQuotientSubgroupExistenceInput`; it is proved in
`GorensteinCyclicImageSectionExistence.lean`.  No axiom is added.

The remainder of the source step is formalized here.  In particular, the
fixed-point subgroup is either all of `P / P'` or is proper and
nontrivial.  Its full preimage `Q` in `P` is normal and `M`-invariant.  In
the proper branch one has

`P' < Q < P`,

the quotient `P / Q` is a nontrivial `p`-group, and `[P : Q]` is a
`p`-power.  The canonical copy of `Q` is also normal in the action
semidirect product `P ⋊ M`.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace GroupTheory

variable (M : Type u) (P : Type v)
variable [Group M] [Group P]
variable [MulDistribMulAction M P]

/-- The action of `M` on `P` induces an action homomorphism on the
abelianization `P / P'`. -/
def abelianizationActionHom :
    M →* MulAut (Abelianization P) where
  toFun m :=
    (MulDistribMulAction.toMulEquiv P m).abelianizationCongr
  map_one' := by
    apply MulEquiv.ext
    rintro ⟨z⟩
    change
      Abelianization.of ((1 : M) • z) =
        Abelianization.of z
    rw [one_smul]
  map_mul' m n := by
    apply MulEquiv.ext
    rintro ⟨z⟩
    change
      Abelianization.of ((m * n) • z) =
        Abelianization.of (m • (n • z))
    rw [mul_smul]

/-- The multiplicative action on `P / P'` induced from the action on
`P`. -/
noncomputable instance abelianizationMulDistribMulAction :
    MulDistribMulAction M (Abelianization P) :=
  MulDistribMulAction.compHom
    (Abelianization P) (abelianizationActionHom M P)

@[simp]
theorem smul_abelianization_of
    (m : M) (x : P) :
    m • Abelianization.of x =
      Abelianization.of (m • x) :=
  rfl

/-- The kernel `L` occurring in the source theorem: the elements of `M`
which act trivially on `P`. -/
abbrev okuyamaWajimaActionKernel :
    Subgroup M :=
  (MulDistribMulAction.toMulAut M P).ker

/-- A bundled output of the Gorenstein cyclic-quotient subgroup theorem.

Bundling normality makes the quotient group in `quotient_isCyclic`
available without introducing an axiom or a local choice. -/
structure OkuyamaWajimaCyclicQuotientSubgroup
    (L : Subgroup M) where
  /-- The normal subgroup `U` of `M`. -/
  U : NormalSubgroupData M
  /-- The action kernel is contained in `U`. -/
  L_le_U : L ≤ U.toSubgroup
  /-- The quotient `M / U` is cyclic. -/
  quotient_isCyclic :
    IsCyclic (M ⧸ U.toSubgroup)
  /-- `U` has a nonidentity fixed point on `P / P'`. -/
  fixedPoints_nontrivial :
    (⊥ : Subgroup (Abelianization P)) <
      FixedPoints.subgroup U.toSubgroup
        (Abelianization P)

/-- The exact Gorenstein source interface.

Mathematically, Gorenstein, Chapter 3, Theorem 2.2 supplies this
proposition from the displayed hypotheses: `P` is a nontrivial finite
`p`-group, `M` is a finite `p'`-group, `L` is the kernel of the action,
and `M / L` is abelian.  It is kept as a proposition rather than a
typeclass, and is proved in
`GorensteinCyclicImageSectionExistence.lean`. -/
def GorensteinCyclicQuotientSubgroupExistenceInput
    (p : ℕ)
    [Fact p.Prime]
    [Finite M] [Finite P]
    [Nontrivial P]
    (L : Subgroup M) [L.Normal]
    (_hP : IsPGroup p P)
    (_hM : IsPPrimeGroup p M)
    (_hL : L = okuyamaWajimaActionKernel M P)
    (_hML : IsMulCommutative (M ⧸ L)) :
    Prop :=
  Nonempty (OkuyamaWajimaCyclicQuotientSubgroup M P L)

variable {M P}

/-- Unpack the precisely isolated Gorenstein existence input. -/
theorem exists_okuyamaWajima_cyclicQuotientSubgroup
    {p : ℕ}
    [Fact p.Prime]
    [Finite M] [Finite P]
    [Nontrivial P]
    (L : Subgroup M) [L.Normal]
    (hP : IsPGroup p P)
    (hM : IsPPrimeGroup p M)
    (hL : L = okuyamaWajimaActionKernel M P)
    (hML : IsMulCommutative (M ⧸ L))
    (hGorenstein :
      GorensteinCyclicQuotientSubgroupExistenceInput
        M P p L hP hM hL hML) :
    Nonempty (OkuyamaWajimaCyclicQuotientSubgroup M P L) :=
  hGorenstein

namespace OkuyamaWajimaCyclicQuotientSubgroup

variable {L : Subgroup M}

/-- The `U`-fixed subgroup of the abelianization. -/
abbrev fixedPoints
    (d : OkuyamaWajimaCyclicQuotientSubgroup M P L) :
    Subgroup (Abelianization P) :=
  FixedPoints.subgroup d.U.toSubgroup
    (Abelianization P)

/-- The full preimage in `P` of the `U`-fixed subgroup of `P / P'`.
This is the subgroup denoted `Q` in the proper branch of the printed
proof. -/
abbrev fixedPointPreimage
    (d : OkuyamaWajimaCyclicQuotientSubgroup M P L) :
    Subgroup P :=
  d.fixedPoints.comap Abelianization.of

/-- The exact full-versus-proper dichotomy used in the printed proof. -/
theorem fixedPoints_eq_top_or_proper_nontrivial
    (d : OkuyamaWajimaCyclicQuotientSubgroup M P L) :
    d.fixedPoints = ⊤ ∨
      ((⊥ : Subgroup (Abelianization P)) < d.fixedPoints ∧
        d.fixedPoints < ⊤) := by
  rcases eq_top_or_lt_top d.fixedPoints with htop | hproper
  · exact Or.inl htop
  · exact Or.inr ⟨d.fixedPoints_nontrivial, hproper⟩

/-- The commutator subgroup lies strictly below the fixed-point
preimage.  This is the useful preimage form of the nontriviality supplied
by Gorenstein's theorem. -/
theorem commutator_lt_fixedPointPreimage
    (d : OkuyamaWajimaCyclicQuotientSubgroup M P L) :
    _root_.commutator P < d.fixedPointPreimage := by
  let π : P →* Abelianization P := Abelianization.of
  have hπ : Function.Surjective π :=
    QuotientGroup.mk'_surjective (_root_.commutator P)
  have hcomap :
      (⊥ : Subgroup (Abelianization P)).comap π <
        d.fixedPoints.comap π :=
    (Subgroup.comap_lt_comap_of_surjective hπ).2
      d.fixedPoints_nontrivial
  simpa only [π, MonoidHom.comap_bot,
    Abelianization.ker_of] using hcomap

/-- The fixed-point preimage is nontrivial. -/
theorem bot_lt_fixedPointPreimage
    (d : OkuyamaWajimaCyclicQuotientSubgroup M P L) :
    (⊥ : Subgroup P) < d.fixedPointPreimage :=
  lt_of_le_of_lt bot_le d.commutator_lt_fixedPointPreimage

/-- The fixed-point preimage is normal in `P`. -/
instance fixedPointPreimage_normal
    (d : OkuyamaWajimaCyclicQuotientSubgroup M P L) :
    d.fixedPointPreimage.Normal :=
  Subgroup.Normal.comap inferInstance Abelianization.of

/-- In the full-fixed-point branch, the preimage is all of `P`. -/
theorem fixedPointPreimage_eq_top
    (d : OkuyamaWajimaCyclicQuotientSubgroup M P L)
    (hfull : d.fixedPoints = ⊤) :
    d.fixedPointPreimage = ⊤ := by
  rw [fixedPointPreimage, hfull, Subgroup.comap_top]

/-- In the proper-fixed-point branch, the preimage is proper in `P`. -/
theorem fixedPointPreimage_lt_top
    (d : OkuyamaWajimaCyclicQuotientSubgroup M P L)
    (hproper : d.fixedPoints < ⊤) :
    d.fixedPointPreimage < ⊤ := by
  let π : P →* Abelianization P := Abelianization.of
  have hπ : Function.Surjective π :=
    QuotientGroup.mk'_surjective (_root_.commutator P)
  have hcomap :
      d.fixedPoints.comap π <
        (⊤ : Subgroup (Abelianization P)).comap π :=
    (Subgroup.comap_lt_comap_of_surjective hπ).2 hproper
  simpa only [π, Subgroup.comap_top] using hcomap

/-- Normality of `U` makes its fixed points stable under the whole group
`M`; equivariance of the abelianization map then makes `Q` stable under
`M`. -/
theorem smul_mem_fixedPointPreimage
    (d : OkuyamaWajimaCyclicQuotientSubgroup M P L)
    (m : M) {x : P}
    (hx : x ∈ d.fixedPointPreimage) :
    m • x ∈ d.fixedPointPreimage := by
  change Abelianization.of (m • x) ∈ d.fixedPoints
  rw [← smul_abelianization_of]
  exact smul_mem_fixedPoints_of_normal m hx

/-- The canonical copy of the fixed-point preimage in `P ⋊ M`. -/
abbrev fixedPointPreimageInSemidirect
    (d : OkuyamaWajimaCyclicQuotientSubgroup M P L) :
    Subgroup (actionSemidirectProduct M P) :=
  d.fixedPointPreimage.map
    (SemidirectProduct.inl :
      P →* actionSemidirectProduct M P)

/-- The canonical copy of `Q` is normal in the action semidirect
product.  This packages the two facts used in the source proof: `Q ◁ P`
and `M` normalizes `Q`. -/
instance fixedPointPreimageInSemidirect_normal
    (d : OkuyamaWajimaCyclicQuotientSubgroup M P L) :
    d.fixedPointPreimageInSemidirect.Normal := by
  refine ⟨?_⟩
  rintro _ ⟨q, hq, rfl⟩ g
  refine ⟨g.left * (g.right • q) * g.left⁻¹, ?_, ?_⟩
  · exact (inferInstance :
      d.fixedPointPreimage.Normal).conj_mem
        (g.right • q)
        (d.smul_mem_fixedPointPreimage g.right hq)
        g.left
  · apply SemidirectProduct.ext
    · simp
    · simp

section PGroupConsequences

variable {p : ℕ} [Fact p.Prime]
variable [Finite P]

/-- Every quotient of the ambient `p`-group is again a `p`-group. -/
theorem fixedPointPreimage_quotient_isPGroup
    (d : OkuyamaWajimaCyclicQuotientSubgroup M P L)
    (hP : IsPGroup p P) :
    IsPGroup p (P ⧸ d.fixedPointPreimage) :=
  hP.of_surjective
    (QuotientGroup.mk' d.fixedPointPreimage)
    (QuotientGroup.mk'_surjective d.fixedPointPreimage)

/-- In the proper branch, the quotient `P / Q` is nontrivial. -/
theorem fixedPointPreimage_quotient_nontrivial
    (d : OkuyamaWajimaCyclicQuotientSubgroup M P L)
    (hproper : d.fixedPoints < ⊤) :
    Nontrivial (P ⧸ d.fixedPointPreimage) :=
  QuotientGroup.nontrivial_iff.mpr
    (d.fixedPointPreimage_lt_top hproper).ne

/-- In the proper branch, `Q` has strictly smaller order than `P`. -/
theorem fixedPointPreimage_card_lt
    (d : OkuyamaWajimaCyclicQuotientSubgroup M P L)
    (hproper : d.fixedPoints < ⊤) :
    Nat.card d.fixedPointPreimage < Nat.card P := by
  obtain ⟨x, _hxP, hxQ⟩ :=
    SetLike.exists_of_lt
      (d.fixedPointPreimage_lt_top hproper)
  exact Finite.card_subtype_lt hxQ

/-- The index `[P : Q]` is a power of `p`. -/
theorem fixedPointPreimage_index_eq_prime_power
    (d : OkuyamaWajimaCyclicQuotientSubgroup M P L)
    (hP : IsPGroup p P) :
    ∃ n : ℕ, d.fixedPointPreimage.index = p ^ n := by
  rw [Subgroup.index_eq_card]
  exact IsPGroup.iff_card.mp
    (d.fixedPointPreimage_quotient_isPGroup hP)

/-- Complete subgroup information in the proper branch, in the form
needed to construct the smaller induction problem. -/
theorem properBranch_preimage_data
    (d : OkuyamaWajimaCyclicQuotientSubgroup M P L)
    (hP : IsPGroup p P)
    (hproper : d.fixedPoints < ⊤) :
    _root_.commutator P < d.fixedPointPreimage ∧
      d.fixedPointPreimage < ⊤ ∧
      IsPGroup p (P ⧸ d.fixedPointPreimage) ∧
      ∃ n : ℕ, d.fixedPointPreimage.index = p ^ n :=
  ⟨d.commutator_lt_fixedPointPreimage,
    d.fixedPointPreimage_lt_top hproper,
    d.fixedPointPreimage_quotient_isPGroup hP,
    d.fixedPointPreimage_index_eq_prime_power hP⟩

end PGroupConsequences

end OkuyamaWajimaCyclicQuotientSubgroup

end GroupTheory
end McKayConjecture
