/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.NoncommPiCoprod
import McKayConjecture.GroupTheory.MinimalNormalCharacteristic

/-!
# Simple factors of a nonabelian minimal normal subgroup

A finite nonabelian minimal normal subgroup is an internal direct product of
isomorphic nonabelian simple groups.  We construct the factors as the
distinct conjugates, under the ambient group, of a chosen minimal normal
subgroup of the given minimal normal subgroup.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory

open scoped IsMulCommutative

variable {G : Type u} [Group G]

namespace MinimalNormalFactors

/-- A chosen minimal normal subgroup of a nontrivial finite group. -/
def chosenMinimalNormalSubgroup
    (H : Type u) [Group H] [Finite H] [Nontrivial H] :
    Subgroup H :=
  Classical.choose (exists_minimalNormal (G := H))

/-- The chosen subgroup is minimal normal. -/
theorem chosenMinimalNormalSubgroup_isMinimalNormal
    (H : Type u) [Group H] [Finite H] [Nontrivial H] :
    IsMinimalNormal (chosenMinimalNormalSubgroup H) :=
  Classical.choose_spec (exists_minimalNormal (G := H))

/-- The conjugate inside a normal subgroup `N` of a subgroup `L ≤ N`. -/
def conjugateFactor
    (N : Subgroup G) [N.Normal] (L : Subgroup N) (g : G) :
    Subgroup N :=
  L.map (MulAut.conjNormal g).toMonoidHom

/-- The finite index type of distinct ambient conjugates of `L`.  Indexing
by the subgroups themselves removes repetitions from the orbit. -/
def ConjugateFactorIndex
    (N : Subgroup G) [N.Normal] (L : Subgroup N) :=
  {K : Subgroup N // ∃ g : G, conjugateFactor N L g = K}

/-- The subgroup represented by an index in the conjugacy orbit. -/
def conjugateFactorFamily
    (N : Subgroup G) [N.Normal] (L : Subgroup N)
    (i : ConjugateFactorIndex N L) :
    Subgroup N :=
  i.1

instance conjugateFactorIndex_finite
    [Finite G] (N : Subgroup G) [N.Normal] (L : Subgroup N) :
    Finite (ConjugateFactorIndex N L) := by
  exact Finite.of_injective
    (fun i : ConjugateFactorIndex N L ↦
      (i.1 : Set N))
    (fun _ _ h ↦ Subtype.ext (SetLike.ext' h))

theorem conjugateFactor_one
    (N : Subgroup G) [N.Normal] (L : Subgroup N) :
    conjugateFactor N L 1 = L := by
  have h :
      (MulAut.conjNormal (H := N) 1).toMonoidHom =
        MonoidHom.id N := by
    ext x
    simp
  change L.map (MulAut.conjNormal (H := N) 1).toMonoidHom = L
  rw [h]
  exact Subgroup.map_id (K := L)

theorem conjugateFactor_isMinimalNormal
    (N : Subgroup G) [N.Normal] {L : Subgroup N}
    (hL : IsMinimalNormal L) (g : G) :
    IsMinimalNormal (conjugateFactor N L g) := by
  exact hL.map_equiv (MulAut.conjNormal g)

theorem conjugateFactorFamily_isMinimalNormal
    (N : Subgroup G) [N.Normal] {L : Subgroup N}
    (hL : IsMinimalNormal L) (i : ConjugateFactorIndex N L) :
    IsMinimalNormal (conjugateFactorFamily N L i) := by
  obtain ⟨g, hg⟩ := i.2
  simpa [conjugateFactorFamily, hg] using
    conjugateFactor_isMinimalNormal N hL g

theorem conjugateFactor_iSup_map_normal
    (N : Subgroup G) [N.Normal] (L : Subgroup N) :
    ((⨆ g : G, conjugateFactor N L g).map N.subtype).Normal := by
  rw [Subgroup.normal_iff_map_conj_eq]
  intro x
  calc
    ((⨆ g : G, conjugateFactor N L g).map N.subtype).map
          (MulAut.conj x) =
        ((⨆ g : G, conjugateFactor N L g).map
          (MulAut.conjNormal x).toMonoidHom).map N.subtype := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    _ = (⨆ g : G, conjugateFactor N L g).map N.subtype := by
      rw [Subgroup.map_iSup]
      conv_rhs =>
        rw [← Equiv.iSup_comp (Equiv.mulLeft x)]
      simp [conjugateFactor, Subgroup.map_map, MulAut.mul_def]

theorem conjugateFactor_iSup_eq_top
    [Finite G] {N : Subgroup G} [N.Normal]
    (hN : IsMinimalNormal N)
    {L : Subgroup N} (hL : IsMinimalNormal L) :
    ⨆ g : G, conjugateFactor N L g = ⊤ := by
  let R : Subgroup N :=
    ⨆ g : G, conjugateFactor N L g
  have hRnormal : (R.map N.subtype).Normal :=
    conjugateFactor_iSup_map_normal N L
  have hRne : R ≠ ⊥ := by
    intro hbot
    apply hL.ne_bot
    apply le_antisymm
    · have hle : conjugateFactor N L 1 ≤ R :=
        le_iSup (fun g : G ↦ conjugateFactor N L g) 1
      simpa [conjugateFactor_one N L, hbot] using hle
    · exact bot_le
  have hRmapNe : R.map N.subtype ≠ ⊥ := by
    intro hbot
    exact hRne
      ((R.map_eq_bot_iff_of_injective
        (f := N.subtype) Subtype.coe_injective).mp hbot)
  have hRmapLe : R.map N.subtype ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact x.property
  have hRmapEq : R.map N.subtype = N :=
    hN.eq_of_normal_le hRnormal hRmapNe hRmapLe
  apply Subgroup.map_injective
    (f := N.subtype) Subtype.coe_injective
  calc
    R.map N.subtype = N := hRmapEq
    _ = (⊤ : Subgroup N).map N.subtype := by
      rw [← MonoidHom.range_eq_map, N.range_subtype]

theorem conjugateFactorFamily_iSup_eq_top
    [Finite G] {N : Subgroup G} [N.Normal]
    (hN : IsMinimalNormal N)
    {L : Subgroup N} (hL : IsMinimalNormal L) :
    ⨆ i : ConjugateFactorIndex N L,
        conjugateFactorFamily N L i = ⊤ := by
  rw [← conjugateFactor_iSup_eq_top hN hL]
  apply le_antisymm
  · apply iSup_le
    intro i
    obtain ⟨g, hg⟩ := i.2
    change i.1 ≤ ⨆ x : G, conjugateFactor N L x
    rw [← hg]
    exact le_iSup (fun x : G ↦ conjugateFactor N L x) g
  · apply iSup_le
    intro g
    exact le_iSup
      (fun i : ConjugateFactorIndex N L ↦
        conjugateFactorFamily N L i)
      ⟨conjugateFactor N L g, ⟨g, rfl⟩⟩

/-- The orbit of a nontrivial subgroup is nonempty. -/
def identityConjugateFactorIndex
    (N : Subgroup G) [N.Normal] (L : Subgroup N) :
    ConjugateFactorIndex N L :=
  ⟨L, ⟨1, conjugateFactor_one N L⟩⟩

/-- Each indexed factor is an ambient conjugate of the initial factor. -/
theorem conjugateFactorFamily_eq_conjugate
    (N : Subgroup G) [N.Normal] (L : Subgroup N)
    (i : ConjugateFactorIndex N L) :
    ∃ g : G,
      conjugateFactorFamily N L i =
        conjugateFactor N L g := by
  obtain ⟨g, hg⟩ := i.2
  exact ⟨g, hg.symm⟩

/-- Any two indexed factors are conjugate by an element of the ambient
group. -/
theorem conjugateFactorFamily_pairwise_conjugate
    (N : Subgroup G) [N.Normal] (L : Subgroup N)
    (i j : ConjugateFactorIndex N L) :
    ∃ g : G,
      conjugateFactorFamily N L j =
        (conjugateFactorFamily N L i).map
          (MulAut.conjNormal g).toMonoidHom := by
  obtain ⟨g, hgi⟩ := i.2
  obtain ⟨h, hhj⟩ := j.2
  refine ⟨h * g⁻¹, ?_⟩
  change j.1 =
    i.1.map (MulAut.conjNormal (h * g⁻¹)).toMonoidHom
  rw [← hgi, ← hhj]
  simp only [conjugateFactor, Subgroup.map_map, map_mul,
    map_inv]
  congr 1
  ext x
  simp

/-- Distinct indexed conjugate factors centralize one another. -/
theorem conjugateFactorFamily_pairwise_commute
    (N : Subgroup G) [N.Normal] {L : Subgroup N}
    (hL : IsMinimalNormal L) :
    Pairwise fun i j : ConjugateFactorIndex N L ↦
      ∀ x y : N,
        x ∈ conjugateFactorFamily N L i →
        y ∈ conjugateFactorFamily N L j →
        Commute x y := by
  intro i j hij x y hx hy
  exact
    (conjugateFactorFamily_isMinimalNormal N hL i).commute_of_ne
      (conjugateFactorFamily_isMinimalNormal N hL j)
      (fun heq ↦ hij (Subtype.ext heq)) hx hy

/-- Commutativity of a subgroup is invariant under transport by a group
equivalence. -/
theorem isMulCommutative_map_equiv_iff
    {H K : Type*} [Group H] [Group K]
    (L : Subgroup H) (e : H ≃* K) :
    IsMulCommutative (L.map e.toMonoidHom) ↔
      IsMulCommutative L := by
  constructor
  · intro h
    letI : IsMulCommutative (L.map e.toMonoidHom) := h
    haveI :
        IsMulCommutative
          ((L.map e.toMonoidHom).map e.symm.toMonoidHom) :=
      inferInstance
    have heq :
        (L.map e.toMonoidHom).map e.symm.toMonoidHom = L := by
      simp [Subgroup.map_map]
    exact heq ▸ inferInstance
  · intro h
    letI : IsMulCommutative L := h
    infer_instance

/-- The chosen inner minimal normal subgroup of a nonabelian minimal normal
subgroup is itself nonabelian. -/
theorem not_isMulCommutative_of_conjugateFactor_iSup_eq_top
    [Finite G] {N : Subgroup G} [N.Normal]
    (hnoncomm : ¬ IsMulCommutative N)
    {L : Subgroup N} (hL : IsMinimalNormal L)
    (htop :
      ⨆ i : ConjugateFactorIndex N L,
        conjugateFactorFamily N L i = ⊤) :
    ¬ IsMulCommutative L := by
  intro hLcomm
  let I := ConjugateFactorIndex N L
  let H : I → Subgroup N :=
    conjugateFactorFamily N L
  letI : Fintype I := Fintype.ofFinite I
  letI : IsMulCommutative L := hLcomm
  letI hfactorComm : ∀ i : I, IsMulCommutative (H i) :=
    fun i ↦ by
      obtain ⟨g, hg⟩ := i.2
      change IsMulCommutative i.1
      rw [← hg]
      exact
        (isMulCommutative_map_equiv_iff
          L (MulAut.conjNormal g)).mpr hLcomm
  let hcomm :
      Pairwise fun i j : I ↦
        ∀ x y : N, x ∈ H i → y ∈ H j → Commute x y :=
    conjugateFactorFamily_pairwise_commute N hL
  let productHom : (∀ i : I, H i) →* N :=
    Subgroup.noncommPiCoprod hcomm
  have hrange : productHom.range = ⊤ := by
    change (Subgroup.noncommPiCoprod hcomm).range = ⊤
    rw [Subgroup.noncommPiCoprod_range]
    exact htop
  have hsurjective : Function.Surjective productHom :=
    MonoidHom.range_eq_top.mp hrange
  apply hnoncomm
  exact
    ⟨⟨fun x y ↦ by
      obtain ⟨a, rfl⟩ := hsurjective x
      obtain ⟨b, rfl⟩ := hsurjective y
      simpa using congrArg productHom (mul_comm' a b)⟩⟩

theorem conjugateFactorFamily_not_isMulCommutative
    [Finite G] {N : Subgroup G} [N.Normal]
    (hN : IsMinimalNormal N)
    (hnoncomm : ¬ IsMulCommutative N)
    {L : Subgroup N} (hL : IsMinimalNormal L)
    (i : ConjugateFactorIndex N L) :
    ¬ IsMulCommutative (conjugateFactorFamily N L i) := by
  have hLnoncomm : ¬ IsMulCommutative L :=
    not_isMulCommutative_of_conjugateFactor_iSup_eq_top
      hnoncomm hL
      (conjugateFactorFamily_iSup_eq_top hN hL)
  obtain ⟨g, hg⟩ :=
    conjugateFactorFamily_eq_conjugate N L i
  rw [hg, conjugateFactor,
    isMulCommutative_map_equiv_iff]
  exact hLnoncomm

/-- Every indexed conjugate factor is centerless. -/
theorem conjugateFactorFamily_center_eq_bot
    [Finite G] {N : Subgroup G} [N.Normal]
    (hN : IsMinimalNormal N)
    (hnoncomm : ¬ IsMulCommutative N)
    {L : Subgroup N} (hL : IsMinimalNormal L)
    (i : ConjugateFactorIndex N L) :
    Subgroup.center (conjugateFactorFamily N L i) = ⊥ :=
  IsMinimalNormal.center_eq_bot_of_not_isMulCommutative
    (conjugateFactorFamily_isMinimalNormal N hL i)
    (conjugateFactorFamily_not_isMulCommutative
      hN hnoncomm hL i)

/-- The distinct conjugate factors form an independent family.  The key
kernel calculation is that an element in one factor and in the product of
all the others commutes with its entire factor, hence lies in its center. -/
theorem conjugateFactorFamily_iSupIndep
    [Finite G] {N : Subgroup G} [N.Normal]
    (hN : IsMinimalNormal N)
    (hnoncomm : ¬ IsMulCommutative N)
    {L : Subgroup N} (hL : IsMinimalNormal L) :
    iSupIndep fun i : ConjugateFactorIndex N L ↦
      conjugateFactorFamily N L i := by
  let I := ConjugateFactorIndex N L
  let H : I → Subgroup N :=
    conjugateFactorFamily N L
  let hcomm :
      Pairwise fun i j : I ↦
        ∀ x y : N, x ∈ H i → y ∈ H j → Commute x y :=
    conjugateFactorFamily_pairwise_commute N hL
  intro i
  rw [disjoint_iff_inf_le]
  intro x hx
  have hxi : x ∈ H i := hx.1
  have hxrest :
      x ∈ ⨆ (j : I) (_ : j ≠ i), H j :=
    hx.2
  have hrestCentralizer :
      (⨆ (j : I) (_ : j ≠ i), H j) ≤
        Subgroup.centralizer (H i : Set N) := by
    apply iSup_le
    intro j
    apply iSup_le
    intro hji y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hcomm hji.symm z y hz hy).eq
  have hxcentralizer :
      x ∈ Subgroup.centralizer (H i : Set N) :=
    hrestCentralizer hxrest
  have hxcenter :
      (⟨x, hxi⟩ : H i) ∈ Subgroup.center (H i) := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    exact
      (Subgroup.mem_centralizer_iff.mp
        hxcentralizer z z.2)
  have hxone : (⟨x, hxi⟩ : H i) = 1 := by
    have hxcenter' := hxcenter
    rw [conjugateFactorFamily_center_eq_bot
      hN hnoncomm hL i] at hxcenter'
    simpa using hxcenter'
  simpa using congrArg Subtype.val hxone

/-- The canonical product of the distinct conjugate factors is an
isomorphism onto the minimal normal subgroup. -/
def conjugateFactorProductEquiv
    [Finite G] {N : Subgroup G} [N.Normal]
    (hN : IsMinimalNormal N)
    (hnoncomm : ¬ IsMulCommutative N)
    {L : Subgroup N} (hL : IsMinimalNormal L) :
    (∀ i : ConjugateFactorIndex N L,
        conjugateFactorFamily N L i) ≃* N := by
  let I := ConjugateFactorIndex N L
  let H : I → Subgroup N :=
    conjugateFactorFamily N L
  letI : Fintype I := Fintype.ofFinite I
  let hcomm :
      Pairwise fun i j : I ↦
        ∀ x y : N, x ∈ H i → y ∈ H j → Commute x y :=
    conjugateFactorFamily_pairwise_commute N hL
  apply MulEquiv.ofBijective (Subgroup.noncommPiCoprod hcomm)
  constructor
  · exact
      Subgroup.injective_noncommPiCoprod_of_iSupIndep
        (conjugateFactorFamily_iSupIndep
          hN hnoncomm hL)
  · apply MonoidHom.range_eq_top.mp
    rw [Subgroup.noncommPiCoprod_range]
    exact conjugateFactorFamily_iSup_eq_top hN hL

/-- Each conjugate factor is a simple group.  A subgroup normal in one
factor is normalized by that factor and centralized by all the others;
since the factors generate `N`, it is normal in `N`. -/
theorem conjugateFactorFamily_isSimpleGroup
    [Finite G] {N : Subgroup G} [N.Normal]
    (hN : IsMinimalNormal N)
    {L : Subgroup N} (hL : IsMinimalNormal L)
    (i : ConjugateFactorIndex N L) :
    IsSimpleGroup (conjugateFactorFamily N L i) := by
  let I := ConjugateFactorIndex N L
  let H : I → Subgroup N :=
    conjugateFactorFamily N L
  let hcomm :
      Pairwise fun i j : I ↦
        ∀ x y : N, x ∈ H i → y ∈ H j → Commute x y :=
    conjugateFactorFamily_pairwise_commute N hL
  have htop : ⨆ j : I, H j = ⊤ :=
    conjugateFactorFamily_iSup_eq_top hN hL
  have hmini : IsMinimalNormal (H i) :=
    conjugateFactorFamily_isMinimalNormal N hL i
  rw [Subgroup.isSimpleGroup_iff]
  refine ⟨hmini.ne_bot, ?_⟩
  intro K hKle hKnormal
  have hnormalizer :
      (⨆ j : I, H j) ≤
        Subgroup.normalizer (K : Set N) := by
    apply iSup_le
    intro j
    rw [Subgroup.le_normalizer_iff]
    intro x hx z hzK
    by_cases hji : j = i
    · subst j
      let x' : H i := ⟨x, hx⟩
      let z' : H i := ⟨z, hKle hzK⟩
      have hzconj :
          x' * z' * x'⁻¹ ∈ K.subgroupOf (H i) :=
        hKnormal.conj_mem z' hzK x'
      change x * z * x⁻¹ ∈ K at hzconj
      exact hzconj
    · have hc : Commute x z :=
        hcomm hji x z hx (hKle hzK)
      have heq : x * z * x⁻¹ = z := by
        rw [hc.eq]
        simp
      rw [heq]
      exact hzK
  have hnormalizerTop :
      Subgroup.normalizer (K : Set N) = ⊤ := by
    rw [← top_le_iff, ← htop]
    exact hnormalizer
  have hKnormalN : K.Normal :=
    Subgroup.normalizer_eq_top_iff.mp hnormalizerTop
  exact hmini.eq_bot_or_eq hKnormalN hKle

/-- The complete internal-direct-product data for a finite nonabelian
minimal normal subgroup. -/
structure NonabelianMinimalNormalDecomposition
    (N : Subgroup G) [N.Normal] where
  /-- The finite set of distinct factors. -/
  ι : Type u
  fintype : Fintype ι
  nonempty : Nonempty ι
  /-- The simple factors, regarded as subgroups of `N`. -/
  factor : ι → Subgroup N
  factor_minimalNormal :
    ∀ i, IsMinimalNormal (factor i)
  factor_simple :
    ∀ i, IsSimpleGroup (factor i)
  factor_nonabelian :
    ∀ i, ¬ IsMulCommutative (factor i)
  /-- All factors belong to one ambient conjugacy orbit. -/
  pairwise_conjugate :
    ∀ i j, ∃ g : G,
      factor j =
        (factor i).map
          (MulAut.conjNormal g).toMonoidHom
  /-- Distinct factors centralize one another. -/
  pairwise_commute :
    Pairwise fun i j ↦
      ∀ x y : N,
        x ∈ factor i → y ∈ factor j → Commute x y
  /-- The factor subgroups are independent in the subgroup lattice. -/
  independent :
    iSupIndep factor
  /-- The factors generate `N`. -/
  iSup_eq_top :
    ⨆ i, factor i = ⊤
  /-- The canonical multiplication map is an isomorphism. -/
  productEquiv :
    (∀ i, factor i) ≃* N

/-- Construct the internal direct-product decomposition of a finite
nonabelian minimal normal subgroup. -/
def nonabelianMinimalNormalDecomposition
    [Finite G] {N : Subgroup G} [N.Normal]
    (hN : IsMinimalNormal N)
    (hnoncomm : ¬ IsMulCommutative N) :
    NonabelianMinimalNormalDecomposition N := by
  letI : Nontrivial N :=
    N.nontrivial_iff_ne_bot.mpr hN.ne_bot
  let L : Subgroup N :=
    chosenMinimalNormalSubgroup N
  have hL : IsMinimalNormal L :=
    chosenMinimalNormalSubgroup_isMinimalNormal N
  let I := ConjugateFactorIndex N L
  let H : I → Subgroup N :=
    conjugateFactorFamily N L
  exact
    { ι := I
      fintype := Fintype.ofFinite I
      nonempty := ⟨identityConjugateFactorIndex N L⟩
      factor := H
      factor_minimalNormal :=
        conjugateFactorFamily_isMinimalNormal N hL
      factor_simple :=
        conjugateFactorFamily_isSimpleGroup hN hL
      factor_nonabelian :=
        conjugateFactorFamily_not_isMulCommutative
          hN hnoncomm hL
      pairwise_conjugate :=
        conjugateFactorFamily_pairwise_conjugate N L
      pairwise_commute :=
        conjugateFactorFamily_pairwise_commute N hL
      independent :=
        conjugateFactorFamily_iSupIndep
          hN hnoncomm hL
      iSup_eq_top :=
        conjugateFactorFamily_iSup_eq_top hN hL
      productEquiv :=
        conjugateFactorProductEquiv
          hN hnoncomm hL }

end MinimalNormalFactors

end GroupTheory
end McKayConjecture
