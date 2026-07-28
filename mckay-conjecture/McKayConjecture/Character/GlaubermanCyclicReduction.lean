/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.GlaubermanCorrespondence
import McKayConjecture.Character.GlaubermanCyclicCandidate
import McKayConjecture.Character.GlaubermanLinearCharacter
import McKayConjecture.Character.CyclicDeterminantNormalization
import McKayConjecture.Character.DegreeOneLinear
import McKayConjecture.GroupTheory.PPrimeCore

/-!
# Reduction of cyclic Glauberman correspondence to a signed trace theorem

Suppose a cyclic subgroup `P` and a normal subgroup `K` generate the
ambient finite group.  A chosen generator `g` of `P` generates `G/K`,
and `C_K(g) = C_K(P)`.  Consequently the normalized cyclic trace from
`GlaubermanCyclicCandidate.lean` is an actual class function on the
Glauberman target.

This file proves all of those group-theoretic and representation-theoretic
reductions.  What remains for a general noncommutative coprime kernel is
the classical signed-irreducibility theorem for that concrete trace.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture

variable {G : Type} [Group G] [Finite G]
variable (K P : Subgroup G) [K.Normal]
variable [IsCyclic P]

/-- A chosen generator of the cyclic acting subgroup. -/
def cyclicSubgroupGenerator : P :=
  Classical.choose
    (isCyclic_iff_exists_zpowers_eq_top.mp
      (inferInstance : IsCyclic P))

/-- The chosen element generates `P`. -/
theorem cyclicSubgroupGenerator_zpowers :
    Subgroup.zpowers (cyclicSubgroupGenerator P) = ⊤ :=
  Classical.choose_spec
    (isCyclic_iff_exists_zpowers_eq_top.mp
      (inferInstance : IsCyclic P))

/-- In the ambient group, the powers of the chosen generator are exactly
the elements of `P`. -/
theorem zpowers_cyclicSubgroupGenerator_coe :
    Subgroup.zpowers
        ((cyclicSubgroupGenerator P : P) : G) =
      P := by
  apply le_antisymm
  · rw [Subgroup.zpowers_le]
    exact (cyclicSubgroupGenerator P).2
  · intro x hx
    let xP : P := ⟨x, hx⟩
    have hxTop : xP ∈
        Subgroup.zpowers (cyclicSubgroupGenerator P) := by
      rw [cyclicSubgroupGenerator_zpowers]
      exact Subgroup.mem_top xP
    obtain ⟨i, hi⟩ :=
      Subgroup.mem_zpowers_iff.mp hxTop
    rw [Subgroup.mem_zpowers_iff]
    exact
      ⟨i, by
        simpa only [Subgroup.coe_zpow] using
          congrArg Subtype.val hi⟩

/-- If `K` and cyclic `P` generate `G`, the chosen generator supplies
the coset normal form needed by the cyclic-extension construction. -/
theorem cyclicSubgroupGenerator_coset_normalForm
    (hgenerate : K ⊔ P = ⊤) :
    ∀ x : G, ∃ i : ℤ,
      ((((cyclicSubgroupGenerator P : P) : G) ^ i)⁻¹ * x) ∈ K := by
  intro x
  have hx : x ∈ K ⊔ P := by
    rw [hgenerate]
    exact Subgroup.mem_top x
  obtain ⟨k, hk, a, ha, hka⟩ :=
    Subgroup.mem_sup_of_normal_left.mp hx
  let aP : P := ⟨a, ha⟩
  have haTop :
      aP ∈ Subgroup.zpowers (cyclicSubgroupGenerator P) := by
    rw [cyclicSubgroupGenerator_zpowers]
    exact Subgroup.mem_top aP
  obtain ⟨i, hi⟩ :=
    Subgroup.mem_zpowers_iff.mp haTop
  refine ⟨i, ?_⟩
  have hconj :
      ((((cyclicSubgroupGenerator P : P) : G) ^ i)⁻¹ *
          k *
          ((((cyclicSubgroupGenerator P : P) : G) ^ i)⁻¹)⁻¹) ∈ K :=
    (inferInstance : K.Normal).conj_mem k hk
      ((((cyclicSubgroupGenerator P : P) : G) ^ i)⁻¹)
  have haeq :
      (((cyclicSubgroupGenerator P : P) : G) ^ i) = a := by
    simpa only [Subgroup.coe_zpow] using
      congrArg Subtype.val hi
  have hxeq : k * a = x := hka
  rw [← hxeq, ← haeq]
  simpa only [inv_inv, mul_assoc] using hconj

/-- Centralizing a generator of a cyclic subgroup is equivalent to
centralizing the whole subgroup. -/
theorem centralizer_singleton_cyclicSubgroupGenerator :
    Subgroup.centralizer
        ({((cyclicSubgroupGenerator P : P) : G)} : Set G) =
      Subgroup.centralizer (P : Set G) := by
  let g : G :=
    (cyclicSubgroupGenerator P : P)
  calc
    Subgroup.centralizer ({g} : Set G) =
        Subgroup.centralizer
          (Subgroup.closure ({g} : Set G) : Set G) :=
      (Subgroup.centralizer_closure ({g} : Set G)).symm
    _ = Subgroup.centralizer
          (Subgroup.zpowers g : Set G) := by
      rw [Subgroup.zpowers_eq_closure]
    _ = Subgroup.centralizer (P : Set G) :=
      congrArg
        (fun Q : Subgroup G ↦
          Subgroup.centralizer (Q : Set G))
        (zpowers_cyclicSubgroupGenerator_coe P)

/-- Hence the cyclic fixed-point subgroup is the ordinary Glauberman
fixed-point subgroup `C_K(P)`. -/
theorem cyclicFixedPoints_cyclicSubgroupGenerator :
    cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G) =
      coprimeFixedPoints K P := by
  change
    K ⊓ Subgroup.centralizer
        ({((cyclicSubgroupGenerator P : P) : G)} : Set G) =
      K ⊓ Subgroup.centralizer (P : Set G)
  rw [centralizer_singleton_cyclicSubgroupGenerator]

variable {p : ℕ} [Fact p.Prime]

/-- A `p′`-group and a `p`-group have coprime orders. -/
theorem card_coprime_pPrimeGroup_pGroup
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P) :
    (Nat.card K).Coprime (Nat.card P) := by
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  rw [hn]
  exact (hK.pow_left n).symm

/-- An ambient element lying in both a `p′`-subgroup and a `p`-subgroup
is the identity. -/
theorem eq_one_of_mem_pPrimeGroup_and_pGroup
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    {x : G} (hxK : x ∈ K) (hxP : x ∈ P) :
    x = 1 := by
  have horderK :
      orderOf x ∣ Nat.card K :=
    K.orderOf_dvd_natCard hxK
  have horderP :
      orderOf x ∣ Nat.card P :=
    P.orderOf_dvd_natCard hxP
  have horderCoprime :
      (orderOf x).Coprime (Nat.card P) :=
    (card_coprime_pPrimeGroup_pGroup
      K P hK hP).coprime_dvd_left horderK
  exact orderOf_eq_one_iff.mp
    (horderCoprime.eq_one_of_dvd horderP)

/-- `P`-invariance implies invariance under the chosen cyclic
generator in the convention used by the cyclic extension theorem. -/
theorem cyclicSubgroupGenerator_isInvariantUnder
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    IrreducibleCharacter.IsInvariantUnder K θ.1.1
      ((cyclicSubgroupGenerator P : P) : G) := by
  intro k
  let g : P := cyclicSubgroupGenerator P
  have hinertia :
      ((g : G)⁻¹) ∈
        IrreducibleCharacter.inertia K θ.1.1 :=
    θ.2 (P.inv_mem g.2)
  have hfix :=
    (IrreducibleCharacter.mem_inertia_iff
      K θ.1.1 (g : G)⁻¹).mp hinertia
  have hvalue :=
    congrArg
      (fun χ : IrreducibleCharacter K ↦
        χ.values k) hfix
  rw [IrreducibleCharacter.conjBy_values] at hvalue
  have harg :
      RepresentationTheory.ClassFunction.conjByMulEquiv
          (K := G) (H := K) (g : G) k =
        (MulAut.conjNormal (H := K) (g : G)⁻¹).symm k := by
    apply Subtype.ext
    simp only [
      RepresentationTheory.ClassFunction.conjByMulEquiv_apply,
      MulAut.conjNormal_symm_apply, inv_inv]
  rw [harg]
  exact hvalue

/-- The order of the cyclic `p`-group is coprime to the degree of a
prime-to-`p` character. -/
theorem cyclicPGroup_card_coprime_character_degree
    (hP : IsPGroup p P)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    (Nat.card P).Coprime θ.1.1.degree := by
  have hpdegree :
      p.Coprime θ.1.1.degree :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      θ.1.2
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  rw [hn]
  exact hpdegree.pow_left n

/-- The initially normalized intertwiner has order dividing `|P|`. -/
theorem normalizedCyclicIntertwinerData_unit_pow_card_eq_one
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    (RepresentationTheory.normalizedCyclicIntertwinerData
        K θ.1.1
        ((cyclicSubgroupGenerator P : P) : G)
        (cyclicSubgroupGenerator_isInvariantUnder
          K P θ)).unit ^ Nat.card P =
      1 := by
  let g : P := cyclicSubgroupGenerator P
  let d :=
    RepresentationTheory.normalizedCyclicIntertwinerData
      K θ.1.1 (g : G)
      (cyclicSubgroupGenerator_isInvariantUnder
        K P θ)
  have hgpowP :
      g ^ Nat.card P = 1 :=
    pow_card_eq_one'
  have hgpowG :
      (g : G) ^ Nat.card P = 1 :=
    congrArg Subtype.val hgpowP
  have hmem :
      (g : G) ^ (Nat.card P : ℤ) ∈ K := by
    rw [zpow_natCast, hgpowG]
    exact K.one_mem
  have hnormalized :=
    d.normalized (Nat.card P : ℤ) hmem
  have hsub :
      (⟨(g : G) ^ (Nat.card P : ℤ), hmem⟩ : K) =
        1 := by
    apply Subtype.ext
    change
      (g : G) ^ (Nat.card P : ℤ) =
        (1 : G)
    simpa only [zpow_natCast] using hgpowG
  rw [hsub, map_one] at hnormalized
  simpa only [d, zpow_natCast] using hnormalized

/-- The determinant-one normalization of the cyclic intertwiner.  It
still satisfies both exact cyclic-extension identities. -/
def determinantNormalizedCyclicIntertwinerData
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    RepresentationTheory.NormalizedCyclicIntertwinerData
      K θ.1.1
      ((cyclicSubgroupGenerator P : P) : G)
      (cyclicSubgroupGenerator_isInvariantUnder
        K P θ) := by
  let g : P := cyclicSubgroupGenerator P
  let d :=
    RepresentationTheory.normalizedCyclicIntertwinerData
      K θ.1.1 (g : G)
      (cyclicSubgroupGenerator_isInvariantUnder
        K P θ)
  let z :=
    RepresentationTheory.determinantNormalizingScalar
      d.unit (Nat.card P)
  let Q :=
    RepresentationTheory.determinantNormalizedUnit
      d.unit (Nat.card P)
  refine ⟨Q, ?_, ?_⟩
  · intro k
    change
      (RepresentationTheory.scalarEndomorphismUnit z *
          d.unit) *
          (Representation.asGroupHom
            θ.1.1.realization.ρ) k =
        (Representation.asGroupHom
          θ.1.1.realization.ρ)
            (RepresentationTheory.ClassFunction.conjByMulEquiv
              (K := G) (H := K) (g : G) k) *
          (RepresentationTheory.scalarEndomorphismUnit z *
            d.unit)
    calc
      (RepresentationTheory.scalarEndomorphismUnit z *
            d.unit) *
            (Representation.asGroupHom
              θ.1.1.realization.ρ) k =
          RepresentationTheory.scalarEndomorphismUnit z *
            (d.unit *
              (Representation.asGroupHom
                θ.1.1.realization.ρ) k) := by group
      _ = RepresentationTheory.scalarEndomorphismUnit z *
            ((Representation.asGroupHom
              θ.1.1.realization.ρ)
                (RepresentationTheory.ClassFunction.conjByMulEquiv
                  (K := G) (H := K) (g : G) k) *
              d.unit) := by rw [d.intertwines k]
      _ = (RepresentationTheory.scalarEndomorphismUnit z *
            (Representation.asGroupHom
              θ.1.1.realization.ρ)
                (RepresentationTheory.ClassFunction.conjByMulEquiv
                  (K := G) (H := K) (g : G) k)) *
            d.unit := by group
      _ = ((Representation.asGroupHom
              θ.1.1.realization.ρ)
                (RepresentationTheory.ClassFunction.conjByMulEquiv
                  (K := G) (H := K) (g : G) k) *
            RepresentationTheory.scalarEndomorphismUnit z) *
            d.unit := by
        rw [RepresentationTheory.scalarEndomorphismUnit_comm]
      _ = (Representation.asGroupHom
              θ.1.1.realization.ρ)
                (RepresentationTheory.ClassFunction.conjByMulEquiv
                  (K := G) (H := K) (g : G) k) *
            (RepresentationTheory.scalarEndomorphismUnit z *
              d.unit) := by group
  · intro t ht
    have hgtP :
        (g : G) ^ t ∈ P :=
      P.zpow_mem g.2 t
    have hgt :
        (g : G) ^ t = 1 :=
      eq_one_of_mem_pPrimeGroup_and_pGroup
        K P hK hP ht hgtP
    have horder :
        orderOf (g : G) = Nat.card P :=
      (Subgroup.orderOf_coe g).trans
        (orderOf_eq_card_of_zpowers_eq_top
          (cyclicSubgroupGenerator_zpowers P))
    have hdvd :
        (Nat.card P : ℤ) ∣ t := by
      rw [← horder]
      exact
        orderOf_dvd_iff_zpow_eq_one.mpr hgt
    have hQpow :
        Q ^ Nat.card P = 1 :=
      RepresentationTheory.determinantNormalizedUnit_pow_eq_one
        d.unit (Nat.card P)
        (normalizedCyclicIntertwinerData_unit_pow_card_eq_one
          K P θ)
    have hQt : Q ^ t = 1 := by
      obtain ⟨s, rfl⟩ := hdvd
      rw [zpow_mul, zpow_natCast, hQpow,
        one_zpow]
    have hsub :
        (⟨(g : G) ^ t, ht⟩ : K) = 1 := by
      apply Subtype.ext
      exact hgt
    rw [hQt, hsub, map_one]

/-- The preceding cyclic intertwiner has determinant one. -/
theorem determinantNormalizedCyclicIntertwinerData_determinant
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    RepresentationTheory.endomorphismUnitDeterminant
        (determinantNormalizedCyclicIntertwinerData
          K P hK hP θ).unit =
      1 := by
  have hcoprime :
      (Nat.card P).Coprime
        (Module.finrank ℂ θ.1.1.realization) := by
    rw [θ.1.1.realization_finrank]
    exact
      cyclicPGroup_card_coprime_character_degree
        K P hP θ
  exact
    RepresentationTheory.endomorphismUnitDeterminant_determinantNormalizedUnit
      (RepresentationTheory.normalizedCyclicIntertwinerData
        K θ.1.1
        ((cyclicSubgroupGenerator P : P) : G)
        (cyclicSubgroupGenerator_isInvariantUnder
          K P θ)).unit
      (Nat.card P)
      hcoprime
      (normalizedCyclicIntertwinerData_unit_pow_card_eq_one
        K P θ)

/-- The cyclic extension representation built from the determinant-one
intertwiner. -/
def determinantNormalizedCyclicExtension
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    Representation ℂ G θ.1.1.realization :=
  let d :=
    determinantNormalizedCyclicIntertwinerData
      K P hK hP θ
  RepresentationTheory.cyclicExtension
    θ.1.1.realization.ρ
    ((cyclicSubgroupGenerator P : P) : G)
    d.unit d.intertwines d.normalized
    (cyclicSubgroupGenerator_coset_normalForm
      K P hgenerate)

/-- The determinant-normalized extension is irreducible. -/
theorem determinantNormalizedCyclicExtension_isIrreducible
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    Representation.IsIrreducible
      (determinantNormalizedCyclicExtension
        K P hK hP hgenerate θ) := by
  letI : Representation.IsIrreducible
      θ.1.1.realization.ρ :=
    CliffordRestriction.isIrreducible_of_simple
      θ.1.1.realization
  exact
    RepresentationTheory.isIrreducible_cyclicExtension
      (determinantNormalizedCyclicIntertwinerData
        K P hK hP θ).intertwines
      (determinantNormalizedCyclicIntertwinerData
        K P hK hP θ).normalized
      (cyclicSubgroupGenerator_coset_normalForm
        K P hgenerate)

/-- The irreducible character afforded by the determinant-normalized
cyclic extension. -/
def determinantNormalizedCyclicExtensionCharacter
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    IrreducibleCharacter G := by
  let ρ :=
    determinantNormalizedCyclicExtension
      K P hK hP hgenerate θ
  letI : Representation.IsIrreducible ρ :=
    determinantNormalizedCyclicExtension_isIrreducible
      K P hK hP hgenerate θ
  letI : Simple (FDRep.of ρ) :=
    RepresentationTheory.simple_fdRep_of_isIrreducible
      ρ
  exact IrreducibleCharacter.ofSimple (FDRep.of ρ)

/-- The determinant-normalized cyclic character extends the original
kernel character. -/
theorem determinantNormalizedCyclicExtensionCharacter_isExtension
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    IrreducibleCharacter.IsExtensionAlong K.subtype θ.1.1
      (determinantNormalizedCyclicExtensionCharacter
        K P hK hP hgenerate θ) := by
  intro k
  change
    LinearMap.trace ℂ θ.1.1.realization
        (determinantNormalizedCyclicExtension
          K P hK hP hgenerate θ (K.subtype k)) =
      θ.1.1.values k
  have hcomp :=
    RepresentationTheory.cyclicExtension_comp_subtype
      (determinantNormalizedCyclicIntertwinerData
        K P hK hP θ).intertwines
      (determinantNormalizedCyclicIntertwinerData
        K P hK hP θ).normalized
      (cyclicSubgroupGenerator_coset_normalForm
        K P hgenerate)
  rw [show
    determinantNormalizedCyclicExtension
        K P hK hP hgenerate θ (K.subtype k) =
      θ.1.1.realization.ρ k by
        exact DFunLike.congr_fun hcomp k]
  exact congrFun θ.1.1.realization_character k

/-- The determinant-normalized extension has prime-to-`p` degree. -/
def determinantNormalizedCyclicExtensionPPrimeCharacter
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    PPrimeIrreducibleCharacter G p :=
  ⟨determinantNormalizedCyclicExtensionCharacter
      K P hK hP hgenerate θ,
    (determinantNormalizedCyclicExtensionCharacter_isExtension
      K P hK hP hgenerate θ).isPPrimeDegree_iff p |>.2
        θ.1.2⟩

@[simp]
theorem determinantNormalizedCyclicExtensionPPrimeCharacter_coe
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    (determinantNormalizedCyclicExtensionPPrimeCharacter
      K P hK hP hgenerate θ).1 =
        determinantNormalizedCyclicExtensionCharacter
          K P hK hP hgenerate θ :=
  rfl

/-- The determinant-normalized twisted trace before identifying
`C_K(g)` with `C_K(P)`. -/
def determinantNormalizedCyclicTrace
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    ClassFunction
      (cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G)) :=
  let d :=
    determinantNormalizedCyclicIntertwinerData
      K P hK hP θ
  RepresentationTheory.cyclicTwistedTraceClassFunction
    d.intertwines d.normalized
    (cyclicSubgroupGenerator_coset_normalForm
      K P hgenerate)

/-- The determinant-normalized trace is exactly the extension character
on the generator coset. -/
@[simp]
theorem determinantNormalizedCyclicTrace_eq_extensionCharacter
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (c :
      cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G)) :
    determinantNormalizedCyclicTrace
        K P hK hP hgenerate θ c =
      (determinantNormalizedCyclicExtensionCharacter
        K P hK hP hgenerate θ).values
          (((cyclicSubgroupGenerator P : P) : G) *
            (c : G)) := by
  simp [
    determinantNormalizedCyclicTrace,
    RepresentationTheory.cyclicTwistedTraceClassFunction,
    determinantNormalizedCyclicExtensionCharacter,
    determinantNormalizedCyclicExtension]

/-- On the linear stratum, determinant normalization removes the
root-of-unity ambiguity completely: the cyclic trace is ordinary
restriction, with positive sign. -/
theorem determinantNormalizedCyclicTrace_eq_of_degree_one
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (hdegree : θ.1.1.degree = 1)
    (c :
      cyclicFixedPoints K
        ((cyclicSubgroupGenerator P : P) : G)) :
    determinantNormalizedCyclicTrace
        K P hK hP hgenerate θ c =
      θ.1.1.values
        (cyclicFixedPointsInclusion K
          ((cyclicSubgroupGenerator P : P) : G) c) := by
  let d :=
    determinantNormalizedCyclicIntertwinerData
      K P hK hP θ
  let ρc :=
    θ.1.1.realization.ρ
      (cyclicFixedPointsInclusion K
        ((cyclicSubgroupGenerator P : P) : G) c)
  have hfinrank :
      Module.finrank ℂ θ.1.1.realization = 1 :=
    θ.1.1.realization_finrank.trans hdegree
  have hdetP :
      LinearMap.det
          (d.unit :
            Module.End ℂ θ.1.1.realization) =
        1 := by
    change
      LinearMap.det
          ((determinantNormalizedCyclicIntertwinerData
              K P hK hP θ).unit :
            Module.End ℂ θ.1.1.realization) =
        1
    have hdet :=
      determinantNormalizedCyclicIntertwinerData_determinant
        K P hK hP θ
    have hdetval := congrArg Units.val hdet
    simpa [
      RepresentationTheory.endomorphismUnitDeterminant,
      LinearEquiv.coe_det] using hdetval
  rw [determinantNormalizedCyclicTrace,
    RepresentationTheory.cyclicTwistedTraceClassFunction_apply]
  change
    LinearMap.trace ℂ θ.1.1.realization
        ((d.unit :
          Module.End ℂ θ.1.1.realization) * ρc) =
      θ.1.1.values
        (cyclicFixedPointsInclusion K
          ((cyclicSubgroupGenerator P : P) : G) c)
  calc
    LinearMap.trace ℂ θ.1.1.realization
          ((d.unit :
            Module.End ℂ θ.1.1.realization) * ρc) =
        LinearMap.det
          ((d.unit :
            Module.End ℂ θ.1.1.realization) * ρc) :=
      IrreducibleCharacter.trace_eq_det_of_finrank_eq_one
        hfinrank _
    _ = LinearMap.det
          (d.unit :
            Module.End ℂ θ.1.1.realization) *
        LinearMap.det ρc := by
      rw [Module.End.mul_eq_comp,
        LinearMap.det_comp]
    _ = LinearMap.det ρc := by
      rw [hdetP, one_mul]
    _ = LinearMap.trace ℂ θ.1.1.realization ρc :=
      (IrreducibleCharacter.trace_eq_det_of_finrank_eq_one
        hfinrank ρc).symm
    _ = θ.1.1.values
        (cyclicFixedPointsInclusion K
          ((cyclicSubgroupGenerator P : P) : G) c) :=
      congrFun θ.1.1.realization_character _

/-- The fully constructed cyclic trace, now transported to the exact
Glauberman target `C_K(P)`.  No extension or intertwiner data is an
input: both are constructed from `θ`. -/
def cyclicSubgroupGlaubermanTrace
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p) :
    ClassFunction (coprimeFixedPoints K P) :=
  let e :
      cyclicFixedPoints K
          ((cyclicSubgroupGenerator P : P) : G) ≃*
        coprimeFixedPoints K P :=
    MulEquiv.subgroupCongr
      (cyclicFixedPoints_cyclicSubgroupGenerator K P)
  let f :=
    determinantNormalizedCyclicTrace
      K P hK hP hgenerate θ
  ⟨fun c ↦ f (e.symm c), by
    intro c x
    change
      f (e.symm (x * c * x⁻¹)) =
        f (e.symm c)
    rw [map_mul, map_mul, map_inv,
      ClassFunction.conj_apply]⟩

@[simp]
theorem cyclicSubgroupGlaubermanTrace_apply
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (c : coprimeFixedPoints K P) :
    cyclicSubgroupGlaubermanTrace
        K P hK hP hgenerate θ c =
      determinantNormalizedCyclicTrace
        K P hK hP hgenerate θ
          ((MulEquiv.subgroupCongr
            (cyclicFixedPoints_cyclicSubgroupGenerator
              K P)).symm c) :=
  rfl

/-- For an arbitrary, possibly noncommutative kernel, the
determinant-normalized cyclic construction agrees with the already
proved Glauberman correspondent on the degree-one stratum.  In
particular, the residual sign in the general cyclic theorem is positive
on this stratum. -/
theorem cyclicSubgroupGlaubermanTrace_eq_linearCandidate
    (hK : GroupTheory.IsPPrimeGroup p K)
    (hP : IsPGroup p P)
    (hgenerate : K ⊔ P = ⊤)
    (θ : PInvariantPPrimeIrreducibleCharacter K P p)
    (hdegree : θ.1.1.degree = 1) :
    cyclicSubgroupGlaubermanTrace
        K P hK hP hgenerate θ =
      (linearGlaubermanCandidate
        K P θ hdegree).1.toClassFunction := by
  apply ClassFunction.ext
  intro c
  let e :
      cyclicFixedPoints K
          ((cyclicSubgroupGenerator P : P) : G) ≃*
        coprimeFixedPoints K P :=
    MulEquiv.subgroupCongr
      (cyclicFixedPoints_cyclicSubgroupGenerator K P)
  have htrace :=
    determinantNormalizedCyclicTrace_eq_of_degree_one
      K P hK hP hgenerate θ hdegree (e.symm c)
  rw [cyclicSubgroupGlaubermanTrace_apply]
  change
    determinantNormalizedCyclicTrace
        K P hK hP hgenerate θ (e.symm c) =
      (linearGlaubermanCandidate
        K P θ hdegree).1.values c
  rw [htrace, linearGlaubermanCandidate_coe,
    IrreducibleCharacter.linearRestriction_values]
  congr 1

end McKayConjecture
