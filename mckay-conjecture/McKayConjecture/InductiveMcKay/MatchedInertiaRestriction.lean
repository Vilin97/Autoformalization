/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralTripleRestrictionWitness
import McKayConjecture.InductiveMcKay.MatchedCentralTripleCliffordAssembly

/-!
# Group data for restriction between matched inertia triples

Let `N ◁ G`, `H ≤ G`, and `M ◁ H`.  An `H`-equivariant equivalence
between prime-to-`p` characters of `N` and `M` sends stabilizers into
stabilizers and hence gives a canonical embedding

`I_H(e θ) → I_G(θ)`.

This file proves the ordinary group conditions needed to construct a
central witness by restricting one projective lift.  The exact
intersection condition necessarily uses the corresponding base-group
identity `N ∩ H = M`.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CharacterTriple
open CliffordCorrespondence
open CliffordEquivalence

variable {G : Type} [Group G] [Finite G]
variable (N H : Subgroup G) [N.Normal]
variable (M : Subgroup H) [M.Normal]
variable {p : ℕ}

namespace MatchedInertiaRestriction

omit [Finite G] in
/-- Rewrite equivariance stated using the ambient `G`-action into the
equivalent restricted `H`-action convention. -/
theorem subgroup_equivariance_of_ambient
    (e :
      PPrimeIrreducibleCharacter N p ≃
        PPrimeIrreducibleCharacter M p)
    (he :
      ∀ (h : H) (χ : PPrimeIrreducibleCharacter N p),
        e (((h : H) : G) • χ) = h • e χ) :
    ∀ (h : H) (χ : PPrimeIrreducibleCharacter N p),
      e (h • χ) = h • e χ := by
  intro h χ
  exact he h χ

/-- Inclusion of the matched target inertia group into the source inertia
group.  Membership in the source inertia group follows from equivariance
and injectivity of the character equivalence. -/
def embedding
    (e :
      PPrimeIrreducibleCharacter N p ≃
        PPrimeIrreducibleCharacter M p)
    (he :
      ∀ (h : H) (χ : PPrimeIrreducibleCharacter N p),
        e (h • χ) = h • e χ)
    (θ : PPrimeIrreducibleCharacter N p) :
    IrreducibleCharacter.inertia M (e θ).1 →*
      IrreducibleCharacter.inertia N θ.1 where
  toFun b :=
    ⟨(((b : IrreducibleCharacter.inertia M (e θ).1) : H) : G), by
      rw [IrreducibleCharacter.mem_inertia_iff]
      have hbφ :
          (b : H) • e θ = e θ := by
        apply Subtype.ext
        exact
          (IrreducibleCharacter.mem_inertia_iff
            M (e θ).1 (b : H)).mp b.property
      have hbθ :
          (((b : H) : G) • θ) = θ := by
        apply e.injective
        have haction :
            (((b : H) : G) • θ) =
              (b : H) • θ :=
          rfl
        rw [haction, he (b : H) θ, hbφ]
      exact congrArg Subtype.val hbθ⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' b c := by
    apply Subtype.ext
    rfl

omit [Finite G] in
@[simp]
theorem embedding_apply_coe
    (e :
      PPrimeIrreducibleCharacter N p ≃
        PPrimeIrreducibleCharacter M p)
    (he :
      ∀ (h : H) (χ : PPrimeIrreducibleCharacter N p),
        e (h • χ) = h • e χ)
    (θ : PPrimeIrreducibleCharacter N p)
    (b : IrreducibleCharacter.inertia M (e θ).1) :
    ((embedding N H M e he θ b :
        IrreducibleCharacter.inertia N θ.1) : G) =
      (((b : IrreducibleCharacter.inertia M (e θ).1) : H) : G) :=
  rfl

omit [Finite G] in
/-- The canonical inertia embedding is injective. -/
theorem embedding_injective
    (e :
      PPrimeIrreducibleCharacter N p ≃
        PPrimeIrreducibleCharacter M p)
    (he :
      ∀ (h : H) (χ : PPrimeIrreducibleCharacter N p),
        e (h • χ) = h • e χ)
    (θ : PPrimeIrreducibleCharacter N p) :
    Function.Injective (embedding N H M e he θ) := by
  intro b c hbc
  apply Subtype.ext
  have hG :=
    congrArg
      (fun x : IrreducibleCharacter.inertia N θ.1 ↦
        (x : G)) hbc
  exact Subtype.ext hG

omit [Finite G] in
/-- An element of `H` stabilizing the source character also stabilizes
its matched target character. -/
theorem mem_target_inertia_of_mem_source_inertia
    (e :
      PPrimeIrreducibleCharacter N p ≃
        PPrimeIrreducibleCharacter M p)
    (he :
      ∀ (h : H) (χ : PPrimeIrreducibleCharacter N p),
        e (h • χ) = h • e χ)
    (θ : PPrimeIrreducibleCharacter N p)
    (h : H)
    (hh :
      (h : G) ∈
        IrreducibleCharacter.inertia N θ.1) :
    (h : H) ∈
      IrreducibleCharacter.inertia M (e θ).1 := by
  rw [IrreducibleCharacter.mem_inertia_iff]
  have hhθG :
      ((h : G) • θ) = θ := by
    apply Subtype.ext
    exact
      (IrreducibleCharacter.mem_inertia_iff
        N θ.1 (h : G)).mp hh
  have hhθH :
      h • θ = θ := by
    exact hhθG
  have hhφ :
      h • e θ = e θ := by
    rw [← he h θ, hhθH]
  exact congrArg Subtype.val hhφ

omit [Finite G] in
/-- If `C_G(N) ≤ H`, then the centralizer of the canonical copy of `N`
inside `I_G(θ)` lies in the image of the matched inertia embedding. -/
theorem centralizer_le_range
    (e :
      PPrimeIrreducibleCharacter N p ≃
        PPrimeIrreducibleCharacter M p)
    (he :
      ∀ (h : H) (χ : PPrimeIrreducibleCharacter N p),
        e (h • χ) = h • e χ)
    (hcentral :
      Subgroup.centralizer (N : Set G) ≤ H)
    (θ : PPrimeIrreducibleCharacter N p) :
    Subgroup.centralizer
        (inertiaNormalCopy N θ.1 :
          Set (IrreducibleCharacter.inertia N θ.1)) ≤
      MonoidHom.range (embedding N H M e he θ) := by
  intro z hz
  have hzCG :
      (z : G) ∈
        Subgroup.centralizer (N : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hz ⊢
    intro n hn
    let nN : N := ⟨n, hn⟩
    let nI : IrreducibleCharacter.inertia N θ.1 :=
      inertiaInclusion N θ.1 nN
    let nCopy : inertiaNormalCopy N θ.1 :=
      ⟨nI, hn⟩
    have hcomm :=
      (Subgroup.mem_centralizer_iff.mp hz)
        (nCopy :
          IrreducibleCharacter.inertia N θ.1)
        nCopy.property
    exact
      congrArg
        (fun x : IrreducibleCharacter.inertia N θ.1 ↦
          (x : G)) hcomm
  let zH : H := ⟨(z : G), hcentral hzCG⟩
  have hzTarget :
      (zH : H) ∈
        IrreducibleCharacter.inertia M (e θ).1 :=
    mem_target_inertia_of_mem_source_inertia
      N H M e he θ zH z.property
  let zTarget :
      IrreducibleCharacter.inertia M (e θ).1 :=
    ⟨zH, hzTarget⟩
  exact
    ⟨zTarget, by
      apply Subtype.ext
      rfl⟩

omit [Finite G] in
/-- If `N` and `H` generate `G`, then the source inertia group is the
product of its canonical normal copy and the image of the matched target
inertia group. -/
theorem ambient_eq_product
    (e :
      PPrimeIrreducibleCharacter N p ≃
        PPrimeIrreducibleCharacter M p)
    (he :
      ∀ (h : H) (χ : PPrimeIrreducibleCharacter N p),
        e (h • χ) = h • e χ)
    (hsup : N ⊔ H = ⊤)
    (θ : PPrimeIrreducibleCharacter N p)
    (a : IrreducibleCharacter.inertia N θ.1) :
    ∃ x : inertiaNormalCopy N θ.1,
      ∃ h : IrreducibleCharacter.inertia M (e θ).1,
        (x : IrreducibleCharacter.inertia N θ.1) *
            embedding N H M e he θ h =
          a := by
  have haSup : (a : G) ∈ N ⊔ H := by
    rw [hsup]
    exact Subgroup.mem_top (a : G)
  obtain ⟨n, hn, h, hh, hprod⟩ :=
    Subgroup.mem_sup_of_normal_left.mp haSup
  let nN : N := ⟨n, hn⟩
  let hH : H := ⟨h, hh⟩
  have haθ :
      ((a : G) • θ) = θ := by
    apply Subtype.ext
    exact
      (IrreducibleCharacter.mem_inertia_iff
        N θ.1 (a : G)).mp a.property
  have hhθ :
      ((hH : H) : G) • θ = θ := by
    calc
      ((hH : H) : G) • θ =
          (nN : G) • (((hH : H) : G) • θ) := by
        symm
        exact
          PPrimeIrreducibleCharacter.normalSubgroup_smul_eq
            N p nN (((hH : H) : G) • θ)
      _ = ((nN : G) * ((hH : H) : G)) • θ := by
        rw [mul_smul]
      _ = (a : G) • θ := by
        rw [hprod]
      _ = θ := haθ
  have hhSource :
      ((hH : H) : G) ∈
        IrreducibleCharacter.inertia N θ.1 := by
    rw [IrreducibleCharacter.mem_inertia_iff]
    exact congrArg Subtype.val hhθ
  have hhTarget :
      (hH : H) ∈
        IrreducibleCharacter.inertia M (e θ).1 :=
    mem_target_inertia_of_mem_source_inertia
      N H M e he θ hH hhSource
  let nInertia :
      IrreducibleCharacter.inertia N θ.1 :=
    inertiaInclusion N θ.1 nN
  let x : inertiaNormalCopy N θ.1 :=
    ⟨nInertia, hn⟩
  let hInertia :
      IrreducibleCharacter.inertia M (e θ).1 :=
    ⟨hH, hhTarget⟩
  exact
    ⟨x, hInertia, by
      apply Subtype.ext
      exact hprod⟩

omit [Finite G] in
/-- The exact base intersection `N ∩ H = M` lifts to the exact
intersection of the canonical normal copies inside the matched inertia
groups. -/
theorem intersection_eq
    (e :
      PPrimeIrreducibleCharacter N p ≃
        PPrimeIrreducibleCharacter M p)
    (he :
      ∀ (h : H) (χ : PPrimeIrreducibleCharacter N p),
        e (h • χ) = h • e χ)
    (hintersection :
      N ⊓ H = M.map H.subtype)
    (θ : PPrimeIrreducibleCharacter N p) :
    inertiaNormalCopy N θ.1 ⊓
        MonoidHom.range (embedding N H M e he θ) =
      (inertiaNormalCopy M (e θ).1).map
        (embedding N H M e he θ) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨b, hbz⟩ := hz.2
    have hzN := hz.1
    change (z : G) ∈ N at hzN
    have hbzG :
        (((b :
          IrreducibleCharacter.inertia M (e θ).1) : H) : G) =
          (z : G) :=
      congrArg
        (fun x : IrreducibleCharacter.inertia N θ.1 ↦
          (x : G)) hbz
    have hbN :
        (((b :
          IrreducibleCharacter.inertia M (e θ).1) : H) : G) ∈ N :=
      hbzG.symm ▸ hzN
    have hbInf :
        (((b :
          IrreducibleCharacter.inertia M (e θ).1) : H) : G) ∈
          N ⊓ H :=
      ⟨hbN, (b : H).property⟩
    have hbMap :
        (((b :
          IrreducibleCharacter.inertia M (e θ).1) : H) : G) ∈
          M.map H.subtype := by
      rw [← hintersection]
      exact hbInf
    obtain ⟨m, hm, hmb⟩ :=
      Subgroup.mem_map.mp hbMap
    have hmEq :
        m = (b : H) := by
      apply Subtype.ext
      exact hmb
    have hbM :
        (b : H) ∈ M := by
      rw [← hmEq]
      exact hm
    exact
      ⟨b, hbM, hbz⟩
  · intro z hz
    obtain ⟨b, hbM, hbz⟩ := hz
    have hbMap :
        (((b :
          IrreducibleCharacter.inertia M (e θ).1) : H) : G) ∈
          M.map H.subtype :=
      ⟨(b : H), hbM, rfl⟩
    have hbInf :
        (((b :
          IrreducibleCharacter.inertia M (e θ).1) : H) : G) ∈
          N ⊓ H := by
      rw [hintersection]
      exact hbMap
    have hbzG :
        (((b :
          IrreducibleCharacter.inertia M (e θ).1) : H) : G) =
          (z : G) :=
      congrArg
        (fun x : IrreducibleCharacter.inertia N θ.1 ↦
          (x : G)) hbz
    constructor
    · change (z : G) ∈ N
      exact hbzG ▸ hbInf.1
    · exact ⟨b, hbz⟩

/-- Package the canonical inertia embedding and its three exact group
properties as the input expected by projective restriction. -/
theorem centralRestrictionGroupData
    (e :
      PPrimeIrreducibleCharacter N p ≃
        PPrimeIrreducibleCharacter M p)
    (he :
      ∀ (h : H) (χ : PPrimeIrreducibleCharacter N p),
        e (h • χ) = h • e χ)
    (hsup : N ⊔ H = ⊤)
    (hcentral :
      Subgroup.centralizer (N : Set G) ≤ H)
    (hintersection :
      N ⊓ H = M.map H.subtype)
    (θ : PPrimeIrreducibleCharacter N p) :
    CentralRestrictionGroupData
      (ofInertia N θ.1)
      (ofInertia M (e θ).1)
      (embedding N H M e he θ) where
  embedding_injective :=
    embedding_injective N H M e he θ
  centralizer_le :=
    centralizer_le_range N H M e he hcentral θ
  ambient_eq_product :=
    ambient_eq_product N H M e he hsup θ
  intersection_eq :=
    intersection_eq N H M e he hintersection θ

end MatchedInertiaRestriction

namespace MatchedCentralTripleCliffordAssemblyData

variable {N H M}

/-- The canonical target-to-source inertia embedding attached to one
matched character. -/
def inertiaEmbedding
    (d : MatchedCentralTripleCliffordAssemblyData N H M p)
    (θ : PPrimeIrreducibleCharacter N p) :
    IrreducibleCharacter.inertia M
        (d.characterEquiv θ).1 →*
      IrreducibleCharacter.inertia N θ.1 :=
  MatchedInertiaRestriction.embedding
    N H M d.characterEquiv d.characterEquiv_smul θ

@[simp]
theorem inertiaEmbedding_apply_coe
    (d : MatchedCentralTripleCliffordAssemblyData N H M p)
    (θ : PPrimeIrreducibleCharacter N p)
    (b :
      IrreducibleCharacter.inertia M
        (d.characterEquiv θ).1) :
    ((d.inertiaEmbedding θ b :
        IrreducibleCharacter.inertia N θ.1) : G) =
      (((b :
        IrreducibleCharacter.inertia M
          (d.characterEquiv θ).1) : H) : G) :=
  rfl

/-- The exact inertia-restriction group data attached to matched
Clifford-assembly data.  The only additional inputs are the centralizer
containment and the necessary base intersection identity. -/
theorem inertiaRestrictionGroupData
    (d : MatchedCentralTripleCliffordAssemblyData N H M p)
    (hcentral :
      Subgroup.centralizer (N : Set G) ≤ H)
    (hintersection :
      N ⊓ H = M.map H.subtype)
    (θ : PPrimeIrreducibleCharacter N p) :
    CentralRestrictionGroupData
      (ofInertia N θ.1)
      (ofInertia M (d.characterEquiv θ).1)
      (d.inertiaEmbedding θ) :=
  MatchedInertiaRestriction.centralRestrictionGroupData
    N H M d.characterEquiv d.characterEquiv_smul
      d.sup_eq_top hcentral hintersection θ

end MatchedCentralTripleCliffordAssemblyData

end InductiveMcKay
end McKayConjecture
