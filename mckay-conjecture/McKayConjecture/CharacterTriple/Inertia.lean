/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordEquivalence
import McKayConjecture.Character.CliffordActiveOrbit
import McKayConjecture.Character.CliffordPPrimeCorrespondence
import McKayConjecture.Character.PPrimeCliffordOrbit
import McKayConjecture.CharacterTriple.CentralCharacterBijection
import McKayConjecture.CharacterTriple.CentralIsomorphism

/-!
# Character triples attached to inertia groups

For a normal subgroup `N ◁ G` and `θ ∈ Irr(N)`, the inertia group
`I_G(θ)` contains a canonical copy of `N`.  The transported character on
that copy is invariant under the inertia group and hence defines a
character triple.  This is the canonical form needed to apply central
character-triple correspondences inside Clifford blocks.
-/

noncomputable section

open CategoryTheory

namespace McKayConjecture
namespace CharacterTriple

open CliffordEquivalence
open CliffordCorrespondence

variable {G : Type} [Group G] [Finite G]
variable (N : Subgroup G) [N.Normal]
variable (θ : IrreducibleCharacter N)

noncomputable local instance inertiaCharacterTripleFintype :
    Fintype G :=
  Fintype.ofFinite G

/-- The canonical character triple
`(I_G(θ), N, θ)`, with `N` represented by its internal copy in the
inertia group. -/
def ofInertia :
    CharacterTriple (IrreducibleCharacter.inertia N θ) where
  normalSubgroup := inertiaNormalCopy N θ
  isNormal := inferInstance
  character := inertiaCopyCharacter N θ
  isInvariant := by
    intro a n
    have hfix :=
      inertiaCopyCharacter_invariant N θ a⁻¹
    have hvalue :=
      congrArg
        (fun χ : IrreducibleCharacter
            (inertiaNormalCopy N θ) ↦
          χ.values n)
        hfix
    rw [IrreducibleCharacter.conjBy_values] at hvalue
    convert hvalue using 1
    apply congrArg (inertiaCopyCharacter N θ).values
    apply Subtype.ext
    simp [conjugateNormalElement]

@[simp]
theorem ofInertia_normalSubgroup :
    (ofInertia N θ).normalSubgroup =
      inertiaNormalCopy N θ :=
  rfl

@[simp]
theorem ofInertia_character :
    (ofInertia N θ).character =
      inertiaCopyCharacter N θ :=
  rfl

/-! ### Comparing the two standard copies of the normal character -/

/-- The underlying intertwining map obtained by transporting a
constituent map from the canonical copy in the inertia group back to the
original normal subgroup. -/
def inertiaOriginalIntertwiningMap
    (ψ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (f :
      (inertiaCopyCharacter N θ).realization ⟶
        FDRep.resSubgroup
          (inertiaNormalCopy N θ) ψ.realization) :
    Representation.IntertwiningMap
      θ.realization.ρ
      (FDRep.res
        (inertiaInclusion N θ)
        ψ.realization).ρ := by
  let i := inertiaCopyRealizationIso N θ
  let fCopy :
      FDRep.res
          (inertiaNormalCopyEquiv N θ :
            inertiaNormalCopy N θ →* N)
          θ.realization ⟶
        FDRep.resSubgroup
          (inertiaNormalCopy N θ) ψ.realization :=
    i.inv ≫ f
  let fRep :=
    (FDRep.forget₂HomLinearEquiv _ _).symm fCopy
  exact
    { toLinearMap := fRep.hom.toLinearMap
      isIntertwining' := by
        intro n
        let nCopy : inertiaNormalCopy N θ :=
          (inertiaNormalCopyEquiv N θ).symm n
        have hn := fRep.hom.isIntertwining' nCopy
        change
          fRep.hom.toLinearMap ∘ₗ
              θ.realization.ρ n =
            ψ.realization.ρ
                (inertiaInclusion N θ n) ∘ₗ
              fRep.hom.toLinearMap
        change
          fRep.hom.toLinearMap ∘ₗ
              (θ.realization.ρ.comp
                (inertiaNormalCopyEquiv N θ :
                  inertiaNormalCopy N θ →* N)) nCopy =
            ψ.realization.ρ
                ((nCopy :
                  inertiaNormalCopy N θ) :
                  IrreducibleCharacter.inertia N θ) ∘ₗ
              fRep.hom.toLinearMap at hn
        have hnCoordinate :
            inertiaNormalCopyEquiv N θ nCopy = n := by
          simp [nCopy]
        have hnInertia :
            ((nCopy : inertiaNormalCopy N θ) :
                IrreducibleCharacter.inertia N θ) =
              inertiaInclusion N θ n := by
          apply Subtype.ext
          rfl
        simpa [hnCoordinate, hnInertia] using hn }

/-- Transport a constituent map from the canonical copy inside the
inertia group back to the original normal subgroup. -/
def inertiaOriginalConstituentHom
    (ψ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (f :
      (inertiaCopyCharacter N θ).realization ⟶
        FDRep.resSubgroup
          (inertiaNormalCopy N θ) ψ.realization) :
    θ.realization ⟶
      FDRep.res (inertiaInclusion N θ) ψ.realization :=
  FDRep.forget₂HomLinearEquiv _ _
    (Rep.ofHom
      (inertiaOriginalIntertwiningMap N θ ψ f))

/-- The reverse transport of a nonzero constituent map is nonzero. -/
theorem inertiaOriginalConstituentHom_ne_zero
    (ψ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))
    (f :
      (inertiaCopyCharacter N θ).realization ⟶
        FDRep.resSubgroup
          (inertiaNormalCopy N θ) ψ.realization)
    (hf : f ≠ 0) :
    inertiaOriginalConstituentHom N θ ψ f ≠ 0 := by
  intro hzero
  apply hf
  let i := inertiaCopyRealizationIso N θ
  have hcomp :
      i.inv ≫ f = 0 := by
    apply (FDRep.forget₂HomLinearEquiv _ _).symm.injective
    apply Rep.Hom.ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    have hv :=
      ConcreteCategory.congr_hom hzero v
    change
      (inertiaOriginalIntertwiningMap
        N θ ψ f).toLinearMap v = 0 at hv
    dsimp [inertiaOriginalIntertwiningMap] at hv
    change
      (((FDRep.forget₂HomLinearEquiv _ _).symm
        (i.inv ≫ f)).hom.toLinearMap v) = 0
    exact hv
  simpa using
    (cancel_epi i.inv).mp hcomp

/-- Lying over `θ` along the usual inclusion is equivalent to lying over
the transported character on the internal copy of `N` in its inertia
group. -/
theorem liesOverAlong_inertiaCopy_iff
    (ψ : IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ)) :
    LiesOverAlong
        (inertiaNormalCopy N θ).subtype
        (inertiaCopyCharacter N θ) ψ ↔
      LiesOverAlong
        (inertiaInclusion N θ) θ ψ := by
  constructor
  · intro h
    obtain ⟨f, hf⟩ :=
      (liesOverAlong_iff_exists_nonzero
        (inertiaNormalCopy N θ).subtype
        (inertiaCopyCharacter N θ) ψ).mp h
    exact
      (liesOverAlong_iff_exists_nonzero
        (inertiaInclusion N θ) θ ψ).mpr
        ⟨inertiaOriginalConstituentHom N θ ψ f,
          inertiaOriginalConstituentHom_ne_zero
            N θ ψ f hf⟩
  · intro h
    obtain ⟨f, hf⟩ :=
      (liesOverAlong_iff_exists_nonzero
        (inertiaInclusion N θ) θ ψ).mp h
    exact
      (liesOverAlong_iff_exists_nonzero
        (inertiaNormalCopy N θ).subtype
        (inertiaCopyCharacter N θ) ψ).mpr
        ⟨inertiaCopyConstituentHom N θ ψ f,
          inertiaCopyConstituentHom_ne_zero
            N θ ψ f hf⟩

/-- The usual characters of the inertia group lying over `θ` are
canonically the characters lying over the normal character in
`ofInertia N θ`. -/
def irreducibleCharactersOverInertiaEquivTriple :
    IrreducibleCharactersOverInertia N θ ≃
      IrreducibleCharactersOverAlong
        (ofInertia N θ).normalSubgroup.subtype
        (ofInertia N θ).character :=
  (Equiv.refl
    (IrreducibleCharacter
      (IrreducibleCharacter.inertia N θ))).subtypeEquiv
    (fun ψ ↦
      (liesOverAlong_inertiaCopy_iff
        N θ ψ).symm)

@[simp]
theorem irreducibleCharactersOverInertiaEquivTriple_apply_coe
    (ψ : IrreducibleCharactersOverInertia N θ) :
    (irreducibleCharactersOverInertiaEquivTriple
      N θ ψ).1 = ψ.1 :=
  rfl

@[simp]
theorem irreducibleCharactersOverInertiaEquivTriple_symm_apply_coe
    (ψ :
      IrreducibleCharactersOverAlong
        (ofInertia N θ).normalSubgroup.subtype
        (ofInertia N θ).character) :
    ((irreducibleCharactersOverInertiaEquivTriple
      N θ).symm ψ).1 = ψ.1 :=
  rfl

/-- Prime-to-`p` version of
`irreducibleCharactersOverInertiaEquivTriple`. -/
def pPrimeIrreducibleCharactersOverInertiaEquivTriple
    (p : ℕ) :
    PPrimeIrreducibleCharactersOverInertia N θ p ≃
      CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p (ofInertia N θ).normalSubgroup.subtype
          (ofInertia N θ).character :=
  (irreducibleCharactersOverInertiaEquivTriple
    N θ).subtypeEquiv (fun _ ↦ Iff.rfl)

@[simp]
theorem pPrimeIrreducibleCharactersOverInertiaEquivTriple_apply_coe
    (p : ℕ)
    (ψ : PPrimeIrreducibleCharactersOverInertia
      N θ p) :
    (pPrimeIrreducibleCharactersOverInertiaEquivTriple
      N θ p ψ).1.1 = ψ.1.1 :=
  rfl

@[simp]
theorem pPrimeIrreducibleCharactersOverInertiaEquivTriple_symm_apply_coe
    (p : ℕ)
    (ψ :
      CentralCharacterCorrespondence.PPrimeIrreducibleCharactersOverAlong
        p (ofInertia N θ).normalSubgroup.subtype
          (ofInertia N θ).character) :
    ((pPrimeIrreducibleCharactersOverInertiaEquivTriple
      N θ p).symm ψ).1.1 = ψ.1.1 :=
  rfl

namespace CentralIsomorphismWitness

variable {H : Type} [Group H] [Finite H]
variable (M : Subgroup H) [M.Normal]
variable (φ : IrreducibleCharacter M)
variable {V W : Type}
variable [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W]
  [Module.Finite ℂ W] [Nontrivial W]

/-- A central isomorphism between the two canonical inertia triples
gives the usual prime-to-`p` correspondence between inertia-group
characters lying over the original normal characters. -/
def pPrimeInertiaEquiv
    {p : ℕ} (hp : p.Prime)
    (C :
      CentralIsomorphismWitness
        (ofInertia N θ) (ofInertia M φ) V W)
    (hθ : θ.IsPPrimeDegree p)
    (hφ : φ.IsPPrimeDegree p) :
    PPrimeIrreducibleCharactersOverInertia N θ p ≃
      PPrimeIrreducibleCharactersOverInertia M φ p :=
  (pPrimeIrreducibleCharactersOverInertiaEquivTriple
      N θ p).trans
    ((C.centralPPrimeCharacterEquiv hp
      (by
        change
          ¬p ∣ (inertiaCopyCharacter N θ).degree
        simpa only [inertiaCopyCharacter,
          IrreducibleCharacter.comap_degree,
          IrreducibleCharacter.IsPPrimeDegree]
          using hθ)
      (by
        change
          ¬p ∣ (inertiaCopyCharacter M φ).degree
        simpa only [inertiaCopyCharacter,
          IrreducibleCharacter.comap_degree,
          IrreducibleCharacter.IsPPrimeDegree]
          using hφ)).trans
      (pPrimeIrreducibleCharactersOverInertiaEquivTriple
        M φ p).symm)

@[simp]
theorem pPrimeInertiaEquiv_apply_coe
    {p : ℕ} (hp : p.Prime)
    (C :
      CentralIsomorphismWitness
        (ofInertia N θ) (ofInertia M φ) V W)
    (hθ : θ.IsPPrimeDegree p)
    (hφ : φ.IsPPrimeDegree p)
    (ψ :
      PPrimeIrreducibleCharactersOverInertia N θ p) :
    (C.pPrimeInertiaEquiv N θ M φ hp hθ hφ ψ).1.1 =
      (C.centralPPrimeCharacterEquiv hp
        (by
          change
            ¬p ∣ (inertiaCopyCharacter N θ).degree
          simpa only [inertiaCopyCharacter,
            IrreducibleCharacter.comap_degree,
            IrreducibleCharacter.IsPPrimeDegree]
            using hθ)
        (by
          change
            ¬p ∣ (inertiaCopyCharacter M φ).degree
          simpa only [inertiaCopyCharacter,
            IrreducibleCharacter.comap_degree,
            IrreducibleCharacter.IsPPrimeDegree]
            using hφ)
        (pPrimeIrreducibleCharactersOverInertiaEquivTriple
          N θ p ψ)).1.1 :=
  rfl

/-- Combining the central character correspondence with Clifford
induction gives an equivalence of the two active prime-to-`p` Clifford
blocks. -/
def activeOrbitBlockEquiv
    {p : ℕ} (hp : p.Prime)
    (q : CliffordPartition.ActiveOrbit N p)
    (r : CliffordPartition.ActiveOrbit M p)
    (C :
      CentralIsomorphismWitness
        (ofInertia N q.1.out)
        (ofInertia M r.1.out) V W) :
    CliffordPartition.PPrimeOrbitBlock N p q.1 ≃
      CliffordPartition.PPrimeOrbitBlock M p r.1 :=
  (CliffordPartition.activeOrbitCliffordEquiv
      N hp q).symm |>.trans
    ((C.pPrimeInertiaEquiv
      N q.1.out M r.1.out hp
        (CliffordPartition.activeOrbit_out_isPPrimeDegree
          N q)
        (CliffordPartition.activeOrbit_out_isPPrimeDegree
          M r)).trans
      (CliffordPartition.activeOrbitCliffordEquiv
        M hp r))

end CentralIsomorphismWitness

end CharacterTriple
end McKayConjecture
