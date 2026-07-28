/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordBijection
import McKayConjecture.Character.SimpleConstituent

/-!
# Partitioning irreducible characters by Clifford orbits

For a normal subgroup `N ⫳ G`, every irreducible character of `G` lies
over a unique `G`-orbit in `Irr(N)`.  This file packages that uniqueness
and the resulting sigma-type decomposition.  It is the bookkeeping layer
used when local correspondences are assembled orbit by orbit.
-/

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra

namespace McKayConjecture
namespace CliffordPartition

open CliffordCorrespondence
open CliffordEquivalence

variable {G : Type} [Group G] [Fintype G]
variable (N : Subgroup G) [N.Normal]

/-- Conjugacy orbits of irreducible characters of `N` under `G`. -/
abbrev OrbitSpace :=
  MulAction.orbitRel.Quotient G (IrreducibleCharacter N)

/-- The block of ambient irreducible characters lying over an orbit. -/
abbrev OrbitBlock (q : OrbitSpace N) :=
  IrreducibleCharactersOverOrbit N q.out

/-- A nondependent packaging of an orbit together with an ambient
character lying over it.  This is equivalent to the dependent sigma of
`OrbitBlock`s, but its independent character field makes extensionality
convenient. -/
structure TaggedOrbitBlock where
  orbit : OrbitSpace N
  character : IrreducibleCharacter G
  liesOver : LiesOverOrbit N orbit.out character

@[ext]
theorem TaggedOrbitBlock.ext
    {x y : TaggedOrbitBlock N}
    (horbit : x.orbit = y.orbit)
    (hcharacter : x.character = y.character) :
    x = y := by
  cases x
  cases y
  cases horbit
  cases hcharacter
  rfl

/-- Converting a group-algebra module to a representation and back
recovers the original module. -/
private def ofModuleAsModuleEquiv
    {M : Type} [AddCommGroup M] [Module ℂ[N] M]
    [Module ℂ M] [IsScalarTower ℂ ℂ[N] M] :
    (Representation.ofModule' (k := ℂ) (G := N) M).asModule
        ≃ₗ[ℂ[N]] M := by
  let ρ : Representation ℂ N M :=
    Representation.ofModule' M
  have hAlg :
      ρ.asAlgebraHom = Algebra.lsmul ℂ ℂ M := by
    simp [ρ, Representation.asAlgebraHom_def,
      Representation.ofModule']
  exact
  { ρ.asModuleEquiv with
    map_smul' := by
      intro r x
      change
        ρ.asModuleEquiv (r • x) =
          r • ρ.asModuleEquiv x
      exact
        (ρ.asModuleEquiv_map_smul r x).trans (by
          rw [hAlg]
          rfl) }

/-- A group-algebra linear equivalence induces an equivalence between the
corresponding representations, even when the target module was not first
repackaged as an `asModule`. -/
private def representationEquivToOfModule
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ N V)
    {M : Type} [AddCommGroup M] [Module ℂ[N] M]
    [Module ℂ M] [IsScalarTower ℂ ℂ[N] M]
    (e : ρ.asModule ≃ₗ[ℂ[N]] M) :
    ρ.Equiv (Representation.ofModule' M) :=
  representationEquivOfModuleLinearEquiv
    (e.trans (ofModuleAsModuleEquiv (N := N)).symm)

/-- The representation on the `g`-conjugate of the chosen Clifford
constituent. -/
private def conjugateConstituentRepresentation
    (χ : IrreducibleCharacter G) (g : G) :
    Representation ℂ N
      (CliffordTheorem.conjugateConstituent χ.realization N g) :=
  Representation.ofModule' (k := ℂ) (G := N)
    (CliffordTheorem.conjugateConstituent χ.realization N g)

/-- The representation reconstructed from a submodule acts by the
restriction of the ambient representation. -/
private theorem ofModuleSubmodule_apply_coe
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ N V)
    (S : Submodule ℂ[N] ρ.asModule)
    (n : N) (v : S) :
    ((Representation.ofModule' (k := ℂ) (G := N) S) n v :
        ρ.asModule) =
      ρ n (v.1 : ρ.asModule) := by
  change
    ((MonoidAlgebra.of ℂ N n) • v : S).1 =
      ρ n (v.1 : ρ.asModule)
  change
    (MonoidAlgebra.of ℂ N n) • (v.1 : ρ.asModule) =
      ρ n (v.1 : ρ.asModule)
  rw [← ρ.asAlgebraHom_of]
  rfl

/-- The explicit conjugation map on the chosen Clifford constituent is an
equivalence from the twisted constituent representation to the
representation on its conjugate submodule. -/
private def normalConstituentTwistEquiv
    (χ : IrreducibleCharacter G) (g : G) :
    let C := FDRep.normalSimpleConstituent χ.realization N
    Representation.Equiv
      (FDRep.res
        ((MulAut.conjNormal (H := N) g).symm : N →* N) C).ρ
      (conjugateConstituentRepresentation N χ g) := by
  let C := FDRep.normalSimpleConstituent χ.realization N
  let e :=
    CliffordTheorem.simpleConstituentLinearEquivConjugate
      χ.realization N g
  refine Representation.Equiv.mk e ?_
  intro n
  ext v
  let w :
      CliffordTheorem.simpleConstituent
        χ.realization N :=
    show C from v
  simp only [LinearMap.comp_apply]
  change
    χ.realization.ρ g
        (((Representation.ofModule' (k := ℂ) (G := N)
            (CliffordTheorem.simpleConstituent
              χ.realization N))
          ((MulAut.conjNormal (H := N) g).symm n) w :
            CliffordTheorem.simpleConstituent
              χ.realization N).1 : χ.realization) =
      (((Representation.ofModule' (k := ℂ) (G := N)
          (CliffordTheorem.conjugateConstituent
            χ.realization N g))
        n (e w) :
          CliffordTheorem.conjugateConstituent
            χ.realization N g).1 : χ.realization)
  rw [ofModuleSubmodule_apply_coe,
    ofModuleSubmodule_apply_coe]
  let x : χ.realization :=
    restrictionCarrierLinearEquiv N χ.realization
      (Representation.asModuleEquiv
        (FDRep.resSubgroup N χ.realization).ρ w.1)
  change
    χ.realization.ρ g
        (χ.realization.ρ
          (((MulAut.conjNormal (H := N) g).symm n : N) : G)
          x) =
      χ.realization.ρ (n : G)
        (χ.realization.ρ g x)
  rw [← Module.End.mul_apply, ← Module.End.mul_apply,
    ← map_mul, ← map_mul]
  have hgroup :
      g * ((((MulAut.conjNormal (H := N) g).symm n : N) : G)) =
        (n : G) * g := by
    simpa only [MulAut.conjNormal_symm_apply] using
      (show g * (g⁻¹ * (n : G) * g) = (n : G) * g by
        group)
  rw [hgroup]

/-- Any irreducible constituent of an irreducible restriction is conjugate
to the canonical chosen constituent. -/
theorem exists_conjBy_normalSimpleConstituent_eq
    (χ : IrreducibleCharacter G)
    (θ : IrreducibleCharacter N)
    (hθ : LiesOverAlong N.subtype θ χ) :
    ∃ g : G,
      IrreducibleCharacter.conjBy N g
          (χ.normalSimpleConstituent N) =
        θ := by
  obtain ⟨f, hf⟩ :=
    (liesOverAlong_iff_exists_nonzero N.subtype θ χ).mp hθ
  let S : Submodule ℂ[N]
      (Representation.asModule
        (FDRep.resSubgroup N χ.realization).ρ) :=
    constituentSubmodule N θ χ.realization f
  have hS : IsSimpleModule ℂ[N] S := by
    dsimp [S]
    exact
      constituentSubmodule_isSimpleModule
        N θ χ.realization f hf
  letI hSinst : IsSimpleModule ℂ[N] S := hS
  have hex :=
    @CliffordTheorem.simpleConstituent_linearEquiv_conjugate
      ℂ inferInstance G inferInstance χ.realization inferInstance
      N inferInstance S hSinst
  obtain ⟨g, ⟨eS⟩⟩ :=
    hex
  refine ⟨g, ?_⟩
  apply IrreducibleCharacter.ext
  let eθ :
      Representation.asModule θ.realization.ρ ≃ₗ[ℂ[N]]
        CliffordTheorem.conjugateConstituent
          χ.realization N g :=
    (realizationEquivConstituentSubmodule
      N θ χ.realization f hf).trans eS
  let θEquiv :
      Representation.Equiv θ.realization.ρ
        (conjugateConstituentRepresentation N χ g) :=
    representationEquivToOfModule N θ.realization.ρ eθ
  let C := FDRep.normalSimpleConstituent χ.realization N
  let twistEquiv :=
    normalConstituentTwistEquiv N χ g
  have hθchar :
      θ.values =
        (conjugateConstituentRepresentation N χ g).character := by
    rw [← θ.realization_character]
    exact Representation.char_iso θEquiv
  have hcanonical :
      (IrreducibleCharacter.conjBy N g
          (χ.normalSimpleConstituent N)).values =
        (conjugateConstituentRepresentation N χ g).character := by
    rw [← conjugateRealization_character]
    funext n
    change
      (χ.normalSimpleConstituent N).realization.character
          ((MulAut.conjNormal (H := N) g).symm n) =
        (conjugateConstituentRepresentation N χ g).character n
    rw [(χ.normalSimpleConstituent N).realization_character]
    change
      C.character
          ((MulAut.conjNormal (H := N) g).symm n) =
        (conjugateConstituentRepresentation N χ g).character n
    exact congrFun (Representation.char_iso twistEquiv) n
  exact hcanonical.trans hθchar.symm

/-- The orbit of the canonical chosen constituent of an ambient
irreducible character. -/
def orbitOf (χ : IrreducibleCharacter G) : OrbitSpace N :=
  Quotient.mk'' (χ.normalSimpleConstituent N)

/-- The canonical constituent belongs to the orbit represented by
`orbitOf`. -/
theorem normalSimpleConstituent_mem_orbitOf
    (χ : IrreducibleCharacter G) :
    χ.normalSimpleConstituent N ∈ (orbitOf N χ).orbit := by
  rw [MulAction.orbitRel.Quotient.mem_orbit]
  rfl

/-- The chosen representative of `orbitOf χ` lies under `χ`, up to the
conjugation built into `LiesOverOrbit`. -/
theorem liesOverOrbit_out_orbitOf
    (χ : IrreducibleCharacter G) :
    LiesOverOrbit N (orbitOf N χ).out χ := by
  let θ := χ.normalSimpleConstituent N
  let q := orbitOf N χ
  have hout :
      q.out ∈ MulAction.orbit G θ := by
    change
      MulAction.orbitRel G (IrreducibleCharacter N)
        q.out θ
    exact Quotient.exact (Quotient.out_eq' q)
  have hθ :
      θ ∈ MulAction.orbit G q.out :=
    MulAction.mem_orbit_symm.mp hout
  obtain ⟨g, hg⟩ := hθ
  refine ⟨g, ?_⟩
  change
    LiesOverAlong N.subtype
      (IrreducibleCharacter.conjBy N g q.out) χ
  change
    IrreducibleCharacter.conjBy N g q.out = θ at hg
  rw [hg]
  exact χ.normalSimpleConstituent_liesOver N

/-- Decompose an ambient irreducible character into its Clifford orbit
and its membership in the corresponding orbit block. -/
def toOrbitBlockSigma (χ : IrreducibleCharacter G) :
    Σ q : OrbitSpace N, OrbitBlock N q :=
  ⟨orbitOf N χ, χ, liesOverOrbit_out_orbitOf N χ⟩

/-- Forget the Clifford-orbit tag. -/
def fromOrbitBlockSigma :
    (Σ q : OrbitSpace N, OrbitBlock N q) →
      IrreducibleCharacter G :=
  fun χ ↦ χ.2.1

@[simp]
theorem fromOrbitBlockSigma_toOrbitBlockSigma
    (χ : IrreducibleCharacter G) :
    fromOrbitBlockSigma N (toOrbitBlockSigma N χ) = χ :=
  rfl

/-- A character lying over the representative of an orbit is assigned
back to exactly that orbit. -/
theorem orbitOf_eq_of_mem_orbitBlock
    (q : OrbitSpace N) (χ : OrbitBlock N q) :
    orbitOf N χ.1 = q := by
  have hout :
      LiesOverAlong N.subtype q.out χ.1 :=
    liesOver_of_liesOverOrbit N q.out χ.1 χ.2
  obtain ⟨g, hg⟩ :=
    exists_conjBy_normalSimpleConstituent_eq
      N χ.1 q.out hout
  have hquot :
      (Quotient.mk''
          (χ.1.normalSimpleConstituent N) :
          OrbitSpace N) =
        Quotient.mk'' q.out := by
    apply Quotient.sound
    change
      χ.1.normalSimpleConstituent N ∈
        MulAction.orbit G q.out
    refine ⟨g⁻¹, ?_⟩
    calc
      g⁻¹ • q.out =
          g⁻¹ •
            IrreducibleCharacter.conjBy N g
              (χ.1.normalSimpleConstituent N) := by
        rw [hg]
      _ = χ.1.normalSimpleConstituent N := by
        simp
  exact hquot.trans (Quotient.out_eq' q)

/-- The nondependent tagged packaging and the dependent sigma packaging
are canonically equivalent. -/
def taggedOrbitBlockEquivSigma :
    TaggedOrbitBlock N ≃
      Σ q : OrbitSpace N, OrbitBlock N q where
  toFun x := ⟨x.orbit, x.character, x.liesOver⟩
  invFun x :=
    { orbit := x.1
      character := x.2.1
      liesOver := x.2.2 }
  left_inv := by
    rintro ⟨q, χ, hχ⟩
    rfl
  right_inv := by
    rintro ⟨q, ⟨χ, hχ⟩⟩
    rfl

/-- An ambient irreducible character is equivalently an orbit tagged with
that character's Clifford block. -/
def taggedOrbitBlockEquiv :
    IrreducibleCharacter G ≃ TaggedOrbitBlock N where
  toFun χ :=
    { orbit := orbitOf N χ
      character := χ
      liesOver := liesOverOrbit_out_orbitOf N χ }
  invFun x := x.character
  left_inv _ := rfl
  right_inv := by
    intro x
    apply TaggedOrbitBlock.ext
    · exact orbitOf_eq_of_mem_orbitBlock N x.orbit
        ⟨x.character, x.liesOver⟩
    · rfl

/-- Ordinary irreducible characters are the disjoint union of the
Clifford blocks indexed by conjugacy orbits in `Irr(N)`. -/
def orbitBlockSigmaEquiv :
    IrreducibleCharacter G ≃
      Σ q : OrbitSpace N, OrbitBlock N q :=
  (taggedOrbitBlockEquiv N).trans
    (taggedOrbitBlockEquivSigma N)

/-! ## Prime-to-`p` restriction -/

/-- The prime-to-`p` part of a Clifford orbit block. -/
def PPrimeOrbitBlock (p : ℕ) (q : OrbitSpace N) :=
  {χ : OrbitBlock N q // χ.1.IsPPrimeDegree p}

/-- A nondependent tagged packaging of a prime-to-`p` ambient character
and its Clifford orbit. -/
structure PPrimeTaggedOrbitBlock (p : ℕ) where
  orbit : OrbitSpace N
  character : PPrimeIrreducibleCharacter G p
  liesOver : LiesOverOrbit N orbit.out character.1

@[ext]
theorem PPrimeTaggedOrbitBlock.ext
    {p : ℕ} {x y : PPrimeTaggedOrbitBlock N p}
    (horbit : x.orbit = y.orbit)
    (hcharacter : x.character = y.character) :
    x = y := by
  cases x
  cases y
  cases horbit
  cases hcharacter
  rfl

/-- The nondependent prime-to-`p` packaging is equivalent to the sigma
of prime-to-`p` orbit blocks. -/
def pPrimeTaggedOrbitBlockEquivSigma (p : ℕ) :
    PPrimeTaggedOrbitBlock N p ≃
      Σ q : OrbitSpace N, PPrimeOrbitBlock N p q where
  toFun x :=
    ⟨x.orbit, ⟨⟨x.character.1, x.liesOver⟩,
      x.character.2⟩⟩
  invFun x :=
    { orbit := x.1
      character := ⟨x.2.1.1, x.2.2⟩
      liesOver := x.2.1.2 }
  left_inv := by
    rintro ⟨q, χ, hχ⟩
    rfl
  right_inv := by
    rintro ⟨q, ⟨⟨χ, hχ⟩, hpχ⟩⟩
    rfl

/-- A prime-to-`p` irreducible character is equivalently its tagged
Clifford block. -/
def pPrimeTaggedOrbitBlockEquiv (p : ℕ) :
    PPrimeIrreducibleCharacter G p ≃
      PPrimeTaggedOrbitBlock N p where
  toFun χ :=
    { orbit := orbitOf N χ.1
      character := χ
      liesOver := liesOverOrbit_out_orbitOf N χ.1 }
  invFun x := x.character
  left_inv _ := rfl
  right_inv := by
    intro x
    apply PPrimeTaggedOrbitBlock.ext
    · exact orbitOf_eq_of_mem_orbitBlock N x.orbit
        ⟨x.character.1, x.liesOver⟩
    · rfl

/-- Prime-to-`p` irreducible characters are the disjoint union of the
prime-to-`p` parts of the Clifford orbit blocks. -/
def pPrimeOrbitBlockSigmaEquiv (p : ℕ) :
    PPrimeIrreducibleCharacter G p ≃
      Σ q : OrbitSpace N, PPrimeOrbitBlock N p q :=
  (pPrimeTaggedOrbitBlockEquiv N p).trans
    (pPrimeTaggedOrbitBlockEquivSigma N p)

end CliffordPartition
end McKayConjecture
