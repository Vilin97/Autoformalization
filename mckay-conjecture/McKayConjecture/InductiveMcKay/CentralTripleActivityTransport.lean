/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ActiveOrbitTransport
import McKayConjecture.InductiveMcKay.CentralTripleCliffordAssembly

/-!
# Transporting activity through central inertia triples

Let `N ◁ G`, let `H ≤ G`, and let `M ◁ H`, with `N ⊔ H = G`.
Suppose an `H`-equivariant equivalence matches the prime-to-`p`
irreducible characters of `N` and `M`.  If the canonical inertia triples
of every matched pair carry a complete central-isomorphism witness, then
the equivalence preserves the exact Clifford activity predicate.

The proof first characterizes activity at a representative `θ` by two
conditions: the inertia index is prime to `p`, and the prime-to-`p`
inertia fiber over `θ` is nonempty.  The central-isomorphism witness
transports the second condition.  The first follows from the equality
of the ambient and restricted stabilizer indices under `N ⊔ H = G`,
together with stabilizer preservation under an equivariant equivalence.
The resulting activity equivalence descends to an equivalence of active
Clifford orbits.
-/

noncomputable section

namespace McKayConjecture

open GroupTheory

namespace CliffordPartition

variable {A : Type} [Group A] [Finite A]
variable (K : Subgroup A) [K.Normal]

noncomputable local instance centralTripleActivityTransportFintypeA :
    Fintype A :=
  Fintype.ofFinite A

omit [Finite A] in
/-- The stabilizer of a prime-to-`p` character is the inertia subgroup
of its underlying irreducible character. -/
theorem pPrime_stabilizer_eq_inertia
    {p : ℕ} (θ : PPrimeIrreducibleCharacter K p) :
    MulAction.stabilizer A θ =
      IrreducibleCharacter.inertia K θ.1 := by
  ext a
  simp only [MulAction.mem_stabilizer_iff]
  constructor
  · intro ha
    exact congrArg Subtype.val ha
  · intro ha
    apply Subtype.ext
    exact ha

/-- Activity of a prime-to-`p` normal-subgroup character is equivalent
to prime-to-`p` inertia index together with a nonempty prime-to-`p`
inertia fiber over that exact representative.

The orbit-block definition uses the quotient's chosen `out`
representative.  `pPrimeOrbitBlockEquivOfQuotientMkEq` supplies the
necessary harmless repackaging between that representative and `θ`. -/
theorem isActivePPrimeCharacter_iff_inertia
    {p : ℕ} (hp : p.Prime)
    (θ : PPrimeIrreducibleCharacter K p) :
    IsActivePPrimeCharacter K θ ↔
      (¬p ∣
          (IrreducibleCharacter.inertia K θ.1).index) ∧
        Nonempty
          (CliffordCorrespondence.PPrimeIrreducibleCharactersOverInertia
            K θ.1 p) := by
  let q : OrbitSpace K :=
    Quotient.mk'' θ.1
  have hq :
      (Quotient.mk'' q.out : OrbitSpace K) =
        Quotient.mk'' θ.1 :=
    Quotient.out_eq' q
  constructor
  · intro hactive
    obtain ⟨χ⟩ := hactive
    let χθ :
        CliffordCorrespondence.PPrimeIrreducibleCharactersOverOrbit
          K θ.1 p :=
      pPrimeOrbitBlockEquivOfQuotientMkEq
        K hq p χ
    let ψ :
        CliffordCorrespondence.IrreducibleCharactersOverInertia
          K θ.1 :=
      (CliffordEquivalence.cliffordCorrespondenceEquiv
        K θ.1).symm χθ.1
    have hinduced :
        CliffordEquivalence.induceOverInertiaOrbit
            K θ.1 ψ =
          χθ.1 :=
      (CliffordEquivalence.cliffordCorrespondenceEquiv
        K θ.1).apply_symm_apply χθ.1
    have hpInduced :
        (CliffordEquivalence.induceOverInertiaOrbit
          K θ.1 ψ).1.IsPPrimeDegree p := by
      rw [hinduced]
      exact χθ.2
    have hindex :
        ¬p ∣
          (IrreducibleCharacter.inertia K θ.1).index := by
      have hproduct :=
        (CliffordEquivalence.induceOverInertiaOrbit_isPPrimeDegree_iff_index_mul_degree
          K θ.1 p ψ).mp hpInduced
      intro hdvd
      exact hproduct
        (dvd_mul_of_dvd_left hdvd ψ.1.degree)
    refine ⟨hindex, ⟨⟨ψ, ?_⟩⟩⟩
    exact
      (CliffordEquivalence.induceOverInertiaOrbit_isPPrimeDegree_iff_of_index
        K θ.1 hp hindex ψ).mp hpInduced
  · rintro ⟨hindex, ⟨ψ⟩⟩
    let χθ :
        CliffordCorrespondence.PPrimeIrreducibleCharactersOverOrbit
          K θ.1 p :=
      CliffordEquivalence.cliffordPPrimeCorrespondence
        K θ.1 hp hindex ψ
    refine ⟨?_⟩
    exact
      pPrimeOrbitBlockEquivOfQuotientMkEq
        K hq.symm p χθ

end CliffordPartition

namespace InductiveMcKay

open CliffordPartition
open CharacterTriple

variable {G : Type} [Group G] [Finite G]
variable (N H : Subgroup G) [N.Normal]
variable (M : Subgroup H) [M.Normal]
variable {p : ℕ} [Fact p.Prime]

noncomputable local instance centralTripleActivityTransportFintypeG :
    Fintype G :=
  Fintype.ofFinite G

noncomputable local instance centralTripleActivityTransportFintypeH :
    Fintype H :=
  Fintype.ofFinite H

omit [Finite G] [Fact p.Prime] in
/-- Under `N ⊔ H = G`, an `H`-equivariant equivalence identifies the
source inertia index in `G` with the target inertia index in `H`. -/
theorem inertia_index_eq_of_equivariant_equiv
    (hsup : N ⊔ H = ⊤)
    (e :
      PPrimeIrreducibleCharacter N p ≃
        PPrimeIrreducibleCharacter M p)
    (he :
      ∀ (h : H) (θ : PPrimeIrreducibleCharacter N p),
        e (h • θ) = h • e θ)
    (θ : PPrimeIrreducibleCharacter N p) :
    (IrreducibleCharacter.inertia N θ.1).index =
      (IrreducibleCharacter.inertia M (e θ).1).index := by
  calc
    (IrreducibleCharacter.inertia N θ.1).index =
        (MulAction.stabilizer G θ).index := by
      exact congrArg
        (fun L : Subgroup G => L.index)
        (CliffordPartition.pPrime_stabilizer_eq_inertia
          N θ).symm
    _ = (MulAction.stabilizer H θ).index :=
      PPrimeIrreducibleCharacter.stabilizer_index_eq_subgroup_stabilizer_index_of_sup_eq_top
        N H p hsup θ
    _ = (MulAction.stabilizer H (e θ)).index := by
      exact congrArg
        (fun L : Subgroup H => L.index)
        (GroupTheory.stabilizer_eq_of_equivariant_equiv
          e he θ).symm
    _ = (IrreducibleCharacter.inertia M (e θ).1).index := by
      exact congrArg
        (fun L : Subgroup H => L.index)
        (CliffordPartition.pPrime_stabilizer_eq_inertia
          M (e θ))

/-- Complete central-isomorphism witnesses between all matched inertia
triples force an equivariant prime-to-`p` character equivalence to
preserve the exact activity predicate. -/
theorem isActivePPrimeCharacter_iff_of_completeCentralIsomorphismWitness
    (hsup : N ⊔ H = ⊤)
    (e :
      PPrimeIrreducibleCharacter N p ≃
        PPrimeIrreducibleCharacter M p)
    (he :
      ∀ (h : H) (θ : PPrimeIrreducibleCharacter N p),
        e (h • θ) = h • e θ)
    (C :
      ∀ θ : PPrimeIrreducibleCharacter N p,
        CompleteCentralIsomorphismWitness
          (ofInertia N θ.1)
          (ofInertia M (e θ).1))
    (θ : PPrimeIrreducibleCharacter N p) :
    @IsActivePPrimeCharacter G _ N _ p θ ↔
      @IsActivePPrimeCharacter H _ M _ p (e θ) := by
  let Cθ := C θ
  letI := Cθ.leftAddCommGroup
  letI := Cθ.leftModule
  letI := Cθ.leftModuleFinite
  letI := Cθ.leftNontrivial
  letI := Cθ.rightAddCommGroup
  letI := Cθ.rightModule
  letI := Cθ.rightModuleFinite
  letI := Cθ.rightNontrivial
  have hindex :
      (IrreducibleCharacter.inertia N θ.1).index =
        (IrreducibleCharacter.inertia M (e θ).1).index :=
    inertia_index_eq_of_equivariant_equiv
      N H M hsup e he θ
  constructor
  · intro hactive
    obtain ⟨hindexN, ⟨ψ⟩⟩ :=
      (CliffordPartition.isActivePPrimeCharacter_iff_inertia
        N (Fact.out : p.Prime) θ).mp hactive
    have hindexM :
        ¬p ∣
          (IrreducibleCharacter.inertia M (e θ).1).index := by
      rwa [← hindex]
    let ψM :=
      Cθ.witness.pPrimeInertiaEquiv
        N θ.1 M (e θ).1
        (Fact.out : p.Prime) θ.2 (e θ).2 ψ
    exact
      (CliffordPartition.isActivePPrimeCharacter_iff_inertia
        M (Fact.out : p.Prime) (e θ)).mpr
          ⟨hindexM, ⟨ψM⟩⟩
  · intro hactive
    obtain ⟨hindexM, ⟨ψ⟩⟩ :=
      (CliffordPartition.isActivePPrimeCharacter_iff_inertia
        M (Fact.out : p.Prime) (e θ)).mp hactive
    have hindexN :
        ¬p ∣
          (IrreducibleCharacter.inertia N θ.1).index := by
      rwa [hindex]
    let ψN :=
      (Cθ.witness.pPrimeInertiaEquiv
        N θ.1 M (e θ).1
        (Fact.out : p.Prime) θ.2 (e θ).2).symm ψ
    exact
      (CliffordPartition.isActivePPrimeCharacter_iff_inertia
        N (Fact.out : p.Prime) θ).mpr
          ⟨hindexN, ⟨ψN⟩⟩

/-- The active-orbit equivalence induced by equivariance and complete
central-isomorphism witnesses on every matched inertia pair. -/
def activeOrbitEquivOfCompleteCentralIsomorphismWitness
    (hsup : N ⊔ H = ⊤)
    (e :
      PPrimeIrreducibleCharacter N p ≃
        PPrimeIrreducibleCharacter M p)
    (he :
      ∀ (h : H) (θ : PPrimeIrreducibleCharacter N p),
        e (h • θ) = h • e θ)
    (C :
      ∀ θ : PPrimeIrreducibleCharacter N p,
        CompleteCentralIsomorphismWitness
          (ofInertia N θ.1)
          (ofInertia M (e θ).1)) :
    ActiveOrbit N p ≃ ActiveOrbit M p :=
  activeOrbitEquivOfEquivariantActivityIff
    N H M hsup e he
      (isActivePPrimeCharacter_iff_of_completeCentralIsomorphismWitness
        N H M hsup e he C)

/-- The induced active-orbit equivalence sends the orbit represented by
`θ` to the orbit represented by `e θ`. -/
@[simp]
theorem activeOrbitEquivOfCompleteCentralIsomorphismWitness_apply_coe
    (hsup : N ⊔ H = ⊤)
    (e :
      PPrimeIrreducibleCharacter N p ≃
        PPrimeIrreducibleCharacter M p)
    (he :
      ∀ (h : H) (θ : PPrimeIrreducibleCharacter N p),
        e (h • θ) = h • e θ)
    (C :
      ∀ θ : PPrimeIrreducibleCharacter N p,
        CompleteCentralIsomorphismWitness
          (ofInertia N θ.1)
          (ofInertia M (e θ).1))
    (q : ActiveOrbit N p) :
    (activeOrbitEquivOfCompleteCentralIsomorphismWitness
      N H M hsup e he C q).1 =
        (Quotient.mk'' (e (q.pPrimeOut N)).1 :
          OrbitSpace M) :=
  rfl

end InductiveMcKay
end McKayConjecture
