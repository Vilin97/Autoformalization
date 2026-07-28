/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ActiveOrbitTransport
import McKayConjecture.GroupTheory.PGroupQuotientIndex

/-!
# Active Clifford orbits above a `p`-group quotient

Let `N` be normal in a finite group `G` and suppose that `G/N` is a
`p`-group.  If an orbit in `Irr(N)` lies below a prime-to-`p` irreducible
character of `G`, Clifford's degree formula says that its inertia index is
prime to `p`.  On the other hand, that index divides a power of `p`.
Therefore the inertia group is all of `G`.

This is the ordinary-character part of the first step in the
Okuyama--Wajima/Navarro--Späth central-intersection argument.  The later
Dade--Glauberman--Nagao correspondence between invariant kernel
characters is a separate, genuinely block-theoretic input.
-/

noncomputable section

namespace McKayConjecture
namespace CliffordPartition

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (N : Subgroup G) [N.Normal]

/-- Every active orbit representative is invariant under `G` when the
ambient quotient by the normal subgroup is a `p`-group. -/
theorem activeOrbit_inertia_eq_top_of_quotient_isPGroup
    (hquotient : IsPGroup p (G ⧸ N))
    (q : ActiveOrbit N p) :
    IrreducibleCharacter.inertia N q.1.out = ⊤ := by
  letI : Fintype G := Fintype.ofFinite G
  exact
    GroupTheory.eq_top_of_normal_le_of_quotient_isPGroup
      N (IrreducibleCharacter.inertia N q.1.out)
      (IrreducibleCharacter.subgroup_le_inertia N q.1.out)
      hquotient
      (activeOrbit_inertia_index_isPPrime N q)

omit [Fact p.Prime] in
/-- An active prime-to-`p` character has prime-to-`p` inertia index.

Unlike `activeOrbit_inertia_index_isPPrime`, this version is stated at
the exact representative supplied by the caller. -/
theorem isActivePPrimeCharacter_inertia_index_isPPrime
    (θ : PPrimeIrreducibleCharacter N p)
    (hactive : IsActivePPrimeCharacter N θ) :
    ¬p ∣
      (IrreducibleCharacter.inertia N θ.1).index := by
  letI : Fintype G := Fintype.ofFinite G
  let q : OrbitSpace N :=
    Quotient.mk'' θ.1
  have hq :
      (Quotient.mk'' q.out : OrbitSpace N) =
        Quotient.mk'' θ.1 :=
    Quotient.out_eq' q
  obtain ⟨χ⟩ := hactive
  let χθ :
      CliffordCorrespondence.PPrimeIrreducibleCharactersOverOrbit
        N θ.1 p :=
    pPrimeOrbitBlockEquivOfQuotientMkEq
      N hq p χ
  let ψ :
      CliffordCorrespondence.IrreducibleCharactersOverInertia
        N θ.1 :=
    (CliffordEquivalence.cliffordCorrespondenceEquiv
      N θ.1).symm χθ.1
  have hinduced :
      CliffordEquivalence.induceOverInertiaOrbit
          N θ.1 ψ =
        χθ.1 :=
    (CliffordEquivalence.cliffordCorrespondenceEquiv
      N θ.1).apply_symm_apply χθ.1
  have hpInduced :
      (CliffordEquivalence.induceOverInertiaOrbit
        N θ.1 ψ).1.IsPPrimeDegree p := by
    rw [hinduced]
    exact χθ.2
  have hproduct :=
    (CliffordEquivalence.induceOverInertiaOrbit_isPPrimeDegree_iff_index_mul_degree
      N θ.1 p ψ).mp hpInduced
  intro hdvd
  exact hproduct
    (dvd_mul_of_dvd_left hdvd ψ.1.degree)

/-- The same invariance conclusion for any active prime-to-`p`
character of the normal subgroup, not just the quotient's chosen
representative. -/
theorem inertia_eq_top_of_isActivePPrimeCharacter
    (hquotient : IsPGroup p (G ⧸ N))
    (θ : PPrimeIrreducibleCharacter N p)
    (hactive : IsActivePPrimeCharacter N θ) :
    IrreducibleCharacter.inertia N θ.1 = ⊤ := by
  exact
    GroupTheory.eq_top_of_normal_le_of_quotient_isPGroup
      N (IrreducibleCharacter.inertia N θ.1)
      (IrreducibleCharacter.subgroup_le_inertia N θ.1)
      hquotient
      (isActivePPrimeCharacter_inertia_index_isPPrime
        N θ hactive)

end CliffordPartition
end McKayConjecture
