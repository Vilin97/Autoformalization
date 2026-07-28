/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordActiveOrbit
import McKayConjecture.Character.CliffordDegree

/-!
# Prime-to-`p` representatives of active Clifford orbits

Every representative of an active Clifford orbit has prime-to-`p`
degree.  This file packages the chosen quotient representative as a
`PPrimeIrreducibleCharacter` and identifies active Clifford orbits with
the conjugation-orbit quotient of the **active** prime-to-`p` characters
of the normal subgroup.

The active qualifier is essential.  In general not every conjugacy orbit
in `Irr_{p'}(N)` lies below a character in `Irr_{p'}(G)`.  For example,
when `G = S₃`, `N = A₃`, and `p = 2`, the orbit of the two nontrivial
linear characters of `N` lies only below the degree-two character of
`G`.  Moreover, prime-to-`p` inertia index is only necessary, not
sufficient: for an extraspecial group of order `p³` and its center, all
central characters have inertia index one, while a nontrivial central
character lies only below irreducible characters of degree `p`.

Accordingly, the unrestricted orbit-quotient equivalence is exposed only
under the exact hypothesis `AllPPrimeOrbitsActive`.
-/

noncomputable section

namespace McKayConjecture
namespace CliffordPartition

open CliffordCorrespondence
open CliffordEquivalence

variable {G : Type} [Group G] [Finite G]
variable (N : Subgroup G) [N.Normal]

/-! ## Prime-to-`p` representatives -/

/-- The chosen representative of an active orbit has prime-to-`p`
degree. -/
theorem activeOrbit_out_isPPrimeDegree
    {p : ℕ} (q : ActiveOrbit N p) :
    q.1.out.IsPPrimeDegree p := by
  letI : Fintype G := Fintype.ofFinite G
  let χ : PPrimeIrreducibleCharacter G p :=
    ⟨q.2.some.1.1, q.2.some.2⟩
  have hlies :
      LiesOverAlong N.subtype q.1.out χ.1 :=
    (liesOverOrbit_iff_liesOver N q.1.out χ.1).mp
      q.2.some.1.2
  obtain ⟨g, hg⟩ :=
    exists_conjBy_normalSimpleConstituent_eq
      N χ.1 q.1.out hlies
  rw [← hg, IrreducibleCharacter.IsPPrimeDegree,
    IrreducibleCharacter.conjBy_degree]
  exact
    χ.1.normalSimpleConstituent_isPPrimeDegree
      N χ.2

/-- Every representative of an active orbit has prime-to-`p` degree. -/
theorem isPPrimeDegree_of_mem_activeOrbit
    {p : ℕ} (q : ActiveOrbit N p)
    {θ : IrreducibleCharacter N}
    (hθ : θ ∈ q.1.orbit) :
    θ.IsPPrimeDegree p := by
  have hθ' :
      θ ∈ MulAction.orbit G q.1.out := by
    rwa [← MulAction.orbitRel.Quotient.orbit_eq_orbit_out
      q.1 Quotient.out_eq']
  obtain ⟨g, rfl⟩ :=
    (MulAction.mem_orbit_iff.mp hθ')
  rw [IrreducibleCharacter.IsPPrimeDegree,
    IrreducibleCharacter.conjBy_degree]
  exact activeOrbit_out_isPPrimeDegree N q

/-- Quotient-equality form of
`isPPrimeDegree_of_mem_activeOrbit`. -/
theorem isPPrimeDegree_of_mk_eq_activeOrbit
    {p : ℕ} (q : ActiveOrbit N p)
    {θ : IrreducibleCharacter N}
    (hθ :
      (Quotient.mk'' θ : OrbitSpace N) = q.1) :
    θ.IsPPrimeDegree p :=
  isPPrimeDegree_of_mem_activeOrbit N q
    (MulAction.orbitRel.Quotient.mem_orbit.mpr hθ)

/-- The canonical chosen representative of an active orbit, packaged as
a prime-to-`p` irreducible character. -/
def ActiveOrbit.pPrimeOut
    {p : ℕ} (q : ActiveOrbit N p) :
    PPrimeIrreducibleCharacter N p :=
  ⟨q.1.out, activeOrbit_out_isPPrimeDegree N q⟩

@[simp]
theorem ActiveOrbit.pPrimeOut_coe
    {p : ℕ} (q : ActiveOrbit N p) :
    (q.pPrimeOut N).1 =
      q.1.out :=
  rfl

/-- The chosen prime-to-`p` representative lies in its active Clifford
orbit. -/
theorem ActiveOrbit.pPrimeOut_mem_orbit
    {p : ℕ} (q : ActiveOrbit N p) :
    (q.pPrimeOut N).1 ∈ q.1.orbit := by
  rw [ActiveOrbit.pPrimeOut_coe,
    MulAction.orbitRel.Quotient.mem_orbit]
  exact Quotient.out_eq' q.1

/-! ## The active prime-to-`p` subtype -/

/-- A prime-to-`p` character of `N` is active when its ambient
conjugacy orbit carries a prime-to-`p` irreducible character of `G`. -/
def IsActivePPrimeCharacter
    {p : ℕ} (θ : PPrimeIrreducibleCharacter N p) : Prop :=
  Nonempty
    (PPrimeOrbitBlock N p
      (Quotient.mk'' θ.1 : OrbitSpace N))

/-- Prime-to-`p` irreducible characters of `N` whose ambient conjugacy
orbit is active. -/
def ActivePPrimeIrreducibleCharacter (p : ℕ) :=
  {θ : PPrimeIrreducibleCharacter N p //
    IsActivePPrimeCharacter N θ}

/-- The exact hypothesis under which every prime-to-`p` character of
`N` belongs to an active orbit. -/
def AllPPrimeOrbitsActive (p : ℕ) : Prop :=
  ∀ θ : PPrimeIrreducibleCharacter N p,
    IsActivePPrimeCharacter N θ

omit [Finite G] in
@[simp]
theorem pPrime_smul_coe
    {p : ℕ} (g : G)
    (θ : PPrimeIrreducibleCharacter N p) :
    (g • θ).1 =
      IrreducibleCharacter.conjBy N g θ.1 :=
  rfl

omit [Finite G] in
@[simp]
theorem pPrime_mk_smul_eq_mk
    {p : ℕ} (g : G)
    (θ : PPrimeIrreducibleCharacter N p) :
    (Quotient.mk'' ((g • θ).1) : OrbitSpace N) =
      Quotient.mk'' θ.1 := by
  apply Quotient.sound
  exact MulAction.mem_orbit θ.1 g

omit [Finite G] in
@[simp]
theorem isActivePPrimeCharacter_smul_iff
    {p : ℕ} (g : G)
    (θ : PPrimeIrreducibleCharacter N p) :
    IsActivePPrimeCharacter N (g • θ) ↔
      IsActivePPrimeCharacter N θ := by
  simp only [IsActivePPrimeCharacter,
    pPrime_mk_smul_eq_mk]

/-- The ambient conjugation action preserves the active prime-to-`p`
subtype. -/
instance activePPrimeMulAction
    (p : ℕ) :
    MulAction G (ActivePPrimeIrreducibleCharacter N p) where
  smul g θ :=
    ⟨g • θ.1,
      (isActivePPrimeCharacter_smul_iff
        N g θ.1).mpr θ.2⟩
  one_smul θ := by
    apply Subtype.ext
    exact one_smul G θ.1
  mul_smul g h θ := by
    apply Subtype.ext
    exact mul_smul g h θ.1

omit [Finite G] in
@[simp]
theorem activePPrime_smul_coe
    {p : ℕ} (g : G)
    (θ : ActivePPrimeIrreducibleCharacter N p) :
    (g • θ : ActivePPrimeIrreducibleCharacter N p).1 =
      g • θ.1 :=
  rfl

/-- Ambient conjugacy orbits of active prime-to-`p` irreducible
characters of `N`. -/
abbrev ActivePPrimeOrbitSpace (p : ℕ) :=
  MulAction.orbitRel.Quotient G
    (ActivePPrimeIrreducibleCharacter N p)

/-- Regard an active prime-to-`p` character as its active Clifford
orbit. -/
def activeOrbitOfPPrime
    {p : ℕ}
    (θ : ActivePPrimeIrreducibleCharacter N p) :
    ActiveOrbit N p :=
  ⟨Quotient.mk'' θ.1.1, θ.2⟩

omit [Finite G] in
@[simp]
theorem activeOrbitOfPPrime_coe
    {p : ℕ}
    (θ : ActivePPrimeIrreducibleCharacter N p) :
    (activeOrbitOfPPrime N θ).1 =
      (Quotient.mk'' θ.1.1 : OrbitSpace N) :=
  rfl

omit [Finite G] in
@[simp]
theorem activeOrbitOfPPrime_smul
    {p : ℕ} (g : G)
    (θ : ActivePPrimeIrreducibleCharacter N p) :
    activeOrbitOfPPrime N (g • θ) =
      activeOrbitOfPPrime N θ := by
  apply Subtype.ext
  exact pPrime_mk_smul_eq_mk N g θ.1

/-- The canonical active prime-to-`p` representative of an active
Clifford orbit. -/
def activePPrimeOut
    {p : ℕ} (q : ActiveOrbit N p) :
    ActivePPrimeIrreducibleCharacter N p :=
  ⟨q.pPrimeOut N, by
    simpa only [IsActivePPrimeCharacter,
      ActiveOrbit.pPrimeOut_coe,
      Quotient.out_eq'] using q.2⟩

@[simp]
theorem activePPrimeOut_coe
    {p : ℕ} (q : ActiveOrbit N p) :
    (activePPrimeOut N q).1 =
        q.pPrimeOut N :=
  rfl

@[simp]
theorem activeOrbitOfPPrime_activePPrimeOut
    {p : ℕ} (q : ActiveOrbit N p) :
    activeOrbitOfPPrime N (activePPrimeOut N q) = q := by
  apply Subtype.ext
  exact Quotient.out_eq' q.1

/-! ## The active orbit quotient -/

omit [Finite G] in
/-- Two active prime-to-`p` characters define the same orbit in their
subtype exactly when their underlying irreducible characters define the
same Clifford orbit. -/
theorem activePPrime_quotient_mk_eq_iff
    {p : ℕ}
    (θ ψ : ActivePPrimeIrreducibleCharacter N p) :
    (Quotient.mk'' θ : ActivePPrimeOrbitSpace N p) =
        Quotient.mk'' ψ ↔
      (Quotient.mk'' θ.1.1 : OrbitSpace N) =
        Quotient.mk'' ψ.1.1 := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := Quotient.exact h
    apply Quotient.sound
    refine ⟨g, ?_⟩
    exact congrArg
      (fun x :
        ActivePPrimeIrreducibleCharacter N p ↦
          (x.1.1 : IrreducibleCharacter N)) hg
  · intro h
    obtain ⟨g, hg⟩ := Quotient.exact h
    apply Quotient.sound
    refine ⟨g, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hg

/-- Active Clifford orbits are exactly ambient conjugacy orbits on the
active prime-to-`p` irreducible characters of `N`. -/
def activeOrbitEquivActivePPrimeOrbitSpace
    (p : ℕ) :
    ActiveOrbit N p ≃ ActivePPrimeOrbitSpace N p where
  toFun q := Quotient.mk'' (activePPrimeOut N q)
  invFun r :=
    Quotient.liftOn' r
      (activeOrbitOfPPrime N)
      (fun θ ψ h ↦ by
        obtain ⟨g, hg⟩ := h
        rw [← hg, activeOrbitOfPPrime_smul])
  left_inv q := by
    exact activeOrbitOfPPrime_activePPrimeOut N q
  right_inv := by
    intro r
    refine Quotient.inductionOn' r ?_
    intro θ
    apply
      (activePPrime_quotient_mk_eq_iff N _ _).mpr
    exact congrArg Subtype.val
      (activeOrbitOfPPrime_activePPrimeOut
        N (activeOrbitOfPPrime N θ))

@[simp]
theorem activeOrbitEquivActivePPrimeOrbitSpace_apply
    {p : ℕ} (q : ActiveOrbit N p) :
    activeOrbitEquivActivePPrimeOrbitSpace N p q =
      Quotient.mk'' (activePPrimeOut N q) :=
  rfl

@[simp]
theorem activeOrbitEquivActivePPrimeOrbitSpace_symm_mk
    {p : ℕ}
    (θ : ActivePPrimeIrreducibleCharacter N p) :
    (activeOrbitEquivActivePPrimeOrbitSpace N p).symm
        (Quotient.mk'' θ) =
      activeOrbitOfPPrime N θ :=
  rfl

/-- Orbit membership for the representative selected by the active
orbit equivalence. -/
theorem activePPrimeOut_mem_orbit
    {p : ℕ} (q : ActiveOrbit N p) :
    activePPrimeOut N q ∈
      (activeOrbitEquivActivePPrimeOrbitSpace N p q).orbit := by
  rw [activeOrbitEquivActivePPrimeOrbitSpace_apply,
    MulAction.orbitRel.Quotient.orbit_mk]
  exact MulAction.mem_orbit_self _

/-! ## The full quotient under the exact activation hypothesis -/

/-- Ambient conjugacy orbits of all prime-to-`p` irreducible characters
of `N`. -/
abbrev PPrimeOrbitSpace (p : ℕ) :=
  MulAction.orbitRel.Quotient G
    (PPrimeIrreducibleCharacter N p)

omit [Finite G] in
/-- Two prime-to-`p` characters define the same orbit in their subtype
exactly when their underlying irreducible characters define the same
Clifford orbit. -/
theorem pPrime_quotient_mk_eq_iff
    {p : ℕ}
    (θ ψ : PPrimeIrreducibleCharacter N p) :
    (Quotient.mk'' θ : PPrimeOrbitSpace N p) =
        Quotient.mk'' ψ ↔
      (Quotient.mk'' θ.1 : OrbitSpace N) =
        Quotient.mk'' ψ.1 := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := Quotient.exact h
    apply Quotient.sound
    refine ⟨g, ?_⟩
    exact congrArg
      (fun x : PPrimeIrreducibleCharacter N p ↦
        (x.1 : IrreducibleCharacter N)) hg
  · intro h
    obtain ⟨g, hg⟩ := Quotient.exact h
    apply Quotient.sound
    refine ⟨g, ?_⟩
    apply Subtype.ext
    exact hg

/-- Under `AllPPrimeOrbitsActive`, active Clifford orbits are the
conjugation-orbit quotient of all prime-to-`p` irreducible characters of
`N`. -/
def activeOrbitEquivPPrimeOrbitSpace
    (p : ℕ) (hactive : AllPPrimeOrbitsActive N p) :
    ActiveOrbit N p ≃ PPrimeOrbitSpace N p where
  toFun q := Quotient.mk'' q.pPrimeOut
  invFun r :=
    Quotient.liftOn' r
      (fun θ ↦
        ⟨(Quotient.mk'' θ.1 : OrbitSpace N),
          hactive θ⟩)
      (fun θ ψ h ↦ by
        apply Subtype.ext
        obtain ⟨g, hg⟩ := h
        rw [← hg]
        exact pPrime_mk_smul_eq_mk N g ψ)
  left_inv q := by
    apply Subtype.ext
    exact Quotient.out_eq' q.1
  right_inv := by
    intro r
    refine Quotient.inductionOn' r ?_
    intro θ
    apply (pPrime_quotient_mk_eq_iff N _ _).mpr
    change
      (Quotient.mk''
          (ActiveOrbit.pPrimeOut N
            (⟨(Quotient.mk'' θ.1 : OrbitSpace N),
              hactive θ⟩ : ActiveOrbit N p)).1 :
        OrbitSpace N) =
          Quotient.mk'' θ.1
    rw [ActiveOrbit.pPrimeOut_coe,
      Quotient.out_eq']

@[simp]
theorem activeOrbitEquivPPrimeOrbitSpace_apply
    {p : ℕ} (hactive : AllPPrimeOrbitsActive N p)
    (q : ActiveOrbit N p) :
    activeOrbitEquivPPrimeOrbitSpace N p hactive q =
      Quotient.mk'' q.pPrimeOut :=
  rfl

@[simp]
theorem activeOrbitEquivPPrimeOrbitSpace_symm_mk
    {p : ℕ} (hactive : AllPPrimeOrbitsActive N p)
    (θ : PPrimeIrreducibleCharacter N p) :
    (activeOrbitEquivPPrimeOrbitSpace N p hactive).symm
        (Quotient.mk'' θ) =
      ⟨(Quotient.mk'' θ.1 : OrbitSpace N),
        hactive θ⟩ :=
  rfl

/-- Under full activation, the chosen representative belongs to the
prime-to-`p` orbit selected by the full quotient equivalence. -/
theorem pPrimeOut_mem_orbit
    {p : ℕ} (hactive : AllPPrimeOrbitsActive N p)
    (q : ActiveOrbit N p) :
    q.pPrimeOut N ∈
      (activeOrbitEquivPPrimeOrbitSpace
        N p hactive q).orbit := by
  rw [activeOrbitEquivPPrimeOrbitSpace_apply,
    MulAction.orbitRel.Quotient.orbit_mk]
  exact MulAction.mem_orbit_self _

end CliffordPartition
end McKayConjecture
