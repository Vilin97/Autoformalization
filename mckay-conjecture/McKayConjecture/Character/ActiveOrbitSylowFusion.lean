/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ActiveOrbitSylowRepresentative
import McKayConjecture.Character.InternalNormalTransport
import McKayConjecture.GroupTheory.SylowFixedPointFusion

/-!
# Sylow fusion for active prime-to-`p` character orbits

For the ambient conjugation action on `Irr_{p'}(N)`, being fixed by a Sylow
subgroup `P` is equivalent to the familiar containment `P ≤ I_G(θ)`.
Consequently, any subgroup containing `N_G(P)` controls ambient fusion
between such characters.

Applied to the Sylow-adapted representative of an active Clifford orbit,
this shows that every other `P`-fixed prime-to-`p` representative in the same
active orbit is already conjugate to it in the chosen intermediate subgroup.
-/

noncomputable section

namespace McKayConjecture
namespace CliffordPartition

open GroupTheory

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (N : Subgroup G) [N.Normal]

omit [Finite G] [Fact p.Prime] in
/-- A prime-to-`p` character is fixed by `P` exactly when `P` lies in its
ambient inertia subgroup. -/
theorem pPrime_mem_fixedPoints_iff_sylow_le_inertia
    (P : Sylow p G)
    (θ : PPrimeIrreducibleCharacter N p) :
    θ ∈
        MulAction.fixedPoints P
          (PPrimeIrreducibleCharacter N p) ↔
      (P : Subgroup G) ≤
        IrreducibleCharacter.inertia N θ.1 := by
  constructor
  · intro h a ha
    rw [IrreducibleCharacter.mem_inertia_iff]
    have haFix := h ⟨a, ha⟩
    exact congrArg Subtype.val haFix
  · intro h a
    apply Subtype.ext
    exact
      (IrreducibleCharacter.mem_inertia_iff
        N θ.1 (a : G)).mp
          (h a.property)

/-- An intermediate subgroup containing `N_G(P)` controls ambient fusion
between prime-to-`p` characters whose inertia groups contain `P`. -/
theorem pPrime_mem_subgroup_orbit_of_sylow_le_inertia
    (P : Sylow p G)
    (H : Subgroup G)
    (hN : Subgroup.normalizer (P : Set G) ≤ H)
    {θ ψ : PPrimeIrreducibleCharacter N p}
    (hθ :
      (P : Subgroup G) ≤
        IrreducibleCharacter.inertia N θ.1)
    (hψ :
      (P : Subgroup G) ≤
        IrreducibleCharacter.inertia N ψ.1)
    (horbit :
      ψ ∈ MulAction.orbit G θ) :
    ψ ∈ MulAction.orbit H θ :=
  GroupTheory.Sylow.mem_subgroup_orbit_of_fixed_of_normalizer_le
    P H hN
    ((pPrime_mem_fixedPoints_iff_sylow_le_inertia
      N P θ).mpr hθ)
    ((pPrime_mem_fixedPoints_iff_sylow_le_inertia
      N P ψ).mpr hψ)
    horbit

/-- Every `P`-fixed prime-to-`p` representative of an active orbit is
already conjugate under any intermediate subgroup containing `N_G(P)` to
the Sylow-adapted representative of that orbit. -/
theorem ActiveOrbit.pPrime_mem_subgroup_orbit_sylowRepresentative
    (P : Sylow p G)
    (H : Subgroup G)
    (hN : Subgroup.normalizer (P : Set G) ≤ H)
    (q : ActiveOrbit N p)
    (θ : PPrimeIrreducibleCharacter N p)
    (hθ :
      (P : Subgroup G) ≤
        IrreducibleCharacter.inertia N θ.1)
    (hθq : θ.1 ∈ q.1.orbit) :
    θ ∈
      MulAction.orbit H
        (q.pPrimeSylowRepresentative N P) := by
  apply
    pPrime_mem_subgroup_orbit_of_sylow_le_inertia
      N P H hN
      (q.sylow_le_inertia_sylowRepresentative N P)
      hθ
  have hquot :
      (Quotient.mk'' θ.1 : OrbitSpace N) =
        Quotient.mk''
          (q.pPrimeSylowRepresentative N P).1 := by
    calc
      (Quotient.mk'' θ.1 : OrbitSpace N) = q.1 :=
        MulAction.orbitRel.Quotient.mem_orbit.mp hθq
      _ =
          Quotient.mk''
            (q.pPrimeSylowRepresentative N P).1 :=
        (q.mk_sylowRepresentative N P).symm
  obtain ⟨g, hg⟩ := Quotient.exact hquot
  exact
    ⟨g, by
      apply Subtype.ext
      exact hg⟩

/-- Sylow fixed-point fusion survives the identity-on-elements transport
from `N ◁ G` to its internal copy `N.subgroupOf H ◁ H`.

Thus equality of ambient `G`-orbit classes of two `P`-fixed prime-to-`p`
characters implies equality of their transported `H`-orbit classes. -/
theorem internalNormalPPrimeEquiv_quotient_mk_eq_of_sylow_fixed
    (P : Sylow p G)
    (H : Subgroup G)
    (hN : Subgroup.normalizer (P : Set G) ≤ H)
    (hNH : N ≤ H)
    {θ ψ : PPrimeIrreducibleCharacter N p}
    (hθ :
      (P : Subgroup G) ≤
        IrreducibleCharacter.inertia N θ.1)
    (hψ :
      (P : Subgroup G) ≤
        IrreducibleCharacter.inertia N ψ.1)
    (horbit :
      (Quotient.mk'' θ :
          MulAction.orbitRel.Quotient G
            (PPrimeIrreducibleCharacter N p)) =
        Quotient.mk'' ψ) :
    (Quotient.mk''
          (IrreducibleCharacter.internalNormalPPrimeEquiv
            N H hNH p θ) :
        MulAction.orbitRel.Quotient H
          (PPrimeIrreducibleCharacter
            (IrreducibleCharacter.internalNormal N H) p)) =
      Quotient.mk''
        (IrreducibleCharacter.internalNormalPPrimeEquiv
          N H hNH p ψ) := by
  have hG :
      ψ ∈ MulAction.orbit G θ := by
    apply MulAction.mem_orbit_symm.mp
    rw [← MulAction.orbitRel_apply]
    exact Quotient.exact horbit
  have hH :
      ψ ∈ MulAction.orbit H θ :=
    pPrime_mem_subgroup_orbit_of_sylow_le_inertia
      N P H hN hθ hψ hG
  have htransport :
      IrreducibleCharacter.internalNormalPPrimeEquiv
          N H hNH p ψ ∈
        MulAction.orbit H
          (IrreducibleCharacter.internalNormalPPrimeEquiv
            N H hNH p θ) := by
    obtain ⟨h, hh⟩ := hH
    refine ⟨h, ?_⟩
    calc
      h •
          IrreducibleCharacter.internalNormalPPrimeEquiv
            N H hNH p θ =
          IrreducibleCharacter.internalNormalPPrimeEquiv
            N H hNH p (((h : H) : G) • θ) :=
        (IrreducibleCharacter.internalNormalPPrimeEquiv_smul
          N H hNH p h θ).symm
      _ =
          IrreducibleCharacter.internalNormalPPrimeEquiv
            N H hNH p ψ := by
        congr 1
  apply Quotient.sound
  exact MulAction.mem_orbit_symm.mpr htransport

/-- Underlying irreducible-character form of
`internalNormalPPrimeEquiv_quotient_mk_eq_of_sylow_fixed`.

This is convenient when the source orbit equality is stated in the
Clifford orbit space `OrbitSpace N`, as happens for active-orbit
representatives. -/
theorem internalNormalPPrimeEquiv_coe_quotient_mk_eq_of_sylow_fixed
    (P : Sylow p G)
    (H : Subgroup G)
    (hN : Subgroup.normalizer (P : Set G) ≤ H)
    (hNH : N ≤ H)
    {θ ψ : PPrimeIrreducibleCharacter N p}
    (hθ :
      (P : Subgroup G) ≤
        IrreducibleCharacter.inertia N θ.1)
    (hψ :
      (P : Subgroup G) ≤
        IrreducibleCharacter.inertia N ψ.1)
    (horbit :
      (Quotient.mk'' θ.1 : OrbitSpace N) =
        Quotient.mk'' ψ.1) :
    (Quotient.mk''
          (IrreducibleCharacter.internalNormalPPrimeEquiv
            N H hNH p θ).1 :
        MulAction.orbitRel.Quotient H
          (IrreducibleCharacter
            (IrreducibleCharacter.internalNormal N H))) =
      Quotient.mk''
        (IrreducibleCharacter.internalNormalPPrimeEquiv
          N H hNH p ψ).1 := by
  have hpPrimeOrbit :
      (Quotient.mk'' θ :
          MulAction.orbitRel.Quotient G
            (PPrimeIrreducibleCharacter N p)) =
        Quotient.mk'' ψ := by
    obtain ⟨g, hg⟩ := Quotient.exact horbit
    apply Quotient.sound
    refine ⟨g, ?_⟩
    apply Subtype.ext
    exact hg
  have htransport :=
    internalNormalPPrimeEquiv_quotient_mk_eq_of_sylow_fixed
      N P H hN hNH hθ hψ hpPrimeOrbit
  obtain ⟨h, hh⟩ := Quotient.exact htransport
  apply Quotient.sound
  refine ⟨h, ?_⟩
  exact congrArg Subtype.val hh

end CliffordPartition
end McKayConjecture
