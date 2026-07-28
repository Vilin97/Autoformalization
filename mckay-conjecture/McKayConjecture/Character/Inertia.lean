/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import McKayConjecture.Character.Automorphism
import McKayConjecture.Character.ClassFunction

/-!
# Conjugation and inertia of irreducible characters

For a normal subgroup `N ⫳ G`, conjugation gives an action of `G` on
`Irr(N)`.  The stabilizer of a character is its inertia subgroup.  This file
sets up that API and proves the basic inclusion `N ≤ I_G(θ)`.
-/

noncomputable section

universe u

namespace McKayConjecture

variable {G : Type u} [Group G]

namespace IrreducibleCharacter

/-- Conjugation by the ambient group acts on irreducible characters of a
normal subgroup.  Our left-action convention is
`(g • θ)(n) = θ(g⁻¹ n g)`. -/
instance normalSubgroupMulAction (N : Subgroup G) [N.Normal] :
    MulAction G (IrreducibleCharacter N) :=
  MulAction.compHom _ (MulAut.conjNormal (H := N))

/-- The conjugate of an irreducible character of a normal subgroup. -/
abbrev conjBy (N : Subgroup G) [N.Normal] (g : G)
    (θ : IrreducibleCharacter N) : IrreducibleCharacter N :=
  g • θ

@[simp]
theorem conjBy_values (N : Subgroup G) [N.Normal] (g : G)
    (θ : IrreducibleCharacter N) (n : N) :
    (conjBy N g θ).values n =
      θ.values ((MulAut.conjNormal g).symm n) :=
  rfl

@[simp]
theorem conjBy_degree (N : Subgroup G) [N.Normal] (g : G)
    (θ : IrreducibleCharacter N) :
    (conjBy N g θ).degree = θ.degree :=
  rfl

@[simp]
theorem conjBy_one (N : Subgroup G) [N.Normal]
    (θ : IrreducibleCharacter N) :
    conjBy N 1 θ = θ :=
  one_smul G θ

@[simp]
theorem conjBy_mul (N : Subgroup G) [N.Normal] (g h : G)
    (θ : IrreducibleCharacter N) :
    conjBy N (g * h) θ = conjBy N g (conjBy N h θ) :=
  mul_smul g h θ

/-- The inertia subgroup `I_G(θ)` of an irreducible character of a normal
subgroup. -/
abbrev inertia (N : Subgroup G) [N.Normal]
    (θ : IrreducibleCharacter N) : Subgroup G :=
  MulAction.stabilizer G θ

@[simp]
theorem mem_inertia_iff (N : Subgroup G) [N.Normal]
    (θ : IrreducibleCharacter N) (g : G) :
    g ∈ inertia N θ ↔ conjBy N g θ = θ :=
  MulAction.mem_stabilizer_iff

/-- Every element of the normal subgroup fixes each of its characters under
inner conjugation, so `N ≤ I_G(θ)`. -/
theorem subgroup_le_inertia (N : Subgroup G) [N.Normal]
    (θ : IrreducibleCharacter N) :
    N ≤ inertia N θ := by
  intro n hn
  rw [mem_inertia_iff]
  apply IrreducibleCharacter.ext
  funext x
  rw [conjBy_values]
  let nN : N := ⟨n, hn⟩
  have hx :
      (MulAut.conjNormal n).symm x =
        nN⁻¹ * x * (nN⁻¹)⁻¹ := by
    apply Subtype.ext
    simp only [MulAut.conjNormal_symm_apply, inv_inv]
    rfl
  rw [hx]
  exact ClassFunction.conj_apply θ.toClassFunction x nN⁻¹

/-- The ambient conjugacy orbit of an irreducible character of `N`. -/
abbrev conjByOrbit (N : Subgroup G) [N.Normal]
    (θ : IrreducibleCharacter N) :=
  MulAction.orbit G θ

/-- Orbit--stabilizer identifies the conjugacy orbit with the quotient by the
inertia subgroup. -/
def conjByOrbitEquivQuotientInertia (N : Subgroup G) [N.Normal]
    (θ : IrreducibleCharacter N) :
    conjByOrbit N θ ≃ G ⧸ inertia N θ :=
  MulAction.orbitEquivQuotientStabilizer G θ

@[simp]
theorem conjByOrbitEquivQuotientInertia_symm_apply
    (N : Subgroup G) [N.Normal] (θ : IrreducibleCharacter N) (g : G) :
    ((conjByOrbitEquivQuotientInertia N θ).symm
      (g : G ⧸ inertia N θ) : IrreducibleCharacter N) =
        conjBy N g θ :=
  MulAction.orbitEquivQuotientStabilizer_symm_apply G θ g

/-- The inertia quotient `I_G(θ)/N`, defined using the canonical normality of
`N` inside its inertia subgroup. -/
abbrev inertiaQuotient (N : Subgroup G) [N.Normal]
    (θ : IrreducibleCharacter N) :=
  inertia N θ ⧸ N.subgroupOf (inertia N θ)

end IrreducibleCharacter

/-- The conjugation action preserves the `p'`-degree subtype. -/
instance normalSubgroupPPrimeMulAction (N : Subgroup G) [N.Normal] (p : ℕ) :
    MulAction G (PPrimeIrreducibleCharacter N p) :=
  MulAction.compHom _ (MulAut.conjNormal (H := N))

end McKayConjecture
