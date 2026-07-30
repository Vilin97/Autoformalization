/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.CliffordEquivalence
import McKayConjecture.Character.GlaubermanCorrespondence
import McKayConjecture.GroupTheory.FrattiniArgument

/-!
# The normal product inside the inertia of an invariant character

Let `K ◁ G`, let `P` be Sylow in `G`, and let `theta` be a `P`-invariant
irreducible character of `K`.  Then `P` is still Sylow in
`I_G(theta)`.  This file identifies the join of the canonical copy of `K`
and that restricted Sylow subgroup with the internal copy of `K P`.

If `K P ◁ G`, the identified normal product is normal in the inertia
group.  The Frattini argument then gives the exact product hypothesis used
by the printed Okuyama--Wajima theorem:

`K_I ∨ N_{I_G(theta)}(P) = I_G(theta)`.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open CliffordEquivalence
open GroupTheory

variable {G : Type} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- The ambient Sylow subgroup restricted to the inertia group of an
invariant normal character. -/
def invariantCharacterInertiaSylow
    (K : Subgroup G) [K.Normal]
    (P : Sylow p G)
    (theta : PInvariantPPrimeIrreducibleCharacter K P p) :
    Sylow p (IrreducibleCharacter.inertia K theta.1.1) :=
  P.subtype theta.2

omit [Finite G] [Fact p.Prime] in
@[simp]
theorem coe_invariantCharacterInertiaSylow
    (K : Subgroup G) [K.Normal]
    (P : Sylow p G)
    (theta : PInvariantPPrimeIrreducibleCharacter K P p) :
    (invariantCharacterInertiaSylow K P theta :
        Subgroup (IrreducibleCharacter.inertia K theta.1.1)) =
      (P : Subgroup G).subgroupOf
        (IrreducibleCharacter.inertia K theta.1.1) :=
  rfl

omit [Finite G] [Fact p.Prime] in
/-- The internal `K P` is exactly the join of the canonical kernel copy
and the restricted Sylow subgroup. -/
theorem invariantCharacterInertia_normalProduct_eq
    (K : Subgroup G) [K.Normal]
    (P : Sylow p G)
    (theta : PInvariantPPrimeIrreducibleCharacter K P p) :
    inertiaNormalCopy K theta.1.1 ⊔
        (invariantCharacterInertiaSylow K P theta :
          Subgroup (IrreducibleCharacter.inertia K theta.1.1)) =
      (K ⊔ (P : Subgroup G)).subgroupOf
        (IrreducibleCharacter.inertia K theta.1.1) := by
  rw [coe_invariantCharacterInertiaSylow,
    ← Subgroup.subgroupOf_sup
      (IrreducibleCharacter.subgroup_le_inertia K theta.1.1)
      theta.2]

omit [Finite G] [Fact p.Prime] in
/-- Normality of `K P` in the original ambient group descends to the
normal product inside the character inertia group. -/
theorem invariantCharacterInertia_normalProduct_normal
    (K : Subgroup G) [K.Normal]
    (P : Sylow p G)
    (theta : PInvariantPPrimeIrreducibleCharacter K P p)
    (hKP : (K ⊔ (P : Subgroup G)).Normal) :
    (inertiaNormalCopy K theta.1.1 ⊔
      (invariantCharacterInertiaSylow K P theta :
        Subgroup
          (IrreducibleCharacter.inertia K theta.1.1))).Normal := by
  rw [invariantCharacterInertia_normalProduct_eq]
  exact hKP.subgroupOf
    (IrreducibleCharacter.inertia K theta.1.1)

/-- Frattini's argument in the exact orientation required by the printed
Okuyama--Wajima product hypothesis. -/
theorem invariantCharacterInertia_sup_normalizer_eq_top
    (K : Subgroup G) [K.Normal]
    (P : Sylow p G)
    (theta : PInvariantPPrimeIrreducibleCharacter K P p)
    (hKP : (K ⊔ (P : Subgroup G)).Normal) :
    inertiaNormalCopy K theta.1.1 ⊔
        Subgroup.normalizer
          ((invariantCharacterInertiaSylow K P theta :
            Subgroup
              (IrreducibleCharacter.inertia K theta.1.1)) :
            Set (IrreducibleCharacter.inertia K theta.1.1)) =
      ⊤ := by
  let Γ := IrreducibleCharacter.inertia K theta.1.1
  let S : Sylow p Γ :=
    invariantCharacterInertiaSylow K P theta
  let L : Subgroup Γ :=
    inertiaNormalCopy K theta.1.1
  have hnormal : (L ⊔ (S : Subgroup Γ)).Normal :=
    invariantCharacterInertia_normalProduct_normal
      K P theta hKP
  letI : (L ⊔ (S : Subgroup Γ)).Normal := hnormal
  have hfrattini :
      Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) ⊔
          (L ⊔ (S : Subgroup Γ)) =
        (⊤ : Subgroup Γ) := by
    exact
      Sylow.normalizer_sup_eq_top' S
        (show
          (S : Subgroup Γ) ≤
            L ⊔ (S : Subgroup Γ) from
          le_sup_right)
  change
    L ⊔ Subgroup.normalizer ((S : Subgroup Γ) : Set Γ) =
      (⊤ : Subgroup Γ)
  apply top_unique
  rw [← hfrattini]
  exact
    sup_le le_sup_right
      (sup_le le_sup_left
        (Subgroup.le_normalizer.trans le_sup_right))

end InductiveMcKay
end McKayConjecture
