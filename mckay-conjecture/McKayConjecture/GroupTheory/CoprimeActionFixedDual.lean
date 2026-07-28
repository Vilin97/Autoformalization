/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.GroupTheory.OrderOfElement

/-!
# Fixed duals for coprime actions on finite commutative groups

Let a finite group `P` act by automorphisms on a finite commutative group
`A`, with `|A|` and `|P|` coprime.  The norm

`N(a) = ∏ g : P, g • a`

lands in `Aᴾ`.  Taking the unique `|P|`-th root in `Aᴾ` gives a
retraction `A → Aᴾ`.  Precomposition with this retraction proves that
restriction is an equivalence

`Hom(A, B)ᴾ ≃ Hom(Aᴾ, B)`

for every commutative target group `B`.

The proof of injectivity uses the unique `|P|`-th root of `a` in `A`.
This avoids any divisibility assumption on the target group.
-/

noncomputable section

open scoped BigOperators

namespace McKayConjecture
namespace GroupTheory

variable (P A : Type*)
variable [Group P] [Fintype P]
variable [CommGroup A] [Fintype A]
variable [MulDistribMulAction P A]

/-- The subgroup of elements of `A` fixed by the whole `P`-action. -/
abbrev actionFixedPoints : Subgroup A :=
  FixedPoints.subgroup P A

/-- The norm for a finite group action on a commutative group. -/
def actionNorm : A →* A where
  toFun a := ∏ g : P, g • a
  map_one' := by simp
  map_mul' a b := by
    simp only [smul_mul', Finset.prod_mul_distrib]

@[simp]
theorem actionNorm_apply (a : A) :
    actionNorm P A a = ∏ g : P, g • a :=
  rfl

/-- The action norm is fixed by every acting element. -/
theorem smul_actionNorm (g : P) (a : A) :
    g • actionNorm P A a = actionNorm P A a :=
  Finset.smul_prod_perm a g

/-- The action norm, with its codomain restricted to the fixed-point
subgroup. -/
def actionNormToFixed :
    A →* actionFixedPoints P A where
  toFun a :=
    ⟨actionNorm P A a,
      fun g ↦ smul_actionNorm P A g a⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (actionNorm P A)
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul (actionNorm P A) a b

@[simp]
theorem actionNormToFixed_coe (a : A) :
    (actionNormToFixed P A a :
      actionFixedPoints P A) =
      ⟨actionNorm P A a,
        fun g ↦ smul_actionNorm P A g a⟩ :=
  rfl

@[simp]
theorem actionNormToFixed_val (a : A) :
    ((actionNormToFixed P A a :
      actionFixedPoints P A) : A) =
      actionNorm P A a :=
  rfl

/-- On a fixed point, the norm is the `|P|`-th power map. -/
theorem actionNormToFixed_apply_fixed
    (a : actionFixedPoints P A) :
    actionNormToFixed P A a =
      a ^ Nat.card P := by
  apply Subtype.ext
  change
    (∏ g : P, g • (a : A)) =
      (a : A) ^ Nat.card P
  calc
    (∏ g : P, g • (a : A)) =
        ∏ _g : P, (a : A) := by
          apply Finset.prod_congr rfl
          intro g _hg
          exact a.property g
    _ = (a : A) ^ Nat.card P := by
          simp

/-- The order of the fixed-point subgroup is also coprime to `|P|`. -/
theorem card_actionFixedPoints_coprime
    (hcoprime :
      (Nat.card A).Coprime (Nat.card P)) :
    (Nat.card (actionFixedPoints P A)).Coprime
      (Nat.card P) :=
  hcoprime.coprime_dvd_left
    (Subgroup.card_subgroup_dvd_card
      (actionFixedPoints P A))

/-- The norm followed by the inverse `|P|`-power map is a retraction onto
the fixed points. -/
def fixedPointRetraction
    (hcoprime :
      (Nat.card A).Coprime (Nat.card P)) :
    A →* actionFixedPoints P A where
  toFun a :=
    (powCoprime
      (card_actionFixedPoints_coprime
        P A hcoprime)).symm
      (actionNormToFixed P A a)
  map_one' := by
    apply Subtype.ext
    simp [actionNormToFixed, actionNorm]
  map_mul' a b := by
    change
      (actionNormToFixed P A (a * b)) ^
          (Nat.card (actionFixedPoints P A)).gcdB
            (Nat.card P) =
        (actionNormToFixed P A a) ^
            (Nat.card (actionFixedPoints P A)).gcdB
              (Nat.card P) *
          (actionNormToFixed P A b) ^
            (Nat.card (actionFixedPoints P A)).gcdB
              (Nat.card P)
    rw [map_mul, mul_zpow]

/-- The fixed-point retraction is the identity on fixed points. -/
@[simp]
theorem fixedPointRetraction_apply_fixed
    (hcoprime :
      (Nat.card A).Coprime (Nat.card P))
    (a : actionFixedPoints P A) :
    fixedPointRetraction P A hcoprime a = a := by
  change
    (powCoprime
      (card_actionFixedPoints_coprime
        P A hcoprime)).symm
      (actionNormToFixed P A a) =
        a
  rw [actionNormToFixed_apply_fixed]
  exact
    (powCoprime
      (card_actionFixedPoints_coprime
        P A hcoprime)).symm_apply_apply a

/-- The fixed-point retraction is invariant under the action. -/
theorem fixedPointRetraction_smul
    (hcoprime :
      (Nat.card A).Coprime (Nat.card P))
    (g : P) (a : A) :
    fixedPointRetraction P A hcoprime (g • a) =
      fixedPointRetraction P A hcoprime a := by
  change
    (powCoprime
      (card_actionFixedPoints_coprime
        P A hcoprime)).symm
      (actionNormToFixed P A (g • a)) =
    (powCoprime
      (card_actionFixedPoints_coprime
        P A hcoprime)).symm
      (actionNormToFixed P A a)
  congr 1
  apply Subtype.ext
  change
    (∏ h : P, h • (g • a)) =
      ∏ h : P, h • a
  simp only [← mul_smul]
  exact
    Fintype.prod_bijective (· * g)
      (Group.mulRight_bijective g)
      (fun h : P ↦ (h * g) • a)
      (fun h : P ↦ h • a)
      (fun _h ↦ rfl)

/-- Multiplicative homomorphisms out of `A` that are invariant under the
`P`-action. -/
abbrev InvariantMonoidHom
    (B : Type*) [CommGroup B] :=
  {f : A →* B // ∀ g : P, ∀ a : A, f (g • a) = f a}

variable {P A}
variable (B : Type*) [CommGroup B]

/-- Restriction identifies invariant homomorphisms from `A` with
homomorphisms from the fixed-point subgroup. -/
def invariantMonoidHomEquivFixedPoints
    (hcoprime :
      (Nat.card A).Coprime (Nat.card P)) :
    InvariantMonoidHom P A B ≃
      (actionFixedPoints P A →* B) where
  toFun f :=
    f.1.comp (actionFixedPoints P A).subtype
  invFun f :=
    ⟨f.comp (fixedPointRetraction P A hcoprime),
      fun g a ↦ by
        simp only [MonoidHom.comp_apply]
        rw [fixedPointRetraction_smul]⟩
  right_inv f := by
    apply MonoidHom.ext
    intro a
    simp only [MonoidHom.comp_apply]
    change
      f (fixedPointRetraction
        P A hcoprime (a : A)) =
        f a
    rw [fixedPointRetraction_apply_fixed]
  left_inv f := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro a
    let b : A :=
      (powCoprime hcoprime).symm a
    have hbpow :
        b ^ Nat.card P = a :=
      (powCoprime hcoprime).apply_symm_apply a
    have hretract :
        fixedPointRetraction P A hcoprime a =
          actionNormToFixed P A b := by
      change
        (powCoprime
          (card_actionFixedPoints_coprime
            P A hcoprime)).symm
          (actionNormToFixed P A a) =
            actionNormToFixed P A b
      rw [← hbpow, map_pow]
      exact
        (powCoprime
          (card_actionFixedPoints_coprime
            P A hcoprime)).symm_apply_apply
          (actionNormToFixed P A b)
    change
      f.1
          ((fixedPointRetraction
            P A hcoprime a :
              actionFixedPoints P A) : A) =
        f.1 a
    rw [hretract, actionNormToFixed_val]
    calc
      f.1 (actionNorm P A b) =
          ∏ g : P, f.1 (g • b) := by
            rw [actionNorm_apply, map_prod]
      _ = ∏ _g : P, f.1 b := by
            apply Finset.prod_congr rfl
            intro g _hg
            exact f.2 g b
      _ = (f.1 b) ^ Nat.card P := by
            simp
      _ = f.1 (b ^ Nat.card P) := by
            rw [map_pow]
      _ = f.1 a := by
            rw [hbpow]

@[simp]
theorem invariantMonoidHomEquivFixedPoints_apply
    (hcoprime :
      (Nat.card A).Coprime (Nat.card P))
    (f : InvariantMonoidHom P A B) :
    invariantMonoidHomEquivFixedPoints
        B hcoprime f =
      f.1.comp (actionFixedPoints P A).subtype :=
  rfl

end GroupTheory
end McKayConjecture
