/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ClassFunction

/-!
# The pointwise ring of class functions

Complex class functions are closed under pointwise multiplication and
contain the constant functions.  This file equips `ClassFunction G` with
the resulting commutative ring and complex-algebra structures.

The additive and scalar structures were already inherited from the
defining submodule.  All evaluation lemmas are stated explicitly so
pointwise polynomial identities can be proved by extensionality.
-/

noncomputable section

namespace McKayConjecture
namespace ClassFunction

universe u

variable {G : Type u} [Group G]

instance instOne : One (ClassFunction G) where
  one :=
    ⟨fun _ => 1, by
      intro _ _
      rfl⟩

@[simp]
theorem one_apply (g : G) :
    (1 : ClassFunction G) g = 1 :=
  rfl

instance instMul : Mul (ClassFunction G) where
  mul f k :=
    ⟨fun g => f g * k g, by
      intro g h
      change
        f (h * g * h⁻¹) * k (h * g * h⁻¹) =
          f g * k g
      rw [ClassFunction.conj_apply f,
        ClassFunction.conj_apply k]⟩

@[simp]
theorem mul_apply
    (f k : ClassFunction G) (g : G) :
    (f * k) g = f g * k g :=
  rfl

instance instPowNat : Pow (ClassFunction G) ℕ where
  pow f n :=
    ⟨fun g => (f g) ^ n, by
      intro g h
      change (f (h * g * h⁻¹)) ^ n = (f g) ^ n
      rw [ClassFunction.conj_apply f]⟩

@[simp]
theorem pow_apply
    (f : ClassFunction G) (n : ℕ) (g : G) :
    (f ^ n) g = (f g) ^ n :=
  rfl

instance instNatCast : NatCast (ClassFunction G) where
  natCast n :=
    ⟨fun _ => (n : ℂ), by
      intro _ _
      rfl⟩

@[simp]
theorem natCast_apply (n : ℕ) (g : G) :
    (n : ClassFunction G) g = (n : ℂ) :=
  rfl

instance instIntCast : IntCast (ClassFunction G) where
  intCast z :=
    ⟨fun _ => (z : ℂ), by
      intro _ _
      rfl⟩

@[simp]
theorem intCast_apply (z : ℤ) (g : G) :
    (z : ClassFunction G) g = (z : ℂ) :=
  rfl

@[simp]
theorem zero_apply (g : G) :
    (0 : ClassFunction G) g = 0 :=
  rfl

@[simp]
theorem add_apply
    (f k : ClassFunction G) (g : G) :
    (f + k) g = f g + k g :=
  rfl

@[simp]
theorem neg_apply
    (f : ClassFunction G) (g : G) :
    (-f) g = -f g :=
  rfl

@[simp]
theorem sub_apply
    (f k : ClassFunction G) (g : G) :
    (f - k) g = f g - k g :=
  rfl

@[simp]
theorem nsmul_apply
    (n : ℕ) (f : ClassFunction G) (g : G) :
    (n • f) g = n • f g :=
  rfl

@[simp]
theorem zsmul_apply
    (z : ℤ) (f : ClassFunction G) (g : G) :
    (z • f) g = z • f g :=
  rfl

instance instCommRing : CommRing (ClassFunction G) :=
  Function.Injective.commRing
    (fun f : ClassFunction G => (f : G → ℂ))
    Subtype.coe_injective
    rfl rfl
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ => rfl)
    (fun _ => rfl)

instance instAlgebra : Algebra ℂ (ClassFunction G) :=
  Algebra.ofModule
    (fun _ _ _ => by ext; simp [mul_assoc])
    (fun _ _ _ => by
      ext
      simp [mul_left_comm])

@[simp]
theorem algebraMap_apply
    (c : ℂ) (g : G) :
    algebraMap ℂ (ClassFunction G) c g = c := by
  change (c • (1 : ClassFunction G)) g = c
  simp

end ClassFunction
end McKayConjecture
