/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import McKayConjecture.Character.GeneralizedCharacter

/-!
# Restriction to elementary direct products

A `p`-elementary group is the direct product of a cyclic group of order
prime to `p` and a `p`-group.  We package such a decomposition internally,
construct its multiplication equivalence, and define restriction of class
functions all the way to the displayed direct product.

Every generalized character remains generalized after this restriction.
Brauer's characterization is the difficult converse: generalizedness of all
elementary restrictions forces generalizedness of the ambient class
function.  That converse is deliberately not assumed in this file.
-/

noncomputable section

namespace McKayConjecture

universe u

/-- Internal data exhibiting a finite group as a `p`-elementary direct
product. -/
structure PElementaryDecomposition
    (p : ℕ) (E : Type u) [Group E] where
  /-- The cyclic prime-to-`p` factor. -/
  cyclicPart : Subgroup E
  /-- The `p`-group factor. -/
  pPart : Subgroup E
  /-- The first factor is cyclic. -/
  cyclic : IsCyclic cyclicPart
  /-- The first factor has order prime to `p`. -/
  cyclicPart_coprime : p.Coprime (Nat.card cyclicPart)
  /-- The second factor is a `p`-group. -/
  isPGroup : IsPGroup p pPart
  /-- The cyclic factor is normal. -/
  cyclicPart_normal : cyclicPart.Normal
  /-- The `p`-factor is normal. -/
  pPart_normal : pPart.Normal
  /-- Multiplication gives a unique factorization of every element. -/
  complementary : cyclicPart.IsComplement' pPart

namespace PElementaryDecomposition

variable {p : ℕ} {E : Type u} [Group E]

/-- Elements of the two factors commute. -/
theorem commute
    (D : PElementaryDecomposition p E)
    (c : D.cyclicPart) (x : D.pPart) :
    Commute (c : E) (x : E) :=
  Subgroup.commute_of_normal_of_disjoint
    D.cyclicPart D.pPart
    D.cyclicPart_normal D.pPart_normal
    D.complementary.disjoint
    c x c.property x.property

/-- Multiplication from the displayed direct product to the elementary
group. -/
def multiplicationHom
    (D : PElementaryDecomposition p E) :
    D.cyclicPart × D.pPart →* E where
  toFun z := (z.1 : E) * (z.2 : E)
  map_one' := by simp
  map_mul' x y := by
    change
      ((x.1 : E) * (y.1 : E)) *
          ((x.2 : E) * (y.2 : E)) =
        ((x.1 : E) * (x.2 : E)) *
          ((y.1 : E) * (y.2 : E))
    rw [mul_assoc, ← mul_assoc (y.1 : E)]
    rw [(D.commute y.1 x.2).eq]
    simp only [mul_assoc]

@[simp]
theorem multiplicationHom_apply
    (D : PElementaryDecomposition p E)
    (z : D.cyclicPart × D.pPart) :
    D.multiplicationHom z = (z.1 : E) * (z.2 : E) :=
  rfl

/-- A `p`-elementary decomposition identifies the group with the direct
product of its two displayed factors. -/
def multiplicationEquiv
    (D : PElementaryDecomposition p E) :
    D.cyclicPart × D.pPart ≃* E :=
  MulEquiv.ofBijective D.multiplicationHom D.complementary

@[simp]
theorem multiplicationEquiv_apply
    (D : PElementaryDecomposition p E)
    (z : D.cyclicPart × D.pPart) :
    D.multiplicationEquiv z =
      (z.1 : E) * (z.2 : E) :=
  rfl

/-- The homomorphism from an elementary direct-product presentation of a
subgroup into the ambient group. -/
def ambientHom
    {G : Type u} [Group G]
    (S : Subgroup G)
    (D : PElementaryDecomposition p S) :
    D.cyclicPart × D.pPart →* G :=
  S.subtype.comp D.multiplicationEquiv.toMonoidHom

@[simp]
theorem ambientHom_apply
    {G : Type u} [Group G]
    (S : Subgroup G)
    (D : PElementaryDecomposition p S)
    (z : D.cyclicPart × D.pPart) :
    D.ambientHom S z =
      (((z.1 : S) * (z.2 : S) : S) : G) :=
  rfl

end PElementaryDecomposition

namespace ClassFunction

variable {p : ℕ} {G : Type} [Group G]

/-- Restrict a class function on `G` to the direct-product coordinates of a
displayed `p`-elementary subgroup. -/
def restrictToPElementaryProduct
    (S : Subgroup G)
    (D : PElementaryDecomposition p S) :
    ClassFunction G →ₗ[ℂ]
      ClassFunction (D.cyclicPart × D.pPart) :=
  comapLinearMap (D.ambientHom S)

@[simp]
theorem restrictToPElementaryProduct_apply
    (S : Subgroup G)
    (D : PElementaryDecomposition p S)
    (f : ClassFunction G)
    (z : D.cyclicPart × D.pPart) :
    restrictToPElementaryProduct S D f z =
      f (((z.1 : S) * (z.2 : S) : S) : G) :=
  rfl

/-- Restriction to elementary product coordinates factors through ordinary
subgroup restriction and the multiplication equivalence. -/
theorem restrictToPElementaryProduct_eq_comap_subgroup
    (S : Subgroup G)
    (D : PElementaryDecomposition p S)
    (f : ClassFunction G) :
    restrictToPElementaryProduct S D f =
      comapLinearMap D.multiplicationEquiv.toMonoidHom
        (comapLinearMap S.subtype f) := by
  ext z
  rfl

/-- Generalized characters restrict to generalized characters on every
displayed elementary direct product. -/
theorem IsGeneralizedCharacter.restrictToPElementaryProduct
    [Finite G]
    (S : Subgroup G)
    (D : PElementaryDecomposition p S)
    {f : ClassFunction G}
    (hf : IsGeneralizedCharacter f) :
    IsGeneralizedCharacter
      (restrictToPElementaryProduct S D f) :=
  hf.comap (D.ambientHom S)

end ClassFunction
end McKayConjecture
