/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixSchurThreeNormalizerSemidirect

/-!
# Computable coordinates for the three-normalizer of `6.A₆`

The Heisenberg factor is written as triples over `ZMod 3`, with

`(z,x,y) * (z',x',y') = (z + z' + y*x', x + x', y + y')`.

This is the collected multiplication law already proved for the explicit
Sylow subgroup in the Schur presentation.  Giving the factor a genuinely
computable finite model makes exhaustive conjugacy-class and character-row
certificates possible without evaluating quotient-group normal forms.
-/

namespace McKayConjecture
namespace GroupTheory

/-- Computable coordinates for the exponent-three Heisenberg group. -/
@[ext]
structure AlternatingSixThreeHeisenbergCoordinates where
  z : ZMod 3
  x : ZMod 3
  y : ZMod 3
deriving DecidableEq, Fintype

namespace AlternatingSixThreeHeisenbergCoordinates

instance : One AlternatingSixThreeHeisenbergCoordinates :=
  ⟨⟨0, 0, 0⟩⟩

instance : Mul AlternatingSixThreeHeisenbergCoordinates where
  mul q r :=
    ⟨q.z + r.z + q.y * r.x,
      q.x + r.x,
      q.y + r.y⟩

instance : Inv AlternatingSixThreeHeisenbergCoordinates where
  inv q :=
    ⟨-q.z + q.y * q.x, -q.x, -q.y⟩

instance : Group AlternatingSixThreeHeisenbergCoordinates where
  mul_assoc := by
    intro q r s
    ext
    · change
        (q.z + r.z + q.y * r.x) + s.z +
            (q.y + r.y) * s.x =
          q.z + (r.z + s.z + r.y * s.x) +
            q.y * (r.x + s.x)
      rw [add_mul, mul_add]
      abel
    · exact add_assoc q.x r.x s.x
    · exact add_assoc q.y r.y s.y
  one_mul := by
    intro q
    ext
    · change 0 + q.z + 0 * q.x = q.z
      rw [zero_add, zero_mul, add_zero]
    · exact zero_add q.x
    · exact zero_add q.y
  mul_one := by
    intro q
    ext
    · change q.z + 0 + q.y * 0 = q.z
      rw [add_zero, mul_zero, add_zero]
    · exact add_zero q.x
    · exact add_zero q.y
  inv_mul_cancel := by
    intro q
    ext
    · change
        (-q.z + q.y * q.x) + q.z + (-q.y) * q.x = 0
      rw [neg_mul]
      abel
    · exact neg_add_cancel q.x
    · exact neg_add_cancel q.y

end AlternatingSixThreeHeisenbergCoordinates

/-- Coordinate triples are the ordinary product of three copies of
`ZMod 3` as a finite set. -/
def alternatingSixThreeHeisenbergCoordinatesEquivProd :
    AlternatingSixThreeHeisenbergCoordinates ≃
      ZMod 3 × ZMod 3 × ZMod 3 where
  toFun q := (q.z, q.x, q.y)
  invFun q := ⟨q.1, q.2.1, q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem natCard_alternatingSixThreeHeisenbergCoordinates :
    Nat.card AlternatingSixThreeHeisenbergCoordinates = 27 := by
  calc
    Nat.card AlternatingSixThreeHeisenbergCoordinates =
        Nat.card (ZMod 3 × ZMod 3 × ZMod 3) :=
      Nat.card_congr
        alternatingSixThreeHeisenbergCoordinatesEquivProd
    _ = 27 := by
      rw [Nat.card_prod, Nat.card_prod]
      norm_num

/-- Forget the ring presentation of the coordinates and recover the
`Fin 3` coordinates used in the Schur-cover normal-form theorem. -/
def alternatingSixThreeHeisenbergCoordinatesToSchurCoordinates :
    AlternatingSixThreeHeisenbergCoordinates ≃
      AlternatingSixSchurSylowThreeCoordinates where
  toFun q := ⟨q.z, q.x, q.y⟩
  invFun q := ⟨q.z, q.x, q.y⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Evaluate a computable coordinate triple in the explicit Schur-cover
Heisenberg subgroup. -/
noncomputable def alternatingSixThreeHeisenbergCoordinatesToSchurSylow :
    AlternatingSixThreeHeisenbergCoordinates →
      alternatingSixSchurSylowThreeSubgroup :=
  alternatingSixSchurSylowThreeCoordinateEquiv ∘
    alternatingSixThreeHeisenbergCoordinatesToSchurCoordinates

theorem alternatingSixThreeHeisenbergCoordinatesToSchurSylow_mul
    (q r : AlternatingSixThreeHeisenbergCoordinates) :
    alternatingSixThreeHeisenbergCoordinatesToSchurSylow (q * r) =
      alternatingSixThreeHeisenbergCoordinatesToSchurSylow q *
        alternatingSixThreeHeisenbergCoordinatesToSchurSylow r := by
  apply Subtype.ext
  change
    alternatingSixSchurSylowThreeZ ^
          (q.z + r.z + q.y * r.x).val *
        alternatingSixSchurSylowThreeX ^ (q.x + r.x).val *
          alternatingSixSchurSylowThreeY ^ (q.y + r.y).val =
      (alternatingSixSchurSylowThreeZ ^ q.z.val *
          alternatingSixSchurSylowThreeX ^ q.x.val *
            alternatingSixSchurSylowThreeY ^ q.y.val) *
        (alternatingSixSchurSylowThreeZ ^ r.z.val *
          alternatingSixSchurSylowThreeX ^ r.x.val *
            alternatingSixSchurSylowThreeY ^ r.y.val)
  rw [
    show
      (q.z + r.z + q.y * r.x).val =
        (q.z.val + r.z.val + q.y.val * r.x.val) % 3 by
          simp only [ZMod.val_add, ZMod.val_mul]
          omega,
    show
      (q.x + r.x).val =
        (q.x.val + r.x.val) % 3 by
          exact ZMod.val_add q.x r.x,
    show
      (q.y + r.y).val =
        (q.y.val + r.y.val) % 3 by
          exact ZMod.val_add q.y r.y,
    ← pow_eq_pow_mod
      (q.z.val + r.z.val + q.y.val * r.x.val)
      alternatingSixSchurSylowThreeZ_cube,
    ← pow_eq_pow_mod
      (q.x.val + r.x.val)
      alternatingSixSchurSylowThreeX_cube,
    ← pow_eq_pow_mod
      (q.y.val + r.y.val)
      alternatingSixSchurSylowThreeY_cube
  ]
  exact
    (alternatingSixSchurSylowThree_collect
      q.z.val q.x.val q.y.val
      r.z.val r.x.val r.y.val).symm

/-- The explicit Heisenberg Sylow subgroup is the computable coordinate
group above, as a group rather than merely as a finite set. -/
noncomputable def alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow :
    AlternatingSixThreeHeisenbergCoordinates ≃*
      alternatingSixSchurSylowThreeSubgroup where
  toEquiv :=
    alternatingSixThreeHeisenbergCoordinatesToSchurCoordinates.trans
      alternatingSixSchurSylowThreeCoordinateEquiv
  map_mul' :=
    alternatingSixThreeHeisenbergCoordinatesToSchurSylow_mul

@[simp]
theorem alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow_Z :
    alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow
        ⟨1, 0, 0⟩ =
      alternatingSixSchurSylowThreeZElement := by
  apply Subtype.ext
  change
    alternatingSixSchurSylowThreeZ ^ 1 *
        alternatingSixSchurSylowThreeX ^ 0 *
          alternatingSixSchurSylowThreeY ^ 0 =
      alternatingSixSchurSylowThreeZ
  simp [
    alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow,
    alternatingSixThreeHeisenbergCoordinatesToSchurCoordinates,
    alternatingSixSchurSylowThreeCoordinateEquiv,
    alternatingSixSchurSylowThreeParameterizedElement,
    alternatingSixSchurSylowThreeZElement
  ]

@[simp]
theorem alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow_X :
    alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow
        ⟨0, 1, 0⟩ =
      alternatingSixSchurSylowThreeXElement := by
  apply Subtype.ext
  change
    alternatingSixSchurSylowThreeZ ^ 0 *
        alternatingSixSchurSylowThreeX ^ 1 *
          alternatingSixSchurSylowThreeY ^ 0 =
      alternatingSixSchurSylowThreeX
  simp [
    alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow,
    alternatingSixThreeHeisenbergCoordinatesToSchurCoordinates,
    alternatingSixSchurSylowThreeCoordinateEquiv,
    alternatingSixSchurSylowThreeParameterizedElement,
    alternatingSixSchurSylowThreeXElement
  ]

@[simp]
theorem alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow_Y :
    alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow
        ⟨0, 0, 1⟩ =
      alternatingSixSchurSylowThreeYElement := by
  apply Subtype.ext
  change
    alternatingSixSchurSylowThreeZ ^ 0 *
        alternatingSixSchurSylowThreeX ^ 0 *
          alternatingSixSchurSylowThreeY ^ 1 =
      alternatingSixSchurSylowThreeY
  simp [
    alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow,
    alternatingSixThreeHeisenbergCoordinatesToSchurCoordinates,
    alternatingSixSchurSylowThreeCoordinateEquiv,
    alternatingSixSchurSylowThreeParameterizedElement,
    alternatingSixSchurSylowThreeYElement
  ]

/-! ### The computable order-four action -/

/-- The central coordinate generator. -/
def alternatingSixThreeHeisenbergCoordinateZ :
    AlternatingSixThreeHeisenbergCoordinates :=
  ⟨1, 0, 0⟩

/-- The first noncentral coordinate generator. -/
def alternatingSixThreeHeisenbergCoordinateX :
    AlternatingSixThreeHeisenbergCoordinates :=
  ⟨0, 1, 0⟩

/-- The second noncentral coordinate generator. -/
def alternatingSixThreeHeisenbergCoordinateY :
    AlternatingSixThreeHeisenbergCoordinates :=
  ⟨0, 0, 1⟩

@[simp]
theorem
    alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow_coordinateZ :
    alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow
        alternatingSixThreeHeisenbergCoordinateZ =
      alternatingSixSchurSylowThreeZElement :=
  alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow_Z

@[simp]
theorem
    alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow_coordinateX :
    alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow
        alternatingSixThreeHeisenbergCoordinateX =
      alternatingSixSchurSylowThreeXElement :=
  alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow_X

@[simp]
theorem
    alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow_coordinateY :
    alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow
        alternatingSixThreeHeisenbergCoordinateY =
      alternatingSixSchurSylowThreeYElement :=
  alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow_Y

/-- Every coordinate triple is its collected `Z^z X^x Y^y` word. -/
theorem alternatingSixThreeHeisenbergCoordinate_decompose
    (q : AlternatingSixThreeHeisenbergCoordinates) :
    q =
      alternatingSixThreeHeisenbergCoordinateZ ^ q.z.val *
        alternatingSixThreeHeisenbergCoordinateX ^ q.x.val *
          alternatingSixThreeHeisenbergCoordinateY ^ q.y.val := by
  rcases q with ⟨z, x, y⟩
  fin_cases z <;> fin_cases x <;> fin_cases y <;> decide

/-- The automorphism induced by the chosen order-eight normalizer lift.
It fixes the central coordinate and sends the standard generators by
`X ↦ ZY`, `Y ↦ X²`. -/
def alternatingSixThreeHeisenbergCoordinateGenerator :
    MulAut AlternatingSixThreeHeisenbergCoordinates where
  toFun q :=
    ⟨q.z + q.x - q.x * q.y, -q.y, q.x⟩
  invFun q :=
    ⟨q.z - q.y - q.x * q.y, q.y, -q.x⟩
  left_inv := by
    intro q
    ext
    · change
        (q.z + q.x - q.x * q.y) - q.x -
            (-q.y) * q.x =
          q.z
      rw [neg_mul, mul_comm q.y q.x]
      abel
    · rfl
    · exact neg_neg q.y
  right_inv := by
    intro q
    ext
    · change
        (q.z - q.y - q.x * q.y) + q.y -
            q.y * (-q.x) =
          q.z
      rw [mul_neg, mul_comm q.y q.x]
      abel
    · exact neg_neg q.x
    · rfl
  map_mul' := by
    intro q r
    ext
    · change
        q.z + r.z + q.y * r.x + (q.x + r.x) -
              (q.x + r.x) * (q.y + r.y) =
          (q.z + q.x - q.x * q.y) +
              (r.z + r.x - r.x * r.y) +
            q.x * (-r.y)
      rw [add_mul, mul_add, mul_add, mul_neg,
        mul_comm q.y r.x]
      abel
    · exact neg_add q.y r.y
    · rfl

@[simp]
theorem alternatingSixThreeHeisenbergCoordinateGenerator_Z :
    alternatingSixThreeHeisenbergCoordinateGenerator
        alternatingSixThreeHeisenbergCoordinateZ =
      alternatingSixThreeHeisenbergCoordinateZ := by
  rfl

@[simp]
theorem alternatingSixThreeHeisenbergCoordinateGenerator_X :
    alternatingSixThreeHeisenbergCoordinateGenerator
        alternatingSixThreeHeisenbergCoordinateX =
      alternatingSixThreeHeisenbergCoordinateZ *
        alternatingSixThreeHeisenbergCoordinateY := by
  decide

@[simp]
theorem alternatingSixThreeHeisenbergCoordinateGenerator_Y :
    alternatingSixThreeHeisenbergCoordinateGenerator
        alternatingSixThreeHeisenbergCoordinateY =
      alternatingSixThreeHeisenbergCoordinateX ^ 2 := by
  decide

/-- On the generator of `C₈`, the coordinate action is exactly the
Schur-normalizer action under the Heisenberg factor equivalence. -/
theorem
    alternatingSixThreeHeisenbergCoordinateGenerator_intertwinesSchur :
    alternatingSixThreeHeisenbergCoordinateGenerator.trans
        alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow =
      alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow.trans
        (alternatingSixSchurThreeCyclicEightAction
          (Multiplicative.ofAdd 1)) := by
  apply DFunLike.ext
  intro q
  let word :=
    alternatingSixThreeHeisenbergCoordinateZ ^ q.z.val *
      alternatingSixThreeHeisenbergCoordinateX ^ q.x.val *
        alternatingSixThreeHeisenbergCoordinateY ^ q.y.val
  have hq : q = word :=
    alternatingSixThreeHeisenbergCoordinate_decompose q
  calc
    alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow
        (alternatingSixThreeHeisenbergCoordinateGenerator q) =
      alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow
        (alternatingSixThreeHeisenbergCoordinateGenerator word) :=
      congrArg
        (fun r =>
          alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow
            (alternatingSixThreeHeisenbergCoordinateGenerator r))
        hq
    _ =
      alternatingSixSchurThreeCyclicEightAction
          (Multiplicative.ofAdd 1)
        (alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow word) := by
      simp only [
        word,
        map_mul,
        map_pow,
        alternatingSixThreeHeisenbergCoordinateGenerator_Z,
        alternatingSixThreeHeisenbergCoordinateGenerator_X,
        alternatingSixThreeHeisenbergCoordinateGenerator_Y,
        alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow_coordinateZ,
        alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow_coordinateX,
        alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow_coordinateY,
        alternatingSixSchurThreeCyclicEightAction_generator_Z,
        alternatingSixSchurThreeCyclicEightAction_generator_X,
        alternatingSixSchurThreeCyclicEightAction_generator_Y
      ]
    _ =
      alternatingSixSchurThreeCyclicEightAction
          (Multiplicative.ofAdd 1)
        (alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow q) :=
      congrArg
        (fun r =>
          alternatingSixSchurThreeCyclicEightAction
              (Multiplicative.ofAdd 1)
            (alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow r))
        hq.symm

theorem alternatingSixThreeHeisenbergCoordinateGenerator_pow_four :
    alternatingSixThreeHeisenbergCoordinateGenerator ^ 4 = 1 := by
  apply DFunLike.ext
  rintro ⟨z, x, y⟩
  fin_cases z <;> fin_cases x <;> fin_cases y <;> decide

theorem alternatingSixThreeHeisenbergCoordinateGenerator_pow_eight :
    alternatingSixThreeHeisenbergCoordinateGenerator ^ 8 = 1 := by
  rw [show 8 = 4 + 4 by norm_num, pow_add,
    alternatingSixThreeHeisenbergCoordinateGenerator_pow_four,
    one_mul]

/-- The `C₈` action on the computable Heisenberg coordinates.  It factors
through the quotient `C₄`, while the kernel element of order two remains
visible in the semidirect product. -/
def alternatingSixThreeHeisenbergCoordinateAction :
    AlternatingSixThreeCyclicEight →*
      MulAut AlternatingSixThreeHeisenbergCoordinates where
  toFun c :=
    QuaternionGroup.zmodPower
      alternatingSixThreeHeisenbergCoordinateGenerator
      alternatingSixThreeHeisenbergCoordinateGenerator_pow_eight
      c.toAdd
  map_one' :=
    QuaternionGroup.zmodPower_zero
      alternatingSixThreeHeisenbergCoordinateGenerator
      alternatingSixThreeHeisenbergCoordinateGenerator_pow_eight
  map_mul' c d :=
    QuaternionGroup.zmodPower_add
      alternatingSixThreeHeisenbergCoordinateGenerator
      alternatingSixThreeHeisenbergCoordinateGenerator_pow_eight
      c.toAdd d.toAdd

/-- Conjugating the coordinate generator across the Heisenberg
equivalence gives the already proved Schur action generator. -/
theorem
    alternatingSixThreeHeisenbergCoordinateGenerator_transport :
    MulAut.congr
        alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow
        alternatingSixThreeHeisenbergCoordinateGenerator =
      alternatingSixSchurThreeCyclicEightAction
        (Multiplicative.ofAdd 1) := by
  calc
    MulAut.congr
        alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow
        alternatingSixThreeHeisenbergCoordinateGenerator =
      alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow.symm.trans
        (alternatingSixThreeHeisenbergCoordinateGenerator.trans
          alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow) :=
      rfl
    _ =
      alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow.symm.trans
        (alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow.trans
          (alternatingSixSchurThreeCyclicEightAction
            (Multiplicative.ofAdd 1))) := by
      rw [
        alternatingSixThreeHeisenbergCoordinateGenerator_intertwinesSchur
      ]
    _ =
      alternatingSixSchurThreeCyclicEightAction
        (Multiplicative.ofAdd 1) := by
      apply MulEquiv.ext
      intro g
      simp

/-- The full coordinate action, not only its generator, transports to the
Schur action. -/
theorem alternatingSixThreeHeisenbergCoordinateAction_transport :
    (MulAut.congr
        alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow).toMonoidHom.comp
        alternatingSixThreeHeisenbergCoordinateAction =
      alternatingSixSchurThreeCyclicEightAction := by
  apply MonoidHom.ext
  have hgenerator :
      ((MulAut.congr
          alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow).toMonoidHom.comp
          alternatingSixThreeHeisenbergCoordinateAction)
          (Multiplicative.ofAdd (1 : ZMod 8)) =
        alternatingSixSchurThreeCyclicEightAction
          (Multiplicative.ofAdd (1 : ZMod 8)) := by
    change
      MulAut.congr
          alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow
          (QuaternionGroup.zmodPower
            alternatingSixThreeHeisenbergCoordinateGenerator
            alternatingSixThreeHeisenbergCoordinateGenerator_pow_eight
            (1 : ZMod 8)) =
        alternatingSixSchurThreeCyclicEightAction
          (Multiplicative.ofAdd (1 : ZMod 8))
    have hpower :
        QuaternionGroup.zmodPower
            alternatingSixThreeHeisenbergCoordinateGenerator
            alternatingSixThreeHeisenbergCoordinateGenerator_pow_eight
            (1 : ZMod 8) =
          alternatingSixThreeHeisenbergCoordinateGenerator := by
      simpa using
        (QuaternionGroup.zmodPower_natCast
          alternatingSixThreeHeisenbergCoordinateGenerator
          alternatingSixThreeHeisenbergCoordinateGenerator_pow_eight
          1)
    rw [hpower]
    exact
      alternatingSixThreeHeisenbergCoordinateGenerator_transport
  intro c
  obtain ⟨n, hn⟩ :=
    ZMod.intCast_surjective (Multiplicative.toAdd c)
  have hc :
      c = Multiplicative.ofAdd (n : ZMod 8) := by
    apply Multiplicative.toAdd.injective
    exact hn.symm
  subst c
  rw [show
      Multiplicative.ofAdd (n : ZMod 8) =
        (Multiplicative.ofAdd (1 : ZMod 8)) ^ n by
        apply Multiplicative.toAdd.injective
        simp]
  rw [map_zpow, map_zpow,
    hgenerator]

/-- Pointwise form of the transported-action identity, in the exact
orientation required by `SemidirectProduct.congr`. -/
theorem alternatingSixThreeHeisenbergCoordinateAction_intertwinesSchur
    (c : AlternatingSixThreeCyclicEight) :
    (alternatingSixThreeHeisenbergCoordinateAction c).trans
        alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow =
      alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow.trans
        (alternatingSixSchurThreeCyclicEightAction c) := by
  have hc :=
    DFunLike.congr_fun
      alternatingSixThreeHeisenbergCoordinateAction_transport c
  apply MulEquiv.ext
  intro g
  have hg :=
    DFunLike.congr_fun hc
      (alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow g)
  simpa [MulAut.congr, MulEquiv.trans_apply] using hg

/-- A completely computable 216-element coordinate model of the exact
three-normalizer. -/
abbrev AlternatingSixThreeNormalizerCoordinates :=
  AlternatingSixThreeHeisenbergCoordinates ⋊[
    alternatingSixThreeHeisenbergCoordinateAction]
      AlternatingSixThreeCyclicEight

instance alternatingSixThreeNormalizerCoordinatesFintype :
    Fintype AlternatingSixThreeNormalizerCoordinates :=
  Fintype.ofEquiv
    (AlternatingSixThreeHeisenbergCoordinates ×
      AlternatingSixThreeCyclicEight)
    SemidirectProduct.equivProd.symm

/-- The computable coordinate model is the concrete-factor semidirect
model previously identified with the exact normalizer. -/
noncomputable def
    alternatingSixThreeNormalizerCoordinatesEquivHeisenbergSemidirect :
    AlternatingSixThreeNormalizerCoordinates ≃*
      AlternatingSixThreeHeisenbergCyclicEightSemidirect :=
  SemidirectProduct.congr
    alternatingSixThreeHeisenbergCoordinatesEquivSchurSylow
    (MulEquiv.refl AlternatingSixThreeCyclicEight)
    alternatingSixThreeHeisenbergCoordinateAction_intertwinesSchur

/-- The computable 216-element group is the exact normalizer in the
presented Schur cover. -/
noncomputable def
    alternatingSixThreeNormalizerCoordinatesEquivSchurNormalizer :
    AlternatingSixThreeNormalizerCoordinates ≃*
      AlternatingSixSchurThreeNormalizer :=
  alternatingSixThreeNormalizerCoordinatesEquivHeisenbergSemidirect.trans
    alternatingSixThreeHeisenbergCyclicEightEquivSchurNormalizer

@[simp]
theorem natCard_alternatingSixThreeNormalizerCoordinates :
    Nat.card AlternatingSixThreeNormalizerCoordinates = 216 := by
  calc
    Nat.card AlternatingSixThreeNormalizerCoordinates =
        Nat.card
          (AlternatingSixThreeHeisenbergCoordinates ×
            AlternatingSixThreeCyclicEight) :=
      Nat.card_congr SemidirectProduct.equivProd
    _ =
        Nat.card AlternatingSixThreeHeisenbergCoordinates *
          Nat.card AlternatingSixThreeCyclicEight :=
      by rw [Nat.card_prod]
    _ = 216 := by
      rw [natCard_alternatingSixThreeHeisenbergCoordinates]
      change 27 * Nat.card (Multiplicative (ZMod 8)) = 216
      rw [Nat.card_congr Multiplicative.toAdd]
      norm_num

end GroupTheory
end McKayConjecture
