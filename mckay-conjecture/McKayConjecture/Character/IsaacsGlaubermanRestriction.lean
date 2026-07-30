/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ActionInvariantOver
import McKayConjecture.Character.CharacterDegreeDivisibility
import McKayConjecture.Character.ExtensionFromDegree
import McKayConjecture.Character.GlaubermanAction
import McKayConjecture.Character.OverAlongTransport
import McKayConjecture.GroupTheory.PPrimeCore

/-!
# Isaacs's subgroup-compatible Glauberman theorem

Isaacs, *Character Theory of Finite Groups*, Theorem 13.29, is the
subgroup-compatibility theorem for the Glauberman correspondence.  Let a
finite solvable group `S` act coprimely on a finite group `G`, preserve
`N ◁ G`, and let `chi` and `theta` be `S`-invariant irreducible
characters of `G` and `N`.  Writing stars for the two Glauberman
correspondents, the theorem says

`chi` lies over `theta` if and only if `chi*` lies over `theta*`

on `N ∩ FixedPoints S G`.

Okuyama--Wajima use exactly the specialization in which `S` is a
`p`-group and `G` is a `p'`-group on pp. 803--804 of the proof of their
Theorem 2(3).  There `S = P`, `G = U K`, `N = K`, the fixed group of
`G` is `U`, and the fixed group of `N` is `L`.  Thus Theorem 13.29
restricts the ambient Glauberman bijection to

`Irr_P(U K | theta) ≃ Irr(U | phi)`.

The printed characterization
`(restriction chi U, eta) ≠ 0 (mod p)` then comes from the defining
multiplicity property of the ambient Glauberman correspondence, not
from an additional assertion in Theorem 13.29.

This file isolates the exact statement used downstream as the explicit
proposition `IsaacsGlaubermanRestrictionInput`.  It is the exact
`p`/`p'` specialization used by Okuyama--Wajima, not an axiom or a
typeclass.  This file proves all subsequent coordinate, fibre,
multiplicity, ordinary-cardinality, and conditional extension adapters.
The proposition itself is proved from the existing character-theory API
in `IsaacsGlaubermanRestrictionReduction.lean`.

The two actions are explicit typeclass parameters, and `hsmul` records
that the action on `N` is the restriction of the action on `G`.  This
avoids any hidden choice of action instance.  No degree preservation by
Glauberman correspondence is asserted: that would strengthen the source
theorem and is false in general.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Theorem 13.29.
* T. Okuyama and M. Wajima, *Character correspondence and p-blocks of
  p-solvable groups*, Osaka J. Math. 17 (1980), 801--806, pp. 803--804.
-/

noncomputable section

namespace McKayConjecture

open CliffordCorrespondence

variable {S G : Type}
variable [Group S] [Group G] [Finite S] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (N : Subgroup G) [N.Normal]
variable [MulDistribMulAction S G]
variable [MulDistribMulAction S N]

namespace IsaacsGlaubermanRestriction

variable
  (hsmul : ∀ (s : S) (n : N),
    ((s • n : N) : G) = s • (n : G))

/-! ## Fixed points of the preserved normal subgroup -/

/-- The canonical inclusion `N^S → G^S`. -/
def fixedNormalInclusion :
    FixedPoints.subgroup S N →*
      FixedPoints.subgroup S G where
  toFun n :=
    ⟨(n.1 : G), fun s ↦ by
      calc
        s • (n.1 : G) =
            ((s • n.1 : N) : G) :=
          (hsmul s n.1).symm
        _ = (n.1 : G) :=
          congrArg Subtype.val (n.2 s)⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    rfl

@[simp]
theorem fixedNormalInclusion_apply_coe
    (n : FixedPoints.subgroup S N) :
    ((fixedNormalInclusion N hsmul n :
        FixedPoints.subgroup S G) : G) =
      ((n : N) : G) :=
  rfl

/-- The fixed-point inclusion is injective. -/
theorem fixedNormalInclusion_injective :
    Function.Injective (fixedNormalInclusion N hsmul) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg
    (fun z : FixedPoints.subgroup S G ↦ (z : G))
    hxy

/-- The literal subgroup `N ∩ G^S` inside the fixed-point group `G^S`. -/
abbrev fixedNormalSubgroup :
    Subgroup (FixedPoints.subgroup S G) :=
  N.comap (actionFixedPointsInclusion S G)

/-- The fixed points of `N` are canonically isomorphic to the literal
intersection subgroup `N ∩ G^S` inside `G^S`. -/
def fixedNormalSubgroupEquiv :
    FixedPoints.subgroup S N ≃*
      fixedNormalSubgroup (S := S) (G := G) N where
  toFun n :=
    ⟨fixedNormalInclusion N hsmul n, n.1.2⟩
  invFun n :=
    ⟨⟨((n.1 : FixedPoints.subgroup S G) : G), n.2⟩,
      fun s ↦ by
        apply Subtype.ext
        calc
          ((s •
              (⟨((n.1 : FixedPoints.subgroup S G) : G),
                n.2⟩ : N) : N) : G) =
              s • ((n.1 : FixedPoints.subgroup S G) : G) :=
            hsmul s
              ⟨((n.1 : FixedPoints.subgroup S G) : G), n.2⟩
          _ = ((n.1 : FixedPoints.subgroup S G) : G) :=
            n.1.2 s⟩
  left_inv n := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv n := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

@[simp]
theorem fixedNormalSubgroupEquiv_apply_coe
    (n : FixedPoints.subgroup S N) :
    (((fixedNormalSubgroupEquiv N hsmul n :
        fixedNormalSubgroup (S := S) (G := G) N) :
          FixedPoints.subgroup S G) : G) =
      ((n : N) : G) :=
  rfl

/-- The fixed-point inclusion factors through the literal intersection. -/
theorem fixedNormalSubgroupEquiv_commutes :
    (fixedNormalSubgroup (S := S) (G := G) N).subtype.comp
        (fixedNormalSubgroupEquiv N hsmul).toMonoidHom =
      fixedNormalInclusion N hsmul := by
  ext n
  rfl

/-- Since `N ◁ G`, the intersection `N ∩ G^S` is normal in `G^S`. -/
theorem fixedNormalSubgroup_normal :
    (fixedNormalSubgroup (S := S) (G := G) N).Normal :=
  inferInstance

/-! ## Literal-intersection coordinates -/

/-- Restriction multiplicity is unchanged when `N^S` is replaced by the
literal subgroup `N ∩ G^S` of `G^S`. -/
theorem restrictionMultiplicity_fixedNormalSubgroupEquiv
    (phi : IrreducibleCharacter (FixedPoints.subgroup S N))
    (chi : IrreducibleCharacter (FixedPoints.subgroup S G)) :
    restrictionMultiplicity
        (fixedNormalSubgroup (S := S) (G := G) N).subtype
        (phi.comap (fixedNormalSubgroupEquiv N hsmul).symm)
        chi =
      restrictionMultiplicity
        (fixedNormalInclusion N hsmul)
        phi chi := by
  exact
    restrictionMultiplicity_comap_equiv
      (MulEquiv.refl (FixedPoints.subgroup S G))
      (fixedNormalSubgroupEquiv N hsmul).symm
      (fixedNormalInclusion N hsmul)
      (fixedNormalSubgroup (S := S) (G := G) N).subtype
      (by
        ext n
        rfl)
      phi chi

/-- Lying over is unchanged by the fixed-intersection coordinate change. -/
theorem liesOver_fixedNormalSubgroupEquiv_iff
    (phi : IrreducibleCharacter (FixedPoints.subgroup S N))
    (chi : IrreducibleCharacter (FixedPoints.subgroup S G)) :
    LiesOverAlong
        (fixedNormalSubgroup (S := S) (G := G) N).subtype
        (phi.comap (fixedNormalSubgroupEquiv N hsmul).symm)
        chi ↔
      LiesOverAlong
        (fixedNormalInclusion N hsmul)
        phi chi := by
  rw [LiesOverAlong, LiesOverAlong,
    restrictionMultiplicity_fixedNormalSubgroupEquiv
      N hsmul phi chi]

/-- Exact extension is likewise unchanged by replacing `N^S` with the
literal subgroup `N ∩ G^S`. -/
theorem isExtensionAlong_fixedNormalSubgroupEquiv_iff
    (phi : IrreducibleCharacter (FixedPoints.subgroup S N))
    (chi : IrreducibleCharacter (FixedPoints.subgroup S G)) :
    IrreducibleCharacter.IsExtensionAlong
        (fixedNormalSubgroup (S := S) (G := G) N).subtype
        (phi.comap (fixedNormalSubgroupEquiv N hsmul).symm)
        chi ↔
      IrreducibleCharacter.IsExtensionAlong
        (fixedNormalInclusion N hsmul)
        phi chi := by
  constructor
  · intro hext n
    have hvalue :=
      hext (fixedNormalSubgroupEquiv N hsmul n)
    have hinc :
        (fixedNormalSubgroup (S := S) (G := G) N).subtype
            (fixedNormalSubgroupEquiv N hsmul n) =
          fixedNormalInclusion N hsmul n :=
      congrArg
        (fun f :
          FixedPoints.subgroup S N →*
            FixedPoints.subgroup S G ↦ f n)
        (fixedNormalSubgroupEquiv_commutes N hsmul)
    calc
      chi.values (fixedNormalInclusion N hsmul n) =
          chi.values
            ((fixedNormalSubgroup
              (S := S) (G := G) N).subtype
                (fixedNormalSubgroupEquiv N hsmul n)) :=
        congrArg chi.values hinc.symm
      _ =
          (phi.comap
            (fixedNormalSubgroupEquiv N hsmul).symm).values
              (fixedNormalSubgroupEquiv N hsmul n) :=
        hvalue
      _ = phi.values n := by simp
  · intro hext n
    have hvalue :=
      hext ((fixedNormalSubgroupEquiv N hsmul).symm n)
    have hinc :
        fixedNormalInclusion N hsmul
            ((fixedNormalSubgroupEquiv N hsmul).symm n) =
          (fixedNormalSubgroup
            (S := S) (G := G) N).subtype n := by
      rw [← fixedNormalSubgroupEquiv_commutes N hsmul]
      simp
    calc
      chi.values
          ((fixedNormalSubgroup
            (S := S) (G := G) N).subtype n) =
          chi.values
            (fixedNormalInclusion N hsmul
              ((fixedNormalSubgroupEquiv N hsmul).symm n)) :=
        congrArg chi.values hinc.symm
      _ =
          phi.values
            ((fixedNormalSubgroupEquiv N hsmul).symm n) :=
        hvalue
      _ =
          (phi.comap
            (fixedNormalSubgroupEquiv N hsmul).symm).values n :=
        rfl

/-! ## The exact source-theorem interface -/

/-- The exact `p`-group-on-`p'`-group specialization of Isaacs,
Theorem 13.29, used by Okuyama--Wajima.

The conclusion only preserves and reflects ordinary lying over.  It
asserts neither equality of degrees nor prime-to-`p` multiplicity along
`N^S → G^S`. -/
def IsaacsGlaubermanRestrictionInput
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p) : Prop :=
  IsPGroup p S →
    GroupTheory.IsPPrimeGroup p G →
      ∀
        (chi :
          ActionInvariantPPrimeIrreducibleCharacter S G p)
        (theta :
          ActionInvariantPPrimeIrreducibleCharacter S N p),
        LiesOverAlong N.subtype theta.1.1 chi.1.1 ↔
          LiesOverAlong
            (fixedNormalInclusion N hsmul)
            (dN.characterEquiv theta).1
            (dG.characterEquiv chi).1

/-- Named eliminator for the explicit Isaacs 13.29 input. -/
theorem liesOver_iff_correspondents_lieOver
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p)
    (hisaacs :
      IsaacsGlaubermanRestrictionInput N hsmul dG dN)
    (hS : IsPGroup p S)
    (hG : GroupTheory.IsPPrimeGroup p G)
    (chi :
      ActionInvariantPPrimeIrreducibleCharacter S G p)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p) :
    LiesOverAlong N.subtype theta.1.1 chi.1.1 ↔
      LiesOverAlong
        (fixedNormalInclusion N hsmul)
        (dN.characterEquiv theta).1
        (dG.characterEquiv chi).1 :=
  hisaacs hS hG chi theta

/-! ## Restricting the Glauberman equivalence to a fibre -/

/-- Invariant prime-to-`p` characters of `G` lying over a fixed invariant
character of `N`. -/
def InvariantPPrimeCharactersOver
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p) :=
  {chi :
      ActionInvariantPPrimeIrreducibleCharacter S G p //
    LiesOverAlong N.subtype theta.1.1 chi.1.1}

/-- Transport the fixed normal correspondent from `N^S` to the literal
normal subgroup `N ∩ G^S`. -/
def fixedNormalCorrespondent
    (dN : ActionGlaubermanCorrespondence S N p)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p) :
    PPrimeIrreducibleCharacter
      (fixedNormalSubgroup (S := S) (G := G) N) p :=
  IrreducibleCharacter.pPrimeComapEquiv p
    (fixedNormalSubgroupEquiv N hsmul).symm
    (dN.characterEquiv theta)

@[simp]
theorem fixedNormalCorrespondent_coe
    (dN : ActionGlaubermanCorrespondence S N p)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p) :
    (fixedNormalCorrespondent N hsmul dN theta).1 =
      (dN.characterEquiv theta).1.comap
        (fixedNormalSubgroupEquiv N hsmul).symm :=
  rfl

/-- Passing to the literal fixed-intersection coordinate does not change
the degree of the normal Glauberman correspondent. -/
@[simp]
theorem fixedNormalCorrespondent_degree
    (dN : ActionGlaubermanCorrespondence S N p)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p) :
    (fixedNormalCorrespondent N hsmul dN theta).1.degree =
      (dN.characterEquiv theta).1.degree :=
  IrreducibleCharacter.comap_degree
    (fixedNormalSubgroupEquiv N hsmul).symm
    (dN.characterEquiv theta).1

/-- Isaacs 13.29 restricts the ambient Glauberman equivalence to the
fibres over `theta` and its correspondent. -/
def invariantPPrimeCharactersOverEquiv
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p)
    (hisaacs :
      IsaacsGlaubermanRestrictionInput N hsmul dG dN)
    (hS : IsPGroup p S)
    (hG : GroupTheory.IsPPrimeGroup p G)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p) :
    InvariantPPrimeCharactersOver N theta ≃
      PPrimeIrreducibleCharactersOverAlong
        (fixedNormalSubgroup (S := S) (G := G) N).subtype
        (fixedNormalCorrespondent N hsmul dN theta).1 p where
  toFun chi := by
    let eta := dG.characterEquiv chi.1
    refine ⟨⟨eta.1, ?_⟩, eta.2⟩
    apply
      (liesOver_fixedNormalSubgroupEquiv_iff
        N hsmul (dN.characterEquiv theta).1 eta.1).2
    exact (hisaacs hS hG chi.1 theta).1 chi.2
  invFun eta := by
    let chi := dG.characterEquiv.symm ⟨eta.1.1, eta.2⟩
    refine ⟨chi, ?_⟩
    apply (hisaacs hS hG chi theta).2
    have heta :
        LiesOverAlong
          (fixedNormalInclusion N hsmul)
          (dN.characterEquiv theta).1 eta.1.1 :=
      (liesOver_fixedNormalSubgroupEquiv_iff
        N hsmul (dN.characterEquiv theta).1 eta.1.1).1
          eta.1.2
    have hback :
        dG.characterEquiv chi =
          ⟨eta.1.1, eta.2⟩ := by
      exact dG.characterEquiv.apply_symm_apply
        ⟨eta.1.1, eta.2⟩
    rw [hback]
    exact heta
  left_inv chi := by
    apply Subtype.ext
    exact dG.characterEquiv.symm_apply_apply chi.1
  right_inv eta := by
    have hirr :
        (dG.characterEquiv
          (dG.characterEquiv.symm
            ⟨eta.1.1, eta.2⟩)).1 =
          eta.1.1 :=
      congrArg Subtype.val
        (dG.characterEquiv.apply_symm_apply
          ⟨eta.1.1, eta.2⟩)
    exact Subtype.ext (Subtype.ext hirr)

@[simp]
theorem invariantPPrimeCharactersOverEquiv_apply_coe
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p)
    (hisaacs :
      IsaacsGlaubermanRestrictionInput N hsmul dG dN)
    (hS : IsPGroup p S)
    (hG : GroupTheory.IsPPrimeGroup p G)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p)
    (chi : InvariantPPrimeCharactersOver N theta) :
    (invariantPPrimeCharactersOverEquiv
      N hsmul dG dN hisaacs hS hG theta chi).1.1 =
        (dG.characterEquiv chi.1).1 :=
  rfl

/-- The image lies over the fixed normal correspondent. -/
theorem invariantPPrimeCharactersOverEquiv_liesOver
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p)
    (hisaacs :
      IsaacsGlaubermanRestrictionInput N hsmul dG dN)
    (hS : IsPGroup p S)
    (hG : GroupTheory.IsPPrimeGroup p G)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p)
    (chi : InvariantPPrimeCharactersOver N theta) :
    LiesOverAlong
      (fixedNormalSubgroup (S := S) (G := G) N).subtype
      (fixedNormalCorrespondent N hsmul dN theta).1
      (invariantPPrimeCharactersOverEquiv
        N hsmul dG dN hisaacs hS hG theta chi).1.1 :=
  (invariantPPrimeCharactersOverEquiv
    N hsmul dG dN hisaacs hS hG theta chi).1.2

/-! ## The printed prime-to-`p` characterization -/

/-- The selected target character has prime-to-`p` multiplicity in the
restriction of the source character to `G^S`. -/
theorem invariantPPrimeCharactersOverEquiv_multiplicity_isPPrime
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p)
    (hisaacs :
      IsaacsGlaubermanRestrictionInput N hsmul dG dN)
    (hS : IsPGroup p S)
    (hG : GroupTheory.IsPPrimeGroup p G)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p)
    (chi : InvariantPPrimeCharactersOver N theta) :
    ¬p ∣
      restrictionMultiplicity
        (actionFixedPointsInclusion S G)
        (invariantPPrimeCharactersOverEquiv
          N hsmul dG dN hisaacs hS hG theta chi).1.1
        chi.1.1.1 := by
  change
    ¬p ∣
      restrictionMultiplicity
        (actionFixedPointsInclusion S G)
        (dG.characterEquiv chi.1).1 chi.1.1.1
  exact dG.multiplicity_isPPrime chi.1

/-- In the target fibre, prime-to-`p` ambient restriction multiplicity
characterizes exactly the image of a source character. -/
theorem eq_invariantPPrimeCharactersOverEquiv_apply_iff
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p)
    (hisaacs :
      IsaacsGlaubermanRestrictionInput N hsmul dG dN)
    (hS : IsPGroup p S)
    (hG : GroupTheory.IsPPrimeGroup p G)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p)
    (chi : InvariantPPrimeCharactersOver N theta)
    (eta :
      PPrimeIrreducibleCharactersOverAlong
        (fixedNormalSubgroup (S := S) (G := G) N).subtype
        (fixedNormalCorrespondent N hsmul dN theta).1 p) :
    eta =
        invariantPPrimeCharactersOverEquiv
          N hsmul dG dN hisaacs hS hG theta chi ↔
      ¬p ∣
        restrictionMultiplicity
          (actionFixedPointsInclusion S G)
          eta.1.1 chi.1.1.1 := by
  constructor
  · intro heta
    subst eta
    exact
      invariantPPrimeCharactersOverEquiv_multiplicity_isPPrime
        N hsmul dG dN hisaacs hS hG theta chi
  · intro hmult
    have hirr :
        eta.1.1 = (dG.characterEquiv chi.1).1 :=
      congrArg Subtype.val
        (dG.eq_correspondent_of_multiplicity_isPPrime
          chi.1 ⟨eta.1.1, eta.2⟩ hmult)
    exact Subtype.ext (Subtype.ext hirr)

/-- Exact invariant prime-to-`p` fibre-cardinality identity. -/
theorem natCard_invariantPPrimeCharactersOver_eq
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p)
    (hisaacs :
      IsaacsGlaubermanRestrictionInput N hsmul dG dN)
    (hS : IsPGroup p S)
    (hG : GroupTheory.IsPPrimeGroup p G)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p) :
    Nat.card (InvariantPPrimeCharactersOver N theta) =
      Nat.card
        (PPrimeIrreducibleCharactersOverAlong
          (fixedNormalSubgroup (S := S) (G := G) N).subtype
          (fixedNormalCorrespondent N hsmul dN theta).1 p) :=
  Nat.card_congr
    (invariantPPrimeCharactersOverEquiv
      N hsmul dG dN hisaacs hS hG theta)

/-! ## Ordinary invariant-source form -/

/-- Every irreducible character of a finite `p'`-group has
prime-to-`p` degree. -/
theorem isPPrimeDegree_of_isPPrimeGroup
    {H : Type} [Group H] [Finite H]
    (hH : GroupTheory.IsPPrimeGroup p H)
    (chi : IrreducibleCharacter H) :
    chi.IsPPrimeDegree p := by
  rw [IrreducibleCharacter.IsPPrimeDegree]
  intro hpdegree
  have hpcard : p ∣ Nat.card H :=
    hpdegree.trans chi.degree_dvd_card
  exact
    ((GroupTheory.isPPrimeGroup_iff_not_dvd
      (G := H) Fact.out).mp hH) hpcard

/-- The ordinary `S`-invariant part of the source lying-over fibre.

This is deliberately a subfibre of the full source fibre.  Isaacs 13.28
only supplies invariant constituents; it does not say that every source
constituent is invariant. -/
def InvariantCharactersOver
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p) :=
  {chi :
      IrreducibleCharactersOverAlong N.subtype theta.1.1 //
    ∀ (s : S) (g : G),
      chi.1.values (s • g) = chi.1.values g}

/-- In a `p'`-group, adding prime-to-`p` degree data to the invariant
source subfibre changes no characters. -/
def invariantCharactersOverEquivInvariantPPrime
    (hG : GroupTheory.IsPPrimeGroup p G)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p) :
    InvariantCharactersOver N theta ≃
      InvariantPPrimeCharactersOver N theta where
  toFun chi :=
    ⟨⟨⟨chi.1.1,
          isPPrimeDegree_of_isPPrimeGroup hG chi.1.1⟩,
        chi.2⟩,
      chi.1.2⟩
  invFun chi :=
    ⟨⟨chi.1.1.1, chi.2⟩, chi.1.2⟩
  left_inv chi := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv chi := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- On `G^S`, prime-to-`p` degree is automatic and can be erased. -/
def targetPPrimeFibreEquivOrdinary
    (hG : GroupTheory.IsPPrimeGroup p G)
    (dN : ActionGlaubermanCorrespondence S N p)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p) :
    PPrimeIrreducibleCharactersOverAlong
        (fixedNormalSubgroup (S := S) (G := G) N).subtype
        (fixedNormalCorrespondent N hsmul dN theta).1 p ≃
      IrreducibleCharactersOverAlong
        (fixedNormalSubgroup (S := S) (G := G) N).subtype
        (fixedNormalCorrespondent N hsmul dN theta).1 :=
  pPrimeIrreducibleCharactersOverAlongEquivOfForallIsPPrimeDegree
    (fixedNormalSubgroup (S := S) (G := G) N).subtype
    (fixedNormalCorrespondent N hsmul dN theta).1
    p
    (fun chi ↦
      isPPrimeDegree_of_isPPrimeGroup
        (hG.to_subgroup (FixedPoints.subgroup S G))
        chi.1)

/-- Ordinary-character form of Isaacs 13.29 used in the corrected
Okuyama--Wajima full-fixed count: the invariant source subfibre, not the
whole source fibre, is equivalent to the full fixed-point target fibre. -/
def invariantCharactersOverEquiv
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p)
    (hisaacs :
      IsaacsGlaubermanRestrictionInput N hsmul dG dN)
    (hS : IsPGroup p S)
    (hG : GroupTheory.IsPPrimeGroup p G)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p) :
    InvariantCharactersOver N theta ≃
      IrreducibleCharactersOverAlong
        (fixedNormalSubgroup (S := S) (G := G) N).subtype
        (fixedNormalCorrespondent N hsmul dN theta).1 :=
  (invariantCharactersOverEquivInvariantPPrime
      N hG theta).trans
    ((invariantPPrimeCharactersOverEquiv
      N hsmul dG dN hisaacs hS hG theta).trans
        (targetPPrimeFibreEquivOrdinary
          N hsmul hG dN theta))

@[simp]
theorem invariantCharactersOverEquiv_apply_coe
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p)
    (hisaacs :
      IsaacsGlaubermanRestrictionInput N hsmul dG dN)
    (hS : IsPGroup p S)
    (hG : GroupTheory.IsPPrimeGroup p G)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p)
    (chi : InvariantCharactersOver N theta) :
    (invariantCharactersOverEquiv
      N hsmul dG dN hisaacs hS hG theta chi).1 =
        (dG.characterEquiv
          (invariantCharactersOverEquivInvariantPPrime
            N hG theta chi).1).1 :=
  rfl

/-- Ordinary invariant-source fibre-cardinality identity. -/
theorem natCard_invariantCharactersOver_eq
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p)
    (hisaacs :
      IsaacsGlaubermanRestrictionInput N hsmul dG dN)
    (hS : IsPGroup p S)
    (hG : GroupTheory.IsPPrimeGroup p G)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p) :
    Nat.card (InvariantCharactersOver N theta) =
      Nat.card
        (IrreducibleCharactersOverAlong
          (fixedNormalSubgroup (S := S) (G := G) N).subtype
          (fixedNormalCorrespondent N hsmul dN theta).1) :=
  Nat.card_congr
    (invariantCharactersOverEquiv
      N hsmul dG dN hisaacs hS hG theta)

/-- The invariant source fibre embeds in the full source fibre. -/
def invariantCharactersOverEmbedding
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p) :
    InvariantCharactersOver N theta ↪
      IrreducibleCharactersOverAlong N.subtype theta.1.1 where
  toFun chi := chi.1
  inj' := Subtype.val_injective

/-- The invariant source fibre has at most the cardinality of the full
source fibre. -/
theorem natCard_invariantCharactersOver_le
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p) :
    Nat.card (InvariantCharactersOver N theta) ≤
      Nat.card
        (IrreducibleCharactersOverAlong N.subtype theta.1.1) :=
  Nat.card_le_card_of_injective
    (invariantCharactersOverEmbedding N theta)
    (invariantCharactersOverEmbedding N theta).injective

/-- The exact lower-bound seam used with `ExtensionFromMaximalFibre`:
the full source fibre is at least as large as the fixed-point target
fibre. -/
theorem natCard_target_le_fullSource
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p)
    (hisaacs :
      IsaacsGlaubermanRestrictionInput N hsmul dG dN)
    (hS : IsPGroup p S)
    (hG : GroupTheory.IsPPrimeGroup p G)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p) :
    Nat.card
        (IrreducibleCharactersOverAlong
          (fixedNormalSubgroup (S := S) (G := G) N).subtype
          (fixedNormalCorrespondent N hsmul dN theta).1) ≤
      Nat.card
        (IrreducibleCharactersOverAlong N.subtype theta.1.1) := by
  calc
    Nat.card
        (IrreducibleCharactersOverAlong
          (fixedNormalSubgroup (S := S) (G := G) N).subtype
          (fixedNormalCorrespondent N hsmul dN theta).1) =
        Nat.card (InvariantCharactersOver N theta) :=
      (natCard_invariantCharactersOver_eq
        N hsmul dG dN hisaacs hS hG theta).symm
    _ ≤
        Nat.card
          (IrreducibleCharactersOverAlong
            N.subtype theta.1.1) :=
      natCard_invariantCharactersOver_le N theta

/-! ## Degree and extension adapters -/

/-- A source fibre member with the base degree is an extension. -/
theorem source_isExtension_of_degree_eq
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p)
    (chi : InvariantPPrimeCharactersOver N theta)
    (hdegree : chi.1.1.1.degree = theta.1.1.degree) :
    IrreducibleCharacter.IsExtension N theta.1.1 chi.1.1.1 :=
  IrreducibleCharacter.IsExtensionAlong.of_liesOver_of_degree_eq
    chi.2 hdegree

/-- A target image with the fixed-base degree is an extension. -/
theorem target_isExtension_of_degree_eq
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p)
    (hisaacs :
      IsaacsGlaubermanRestrictionInput N hsmul dG dN)
    (hS : IsPGroup p S)
    (hG : GroupTheory.IsPPrimeGroup p G)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p)
    (chi : InvariantPPrimeCharactersOver N theta)
    (hdegree :
      (invariantPPrimeCharactersOverEquiv
          N hsmul dG dN hisaacs hS hG theta chi).1.1.degree =
        (fixedNormalCorrespondent N hsmul dN theta).1.degree) :
    IrreducibleCharacter.IsExtension
      (fixedNormalSubgroup (S := S) (G := G) N)
      (fixedNormalCorrespondent N hsmul dN theta).1
      (invariantPPrimeCharactersOverEquiv
        N hsmul dG dN hisaacs hS hG theta chi).1.1 :=
  IrreducibleCharacter.IsExtensionAlong.of_liesOver_of_degree_eq
    (invariantPPrimeCharactersOverEquiv
      N hsmul dG dN hisaacs hS hG theta chi).1.2
    hdegree

/-- Extension status transfers exactly under an explicit equivalence of
the two degree-equality tests.  This extra hypothesis is essential. -/
theorem source_isExtension_iff_target_isExtension_of_degree_iff
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p)
    (hisaacs :
      IsaacsGlaubermanRestrictionInput N hsmul dG dN)
    (hS : IsPGroup p S)
    (hG : GroupTheory.IsPPrimeGroup p G)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p)
    (chi : InvariantPPrimeCharactersOver N theta)
    (hdegree :
      chi.1.1.1.degree = theta.1.1.degree ↔
        (invariantPPrimeCharactersOverEquiv
            N hsmul dG dN hisaacs hS hG theta chi).1.1.degree =
          (fixedNormalCorrespondent N hsmul dN theta).1.degree) :
    IrreducibleCharacter.IsExtension
        N theta.1.1 chi.1.1.1 ↔
      IrreducibleCharacter.IsExtension
        (fixedNormalSubgroup (S := S) (G := G) N)
        (fixedNormalCorrespondent N hsmul dN theta).1
        (invariantPPrimeCharactersOverEquiv
          N hsmul dG dN hisaacs hS hG theta chi).1.1 := by
  constructor
  · intro hsource
    exact
      target_isExtension_of_degree_eq
        N hsmul dG dN hisaacs hS hG theta chi
        (hdegree.1 hsource.degree_eq)
  · intro htarget
    exact
      source_isExtension_of_degree_eq
        N theta chi
        (hdegree.2 htarget.degree_eq)

end IsaacsGlaubermanRestriction

end McKayConjecture
