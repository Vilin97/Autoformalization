/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ExtensionFromMaximalFibre
import McKayConjecture.Character.IsaacsGlaubermanRestrictionReduction

/-!
# The full-fixed branch of the printed Okuyama--Wajima induction

This file completes the character-theoretic argument in the full-fixed
branch of Okuyama--Wajima, Theorem 2(3), after the subgroup coordinates
have been supplied.

Isaacs, Theorem 13.29 identifies the action-invariant part of the source
fibre with the whole fixed-point target fibre.  A target extension over a
commutative quotient makes the target fibre have the target subgroup
index many elements.  The invariant source fibre embeds in the full
source fibre, while Clifford theory bounds that full fibre by the source
subgroup index.  Equality of the two indices therefore makes the full
source fibre maximal.  The sum-of-squared-restriction-multiplicities
identity then forces every source character lying over the normal
character to be an extension.

In particular, this argument does not use Isaacs, Theorem 13.28.
The exact `IsaacsGlaubermanRestrictionInput` from Theorem 13.29 is now
proved in `IsaacsGlaubermanRestrictionReduction.lean`; automatic wrappers
below discharge it.  The target extension, commutative target quotient,
ambient invariance, and index equality are kept visible because they are
supplied by the surrounding Okuyama--Wajima subgroup and induction
coordinates.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Theorem 13.29.
* T. Okuyama and M. Wajima, *Character correspondence and p-blocks of
  p-solvable groups*, Osaka J. Math. 17 (1980), 801--806, pp. 803--804.
-/

noncomputable section

namespace McKayConjecture
namespace IsaacsGlaubermanRestriction

open CliffordCorrespondence

variable {S G : Type}
variable [Group S] [Group G] [Finite S] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (N : Subgroup G) [N.Normal]
variable [MulDistribMulAction S G]
variable [MulDistribMulAction S N]

variable
  (hsmul : ∀ (s : S) (n : N),
    ((s • n : N) : G) = s • (n : G))

/-- In the full-fixed branch, every source irreducible character lying
over `theta` is an extension.

The source `G` and `N` specialize to `U K` and `K` in the printed proof.
The target group and normal subgroup are their literal fixed-point
coordinates `G^S` and `N ∩ G^S`, specializing to `U` and `L`.
Consequently `hindex` is the coordinate equality
`[U K : K] = [U : L]`. -/
theorem okuyamaWajimaFullFixed_isExtension
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p)
    (hisaacs :
      IsaacsGlaubermanRestrictionInput N hsmul dG dN)
    (hS : IsPGroup p S)
    (hG : GroupTheory.IsPPrimeGroup p G)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p)
    (hinvariant : ∀ g : G, g • theta.1.1 = theta.1.1)
    [IsMulCommutative
      (FixedPoints.subgroup S G ⧸
        fixedNormalSubgroup (S := S) (G := G) N)]
    (phiExtension :
      IrreducibleCharacter (FixedPoints.subgroup S G))
    (hphiExtension :
      IrreducibleCharacter.IsExtension
        (fixedNormalSubgroup (S := S) (G := G) N)
        (fixedNormalCorrespondent N hsmul dN theta).1
        phiExtension)
    (hindex :
      N.index =
        (fixedNormalSubgroup (S := S) (G := G) N).index)
    (chi :
      IrreducibleCharactersOverAlong N.subtype theta.1.1) :
    IrreducibleCharacter.IsExtension N theta.1.1 chi.1 := by
  letI : Finite (InvariantCharactersOver N theta) :=
    Finite.of_injective
      (invariantCharactersOverEmbedding N theta)
      (invariantCharactersOverEmbedding N theta).injective
  exact
    isExtension_of_invariant_subfibre_equiv_abelian_extension_fibre
      N
      (fixedNormalSubgroup (S := S) (G := G) N)
      theta.1.1
      (fixedNormalCorrespondent N hsmul dN theta).1
      hinvariant
      phiExtension
      hphiExtension
      (invariantCharactersOverEmbedding N theta)
      (invariantCharactersOverEmbedding N theta).injective
      (invariantCharactersOverEquiv
        N hsmul dG dN hisaacs hS hG theta)
      hindex
      chi

/-- Existence form of the source-correct full-fixed argument. -/
theorem okuyamaWajimaFullFixed_exists_extension
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p)
    (hisaacs :
      IsaacsGlaubermanRestrictionInput N hsmul dG dN)
    (hS : IsPGroup p S)
    (hG : GroupTheory.IsPPrimeGroup p G)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p)
    (hinvariant : ∀ g : G, g • theta.1.1 = theta.1.1)
    [IsMulCommutative
      (FixedPoints.subgroup S G ⧸
        fixedNormalSubgroup (S := S) (G := G) N)]
    (phiExtension :
      IrreducibleCharacter (FixedPoints.subgroup S G))
    (hphiExtension :
      IrreducibleCharacter.IsExtension
        (fixedNormalSubgroup (S := S) (G := G) N)
        (fixedNormalCorrespondent N hsmul dN theta).1
        phiExtension)
    (hindex :
      N.index =
        (fixedNormalSubgroup (S := S) (G := G) N).index) :
    ∃ chi : IrreducibleCharacter G,
      IrreducibleCharacter.IsExtension N theta.1.1 chi := by
  letI : Finite (InvariantCharactersOver N theta) :=
    Finite.of_injective
      (invariantCharactersOverEmbedding N theta)
      (invariantCharactersOverEmbedding N theta).injective
  exact
    exists_extension_of_invariant_subfibre_equiv_abelian_extension_fibre
      N
      (fixedNormalSubgroup (S := S) (G := G) N)
      theta.1.1
      (fixedNormalCorrespondent N hsmul dN theta).1
      hinvariant
      phiExtension
      hphiExtension
      (invariantCharactersOverEmbedding N theta)
      (invariantCharactersOverEmbedding N theta).injective
      (invariantCharactersOverEquiv
        N hsmul dG dN hisaacs hS hG theta)
      hindex

/-! ## Automatic forms using the proved Isaacs 13.29 input -/

/-- Full-fixed extension theorem with the proved Isaacs 13.29
compatibility supplied automatically. -/
theorem okuyamaWajimaFullFixed_isExtension_automatic
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p)
    (hS : IsPGroup p S)
    (hG : GroupTheory.IsPPrimeGroup p G)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p)
    (hinvariant : ∀ g : G, g • theta.1.1 = theta.1.1)
    [IsMulCommutative
      (FixedPoints.subgroup S G ⧸
        fixedNormalSubgroup (S := S) (G := G) N)]
    (phiExtension :
      IrreducibleCharacter (FixedPoints.subgroup S G))
    (hphiExtension :
      IrreducibleCharacter.IsExtension
        (fixedNormalSubgroup (S := S) (G := G) N)
        (fixedNormalCorrespondent N hsmul dN theta).1
        phiExtension)
    (hindex :
      N.index =
        (fixedNormalSubgroup (S := S) (G := G) N).index)
    (chi :
      IrreducibleCharactersOverAlong N.subtype theta.1.1) :
    IrreducibleCharacter.IsExtension N theta.1.1 chi.1 :=
  okuyamaWajimaFullFixed_isExtension
    N hsmul dG dN
    (_root_.McKayConjecture.IsaacsGlaubermanRestrictionReduction.isaacsGlaubermanRestrictionInput
      N hsmul dG dN)
    hS hG theta hinvariant phiExtension hphiExtension hindex chi

/-- Existence form with the proved Isaacs 13.29 compatibility supplied
automatically. -/
theorem okuyamaWajimaFullFixed_exists_extension_automatic
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p)
    (hS : IsPGroup p S)
    (hG : GroupTheory.IsPPrimeGroup p G)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p)
    (hinvariant : ∀ g : G, g • theta.1.1 = theta.1.1)
    [IsMulCommutative
      (FixedPoints.subgroup S G ⧸
        fixedNormalSubgroup (S := S) (G := G) N)]
    (phiExtension :
      IrreducibleCharacter (FixedPoints.subgroup S G))
    (hphiExtension :
      IrreducibleCharacter.IsExtension
        (fixedNormalSubgroup (S := S) (G := G) N)
        (fixedNormalCorrespondent N hsmul dN theta).1
        phiExtension)
    (hindex :
      N.index =
        (fixedNormalSubgroup (S := S) (G := G) N).index) :
    ∃ chi : IrreducibleCharacter G,
      IrreducibleCharacter.IsExtension N theta.1.1 chi :=
  okuyamaWajimaFullFixed_exists_extension
    N hsmul dG dN
    (_root_.McKayConjecture.IsaacsGlaubermanRestrictionReduction.isaacsGlaubermanRestrictionInput
      N hsmul dG dN)
    hS hG theta hinvariant phiExtension hphiExtension hindex

/-! ## The reverse maximal-fibre squeeze -/

/-- If a source extension is fixed by the acting group and that group
acts trivially on the source quotient, every Gallagher twist above the
normal character is fixed as well.

This direct value calculation is the elementary replacement for the use
of Isaacs 13.28 in the reverse direction of the printed full-fixed
argument. -/
theorem
    forall_source_liesOver_values_invariant_of_fixedExtension_of_quotientActionTrivial
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p)
    (sourceExtension : IrreducibleCharacter G)
    (hsourceExtension :
      IrreducibleCharacter.IsExtension
        N theta.1.1 sourceExtension)
    (hsourceExtensionInvariant :
      ∀ (s : S) (g : G),
        sourceExtension.values (s • g) =
          sourceExtension.values g)
    (hquotientTrivial :
      ∀ (s : S) (g : G),
        QuotientGroup.mk' N (s • g) =
          QuotientGroup.mk' N g)
    (chi :
      IrreducibleCharactersOverAlong
        N.subtype theta.1.1)
    (s : S) (g : G) :
    chi.1.values (s • g) = chi.1.values g := by
  let beta : IrreducibleCharacter (G ⧸ N) :=
    IrreducibleCharacter.gallagherInverse
      hsourceExtension chi
  have hcharacter :
      IrreducibleCharacter.gallagherTensorCharacter
          hsourceExtension beta =
        chi.1 :=
    congrArg Subtype.val
      (IrreducibleCharacter.gallagherForward_inverse
        hsourceExtension chi)
  rw [← hcharacter,
    IrreducibleCharacter.gallagherTensorCharacter_values,
    IrreducibleCharacter.gallagherTensorCharacter_values,
    hsourceExtensionInvariant,
    hquotientTrivial]

/-- Reverse full-fixed cardinality argument.

Suppose the source character has an extension and the source quotient is
commutative.  Gallagher then makes the complete source fibre have
cardinality `N.index`.  If every source fibre member is action-invariant,
expressed here by equality of the invariant and complete fibre
cardinalities, Isaacs 13.29 transfers that cardinality to the complete
target fibre.  Equality of the two subgroup indices and target invariance
then force a target extension by the same maximal-fibre criterion.

This is the source-correct replacement for the reverse ``similar
argument'' on p. 804 of Okuyama--Wajima.  It does not invoke Isaacs
Theorem 13.28. -/
theorem
    okuyamaWajimaFullFixed_exists_target_extension_of_fullInvariantCardinality
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p)
    (hisaacs :
      IsaacsGlaubermanRestrictionInput N hsmul dG dN)
    (hS : IsPGroup p S)
    (hG : GroupTheory.IsPPrimeGroup p G)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p)
    [IsMulCommutative (G ⧸ N)]
    (sourceExtension : IrreducibleCharacter G)
    (hsourceExtension :
      IrreducibleCharacter.IsExtension
        N theta.1.1 sourceExtension)
    (hfullInvariant :
      Nat.card (InvariantCharactersOver N theta) =
        Nat.card
          (IrreducibleCharactersOverAlong
            N.subtype theta.1.1))
    (htargetInvariant :
      ∀ g : FixedPoints.subgroup S G,
        g • (fixedNormalCorrespondent
          N hsmul dN theta).1 =
            (fixedNormalCorrespondent
              N hsmul dN theta).1)
    (hindex :
      N.index =
        (fixedNormalSubgroup
          (S := S) (G := G) N).index) :
    ∃ eta : IrreducibleCharacter
        (FixedPoints.subgroup S G),
      IrreducibleCharacter.IsExtension
        (fixedNormalSubgroup
          (S := S) (G := G) N)
        (fixedNormalCorrespondent
          N hsmul dN theta).1 eta := by
  have hsourceCard :
      Nat.card
          (IrreducibleCharactersOverAlong
            N.subtype theta.1.1) =
        N.index := by
    calc
      Nat.card
            (IrreducibleCharactersOverAlong
              N.subtype theta.1.1) =
          Nat.card (IrreducibleCharacter (G ⧸ N)) :=
        (Nat.card_congr
          (IrreducibleCharacter.gallagherCorrespondence
            hsourceExtension)).symm
      _ = Nat.card (G ⧸ N) :=
        natCard_irreducibleCharacter_eq_card_of_isMulCommutative
          (G ⧸ N)
      _ = N.index := by
        rw [N.index_eq_card]
  have htargetCard :
      Nat.card
          (IrreducibleCharactersOverAlong
            (fixedNormalSubgroup
              (S := S) (G := G) N).subtype
            (fixedNormalCorrespondent
              N hsmul dN theta).1) =
        (fixedNormalSubgroup
          (S := S) (G := G) N).index := by
    calc
      Nat.card
            (IrreducibleCharactersOverAlong
              (fixedNormalSubgroup
                (S := S) (G := G) N).subtype
              (fixedNormalCorrespondent
                N hsmul dN theta).1) =
          Nat.card (InvariantCharactersOver N theta) :=
        (natCard_invariantCharactersOver_eq
          N hsmul dG dN hisaacs hS hG theta).symm
      _ =
          Nat.card
            (IrreducibleCharactersOverAlong
              N.subtype theta.1.1) :=
        hfullInvariant
      _ = N.index := hsourceCard
      _ =
          (fixedNormalSubgroup
            (S := S) (G := G) N).index :=
        hindex
  exact
    exists_extension_of_natCard_over_eq_index
      (fixedNormalSubgroup
        (S := S) (G := G) N)
      (fixedNormalCorrespondent
        N hsmul dN theta).1
      htargetInvariant htargetCard

/-- Pointwise all-source-invariant form of the reverse full-fixed
argument. -/
theorem
    okuyamaWajimaFullFixed_exists_target_extension_of_allSourceInvariant
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p)
    (hisaacs :
      IsaacsGlaubermanRestrictionInput N hsmul dG dN)
    (hS : IsPGroup p S)
    (hG : GroupTheory.IsPPrimeGroup p G)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p)
    [IsMulCommutative (G ⧸ N)]
    (sourceExtension : IrreducibleCharacter G)
    (hsourceExtension :
      IrreducibleCharacter.IsExtension
        N theta.1.1 sourceExtension)
    (hallSourceInvariant :
      ∀ chi :
          IrreducibleCharactersOverAlong
            N.subtype theta.1.1,
        ∀ (s : S) (g : G),
          chi.1.values (s • g) =
            chi.1.values g)
    (htargetInvariant :
      ∀ g : FixedPoints.subgroup S G,
        g • (fixedNormalCorrespondent
          N hsmul dN theta).1 =
            (fixedNormalCorrespondent
              N hsmul dN theta).1)
    (hindex :
      N.index =
        (fixedNormalSubgroup
          (S := S) (G := G) N).index) :
    ∃ eta : IrreducibleCharacter
        (FixedPoints.subgroup S G),
      IrreducibleCharacter.IsExtension
        (fixedNormalSubgroup
          (S := S) (G := G) N)
        (fixedNormalCorrespondent
          N hsmul dN theta).1 eta := by
  let e :
      InvariantCharactersOver N theta ≃
        IrreducibleCharactersOverAlong
          N.subtype theta.1.1 :=
    { toFun := fun chi ↦ chi.1
      invFun := fun chi ↦ ⟨chi, hallSourceInvariant chi⟩
      left_inv := fun chi ↦ by
        apply Subtype.ext
        rfl
      right_inv := fun _chi ↦ rfl }
  exact
    okuyamaWajimaFullFixed_exists_target_extension_of_fullInvariantCardinality
      N hsmul dG dN hisaacs hS hG theta
      sourceExtension hsourceExtension
      (Nat.card_congr e)
      htargetInvariant hindex

/-- Reverse full-fixed argument with the proved Isaacs 13.29 input
supplied automatically. -/
theorem
    okuyamaWajimaFullFixed_exists_target_extension_of_allSourceInvariant_automatic
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p)
    (hS : IsPGroup p S)
    (hG : GroupTheory.IsPPrimeGroup p G)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p)
    [IsMulCommutative (G ⧸ N)]
    (sourceExtension : IrreducibleCharacter G)
    (hsourceExtension :
      IrreducibleCharacter.IsExtension
        N theta.1.1 sourceExtension)
    (hallSourceInvariant :
      ∀ chi :
          IrreducibleCharactersOverAlong
            N.subtype theta.1.1,
        ∀ (s : S) (g : G),
          chi.1.values (s • g) =
            chi.1.values g)
    (htargetInvariant :
      ∀ g : FixedPoints.subgroup S G,
        g • (fixedNormalCorrespondent
          N hsmul dN theta).1 =
            (fixedNormalCorrespondent
              N hsmul dN theta).1)
    (hindex :
      N.index =
        (fixedNormalSubgroup
          (S := S) (G := G) N).index) :
    ∃ eta : IrreducibleCharacter
        (FixedPoints.subgroup S G),
      IrreducibleCharacter.IsExtension
        (fixedNormalSubgroup
          (S := S) (G := G) N)
        (fixedNormalCorrespondent
          N hsmul dN theta).1 eta :=
  okuyamaWajimaFullFixed_exists_target_extension_of_allSourceInvariant
    N hsmul dG dN
    (_root_.McKayConjecture.IsaacsGlaubermanRestrictionReduction.isaacsGlaubermanRestrictionInput
      N hsmul dG dN)
    hS hG theta sourceExtension hsourceExtension
    hallSourceInvariant htargetInvariant hindex

/-- Fully automatic all-source-invariance part of the reverse full-fixed
argument.  The only remaining semantic inputs are invariance of the chosen
source extension, triviality of the action on the source quotient, and
invariance of the target base character. -/
theorem
    okuyamaWajimaFullFixed_exists_target_extension_of_fixedSourceExtension_automatic
    (dG : ActionGlaubermanCorrespondence S G p)
    (dN : ActionGlaubermanCorrespondence S N p)
    (hS : IsPGroup p S)
    (hG : GroupTheory.IsPPrimeGroup p G)
    (theta :
      ActionInvariantPPrimeIrreducibleCharacter S N p)
    [IsMulCommutative (G ⧸ N)]
    (sourceExtension : IrreducibleCharacter G)
    (hsourceExtension :
      IrreducibleCharacter.IsExtension
        N theta.1.1 sourceExtension)
    (hsourceExtensionInvariant :
      ∀ (s : S) (g : G),
        sourceExtension.values (s • g) =
          sourceExtension.values g)
    (hquotientTrivial :
      ∀ (s : S) (g : G),
        QuotientGroup.mk' N (s • g) =
          QuotientGroup.mk' N g)
    (htargetInvariant :
      ∀ g : FixedPoints.subgroup S G,
        g • (fixedNormalCorrespondent
          N hsmul dN theta).1 =
            (fixedNormalCorrespondent
              N hsmul dN theta).1)
    (hindex :
      N.index =
        (fixedNormalSubgroup
          (S := S) (G := G) N).index) :
    ∃ eta : IrreducibleCharacter
        (FixedPoints.subgroup S G),
      IrreducibleCharacter.IsExtension
        (fixedNormalSubgroup
          (S := S) (G := G) N)
        (fixedNormalCorrespondent
          N hsmul dN theta).1 eta :=
  okuyamaWajimaFullFixed_exists_target_extension_of_allSourceInvariant_automatic
    N hsmul dG dN hS hG theta
    sourceExtension hsourceExtension
    (fun chi s g ↦
      forall_source_liesOver_values_invariant_of_fixedExtension_of_quotientActionTrivial
        N theta sourceExtension hsourceExtension
        hsourceExtensionInvariant hquotientTrivial chi s g)
    htargetInvariant hindex

end IsaacsGlaubermanRestriction
end McKayConjecture
