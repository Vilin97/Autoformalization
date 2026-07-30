/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ExtensionFromDegree
import McKayConjecture.Character.GallagherCommutator
import McKayConjecture.Character.GallagherCorrespondence
import McKayConjecture.Character.IrreducibleCharacterBasis

/-!
# Recognizing extensions from a maximal lying-over fibre

Let `N ◁ G` and let `theta ∈ Irr(N)` be `G`-invariant.  Clifford theory
gives

`[G : N] = ∑_{chi ∈ Irr(G | theta)} e_chi ^ 2`,

where `e_chi` is the restriction multiplicity of `theta` in `chi`.
Consequently the lying-over fibre has at most `[G : N]` elements.  If it
has exactly that many elements, every multiplicity is one, every lying-over
character has the same degree as `theta`, and every such character is an
extension.

This is the numerical Gallagher step used in the full-fixed branch of the
printed Okuyama--Wajima induction.  Isolating it here avoids importing any
of that proof's subgroup coordinates.
-/

noncomputable section

namespace McKayConjecture
namespace CliffordCorrespondence

variable {G : Type} [Group G] [Finite G]

noncomputable local instance maximalFibreIrreducibleCharactersOverAlongFintype
    {A B : Type} [Group A] [Group B] [Finite A]
    (f : B →* A) (eta : IrreducibleCharacter B) :
    Fintype (IrreducibleCharactersOverAlong f eta) := by
  classical
  letI : Fintype (IrreducibleCharacter A) :=
    Fintype.ofFinite _
  unfold IrreducibleCharactersOverAlong
  infer_instance

/-- The sum-of-squared-multiplicities form of the induced-character degree
identity for an invariant normal-subgroup character. -/
theorem sum_sq_restrictionMultiplicity_over_eq_index
    (N : Subgroup G) [N.Normal]
    (theta : IrreducibleCharacter N)
    (hinvariant : ∀ g : G, g • theta = theta) :
    (∑ chi : IrreducibleCharactersOverAlong N.subtype theta,
        restrictionMultiplicity N.subtype theta chi.1 ^ 2) =
      N.index := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (IrreducibleCharacter G) :=
    Fintype.ofFinite _
  letI : Fintype (IrreducibleCharacter N) :=
    Fintype.ofFinite _
  have hdegree :=
    index_mul_degree_eq_sum_restrictionMultiplicity_mul_degree_nat
      N theta
  have hreindex :
      (∑ chi : IrreducibleCharacter G,
          restrictionMultiplicity N.subtype theta chi *
            chi.degree) =
        ∑ chi : IrreducibleCharactersOverAlong N.subtype theta,
          restrictionMultiplicity N.subtype theta chi.1 *
            chi.1.degree := by
    calc
      (∑ chi : IrreducibleCharacter G,
          restrictionMultiplicity N.subtype theta chi *
            chi.degree) =
          ∑ chi : IrreducibleCharacter G,
            if LiesOverAlong N.subtype theta chi then
              restrictionMultiplicity N.subtype theta chi *
                chi.degree
            else 0 := by
        apply Finset.sum_congr rfl
        intro chi _
        by_cases hover :
            LiesOverAlong N.subtype theta chi
        · simp only [hover, ↓reduceIte]
        · have hzero :
              restrictionMultiplicity N.subtype theta chi = 0 := by
            exact Nat.eq_zero_of_not_pos hover
          simp only [hover, ↓reduceIte, hzero, zero_mul]
      _ =
          ∑ chi : IrreducibleCharactersOverAlong N.subtype theta,
            restrictionMultiplicity N.subtype theta chi.1 *
              chi.1.degree := by
        rw [← Finset.sum_filter]
        exact
          Finset.sum_subtype
            (Finset.univ.filter
              (fun chi : IrreducibleCharacter G =>
                LiesOverAlong N.subtype theta chi))
            (by simp)
            (fun chi : IrreducibleCharacter G =>
              restrictionMultiplicity N.subtype theta chi *
                chi.degree)
  have hfactor :
      (∑ chi : IrreducibleCharactersOverAlong N.subtype theta,
          restrictionMultiplicity N.subtype theta chi.1 *
            chi.1.degree) =
        (∑ chi : IrreducibleCharactersOverAlong N.subtype theta,
            restrictionMultiplicity N.subtype theta chi.1 ^ 2) *
          theta.degree := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro chi _
    have hchi :=
      restrictionMultiplicity_mul_degree_eq_degree_of_invariant
        N theta chi.1 hinvariant chi.2
    rw [← hchi]
    simp only [pow_two, mul_assoc]
  apply Nat.eq_of_mul_eq_mul_right theta.degree_pos
  calc
    (∑ chi : IrreducibleCharactersOverAlong N.subtype theta,
          restrictionMultiplicity N.subtype theta chi.1 ^ 2) *
        theta.degree =
        ∑ chi : IrreducibleCharactersOverAlong N.subtype theta,
          restrictionMultiplicity N.subtype theta chi.1 *
            chi.1.degree :=
      hfactor.symm
    _ =
        ∑ chi : IrreducibleCharacter G,
          restrictionMultiplicity N.subtype theta chi *
            chi.degree :=
      hreindex.symm
    _ = N.index * theta.degree :=
      hdegree.symm

/-- The lying-over fibre of an invariant irreducible character has at most
the normal-subgroup index many elements. -/
theorem natCard_irreducibleCharactersOverAlong_le_index
    (N : Subgroup G) [N.Normal]
    (theta : IrreducibleCharacter N)
    (hinvariant : ∀ g : G, g • theta = theta) :
    Nat.card (IrreducibleCharactersOverAlong N.subtype theta) ≤
      N.index := by
  classical
  have hle :
      (∑ _chi : IrreducibleCharactersOverAlong N.subtype theta,
          1) ≤
        ∑ chi : IrreducibleCharactersOverAlong N.subtype theta,
          restrictionMultiplicity N.subtype theta chi.1 ^ 2 := by
    exact Finset.sum_le_sum (fun chi _ => by
      have hpositive :
          0 <
            restrictionMultiplicity N.subtype theta chi.1 :=
        chi.2
      nlinarith)
  calc
    Nat.card
          (IrreducibleCharactersOverAlong N.subtype theta) =
        ∑ _chi : IrreducibleCharactersOverAlong N.subtype theta,
          1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_eq_sum_ones]
    _ ≤
        ∑ chi : IrreducibleCharactersOverAlong N.subtype theta,
          restrictionMultiplicity N.subtype theta chi.1 ^ 2 :=
      hle
    _ = N.index :=
      sum_sq_restrictionMultiplicity_over_eq_index
        N theta hinvariant

/-- If the invariant lying-over fibre has maximal cardinality, every
character in it has restriction multiplicity one. -/
theorem restrictionMultiplicity_eq_one_of_natCard_over_eq_index
    (N : Subgroup G) [N.Normal]
    (theta : IrreducibleCharacter N)
    (hinvariant : ∀ g : G, g • theta = theta)
    (hcard :
      Nat.card (IrreducibleCharactersOverAlong N.subtype theta) =
        N.index)
    (chi : IrreducibleCharactersOverAlong N.subtype theta) :
    restrictionMultiplicity N.subtype theta chi.1 = 1 := by
  classical
  have hsum :
      (∑ _chi : IrreducibleCharactersOverAlong N.subtype theta,
          1) =
        ∑ psi : IrreducibleCharactersOverAlong N.subtype theta,
          restrictionMultiplicity N.subtype theta psi.1 ^ 2 := by
    calc
      (∑ _chi : IrreducibleCharactersOverAlong N.subtype theta,
          1) =
          Nat.card
            (IrreducibleCharactersOverAlong N.subtype theta) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_eq_sum_ones]
      _ = N.index := hcard
      _ =
          ∑ psi : IrreducibleCharactersOverAlong N.subtype theta,
            restrictionMultiplicity N.subtype theta psi.1 ^ 2 :=
        (sum_sq_restrictionMultiplicity_over_eq_index
          N theta hinvariant).symm
  have honeSquare :
      1 =
        restrictionMultiplicity N.subtype theta chi.1 ^ 2 := by
    exact
      (Finset.sum_eq_sum_iff_of_le
        (fun psi _ => by
          have hpositive :
              0 <
                restrictionMultiplicity N.subtype theta psi.1 :=
            psi.2
          nlinarith)).mp hsum chi (Finset.mem_univ chi)
  have hpositive :
      0 <
        restrictionMultiplicity N.subtype theta chi.1 :=
    chi.2
  nlinarith

/-- Maximal lying-over cardinality forces every lying-over irreducible
character to be an exact extension. -/
theorem isExtension_of_natCard_over_eq_index
    (N : Subgroup G) [N.Normal]
    (theta : IrreducibleCharacter N)
    (hinvariant : ∀ g : G, g • theta = theta)
    (hcard :
      Nat.card (IrreducibleCharactersOverAlong N.subtype theta) =
        N.index)
    (chi : IrreducibleCharactersOverAlong N.subtype theta) :
    IrreducibleCharacter.IsExtension N theta chi.1 := by
  apply
    IrreducibleCharacter.IsExtensionAlong.of_liesOver_of_degree_eq
      chi.2
  have hmultiplicity :=
    restrictionMultiplicity_eq_one_of_natCard_over_eq_index
      N theta hinvariant hcard chi
  have hdegree :=
    restrictionMultiplicity_mul_degree_eq_degree_of_invariant
      N theta chi.1 hinvariant chi.2
  simpa [hmultiplicity] using hdegree.symm

/-- Existence form of the maximal-fibre extension criterion. -/
theorem exists_extension_of_natCard_over_eq_index
    (N : Subgroup G) [N.Normal]
    (theta : IrreducibleCharacter N)
    (hinvariant : ∀ g : G, g • theta = theta)
    (hcard :
      Nat.card (IrreducibleCharactersOverAlong N.subtype theta) =
        N.index) :
    ∃ chi : IrreducibleCharacter G,
      IrreducibleCharacter.IsExtension N theta chi := by
  classical
  have hpositive : 0 < N.index :=
    Nat.pos_of_ne_zero N.index_ne_zero_of_finite
  have hfibre :
      Nonempty
        (IrreducibleCharactersOverAlong N.subtype theta) := by
    apply (Nat.card_pos_iff.mp ?_).1
    rw [hcard]
    exact hpositive
  let chi :=
    Classical.choice hfibre
  exact
    ⟨chi.1,
      isExtension_of_natCard_over_eq_index
        N theta hinvariant hcard chi⟩

/-- A finite commutative group has as many irreducible complex characters
as elements. -/
theorem natCard_irreducibleCharacter_eq_card_of_isMulCommutative
    (A : Type) [Group A] [Finite A] [IsMulCommutative A] :
    Nat.card (IrreducibleCharacter A) = Nat.card A := by
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm :=
        isMulCommutative_iff.mp
          (inferInstance : IsMulCommutative A) }
  calc
    Nat.card (IrreducibleCharacter A) =
        Nat.card (ConjClasses A) :=
      ClassFunction.natCard_irreducibleCharacter_eq_conjClasses
    _ = Nat.card A :=
      (Nat.card_congr
        (ConjClasses.mkEquiv (α := A))).symm

/-- Full-fixed-branch cardinality adapter.

Suppose the source lying-over fibre is equivalent to a target fibre over a
normal subgroup with commutative quotient.  If the target normal character
has one extension and the two subgroup indices agree, then the target
Gallagher correspondence makes both fibres have the maximal source size.
Consequently every source lying-over character is an extension.

This is the exact abstract numerical argument in the full-fixed branch of
Okuyama--Wajima's printed induction. -/
theorem isExtension_of_equiv_abelian_extension_fibre
    {H : Type} [Group H] [Finite H]
    (N : Subgroup G) [N.Normal]
    (M : Subgroup H) [M.Normal]
    (theta : IrreducibleCharacter N)
    (phi : IrreducibleCharacter M)
    (hinvariant : ∀ g : G, g • theta = theta)
    [IsMulCommutative (H ⧸ M)]
    (phiExtension : IrreducibleCharacter H)
    (hphiExtension :
      IrreducibleCharacter.IsExtension M phi phiExtension)
    (fibreEquiv :
      IrreducibleCharactersOverAlong N.subtype theta ≃
        IrreducibleCharactersOverAlong M.subtype phi)
    (hindex : N.index = M.index)
    (chi : IrreducibleCharactersOverAlong N.subtype theta) :
    IrreducibleCharacter.IsExtension N theta chi.1 := by
  have htarget :
      Nat.card
          (IrreducibleCharactersOverAlong M.subtype phi) =
        M.index := by
    calc
      Nat.card
            (IrreducibleCharactersOverAlong M.subtype phi) =
          Nat.card (IrreducibleCharacter (H ⧸ M)) :=
        (Nat.card_congr
          (IrreducibleCharacter.gallagherCorrespondence
            hphiExtension)).symm
      _ = Nat.card (H ⧸ M) :=
        natCard_irreducibleCharacter_eq_card_of_isMulCommutative
          (H ⧸ M)
      _ = M.index := by
        rw [M.index_eq_card]
  have hsource :
      Nat.card
          (IrreducibleCharactersOverAlong N.subtype theta) =
        N.index :=
    (Nat.card_congr fibreEquiv).trans
      (htarget.trans hindex.symm)
  exact
    isExtension_of_natCard_over_eq_index
      N theta hinvariant hsource chi

/-- Existence form of the matched abelian-fibre criterion. -/
theorem exists_extension_of_equiv_abelian_extension_fibre
    {H : Type} [Group H] [Finite H]
    (N : Subgroup G) [N.Normal]
    (M : Subgroup H) [M.Normal]
    (theta : IrreducibleCharacter N)
    (phi : IrreducibleCharacter M)
    (hinvariant : ∀ g : G, g • theta = theta)
    [IsMulCommutative (H ⧸ M)]
    (phiExtension : IrreducibleCharacter H)
    (hphiExtension :
      IrreducibleCharacter.IsExtension M phi phiExtension)
    (fibreEquiv :
      IrreducibleCharactersOverAlong N.subtype theta ≃
        IrreducibleCharactersOverAlong M.subtype phi)
    (hindex : N.index = M.index) :
    ∃ chi : IrreducibleCharacter G,
      IrreducibleCharacter.IsExtension N theta chi := by
  classical
  have hfibre :
      Nonempty
        (IrreducibleCharactersOverAlong N.subtype theta) :=
    Nonempty.map fibreEquiv.symm
      ⟨⟨phiExtension, hphiExtension.liesOver⟩⟩
  let chi :=
    Classical.choice hfibre
  exact
    ⟨chi.1,
      isExtension_of_equiv_abelian_extension_fibre
        N M theta phi hinvariant phiExtension hphiExtension
        fibreEquiv hindex chi⟩

/-- Invariant-subfibre form of the full-fixed cardinality squeeze.

The source-side type `I` is intended to be the action-invariant part of a
lying-over fibre.  A 13.29-style equivalence identifies `I` with the full
target fibre, while `toSource` embeds it in the full source fibre.  The
target extension and commutative quotient make `I` have size `M.index`.
If the source and target indices agree, the lower bound from `I` and the
universal Clifford upper bound force the source fibre to be maximal. -/
theorem isExtension_of_invariant_subfibre_equiv_abelian_extension_fibre
    {H I : Type} [Group H] [Finite H] [Finite I]
    (N : Subgroup G) [N.Normal]
    (M : Subgroup H) [M.Normal]
    (theta : IrreducibleCharacter N)
    (phi : IrreducibleCharacter M)
    (hinvariant : ∀ g : G, g • theta = theta)
    [IsMulCommutative (H ⧸ M)]
    (phiExtension : IrreducibleCharacter H)
    (hphiExtension :
      IrreducibleCharacter.IsExtension M phi phiExtension)
    (toSource :
      I →
        IrreducibleCharactersOverAlong N.subtype theta)
    (toSource_injective : Function.Injective toSource)
    (invariantFibreEquiv :
      I ≃ IrreducibleCharactersOverAlong M.subtype phi)
    (hindex : N.index = M.index)
    (chi : IrreducibleCharactersOverAlong N.subtype theta) :
    IrreducibleCharacter.IsExtension N theta chi.1 := by
  have htarget :
      Nat.card
          (IrreducibleCharactersOverAlong M.subtype phi) =
        M.index := by
    calc
      Nat.card
            (IrreducibleCharactersOverAlong M.subtype phi) =
          Nat.card (IrreducibleCharacter (H ⧸ M)) :=
        (Nat.card_congr
          (IrreducibleCharacter.gallagherCorrespondence
            hphiExtension)).symm
      _ = Nat.card (H ⧸ M) :=
        natCard_irreducibleCharacter_eq_card_of_isMulCommutative
          (H ⧸ M)
      _ = M.index := by
        rw [M.index_eq_card]
  have hI :
      Nat.card I = N.index :=
    (Nat.card_congr invariantFibreEquiv).trans
      (htarget.trans hindex.symm)
  have hlower :
      N.index ≤
        Nat.card
          (IrreducibleCharactersOverAlong N.subtype theta) := by
    rw [← hI]
    exact
      Nat.card_le_card_of_injective
        toSource toSource_injective
  have hupper :
      Nat.card
          (IrreducibleCharactersOverAlong N.subtype theta) ≤
        N.index :=
    natCard_irreducibleCharactersOverAlong_le_index
      N theta hinvariant
  have hmax :
      Nat.card
          (IrreducibleCharactersOverAlong N.subtype theta) =
        N.index :=
    Nat.le_antisymm hupper hlower
  exact
    isExtension_of_natCard_over_eq_index
      N theta hinvariant hmax chi

/-- Existence form of the invariant-subfibre cardinality squeeze. -/
theorem exists_extension_of_invariant_subfibre_equiv_abelian_extension_fibre
    {H I : Type} [Group H] [Finite H] [Finite I]
    (N : Subgroup G) [N.Normal]
    (M : Subgroup H) [M.Normal]
    (theta : IrreducibleCharacter N)
    (phi : IrreducibleCharacter M)
    (hinvariant : ∀ g : G, g • theta = theta)
    [IsMulCommutative (H ⧸ M)]
    (phiExtension : IrreducibleCharacter H)
    (hphiExtension :
      IrreducibleCharacter.IsExtension M phi phiExtension)
    (toSource :
      I →
        IrreducibleCharactersOverAlong N.subtype theta)
    (toSource_injective : Function.Injective toSource)
    (invariantFibreEquiv :
      I ≃ IrreducibleCharactersOverAlong M.subtype phi)
    (hindex : N.index = M.index) :
    ∃ chi : IrreducibleCharacter G,
      IrreducibleCharacter.IsExtension N theta chi := by
  classical
  have htargetNonempty :
      Nonempty
        (IrreducibleCharactersOverAlong M.subtype phi) :=
    ⟨⟨phiExtension, hphiExtension.liesOver⟩⟩
  have hINonempty :
      Nonempty I :=
    Nonempty.map invariantFibreEquiv.symm
      htargetNonempty
  let i :=
    Classical.choice hINonempty
  let chi :=
    toSource i
  exact
    ⟨chi.1,
      isExtension_of_invariant_subfibre_equiv_abelian_extension_fibre
        N M theta phi hinvariant phiExtension hphiExtension
        toSource toSource_injective invariantFibreEquiv hindex chi⟩

end CliffordCorrespondence
end McKayConjecture
