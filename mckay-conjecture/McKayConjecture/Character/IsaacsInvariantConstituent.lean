/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.ActionInvariantOver
import McKayConjecture.Character.AutomorphismInertia
import McKayConjecture.Character.ExtensionFromDegree
import McKayConjecture.Character.GallagherCorrespondence
import McKayConjecture.Character.LinearRestrictionMultiplicity
import McKayConjecture.Character.OverAlongTransport
import Mathlib.GroupTheory.Solvable

/-!
# Isaacs's invariant-constituent theorem: exact source boundary

Isaacs, *Character Theory of Finite Groups*, Theorem 13.28, says the
following.  Let a finite group `S` act on a finite group `G`, preserving
`N ◁ G`.  If

* `|S|` is coprime to `|G : N|`,
* `G / N` is solvable, and
* `theta ∈ Irr(N)` is `S`-invariant,

then the induced character `theta ^ G` has an `S`-invariant irreducible
constituent.  By Frobenius reciprocity, the conclusion is exactly the
nonemptiness of the action-invariant part of
`IrreducibleCharactersOverAlong N.subtype theta`.

Okuyama--Wajima use this result on pp. 803--804 in the full-fixed branch
of the proof of their Theorem 2(3).  There `S` is the Sylow `p`-subgroup
`P`; the two ambient groups are `U K` and `U`; and the normal subgroups
are `K` and `L`, respectively.  The displayed equality `C_P(U) = P`
ensures that the quotient-character parameters used by Gallagher are
fixed.

The source-correct formalization in
`OkuyamaWajimaFullFixedBranch.lean` instead uses a shorter cardinality
squeeze based on Theorem 13.29, so it does not depend on the input
isolated here.  This file remains useful as an exact theorem boundary and
as a library of conditional action and Gallagher consequences.

Mathlib and the present repository do not currently contain the
existence argument of Isaacs 13.28.  Accordingly this file introduces
one explicit proposition, `IsaacsInvariantConstituentInput`, which is
precisely the theorem for fixed `S`, `G`, `N`, the action, and `theta`.
It is ordinary data: no new logical primitive or typeclass is introduced.

Everything after that boundary is proved here:

* the source and ambient actions attached to an action preserving `N`;
* conversion between character equality and pointwise value invariance;
* invariance of restriction multiplicity under the simultaneous action;
* extraction of the invariant lying-over character supplied by the input;
* the degree criterion turning such a constituent into an extension; and
* the exact Gallagher consequences for the paper's longer full-fixed route:
  over an abelian quotient every lying-over character is an extension,
  and a fixed base extension together with trivial quotient action makes
  every lying-over character invariant.

The final all-constituents statement is deliberately conditional on the
fixed base extension and the trivial action on `G / N`.  Isaacs 13.28 by
itself asserts existence of one invariant constituent, not invariance of
all constituents.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Theorem 13.28.
* T. Okuyama and M. Wajima, *Character correspondence and p-blocks of
  p-solvable groups*, Osaka J. Math. 17 (1980), 801--806, pp. 803--804.
-/

noncomputable section

namespace McKayConjecture

open CliffordCorrespondence

variable {S G : Type}
variable [Group S] [Group G] [Finite S] [Finite G]
variable (N : Subgroup G) [N.Normal]

namespace IsaacsInvariantConstituent

/-! ## The two actions determined by a subgroup-preserving action -/

/-- Forget that each automorphism in the action preserves `N`. -/
def ambientAction
    (action :
      S →* IrreducibleCharacter.NormalSubgroupAutStabilizer N) :
    S →* MulAut G :=
  (IrreducibleCharacter.NormalSubgroupAutStabilizer N).subtype.comp
    action

/-- Restrict a subgroup-preserving ambient action to `N`. -/
def normalAction
    (action :
      S →* IrreducibleCharacter.NormalSubgroupAutStabilizer N) :
    S →* MulAut N :=
  (IrreducibleCharacter.NormalSubgroupAutStabilizer.restrictionHom
      (N := N)).comp action

omit [Finite S] [Finite G] [N.Normal] in
@[simp]
theorem ambientAction_apply
    (action :
      S →* IrreducibleCharacter.NormalSubgroupAutStabilizer N)
    (s : S) :
    ambientAction N action s = (action s).1 :=
  rfl

omit [Finite S] [Finite G] [N.Normal] in
@[simp]
theorem normalAction_apply
    (action :
      S →* IrreducibleCharacter.NormalSubgroupAutStabilizer N)
    (s : S) :
    normalAction N action s =
      IrreducibleCharacter.NormalSubgroupAutStabilizer.restrict
        (action s) :=
  rfl

/-! ## Fixed-character formulations -/

/-- For an explicitly supplied automorphism, equality under the character
action is equivalent to invariance of values under the direct
automorphism. -/
theorem smul_eq_iff_values_eq
    {H : Type*} [Group H]
    (a : MulAut H) (chi : IrreducibleCharacter H) :
    a • chi = chi ↔
      ∀ h : H, chi.values (a h) = chi.values h := by
  constructor
  · intro hfixed h
    have hinverse : a⁻¹ • chi = chi := by
      calc
        a⁻¹ • chi = a⁻¹ • (a • chi) := by rw [hfixed]
        _ = chi := inv_smul_smul a chi
    have hvalue :=
      congrArg
        (fun psi : IrreducibleCharacter H ↦ psi.values h)
        hinverse
    simpa using hvalue
  · intro hvalues
    apply IrreducibleCharacter.ext
    funext h
    rw [IrreducibleCharacter.smul_values]
    simpa using (hvalues (a.symm h)).symm

omit [Finite S] in
/-- Equality under every automorphism in an explicit action is equivalent
to the usual pointwise invariance of character values. -/
theorem forall_smul_eq_iff_values_eq
    {H : Type*} [Group H]
    (action : S →* MulAut H)
    (chi : IrreducibleCharacter H) :
    (∀ s : S, action s • chi = chi) ↔
      ∀ s : S, ∀ h : H,
        chi.values (action s h) = chi.values h := by
  simp only [smul_eq_iff_values_eq]

/-! ## Simultaneous action and lying over -/

omit [N.Normal] in
/-- Restriction multiplicity is unchanged when an ambient automorphism
preserving `N` acts simultaneously on the source and ambient
characters. -/
theorem restrictionMultiplicity_smul
    (a : IrreducibleCharacter.NormalSubgroupAutStabilizer N)
    (theta : IrreducibleCharacter N)
    (chi : IrreducibleCharacter G) :
    restrictionMultiplicity N.subtype
        (IrreducibleCharacter.NormalSubgroupAutStabilizer.restrict a •
          theta)
        (a.1 • chi) =
      restrictionMultiplicity N.subtype theta chi := by
  let eG : G ≃* G := a.1.symm
  let eN : N ≃* N :=
    (IrreducibleCharacter.NormalSubgroupAutStabilizer.restrict a).symm
  have hcomm :
      eG.toMonoidHom.comp N.subtype =
        N.subtype.comp eN.toMonoidHom := by
    ext n
    exact
      IrreducibleCharacter.NormalSubgroupAutStabilizer.restrict_symm_apply_coe
        a n
  exact
    restrictionMultiplicity_comap_equiv
      eG eN N.subtype N.subtype hcomm theta chi

omit [N.Normal] in
/-- Lying over is unchanged by the simultaneous action. -/
theorem liesOverAlong_smul_iff
    (a : IrreducibleCharacter.NormalSubgroupAutStabilizer N)
    (theta : IrreducibleCharacter N)
    (chi : IrreducibleCharacter G) :
    LiesOverAlong N.subtype
        (IrreducibleCharacter.NormalSubgroupAutStabilizer.restrict a •
          theta)
        (a.1 • chi) ↔
      LiesOverAlong N.subtype theta chi := by
  rw [LiesOverAlong, LiesOverAlong,
    restrictionMultiplicity_smul N a theta chi]

omit [Finite S] [N.Normal] in
/-- If `theta` is fixed, an ambient character lies over `theta` if and
only if each of its action translates does. -/
theorem liesOverAlong_smul_iff_of_theta_invariant
    (action :
      S →* IrreducibleCharacter.NormalSubgroupAutStabilizer N)
    (theta : IrreducibleCharacter N)
    (htheta :
      ∀ s : S, normalAction N action s • theta = theta)
    (s : S) (chi : IrreducibleCharacter G) :
    LiesOverAlong N.subtype theta
        (ambientAction N action s • chi) ↔
      LiesOverAlong N.subtype theta chi := by
  calc
    LiesOverAlong N.subtype theta
          (ambientAction N action s • chi) ↔
        LiesOverAlong N.subtype
          (normalAction N action s • theta)
          (ambientAction N action s • chi) := by
      rw [htheta s]
    _ ↔ LiesOverAlong N.subtype theta chi :=
      liesOverAlong_smul_iff N (action s) theta chi

omit [Finite S] [Finite G] [N.Normal] in
/-- A fixed ambient extension automatically makes its source character
fixed under the restricted action. -/
theorem normal_smul_eq_of_fixed_extension
    (action :
      S →* IrreducibleCharacter.NormalSubgroupAutStabilizer N)
    (theta : IrreducibleCharacter N)
    (psi : IrreducibleCharacter G)
    (hpsi : IrreducibleCharacter.IsExtension N theta psi)
    (hpsiFixed :
      ∀ s : S, ambientAction N action s • psi = psi)
    (s : S) :
    normalAction N action s • theta = theta := by
  apply
    (smul_eq_iff_values_eq
      (normalAction N action s) theta).2
  intro n
  calc
    theta.values (normalAction N action s n) =
        psi.values
          ((normalAction N action s n : N) : G) :=
      (hpsi (normalAction N action s n)).symm
    _ = psi.values (ambientAction N action s (n : G)) := by
      congr 1
    _ = psi.values (n : G) :=
      (smul_eq_iff_values_eq
        (ambientAction N action s) psi).mp
          (hpsiFixed s) (n : G)
    _ = theta.values n := hpsi n

/-! ## The one missing source theorem -/

/-- The exact fixed-parameter input supplied by Isaacs, Theorem 13.28.

The conclusion says that there is an `S`-fixed irreducible character of
`G` lying over `theta`.  The coprimality uses `N.index = |G : N|`, exactly
as in the printed statement.  Solvability is an explicit proposition, not
an inferred typeclass assumption.

This proposition is the only unproved representation-theoretic input in
this file. -/
def IsaacsInvariantConstituentInput
    (action :
      S →* IrreducibleCharacter.NormalSubgroupAutStabilizer N)
    (theta : IrreducibleCharacter N) : Prop :=
  Nat.Coprime (Nat.card S) N.index →
    Group.IsSolvable (G ⧸ N) →
      (∀ s : S, normalAction N action s • theta = theta) →
        Nonempty
          (ActionInvariantIrreducibleCharactersOverAlong
            (ambientAction N action) N.subtype theta)

omit [Finite S] [Finite G] in
/-- Apply the explicit Isaacs 13.28 input.  This named eliminator keeps
the source hypotheses visible at every use site. -/
theorem exists_actionInvariant_over_of_isaacsInput
    (action :
      S →* IrreducibleCharacter.NormalSubgroupAutStabilizer N)
    (theta : IrreducibleCharacter N)
    (hisaacs : IsaacsInvariantConstituentInput N action theta)
    (hcoprime : Nat.Coprime (Nat.card S) N.index)
    (hsolvable : Group.IsSolvable (G ⧸ N))
    (htheta :
      ∀ s : S, normalAction N action s • theta = theta) :
    ∃ chi : IrreducibleCharacter G,
      LiesOverAlong N.subtype theta chi ∧
        ∀ s : S, ambientAction N action s • chi = chi := by
  obtain ⟨chi⟩ :=
    hisaacs hcoprime hsolvable htheta
  exact ⟨chi.1.1, chi.1.2, chi.2⟩

omit [Finite S] [Finite G] in
/-- Pointwise-value form of the Isaacs 13.28 conclusion. -/
theorem exists_values_invariant_over_of_isaacsInput
    (action :
      S →* IrreducibleCharacter.NormalSubgroupAutStabilizer N)
    (theta : IrreducibleCharacter N)
    (hisaacs : IsaacsInvariantConstituentInput N action theta)
    (hcoprime : Nat.Coprime (Nat.card S) N.index)
    (hsolvable : Group.IsSolvable (G ⧸ N))
    (htheta :
      ∀ s : S, normalAction N action s • theta = theta) :
    ∃ chi : IrreducibleCharacter G,
      0 < restrictionMultiplicity N.subtype theta chi ∧
        ∀ s : S, ∀ g : G,
          chi.values (ambientAction N action s g) =
            chi.values g := by
  obtain ⟨chi, hover, hinvariant⟩ :=
    exists_actionInvariant_over_of_isaacsInput
      N action theta hisaacs hcoprime hsolvable htheta
  exact
    ⟨chi, hover,
      (forall_smul_eq_iff_values_eq
        (ambientAction N action) chi).mp hinvariant⟩

/-! ## Degree and extension consequences -/

omit [Finite S] [Finite G] in
/-- An Isaacs invariant constituent of the same degree as `theta` is an
actual extension of `theta`. -/
theorem exists_actionInvariant_extension_of_isaacsInput_of_degree
    (action :
      S →* IrreducibleCharacter.NormalSubgroupAutStabilizer N)
    (theta : IrreducibleCharacter N)
    (hisaacs : IsaacsInvariantConstituentInput N action theta)
    (hcoprime : Nat.Coprime (Nat.card S) N.index)
    (hsolvable : Group.IsSolvable (G ⧸ N))
    (htheta :
      ∀ s : S, normalAction N action s • theta = theta)
    (hdegree :
      ∀ chi : IrreducibleCharacter G,
        LiesOverAlong N.subtype theta chi →
          (∀ s : S, ambientAction N action s • chi = chi) →
            chi.degree = theta.degree) :
    ∃ chi : IrreducibleCharacter G,
      IrreducibleCharacter.IsExtension N theta chi ∧
        ∀ s : S, ambientAction N action s • chi = chi := by
  obtain ⟨chi, hover, hinvariant⟩ :=
    exists_actionInvariant_over_of_isaacsInput
      N action theta hisaacs hcoprime hsolvable htheta
  exact
    ⟨chi,
      IrreducibleCharacter.IsExtensionAlong.of_liesOver_of_degree_eq
        hover (hdegree chi hover hinvariant),
      hinvariant⟩

/-- If an extension of `theta` exists and `G / N` is commutative, every
irreducible character lying over `theta` is itself an extension.

This is the Gallagher step used by Okuyama--Wajima after their cardinality
comparison.  The proof via the existing full Gallagher correspondence is
more direct: every quotient irreducible has degree one. -/
theorem isExtension_of_liesOver_of_extension_of_quotient_commutative
    [IsMulCommutative (G ⧸ N)]
    (theta : IrreducibleCharacter N)
    (psi : IrreducibleCharacter G)
    (hpsi : IrreducibleCharacter.IsExtension N theta psi)
    (chi : IrreducibleCharactersOverAlong N.subtype theta) :
    IrreducibleCharacter.IsExtension N theta chi.1 := by
  let beta : IrreducibleCharacter (G ⧸ N) :=
    IrreducibleCharacter.gallagherInverse hpsi chi
  have hcharacter :
      IrreducibleCharacter.gallagherTensorCharacter hpsi beta =
        chi.1 := by
    exact congrArg Subtype.val
      (IrreducibleCharacter.gallagherForward_inverse hpsi chi)
  apply
    IrreducibleCharacter.IsExtensionAlong.of_liesOver_of_degree_eq
      chi.2
  rw [← hcharacter,
    IrreducibleCharacter.gallagherTensorCharacter_degree,
    hpsi.degree_eq,
    IrreducibleCharacter.degree_eq_one_of_isMulCommutative beta,
    mul_one]

/-! ## A conditional all-constituents route -/

omit [Finite S] in
/-- If a chosen extension is fixed by the ambient action and the action
is trivial on the quotient `G / N`, every Gallagher character above
`theta` is fixed.

The quotient hypothesis is stated directly on quotient-map values.  This
is exactly what the equality `C_P(U) = P` supplies in the full-fixed
Okuyama--Wajima branch; no stronger assertion that the ambient action on
`G` is trivial is used. -/
theorem forall_liesOver_smul_eq_of_fixed_extension_of_quotient_action_trivial
    (action :
      S →* IrreducibleCharacter.NormalSubgroupAutStabilizer N)
    (theta : IrreducibleCharacter N)
    (psi : IrreducibleCharacter G)
    (hpsi : IrreducibleCharacter.IsExtension N theta psi)
    (hpsiFixed :
      ∀ s : S, ambientAction N action s • psi = psi)
    (hquotient :
      ∀ s : S, ∀ g : G,
        QuotientGroup.mk' N (ambientAction N action s g) =
          QuotientGroup.mk' N g)
    (chi : IrreducibleCharactersOverAlong N.subtype theta)
    (s : S) :
    ambientAction N action s • chi.1 = chi.1 := by
  let beta : IrreducibleCharacter (G ⧸ N) :=
    IrreducibleCharacter.gallagherInverse hpsi chi
  have hcharacter :
      IrreducibleCharacter.gallagherTensorCharacter hpsi beta =
        chi.1 := by
    exact congrArg Subtype.val
      (IrreducibleCharacter.gallagherForward_inverse hpsi chi)
  apply IrreducibleCharacter.ext
  funext g
  rw [IrreducibleCharacter.smul_values,
    ← hcharacter,
    IrreducibleCharacter.gallagherTensorCharacter_values,
    IrreducibleCharacter.gallagherTensorCharacter_values]
  have hpsiValue :=
    congrArg
      (fun rho : IrreducibleCharacter G ↦ rho.values g)
      (hpsiFixed s)
  rw [IrreducibleCharacter.smul_values] at hpsiValue
  have hquotientInverse :
      QuotientGroup.mk' N
          ((ambientAction N action s).symm g) =
        QuotientGroup.mk' N g := by
    change
      QuotientGroup.mk' N
          ((ambientAction N action s)⁻¹ g) =
        QuotientGroup.mk' N g
    simpa only [map_inv] using hquotient s⁻¹ g
  rw [hpsiValue, hquotientInverse]

/-- Subtype form of the preceding all-constituents theorem. -/
def actionInvariantOfLiesOverOfFixedExtension
    (action :
      S →* IrreducibleCharacter.NormalSubgroupAutStabilizer N)
    (theta : IrreducibleCharacter N)
    (psi : IrreducibleCharacter G)
    (hpsi : IrreducibleCharacter.IsExtension N theta psi)
    (hpsiFixed :
      ∀ s : S, ambientAction N action s • psi = psi)
    (hquotient :
      ∀ s : S, ∀ g : G,
        QuotientGroup.mk' N (ambientAction N action s g) =
          QuotientGroup.mk' N g)
    (chi : IrreducibleCharactersOverAlong N.subtype theta) :
    ActionInvariantIrreducibleCharactersOverAlong
      (ambientAction N action) N.subtype theta :=
  ⟨chi,
    forall_liesOver_smul_eq_of_fixed_extension_of_quotient_action_trivial
      N action theta psi hpsi hpsiFixed hquotient chi⟩

/-- In the full-fixed branch, forgetting the now-automatic invariance
proof is an equivalence from the invariant fibre to the whole
lying-over fibre. -/
def actionInvariantIrreducibleCharactersOverAlongEquivOfFixedExtension
    (action :
      S →* IrreducibleCharacter.NormalSubgroupAutStabilizer N)
    (theta : IrreducibleCharacter N)
    (psi : IrreducibleCharacter G)
    (hpsi : IrreducibleCharacter.IsExtension N theta psi)
    (hpsiFixed :
      ∀ s : S, ambientAction N action s • psi = psi)
    (hquotient :
      ∀ s : S, ∀ g : G,
        QuotientGroup.mk' N (ambientAction N action s g) =
          QuotientGroup.mk' N g) :
    ActionInvariantIrreducibleCharactersOverAlong
        (ambientAction N action) N.subtype theta ≃
      IrreducibleCharactersOverAlong N.subtype theta where
  toFun chi := chi.1
  invFun :=
    actionInvariantOfLiesOverOfFixedExtension
      N action theta psi hpsi hpsiFixed hquotient
  left_inv chi := by
    apply Subtype.ext
    rfl
  right_inv chi := rfl

omit [Finite S] in
/-- The full-fixed hypotheses make the invariant lying-over fibre and the
ordinary lying-over fibre equinumerous. -/
theorem natCard_actionInvariantIrreducibleCharactersOverAlong_eq_of_fixedExtension
    (action :
      S →* IrreducibleCharacter.NormalSubgroupAutStabilizer N)
    (theta : IrreducibleCharacter N)
    (psi : IrreducibleCharacter G)
    (hpsi : IrreducibleCharacter.IsExtension N theta psi)
    (hpsiFixed :
      ∀ s : S, ambientAction N action s • psi = psi)
    (hquotient :
      ∀ s : S, ∀ g : G,
        QuotientGroup.mk' N (ambientAction N action s g) =
          QuotientGroup.mk' N g) :
    Nat.card
        (ActionInvariantIrreducibleCharactersOverAlong
          (ambientAction N action) N.subtype theta) =
      Nat.card
        (IrreducibleCharactersOverAlong N.subtype theta) :=
  Nat.card_congr
    (actionInvariantIrreducibleCharactersOverAlongEquivOfFixedExtension
      N action theta psi hpsi hpsiFixed hquotient)

end IsaacsInvariantConstituent

end McKayConjecture
