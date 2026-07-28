/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.EndopermutationModule
import McKayConjecture.Character.EndomorphismPermutationBasis
import McKayConjecture.Character.PermutationAlgebraBrauerQuotientBasis

/-!
# Endopermutation modules

An endopermutation module is a linear action of a finite `p`-group
whose conjugation action on the endomorphism algebra has a permutation
basis.  Unlike `PointedEndopermutationModule`, the basis is not required
to contain the identity endomorphism.

The predicate `EndopermutationModule.IsCapped` says that the Brauer
quotient of the conjugation endomorphism algebra is nontrivial.  The
permutation-basis description of Brauer quotients shows that a globally
fixed index in the endomorphism basis implies cappedness.  In
particular, a permutation module with a globally fixed basis index is
capped: the corresponding diagonal matrix unit is fixed.
-/

noncomputable section

namespace Representation

section Definition

variable (p : ℕ) [Fact p.Prime]
variable (k P V : Type)
variable [Field k] [CharP k p]
variable [Group P] [Finite P]
variable [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V]

/-- An unpointed endopermutation module for a finite `p`-group.

The action on the basis indices is stored as data and installed only
locally.  This avoids exporting competing action instances from the
structure. -/
structure EndopermutationModule where
  /-- The linear action on the module. -/
  action : P →* (V ≃ₗ[k] V)
  /-- The acting group is a `p`-group. -/
  isPGroup : IsPGroup p P
  /-- Index type for the permutation basis of the endomorphism algebra. -/
  index : Type
  /-- The permutation action on the endomorphism-basis indices. -/
  indexAction : MulAction P index
  /-- A permutation basis of the conjugation endomorphism algebra. -/
  permutationBasis :
    letI : MulAction P index :=
      indexAction
    letI :=
      endomorphismConjugationMulSemiringAction action
    letI :=
      endomorphismConjugation_smulCommClass action
    PermutationModuleBasis
      (k := k) (P := P) (V := Module.End k V)
      (ι := index)

end Definition

namespace EndopermutationModule

variable
  {p k P V}
  [hp : Fact p.Prime]
  [hk : Field k] [hchar : CharP k p]
  [hP : Group P] [hPfin : Finite P]
  [hV : AddCommGroup V] [hmod : Module k V]
  [hVfin : FiniteDimensional k V]

/-- The Brauer quotient of the conjugation endomorphism algebra. -/
abbrev EndomorphismBrauerQuotient
    (M : EndopermutationModule p k P V) :
    Type :=
  letI : Fintype P :=
    Fintype.ofFinite P
  letI :=
    endomorphismConjugationMulSemiringAction M.action
  letI :=
    endomorphismConjugation_smulCommClass M.action
  BrauerQuotientAlgebra
    (k := k) (P := P) (A := Module.End k V)

/-- An endopermutation module is capped when the Brauer quotient of
its conjugation endomorphism algebra is nontrivial. -/
def IsCapped
    (M : EndopermutationModule p k P V) :
    Prop :=
  Nontrivial M.EndomorphismBrauerQuotient

/-- Indices in the chosen endomorphism basis fixed by the whole group. -/
abbrev FixedIndex
    (M : EndopermutationModule p k P V) :
    Type :=
  letI : MulAction P M.index :=
    M.indexAction
  MulAction.fixedPoints P M.index

omit hp hchar hVfin in
/-- Cappedness is equivalent to properness of the Brauer trace ideal. -/
theorem isCapped_iff_brauerTraceIdeal_ne_top
    (M : EndopermutationModule p k P V) :
    M.IsCapped ↔
      letI : Fintype P :=
        Fintype.ofFinite P
      letI :=
        endomorphismConjugationMulSemiringAction M.action
      letI :=
        endomorphismConjugation_smulCommClass M.action
      brauerTraceIdeal
          (k := k) (P := P) (A := Module.End k V) ≠
        ⊤ := by
  letI : Fintype P :=
    Fintype.ofFinite P
  letI :=
    endomorphismConjugationMulSemiringAction M.action
  letI :=
    endomorphismConjugation_smulCommClass M.action
  exact Ideal.Quotient.nontrivial_iff

/-- A globally fixed index in the endomorphism permutation basis
survives in the Brauer quotient, so the module is capped. -/
theorem isCapped_of_nonempty_fixedIndex
    (M : EndopermutationModule p k P V)
    (hfixed : Nonempty M.FixedIndex) :
    M.IsCapped := by
  letI : Fintype P :=
    Fintype.ofFinite P
  letI : MulAction P M.index :=
    M.indexAction
  letI :=
    endomorphismConjugationMulSemiringAction M.action
  letI :=
    endomorphismConjugation_smulCommClass M.action
  letI : Fintype M.index :=
    FiniteDimensional.fintypeBasisIndex
      M.permutationBasis.basis
  letI : Fintype M.FixedIndex :=
    Fintype.ofFinite M.FixedIndex
  have hfinrank :
      0 <
        Module.finrank k
          (BrauerQuotient
            M.permutationBasis.representation) := by
    rw [
      M.permutationBasis.finrank_brauerQuotient_eq_card_fixedPoints
        M.isPGroup]
    exact Fintype.card_pos_iff.mpr hfixed
  letI hpermutationQuotient :
      Nontrivial
        (BrauerQuotient
          M.permutationBasis.representation) :=
    Module.nontrivial_of_finrank_pos hfinrank
  have hrepresentation :
      M.permutationBasis.representation =
        algebraActionRepresentation
          (k := k) (P := P) (A := Module.End k V) := by
    ext g f
    rfl
  let representationQuotientEquiv :=
    PointedPermutationAlgebraBasis.brauerQuotientEquivOfRepresentationEq
      hrepresentation
  letI algebraActionQuotient :
      Nontrivial
        (BrauerQuotient
          (algebraActionRepresentation
            (k := k) (P := P)
            (A := Module.End k V))) :=
    representationQuotientEquiv.injective.nontrivial
  change
    Nontrivial
      (BrauerQuotientAlgebra
        (k := k) (P := P) (A := Module.End k V))
  exact
    Function.Injective.nontrivial
      (PointedPermutationAlgebraBasis.brauerQuotientAlgebraEquivBrauerQuotient
          (k := k) (P := P)
          (A := Module.End k V)).symm.injective

/-- Cappedness is detected exactly by a globally fixed index in any
chosen permutation basis of the conjugation endomorphism algebra. -/
theorem isCapped_iff_nonempty_fixedIndex
    (M : EndopermutationModule p k P V) :
    M.IsCapped ↔ Nonempty M.FixedIndex := by
  refine ⟨?_, M.isCapped_of_nonempty_fixedIndex⟩
  intro hcap
  letI : Fintype P :=
    Fintype.ofFinite P
  letI : MulAction P M.index :=
    M.indexAction
  letI :=
    endomorphismConjugationMulSemiringAction M.action
  letI :=
    endomorphismConjugation_smulCommClass M.action
  letI : Fintype M.index :=
    FiniteDimensional.fintypeBasisIndex
      M.permutationBasis.basis
  letI : Fintype M.FixedIndex :=
    Fintype.ofFinite M.FixedIndex
  letI algebraQuotientNontrivial :
      Nontrivial
        (BrauerQuotientAlgebra
          (k := k) (P := P) (A := Module.End k V)) :=
    hcap
  have hrepresentation :
      M.permutationBasis.representation =
        algebraActionRepresentation
          (k := k) (P := P) (A := Module.End k V) := by
    ext g f
    rfl
  let quotientEquiv :
      BrauerQuotientAlgebra
          (k := k) (P := P) (A := Module.End k V) ≃ₗ[k]
        BrauerQuotient M.permutationBasis.representation :=
    (PointedPermutationAlgebraBasis.brauerQuotientAlgebraEquivBrauerQuotient
      (k := k) (P := P) (A := Module.End k V)).trans
      (PointedPermutationAlgebraBasis.brauerQuotientEquivOfRepresentationEq
        hrepresentation.symm)
  letI permutationQuotientNontrivial :
      Nontrivial
        (BrauerQuotient M.permutationBasis.representation) :=
    quotientEquiv.injective.nontrivial
  have hpositive :
      0 <
        Module.finrank k
          (BrauerQuotient
            M.permutationBasis.representation) :=
    Module.finrank_pos
  rw [
    M.permutationBasis.finrank_brauerQuotient_eq_card_fixedPoints
      M.isPGroup] at hpositive
  exact Fintype.card_pos_iff.mp hpositive

end EndopermutationModule

namespace PointedEndopermutationModule

variable
  {p k P V}
  [hp : Fact p.Prime]
  [hk : Field k] [hchar : CharP k p]
  [hP : Group P] [hPfin : Finite P]
  [hV : AddCommGroup V] [hmod : Module k V]
  [hVfin : FiniteDimensional k V] [hVne : Nontrivial V]

/-- Forget the distinguished identity vector in a pointed
endopermutation basis. -/
def toEndopermutationModule
    (M : PointedEndopermutationModule p k P V) :
    EndopermutationModule p k P V := by
  letI :=
    endomorphismConjugationMulSemiringAction M.action
  letI :=
    endomorphismConjugation_smulCommClass M.action
  exact
    { action := M.action
      isPGroup := M.isPGroup
      index := M.permutationBasis.index
      indexAction :=
        PointedPermutationAlgebraBasis.indexMulAction
          (B := M.permutationBasis)
      permutationBasis := by
        letI : MulAction P M.permutationBasis.index :=
          PointedPermutationAlgebraBasis.indexMulAction
            (B := M.permutationBasis)
        exact M.permutationBasis.toPermutationModuleBasis }

omit hp hchar hPfin hVfin hVne in
@[simp]
theorem toEndopermutationModule_action
    (M : PointedEndopermutationModule p k P V) :
    M.toEndopermutationModule.action = M.action :=
  rfl

omit hp hchar hPfin hVfin hVne in
@[simp]
theorem toEndopermutationModule_isPGroup
    (M : PointedEndopermutationModule p k P V) :
    M.toEndopermutationModule.isPGroup = M.isPGroup :=
  rfl

omit hVne in
/-- Every pointed endopermutation module is capped after forgetting
the point.  The distinguished identity index is globally fixed. -/
theorem toEndopermutationModule_isCapped
    (M : PointedEndopermutationModule p k P V) :
    M.toEndopermutationModule.IsCapped := by
  letI :=
    endomorphismConjugationMulSemiringAction M.action
  letI :=
    endomorphismConjugation_smulCommClass M.action
  apply
    EndopermutationModule.isCapped_of_nonempty_fixedIndex
      M.toEndopermutationModule
  refine
    ⟨⟨M.permutationBasis.oneIndex, ?_⟩⟩
  intro g
  exact M.permutationBasis.indexAction_oneIndex g

end PointedEndopermutationModule

namespace PermutationModuleBasis

variable
  {p : ℕ} [hp : Fact p.Prime]
  {k P V ι : Type}
  [hk : Field k] [hchar : CharP k p]
  [hP : Group P] [hPfin : Finite P]
  [hV : AddCommGroup V] [hmod : Module k V]
  [hVfin : FiniteDimensional k V]
  [hVaction : DistribMulAction P V]
  [hVscalar : SMulCommClass P k V]
  [hιaction : MulAction P ι] [hιfin : Finite ι]

/-- A permutation basis on a module induces an unpointed
endopermutation structure via its matrix-unit basis. -/
def toEndopermutationModule
    (B : PermutationModuleBasis
      (k := k) (P := P) (V := V) (ι := ι))
    (hPgroup : IsPGroup p P) :
    EndopermutationModule p k P V where
  action :=
    representationLinearAction B.representation
  isPGroup := hPgroup
  index := ι × ι
  indexAction := inferInstance
  permutationBasis := by
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction B.representation)
    letI :=
      endomorphismConjugation_smulCommClass
        (representationLinearAction B.representation)
    exact B.endomorphism

omit hp hchar hPfin hVfin in
@[simp]
theorem toEndopermutationModule_action
    (B : PermutationModuleBasis
      (k := k) (P := P) (V := V) (ι := ι))
    (hPgroup : IsPGroup p P) :
    (B.toEndopermutationModule hPgroup).action =
      representationLinearAction B.representation :=
  rfl

/-- A fixed module-basis index gives a fixed diagonal matrix-unit
index in the induced endomorphism permutation basis. -/
def diagonalFixedIndex
    (B : PermutationModuleBasis
      (k := k) (P := P) (V := V) (ι := ι))
    (hPgroup : IsPGroup p P)
    (i : MulAction.fixedPoints P ι) :
    (B.toEndopermutationModule hPgroup).FixedIndex :=
  ⟨((i : ι), (i : ι)), fun g => by
    apply Prod.ext
    · exact i.property g
    · exact i.property g⟩

omit hp hchar hPfin hVfin in
@[simp]
theorem diagonalFixedIndex_coe
    (B : PermutationModuleBasis
      (k := k) (P := P) (V := V) (ι := ι))
    (hPgroup : IsPGroup p P)
    (i : MulAction.fixedPoints P ι) :
    (B.diagonalFixedIndex hPgroup i :
      (B.toEndopermutationModule hPgroup).index) =
      ((i : ι), (i : ι)) :=
  rfl

/-- A permutation module with at least one globally fixed basis index
is capped. -/
theorem toEndopermutationModule_isCapped_of_nonempty_fixedPoints
    (B : PermutationModuleBasis
      (k := k) (P := P) (V := V) (ι := ι))
    (hPgroup : IsPGroup p P)
    (hfixed :
      Nonempty (MulAction.fixedPoints P ι)) :
    (B.toEndopermutationModule hPgroup).IsCapped :=
  EndopermutationModule.isCapped_of_nonempty_fixedIndex
    (B.toEndopermutationModule hPgroup)
    (hfixed.map (B.diagonalFixedIndex hPgroup))

end PermutationModuleBasis

end Representation
