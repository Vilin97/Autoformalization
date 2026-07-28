/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.AssociatedUniqueness
import McKayConjecture.CharacterTriple.Butterfly

/-!
# Unconditional projective coherence in the Butterfly diagram

This file derives the projective coherence used by the Butterfly theorem.
The proof chooses, for each element of the new Butterfly subgroup, an old
representative inducing the same automorphism of the normal subgroup.  The
defect of this set-theoretic section lies in the centralizer.  The scalar
agreement in the old central-isomorphism witness then makes the two induced
projective multiplication laws agree.
-/

noncomputable section

open CategoryTheory

universe u u' v v'

namespace McKayConjecture
namespace CharacterTriple

section Representatives

variable {A : Type u} {A' : Type u'} {B : Type v} {B' : Type v'}
  [Finite A] [Finite A'] [Finite B] [Finite B']
  [Group A] [Group A'] [Group B] [Group B']
variable {T : CharacterTriple A} {T' : CharacterTriple A'}
  {U : CharacterTriple B} {U' : CharacterTriple B'}
variable {V W : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]
variable (C : CentralIsomorphismWitness T U V W)
  (D : ButterflySubgroupDiagram C T' U')

namespace ButterflySubgroupDiagram

/-- A set-theoretic old representative for an element of the new
Butterfly subgroup. -/
def oldRepresentative (b : B') : B :=
  Classical.choose (by
    have hb :
        D.embedding b ∈
          butterflySubgroup C D.normalEquiv := by
      rw [← D.pullback_eq]
      exact ⟨b, rfl⟩
    exact
      (mem_butterflySubgroup_iff
        C D.normalEquiv (D.embedding b)).mp hb)

/-- The chosen old representative induces the same automorphism of the
identified left normal subgroup. -/
theorem oldRepresentative_action (b : B') :
    C.rightConjugationAction (D.oldRepresentative C b) =
      T.conjugationActionAlong T' D.normalEquiv
        (D.embedding b) :=
  Classical.choose_spec (by
    have hb :
        D.embedding b ∈
          butterflySubgroup C D.normalEquiv := by
      rw [← D.pullback_eq]
      exact ⟨b, rfl⟩
    exact
      (mem_butterflySubgroup_iff
        C D.normalEquiv (D.embedding b)).mp hb)

/-- Multiplicative defect of the chosen set-theoretic representatives. -/
def oldRepresentativeDefect (g h : B') : B :=
  D.oldRepresentative C g *
    D.oldRepresentative C h *
      (D.oldRepresentative C (g * h))⁻¹

/-- The representative defect acts trivially on the old left normal
subgroup. -/
theorem oldRepresentativeDefect_action_eq_one (g h : B') :
    C.rightConjugationAction
        (D.oldRepresentativeDefect C g h) = 1 := by
  rw [oldRepresentativeDefect, map_mul, map_mul, map_inv,
    D.oldRepresentative_action C,
    D.oldRepresentative_action C,
    D.oldRepresentative_action C]
  let f :=
    T.conjugationActionAlong T' D.normalEquiv
  change
    f (D.embedding g) * f (D.embedding h) *
        (f (D.embedding (g * h)))⁻¹ = 1
  rw [map_mul D.embedding g h, map_mul f]
  simp

/-- Hence the image of the representative defect lies in the old
centralizer. -/
theorem oldRepresentativeDefect_mem_centralizer (g h : B') :
    C.embedding (D.oldRepresentativeDefect C g h) ∈
      Subgroup.centralizer (T.normalSubgroup : Set A) := by
  rw [← T.conjugationAction_eq_one_iff]
  exact D.oldRepresentativeDefect_action_eq_one C g h

/-- A new Butterfly element and its chosen old representative induce the
same automorphism after identifying the left normal groups. -/
theorem left_inducesSameAutomorphism (b : B') :
    AssociatedProjectiveRepresentation.InducesSameAutomorphism
      D.normalEquiv (D.embedding b)
        (C.embedding (D.oldRepresentative C b)) := by
  intro x
  have h :=
    DFunLike.congr_fun
      (D.oldRepresentative_action C b)
      (D.normalEquiv x)
  calc
    D.normalEquiv (MulAut.conjNormal (D.embedding b) x) =
        (T.conjugationActionAlong T' D.normalEquiv
          (D.embedding b)) (D.normalEquiv x) :=
      by
        simp [conjugationActionAlong, MulAut.congr]
    _ =
        C.rightConjugationAction
          (D.oldRepresentative C b) (D.normalEquiv x) :=
      h.symm
    _ =
        MulAut.conjNormal
          (C.embedding (D.oldRepresentative C b))
          (D.normalEquiv x) :=
      rfl

/-- Conjugation of the new right normal subgroup agrees with conjugation
after embedding it into the new left normal subgroup. -/
theorem newRightNormalInLeft_conj
    (b : B') (m : U'.normalSubgroup) :
    newRightNormalInLeft C D (MulAut.conjNormal b m) =
      MulAut.conjNormal (D.embedding b)
        (newRightNormalInLeft C D m) := by
  ext
  change
    D.embedding (b * (m : B') * b⁻¹) =
      D.embedding b * D.embedding m *
        (D.embedding b)⁻¹
  simp

/-- The same chosen representative also induces the matching automorphism
on the identified right normal groups. -/
theorem right_inducesSameAutomorphism
    (hchar : D.CharacterCoherence C) (b : B') :
    AssociatedProjectiveRepresentation.InducesSameAutomorphism
      hchar.rightNormalEquiv b
        (D.oldRepresentative C b) := by
  intro m
  apply Subtype.ext
  apply C.embedding_injective
  have hleft :=
    D.left_inducesSameAutomorphism C b
      (newRightNormalInLeft C D m)
  have hcomm :=
    hchar.normal_embedding_commutes m
  have hcommConj :=
    hchar.normal_embedding_commutes
      (MulAut.conjNormal b m)
  calc
    C.embedding
        (hchar.rightNormalEquiv
          (MulAut.conjNormal b m)) =
      (D.normalEquiv
        (newRightNormalInLeft C D
          (MulAut.conjNormal b m)) : A) := by
        exact (congrArg Subtype.val hcommConj).symm
    _ =
      (D.normalEquiv
        (MulAut.conjNormal (D.embedding b)
          (newRightNormalInLeft C D m)) : A) := by
        rw [D.newRightNormalInLeft_conj C]
    _ =
      (MulAut.conjNormal
        (C.embedding (D.oldRepresentative C b))
        (D.normalEquiv
          (newRightNormalInLeft C D m)) :
          T.normalSubgroup) := by
        exact congrArg Subtype.val hleft
    _ =
      (MulAut.conjNormal
        (C.embedding (D.oldRepresentative C b))
        (oldRightNormalInLeft C
          (hchar.rightNormalEquiv m)) :
          T.normalSubgroup) := by
        rw [hcomm]
    _ =
      C.embedding
        (MulAut.conjNormal
          (D.oldRepresentative C b)
          (hchar.rightNormalEquiv m)) := by
        change
          C.embedding (D.oldRepresentative C b) *
              C.embedding (hchar.rightNormalEquiv m) *
                (C.embedding (D.oldRepresentative C b))⁻¹ =
            C.embedding
              (D.oldRepresentative C b *
                hchar.rightNormalEquiv m *
                  (D.oldRepresentative C b)⁻¹)
        simp

end ButterflySubgroupDiagram
end Representatives

section ComparisonScalars

variable {A : Type u} {A' : Type u'} {B : Type v} {B' : Type v'}
  [Finite A] [Finite A'] [Finite B] [Finite B']
  [Group A] [Group A'] [Group B] [Group B']
variable {T : CharacterTriple A} {T' : CharacterTriple A'}
  {U : CharacterTriple B} {U' : CharacterTriple B'}
variable {V W V' W' : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]
  [AddCommGroup V'] [Module ℂ V'] [Module.Finite ℂ V'] [Nontrivial V']
  [AddCommGroup W'] [Module ℂ W'] [Module.Finite ℂ W'] [Nontrivial W']
variable (C : CentralIsomorphismWitness T U V W)
  (D : ButterflySubgroupDiagram C T' U')
variable (P' : ProjectiveRepresentation ℂ A' V')
  (Q' : ProjectiveRepresentation ℂ B' W')
variable (R' : AssociatedProjectiveRepresentation T' V' P')
  (S' : AssociatedProjectiveRepresentation U' W' Q')
variable (hchar : D.CharacterCoherence C)

namespace ButterflySubgroupDiagram

/-- Identification of the new and old left normal-character
representations. -/
def leftRestrictionEquiv :
    Representation.Equiv
      (linearRepresentationOfAction R'.restriction)
      (linearRepresentationOfAction
        (C.leftAssociated.restriction.comp
          D.normalEquiv.toMonoidHom)) :=
  AssociatedProjectiveRepresentation.restrictionEquivAlong
    R' C.leftAssociated D.normalEquiv
      hchar.left_character_agreement

/-- Identification of the new and old right normal-character
representations. -/
def rightRestrictionEquiv :
    Representation.Equiv
      (linearRepresentationOfAction S'.restriction)
      (linearRepresentationOfAction
        (C.rightAssociated.restriction.comp
          hchar.rightNormalEquiv.toMonoidHom)) :=
  AssociatedProjectiveRepresentation.restrictionEquivAlong
    S' C.rightAssociated hchar.rightNormalEquiv
      hchar.right_character_agreement

/-- Scalar comparing the new left operator with the old left operator at a
chosen representative. -/
def leftComparisonScalar (b : B') : ℂˣ :=
  Classical.choose
    (AssociatedProjectiveRepresentation.exists_operator_scalar_along
      R' C.leftAssociated D.normalEquiv
      (D.leftRestrictionEquiv C P' R' hchar)
      (D.embedding b)
      (C.embedding (D.oldRepresentative C b))
      (D.left_inducesSameAutomorphism C b))

/-- Defining identity for the left comparison scalar. -/
theorem leftComparisonScalar_spec (b : B') (z : V') :
    D.leftRestrictionEquiv C P' R' hchar
        (P'.operator (D.embedding b) z) =
      (D.leftComparisonScalar C P' R' hchar b : ℂ) •
        C.leftProjective.operator
          (C.embedding (D.oldRepresentative C b))
          (D.leftRestrictionEquiv C P' R' hchar z) :=
  Classical.choose_spec
    (AssociatedProjectiveRepresentation.exists_operator_scalar_along
      R' C.leftAssociated D.normalEquiv
      (D.leftRestrictionEquiv C P' R' hchar)
      (D.embedding b)
      (C.embedding (D.oldRepresentative C b))
      (D.left_inducesSameAutomorphism C b)) z

/-- Scalar comparing the new right operator with the old right operator at
the same chosen representative. -/
def rightComparisonScalar (b : B') : ℂˣ :=
  Classical.choose
    (AssociatedProjectiveRepresentation.exists_operator_scalar_along
      S' C.rightAssociated hchar.rightNormalEquiv
      (D.rightRestrictionEquiv C Q' S' hchar)
      b (D.oldRepresentative C b)
      (D.right_inducesSameAutomorphism C hchar b))

/-- Defining identity for the right comparison scalar. -/
theorem rightComparisonScalar_spec (b : B') (z : W') :
    D.rightRestrictionEquiv C Q' S' hchar
        (Q'.operator b z) =
      (D.rightComparisonScalar C Q' S' hchar b : ℂ) •
        C.rightProjective.operator
          (D.oldRepresentative C b)
          (D.rightRestrictionEquiv C Q' S' hchar z) :=
  Classical.choose_spec
    (AssociatedProjectiveRepresentation.exists_operator_scalar_along
      S' C.rightAssociated hchar.rightNormalEquiv
      (D.rightRestrictionEquiv C Q' S' hchar)
      b (D.oldRepresentative C b)
      (D.right_inducesSameAutomorphism C hchar b)) z

/-- Gauge correction synchronizing the new right lift with the new left
lift. -/
def butterflyGauge (b : B') : ℂˣ :=
  D.leftComparisonScalar C P' R' hchar b /
    D.rightComparisonScalar C Q' S' hchar b

end ButterflySubgroupDiagram
end ComparisonScalars

section CommonMultiplier

variable {A : Type u} {A' : Type u'} {B : Type v} {B' : Type v'}
  [Finite A] [Finite A'] [Finite B] [Finite B']
  [Group A] [Group A'] [Group B] [Group B']
variable {T : CharacterTriple A} {T' : CharacterTriple A'}
  {U : CharacterTriple B} {U' : CharacterTriple B'}
variable {V W : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]
variable (C : CentralIsomorphismWitness T U V W)
  (D : ButterflySubgroupDiagram C T' U')

namespace ButterflySubgroupDiagram

/-- The old left and right operators attached to chosen representatives
have the same projective multiplication scalar.  The proof is exactly where
the old witness's scalar agreement on the centralizer is used. -/
theorem oldRepresentative_common_multiplier (g h : B') :
    ∃ t : ℂˣ,
      C.leftProjective.operator
          (C.embedding (D.oldRepresentative C g)) *
        C.leftProjective.operator
          (C.embedding (D.oldRepresentative C h)) =
        scalarLinearEquiv ℂ V t *
          C.leftProjective.operator
            (C.embedding (D.oldRepresentative C (g * h))) ∧
      C.rightProjective.operator
          (D.oldRepresentative C g) *
        C.rightProjective.operator
          (D.oldRepresentative C h) =
        scalarLinearEquiv ℂ W t *
          C.rightProjective.operator
            (D.oldRepresentative C (g * h)) := by
  let sg := D.oldRepresentative C g
  let sh := D.oldRepresentative C h
  let sk := D.oldRepresentative C (g * h)
  let d := D.oldRepresentativeDefect C g h
  have hd : d * sk = sg * sh := by
    simp only [d, sg, sh, sk, oldRepresentativeDefect]
    group
  obtain ⟨z, hPz, hQz⟩ :=
    C.scalar_agreement d
      (D.oldRepresentativeDefect_mem_centralizer C g h)
  let alpha :=
    C.leftProjective.factor
      (C.embedding sg) (C.embedding sh)
  let beta :=
    C.leftProjective.factor
      (C.embedding d) (C.embedding sk)
  let t := alpha / beta * z
  have hPmul :
      C.leftProjective.operator (C.embedding sg) *
          C.leftProjective.operator (C.embedding sh) =
        scalarLinearEquiv ℂ V alpha *
          C.leftProjective.operator
            (C.embedding (sg * sh)) := by
    simpa only [alpha, map_mul] using
      C.leftProjective.map_mul
        (C.embedding sg) (C.embedding sh)
  have hPdefect :
      C.leftProjective.operator (C.embedding (d * sk)) =
        scalarLinearEquiv ℂ V beta⁻¹ *
          (C.leftProjective.operator (C.embedding d) *
            C.leftProjective.operator (C.embedding sk)) := by
    have hm :=
      C.leftProjective.map_mul
        (C.embedding d) (C.embedding sk)
    rw [← map_mul C.embedding] at hm
    calc
      C.leftProjective.operator (C.embedding (d * sk)) =
          scalarLinearEquiv ℂ V beta⁻¹ *
            (scalarLinearEquiv ℂ V beta *
              C.leftProjective.operator
                (C.embedding (d * sk))) := by
        rw [← mul_assoc, ← scalarLinearEquiv_mul]
        simp
      _ = scalarLinearEquiv ℂ V beta⁻¹ *
          (C.leftProjective.operator (C.embedding d) *
            C.leftProjective.operator (C.embedding sk)) := by
        rw [hm]
  have hP :
      C.leftProjective.operator (C.embedding sg) *
          C.leftProjective.operator (C.embedding sh) =
        scalarLinearEquiv ℂ V t *
          C.leftProjective.operator (C.embedding sk) := by
    rw [hPmul, ← hd, hPdefect, hPz]
    calc
      scalarLinearEquiv ℂ V alpha *
          (scalarLinearEquiv ℂ V beta⁻¹ *
            (scalarLinearEquiv ℂ V z *
              C.leftProjective.operator (C.embedding sk))) =
        (scalarLinearEquiv ℂ V alpha *
            scalarLinearEquiv ℂ V beta⁻¹) *
          (scalarLinearEquiv ℂ V z *
            C.leftProjective.operator (C.embedding sk)) :=
        (mul_assoc _ _ _).symm
      _ = ((scalarLinearEquiv ℂ V alpha *
              scalarLinearEquiv ℂ V beta⁻¹) *
            scalarLinearEquiv ℂ V z) *
          C.leftProjective.operator (C.embedding sk) :=
        (mul_assoc _ _ _).symm
      _ = scalarLinearEquiv ℂ V t *
          C.leftProjective.operator (C.embedding sk) := by
        rw [← scalarLinearEquiv_mul,
          ← scalarLinearEquiv_mul]
        rfl
  have hQmul :
      C.rightProjective.operator sg *
          C.rightProjective.operator sh =
        scalarLinearEquiv ℂ W alpha *
          C.rightProjective.operator (sg * sh) := by
    have hm := C.rightProjective.map_mul sg sh
    rw [← C.factor_agreement sg sh] at hm
    exact hm
  have hQdefect :
      C.rightProjective.operator (d * sk) =
        scalarLinearEquiv ℂ W beta⁻¹ *
          (C.rightProjective.operator d *
            C.rightProjective.operator sk) := by
    have hm := C.rightProjective.map_mul d sk
    rw [← C.factor_agreement d sk] at hm
    calc
      C.rightProjective.operator (d * sk) =
          scalarLinearEquiv ℂ W beta⁻¹ *
            (scalarLinearEquiv ℂ W beta *
              C.rightProjective.operator (d * sk)) := by
        rw [← mul_assoc, ← scalarLinearEquiv_mul]
        simp
      _ = scalarLinearEquiv ℂ W beta⁻¹ *
          (C.rightProjective.operator d *
            C.rightProjective.operator sk) := by
        rw [hm]
  have hQ :
      C.rightProjective.operator sg *
          C.rightProjective.operator sh =
        scalarLinearEquiv ℂ W t *
          C.rightProjective.operator sk := by
    rw [hQmul, ← hd, hQdefect, hQz]
    calc
      scalarLinearEquiv ℂ W alpha *
          (scalarLinearEquiv ℂ W beta⁻¹ *
            (scalarLinearEquiv ℂ W z *
              C.rightProjective.operator sk)) =
        (scalarLinearEquiv ℂ W alpha *
            scalarLinearEquiv ℂ W beta⁻¹) *
          (scalarLinearEquiv ℂ W z *
            C.rightProjective.operator sk) :=
        (mul_assoc _ _ _).symm
      _ = ((scalarLinearEquiv ℂ W alpha *
              scalarLinearEquiv ℂ W beta⁻¹) *
            scalarLinearEquiv ℂ W z) *
          C.rightProjective.operator sk :=
        (mul_assoc _ _ _).symm
      _ = scalarLinearEquiv ℂ W t *
          C.rightProjective.operator sk := by
        rw [← scalarLinearEquiv_mul,
          ← scalarLinearEquiv_mul]
        rfl
  exact ⟨t, hP, hQ⟩

/-- The common multiplier, chosen once for later factor computations. -/
def oldRepresentativeMultiplier (g h : B') : ℂˣ :=
  Classical.choose (D.oldRepresentative_common_multiplier C g h)

theorem oldRepresentativeMultiplier_left (g h : B') :
    C.leftProjective.operator
        (C.embedding (D.oldRepresentative C g)) *
      C.leftProjective.operator
        (C.embedding (D.oldRepresentative C h)) =
      scalarLinearEquiv ℂ V
          (D.oldRepresentativeMultiplier C g h) *
        C.leftProjective.operator
          (C.embedding (D.oldRepresentative C (g * h))) :=
  (Classical.choose_spec
    (D.oldRepresentative_common_multiplier C g h)).1

theorem oldRepresentativeMultiplier_right (g h : B') :
    C.rightProjective.operator
        (D.oldRepresentative C g) *
      C.rightProjective.operator
        (D.oldRepresentative C h) =
      scalarLinearEquiv ℂ W
          (D.oldRepresentativeMultiplier C g h) *
        C.rightProjective.operator
          (D.oldRepresentative C (g * h)) :=
  (Classical.choose_spec
    (D.oldRepresentative_common_multiplier C g h)).2

end ButterflySubgroupDiagram
end CommonMultiplier

section FactorComparison

variable {G : Type u} [Group G]
variable {X Y : Type}
  [AddCommGroup X] [Module ℂ X] [Nontrivial X]
  [AddCommGroup Y] [Module ℂ Y]

/-- Comparing a projective lift with a set of operators having a specified
projective multiplication law gives the corresponding gauge formula for
its factor set. -/
theorem projectiveFactor_eq_gauge_of_operator_comparison
    (P : ProjectiveRepresentation ℂ G X)
    (L : G → Y ≃ₗ[ℂ] Y)
    (t : G → G → ℂˣ)
    (hmul : ∀ g h,
      L g * L h =
        scalarLinearEquiv ℂ Y (t g h) * L (g * h))
    (E : X ≃ₗ[ℂ] Y)
    (c : G → ℂˣ)
    (hoperator : ∀ (g : G) (x : X),
      E (P.operator g x) =
        (c g : ℂ) • L g (E x))
    (g h : G) :
    P.factor g h =
      c g * c h / c (g * h) * t g h := by
  let Q : ProjectiveRepresentation ℂ G Y :=
    { operator := L
      factor := t
      map_mul := hmul }
  have hop :
      ∀ (a : G) (x : X),
        E (P.operator a x) =
          (Q.rescale c).operator a (E x) := by
    intro a x
    rw [ProjectiveRepresentation.rescale_operator,
      LinearEquiv.mul_apply, scalarLinearEquiv_apply]
    exact hoperator a x
  have hfactor :=
    AssociatedProjectiveRepresentation.factor_eq_of_equiv_operator_eq
      E hop g h
  simpa [Q] using hfactor

end FactorComparison

section ButterflyFactors

variable {A : Type u} {A' : Type u'} {B : Type v} {B' : Type v'}
  [Finite A] [Finite A'] [Finite B] [Finite B']
  [Group A] [Group A'] [Group B] [Group B']
variable {T : CharacterTriple A} {T' : CharacterTriple A'}
  {U : CharacterTriple B} {U' : CharacterTriple B'}
variable {V W V' W' : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]
  [AddCommGroup V'] [Module ℂ V'] [Module.Finite ℂ V'] [Nontrivial V']
  [AddCommGroup W'] [Module ℂ W'] [Module.Finite ℂ W'] [Nontrivial W']
variable (C : CentralIsomorphismWitness T U V W)
  (D : ButterflySubgroupDiagram C T' U')
variable (P' : ProjectiveRepresentation ℂ A' V')
  (Q' : ProjectiveRepresentation ℂ B' W')
variable (R' : AssociatedProjectiveRepresentation T' V' P')
  (S' : AssociatedProjectiveRepresentation U' W' Q')
variable (hchar : D.CharacterCoherence C)

namespace ButterflySubgroupDiagram

/-- Factor formula for the new left lift in terms of the comparison
cochain and the common representative multiplier. -/
theorem left_factor_formula (g h : B') :
    P'.factor (D.embedding g) (D.embedding h) =
      D.leftComparisonScalar C P' R' hchar g *
        D.leftComparisonScalar C P' R' hchar h /
          D.leftComparisonScalar C P' R' hchar (g * h) *
        D.oldRepresentativeMultiplier C g h := by
  let Pcomap := P'.comap D.embedding
  exact
    projectiveFactor_eq_gauge_of_operator_comparison
      Pcomap
      (fun b ↦ C.leftProjective.operator
        (C.embedding (D.oldRepresentative C b)))
      (D.oldRepresentativeMultiplier C)
      (D.oldRepresentativeMultiplier_left C)
      (D.leftRestrictionEquiv C P' R' hchar).toLinearEquiv
      (D.leftComparisonScalar C P' R' hchar)
      (D.leftComparisonScalar_spec C P' R' hchar)
      g h

/-- Factor formula for the new right lift. -/
theorem right_factor_formula (g h : B') :
    Q'.factor g h =
      D.rightComparisonScalar C Q' S' hchar g *
        D.rightComparisonScalar C Q' S' hchar h /
          D.rightComparisonScalar C Q' S' hchar (g * h) *
        D.oldRepresentativeMultiplier C g h := by
  exact
    projectiveFactor_eq_gauge_of_operator_comparison
      Q'
      (fun b ↦ C.rightProjective.operator
        (D.oldRepresentative C b))
      (D.oldRepresentativeMultiplier C)
      (D.oldRepresentativeMultiplier_right C)
      (D.rightRestrictionEquiv C Q' S' hchar).toLinearEquiv
      (D.rightComparisonScalar C Q' S' hchar)
      (D.rightComparisonScalar_spec C Q' S' hchar)
      g h

/-- The Butterfly gauge makes the new left and right factor sets agree
literally. -/
theorem butterflyGauge_factor_agreement (g h : B') :
    P'.factor (D.embedding g) (D.embedding h) =
      (Q'.rescale
        (D.butterflyGauge C P' Q' R' S' hchar)).factor g h := by
  rw [ProjectiveRepresentation.rescale_factor,
    D.left_factor_formula C P' R' hchar,
    D.right_factor_formula C Q' S' hchar]
  unfold butterflyGauge
  apply Units.ext
  simp only [div_eq_mul_inv, Units.val_mul,
    Units.val_inv_eq_inv_val]
  field_simp

end ButterflySubgroupDiagram
end ButterflyFactors

section NormalGauge

variable {A : Type u} {A' : Type u'} {B : Type v} {B' : Type v'}
  [Finite A] [Finite A'] [Finite B] [Finite B']
  [Group A] [Group A'] [Group B] [Group B']
variable {T : CharacterTriple A} {T' : CharacterTriple A'}
  {U : CharacterTriple B} {U' : CharacterTriple B'}
variable {V W V' W' : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]
  [AddCommGroup V'] [Module ℂ V'] [Module.Finite ℂ V'] [Nontrivial V']
  [AddCommGroup W'] [Module ℂ W'] [Module.Finite ℂ W'] [Nontrivial W']
variable (C : CentralIsomorphismWitness T U V W)
  (D : ButterflySubgroupDiagram C T' U')
variable (P' : ProjectiveRepresentation ℂ A' V')
  (Q' : ProjectiveRepresentation ℂ B' W')
variable (R' : AssociatedProjectiveRepresentation T' V' P')
  (S' : AssociatedProjectiveRepresentation U' W' Q')
variable (hchar : D.CharacterCoherence C)

namespace ButterflySubgroupDiagram

/-- On a new normal element, compare the chosen old representative with the
identified old right-normal element. -/
def oldNormalRepresentativeDefect
    (m : U'.normalSubgroup) : B :=
  D.oldRepresentative C (m : B') *
    (hchar.rightNormalEquiv m : B)⁻¹

/-- This normal representative defect acts trivially on the old left
normal subgroup. -/
theorem oldNormalRepresentativeDefect_action_eq_one
    (m : U'.normalSubgroup) :
    C.rightConjugationAction
        (D.oldNormalRepresentativeDefect C hchar m) = 1 := by
  rw [oldNormalRepresentativeDefect, map_mul, map_inv,
    D.oldRepresentative_action C]
  have hnormal :=
    T.conjugationActionAlong_normal T' D.normalEquiv
      (newRightNormalInLeft C D m)
  have hcomm :=
    hchar.normal_embedding_commutes m
  change
    T.conjugationActionAlong T' D.normalEquiv
        (D.embedding m) *
      (T.conjugationAction
        (C.embedding (hchar.rightNormalEquiv m)))⁻¹ = 1
  rw [← coe_newRightNormalInLeft C D m, hnormal, hcomm]
  change
    T.conjugationAction
        (C.embedding (hchar.rightNormalEquiv m)) *
      (T.conjugationAction
        (C.embedding (hchar.rightNormalEquiv m)))⁻¹ = 1
  simp

theorem oldNormalRepresentativeDefect_mem_centralizer
    (m : U'.normalSubgroup) :
    C.embedding
        (D.oldNormalRepresentativeDefect C hchar m) ∈
      Subgroup.centralizer (T.normalSubgroup : Set A) := by
  rw [← T.conjugationAction_eq_one_iff]
  exact
    D.oldNormalRepresentativeDefect_action_eq_one
      C hchar m

/-- The left comparison scalar on a normal element is characterized by the
old normal operator. -/
theorem oldLeftNormal_operator_eq_comparison
    (m : U'.normalSubgroup) :
    C.leftProjective.operator
        (C.embedding (hchar.rightNormalEquiv m)) =
      scalarLinearEquiv ℂ V
          (D.leftComparisonScalar C P' R' hchar (m : B')) *
        C.leftProjective.operator
          (C.embedding
            (D.oldRepresentative C (m : B'))) := by
  apply LinearEquiv.ext
  intro y
  let E := D.leftRestrictionEquiv C P' R' hchar
  let z := E.symm y
  have hinter :=
    LinearMap.congr_fun
      (E.isIntertwining'
        (newRightNormalInLeft C D m)) z
  change
    E (R'.restriction
        (newRightNormalInLeft C D m) z) =
      C.leftAssociated.restriction
        (D.normalEquiv
          (newRightNormalInLeft C D m))
        (E z)
    at hinter
  rw [R'.restriction_apply,
    C.leftAssociated.restriction_apply,
    hchar.normal_embedding_commutes m]
    at hinter
  have hspec :=
    D.leftComparisonScalar_spec
      C P' R' hchar (m : B') z
  change
    E (P'.operator (D.embedding m) z) =
      (D.leftComparisonScalar C P' R' hchar
        (m : B') : ℂ) •
        C.leftProjective.operator
          (C.embedding
            (D.oldRepresentative C (m : B')))
          (E z)
    at hspec
  change
    C.leftProjective.operator
        (C.embedding (hchar.rightNormalEquiv m)) y =
      (D.leftComparisonScalar C P' R' hchar
        (m : B') : ℂ) •
        C.leftProjective.operator
          (C.embedding
            (D.oldRepresentative C (m : B'))) y
  have hfinal := hinter.symm.trans hspec
  have hEz : E z = y :=
    E.apply_symm_apply y
  rw [hEz] at hfinal
  exact hfinal

/-- The analogous characterization for the old right normal operator. -/
theorem oldRightNormal_operator_eq_comparison
    (m : U'.normalSubgroup) :
    C.rightProjective.operator
        (hchar.rightNormalEquiv m) =
      scalarLinearEquiv ℂ W
          (D.rightComparisonScalar C Q' S' hchar (m : B')) *
        C.rightProjective.operator
          (D.oldRepresentative C (m : B')) := by
  apply LinearEquiv.ext
  intro y
  let E := D.rightRestrictionEquiv C Q' S' hchar
  let z := E.symm y
  have hinter :=
    LinearMap.congr_fun (E.isIntertwining' m) z
  change
    E (S'.restriction m z) =
      C.rightAssociated.restriction
        (hchar.rightNormalEquiv m) (E z)
    at hinter
  rw [S'.restriction_apply,
    C.rightAssociated.restriction_apply] at hinter
  have hspec :=
    D.rightComparisonScalar_spec
      C Q' S' hchar (m : B') z
  change
    E (Q'.operator (m : B') z) =
      (D.rightComparisonScalar C Q' S' hchar
        (m : B') : ℂ) •
        C.rightProjective.operator
          (D.oldRepresentative C (m : B')) (E z)
    at hspec
  change
    C.rightProjective.operator
        (hchar.rightNormalEquiv m) y =
      (D.rightComparisonScalar C Q' S' hchar
        (m : B') : ℂ) •
        C.rightProjective.operator
          (D.oldRepresentative C (m : B')) y
  have hfinal := hinter.symm.trans hspec
  have hEz : E z = y :=
    E.apply_symm_apply y
  rw [hEz] at hfinal
  exact hfinal

/-- The left and right comparison scalars coincide on the new normal
subgroup. -/
theorem comparisonScalars_eq_on_normal
    (m : U'.normalSubgroup) :
    D.leftComparisonScalar C P' R' hchar (m : B') =
      D.rightComparisonScalar C Q' S' hchar (m : B') := by
  let s := D.oldRepresentative C (m : B')
  let n : B := hchar.rightNormalEquiv m
  let d := D.oldNormalRepresentativeDefect C hchar m
  have hd : d * n = s := by
    simp only [d, n, s, oldNormalRepresentativeDefect]
    group
  obtain ⟨z, hPz, hQz⟩ :=
    C.scalar_agreement d
      (D.oldNormalRepresentativeDefect_mem_centralizer
        C hchar m)
  let alpha :=
    C.leftProjective.factor
      (C.embedding d) (C.embedding n)
  have hPmul :=
    C.leftProjective.map_mul
      (C.embedding d) (C.embedding n)
  rw [← map_mul C.embedding, hd,
    hPz,
    D.oldLeftNormal_operator_eq_comparison
      C P' R' hchar m]
    at hPmul
  have hleft :
      z *
          D.leftComparisonScalar C P' R' hchar (m : B') =
        alpha := by
    apply scalarLinearEquiv_injective ℂ V
    rw [scalarLinearEquiv_mul]
    apply mul_right_cancel
    simpa only [alpha, mul_assoc] using hPmul
  have hQmul :=
    C.rightProjective.map_mul d n
  rw [← C.factor_agreement d n, hd,
    hQz,
    D.oldRightNormal_operator_eq_comparison
      C Q' S' hchar m]
    at hQmul
  have hright :
      z *
          D.rightComparisonScalar C Q' S' hchar (m : B') =
        alpha := by
    apply scalarLinearEquiv_injective ℂ W
    rw [scalarLinearEquiv_mul]
    apply mul_right_cancel
    simpa only [alpha, mul_assoc] using hQmul
  exact mul_left_cancel (hleft.trans hright.symm)

/-- The Butterfly correction is trivial on the new normal subgroup. -/
theorem butterflyGauge_normal (m : U'.normalSubgroup) :
    D.butterflyGauge C P' Q' R' S' hchar (m : B') = 1 := by
  rw [butterflyGauge,
    D.comparisonScalars_eq_on_normal
      C P' Q' R' S' hchar m]
  simp

/-- The correction is constant on left cosets of the new normal subgroup. -/
theorem butterflyGauge_normal_mul
    (m : U'.normalSubgroup) (b : B') :
    D.butterflyGauge C P' Q' R' S' hchar
        ((m : B') * b) =
      D.butterflyGauge C P' Q' R' S' hchar b := by
  have hfactor :=
    D.butterflyGauge_factor_agreement
      C P' Q' R' S' hchar (m : B') b
  have hleft :
      P'.factor (D.embedding m) (D.embedding b) = 1 := by
    simpa only [coe_newRightNormalInLeft] using
      R'.factor_normal_left
        (newRightNormalInLeft C D m)
        (D.embedding b)
  rw [hleft, ProjectiveRepresentation.rescale_factor,
    S'.factor_normal_left,
    D.butterflyGauge_normal
      C P' Q' R' S' hchar m]
    at hfactor
  have hdiv :
      D.butterflyGauge C P' Q' R' S' hchar b /
          D.butterflyGauge C P' Q' R' S' hchar
            ((m : B') * b) =
        1 := by
    simpa using hfactor.symm
  exact (div_eq_one.mp hdiv).symm

/-- The correction is constant on right cosets of the new normal
subgroup. -/
theorem butterflyGauge_mul_normal
    (b : B') (m : U'.normalSubgroup) :
    D.butterflyGauge C P' Q' R' S' hchar
        (b * (m : B')) =
      D.butterflyGauge C P' Q' R' S' hchar b := by
  have hfactor :=
    D.butterflyGauge_factor_agreement
      C P' Q' R' S' hchar b (m : B')
  have hleft :
      P'.factor (D.embedding b) (D.embedding m) = 1 := by
    simpa only [coe_newRightNormalInLeft] using
      R'.factor_normal_right
        (D.embedding b)
        (newRightNormalInLeft C D m)
  rw [hleft, ProjectiveRepresentation.rescale_factor,
    S'.factor_normal_right,
    D.butterflyGauge_normal
      C P' Q' R' S' hchar m]
    at hfactor
  have hdiv :
      D.butterflyGauge C P' Q' R' S' hchar b /
          D.butterflyGauge C P' Q' R' S' hchar
            (b * (m : B')) =
        1 := by
    simpa using hfactor.symm
  exact (div_eq_one.mp hdiv).symm

/-- The gauge-corrected new right lift remains associated with the new
right character triple. -/
def butterflyRightAssociated :
    AssociatedProjectiveRepresentation U' W'
      (Q'.rescale
        (D.butterflyGauge C P' Q' R' S' hchar)) where
  restriction := S'.restriction
  restriction_apply m := by
    rw [ProjectiveRepresentation.rescale_operator,
      D.butterflyGauge_normal
        C P' Q' R' S' hchar m,
      map_one, one_mul]
    exact S'.restriction_apply m
  restriction_simple := S'.restriction_simple
  restriction_character := S'.restriction_character
  normal_mul m b := by
    rw [ProjectiveRepresentation.rescale_operator,
      ProjectiveRepresentation.rescale_operator,
      ProjectiveRepresentation.rescale_operator,
      D.butterflyGauge_normal_mul
        C P' Q' R' S' hchar m b,
      D.butterflyGauge_normal
        C P' Q' R' S' hchar m,
      map_one, one_mul, S'.normal_mul]
    calc
      scalarLinearEquiv ℂ W'
            (D.butterflyGauge C P' Q' R' S' hchar b) *
          (Q'.operator (m : B') * Q'.operator b) =
        (scalarLinearEquiv ℂ W'
              (D.butterflyGauge C P' Q' R' S' hchar b) *
            Q'.operator (m : B')) *
          Q'.operator b := (mul_assoc _ _ _).symm
      _ = (Q'.operator (m : B') *
            scalarLinearEquiv ℂ W'
              (D.butterflyGauge C P' Q' R' S' hchar b)) *
          Q'.operator b := by
        rw [scalarLinearEquiv_comm]
      _ = Q'.operator (m : B') *
          (scalarLinearEquiv ℂ W'
              (D.butterflyGauge C P' Q' R' S' hchar b) *
            Q'.operator b) := mul_assoc _ _ _
  mul_normal b m := by
    rw [ProjectiveRepresentation.rescale_operator,
      ProjectiveRepresentation.rescale_operator,
      ProjectiveRepresentation.rescale_operator,
      D.butterflyGauge_mul_normal
        C P' Q' R' S' hchar b m,
      D.butterflyGauge_normal
        C P' Q' R' S' hchar m,
      map_one, one_mul, S'.mul_normal]
    exact (mul_assoc _ _ _).symm

end ButterflySubgroupDiagram
end NormalGauge

section DerivedCoherence

variable {A : Type u} {A' : Type u'} {B : Type v} {B' : Type v'}
  [Finite A] [Finite A'] [Finite B] [Finite B']
  [Group A] [Group A'] [Group B] [Group B']
variable {T : CharacterTriple A} {T' : CharacterTriple A'}
  {U : CharacterTriple B} {U' : CharacterTriple B'}
variable {V W V' W' : Type}
  [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]
  [AddCommGroup V'] [Module ℂ V'] [Module.Finite ℂ V'] [Nontrivial V']
  [AddCommGroup W'] [Module ℂ W'] [Module.Finite ℂ W'] [Nontrivial W']
variable (C : CentralIsomorphismWitness T U V W)
  (D : ButterflySubgroupDiagram C T' U')
variable (P' : ProjectiveRepresentation ℂ A' V')
  (Q' : ProjectiveRepresentation ℂ B' W')
variable (R' : AssociatedProjectiveRepresentation T' V' P')
  (S' : AssociatedProjectiveRepresentation U' W' Q')
variable (hchar : D.CharacterCoherence C)

namespace ButterflySubgroupDiagram

/-- The corrected new lifts have the same scalar operator above the new
centralizer. -/
theorem butterflyGauge_scalar_agreement
    (b : B')
    (hb : D.embedding b ∈
      Subgroup.centralizer (T'.normalSubgroup : Set A')) :
    ∃ c : ℂˣ,
      P'.operator (D.embedding b) =
          scalarLinearEquiv ℂ V' c ∧
        (Q'.rescale
          (D.butterflyGauge C P' Q' R' S' hchar)).operator b =
          scalarLinearEquiv ℂ W' c := by
  let s := D.oldRepresentative C b
  have hscentral :
      C.embedding s ∈
        Subgroup.centralizer (T.normalSubgroup : Set A) := by
    rw [← T.conjugationAction_eq_one_iff]
    change C.rightConjugationAction s = 1
    rw [D.oldRepresentative_action C]
    exact
      (T.conjugationActionAlong_eq_one_iff
        T' D.normalEquiv (D.embedding b)).2 hb
  obtain ⟨z, hPz, hQz⟩ :=
    C.scalar_agreement s hscentral
  let l := D.leftComparisonScalar C P' R' hchar b
  let r := D.rightComparisonScalar C Q' S' hchar b
  let c := l * z
  have hleft :
      P'.operator (D.embedding b) =
        scalarLinearEquiv ℂ V' c := by
    apply LinearEquiv.ext
    intro x
    let E := D.leftRestrictionEquiv C P' R' hchar
    apply E.toLinearEquiv.injective
    calc
      E (P'.operator (D.embedding b) x) =
          (l : ℂ) •
            C.leftProjective.operator
              (C.embedding s) (E x) :=
        D.leftComparisonScalar_spec
          C P' R' hchar b x
      _ = (l : ℂ) • ((z : ℂ) • E x) := by
        rw [hPz]
        rfl
      _ = (c : ℂ) • E x := by
        simp [c, smul_smul]
      _ = E ((c : ℂ) • x) :=
        (map_smul E (c : ℂ) x).symm
      _ = E (scalarLinearEquiv ℂ V' c x) :=
        rfl
  have hrightBase :
      Q'.operator b =
        scalarLinearEquiv ℂ W' (r * z) := by
    apply LinearEquiv.ext
    intro x
    let E := D.rightRestrictionEquiv C Q' S' hchar
    apply E.toLinearEquiv.injective
    calc
      E (Q'.operator b x) =
          (r : ℂ) •
            C.rightProjective.operator s (E x) :=
        D.rightComparisonScalar_spec
          C Q' S' hchar b x
      _ = (r : ℂ) • ((z : ℂ) • E x) := by
        rw [hQz]
        rfl
      _ = ((r * z : ℂˣ) : ℂ) • E x := by
        simp [smul_smul]
      _ = E ((((r * z : ℂˣ) : ℂ)) • x) :=
        (map_smul E (((r * z : ℂˣ) : ℂ)) x).symm
      _ = E (scalarLinearEquiv ℂ W' (r * z) x) :=
        rfl
  refine ⟨c, hleft, ?_⟩
  rw [ProjectiveRepresentation.rescale_operator,
    hrightBase, ← scalarLinearEquiv_mul]
  congr 1
  change (l / r) * (r * z) = l * z
  simp [div_eq_mul_inv, mul_assoc]

/-- The projective coherence in the Butterfly theorem follows from the
standard subgroup diagram and character identifications. -/
theorem derivedProjectiveCoherence :
    ButterflyProjectiveCoherence C D P'
      (Q'.rescale
        (D.butterflyGauge C P' Q' R' S' hchar)) where
  factor_agreement :=
    D.butterflyGauge_factor_agreement
      C P' Q' R' S' hchar
  scalar_agreement :=
    D.butterflyGauge_scalar_agreement
      C P' Q' R' S' hchar

end ButterflySubgroupDiagram

/-- **Unconditional Butterfly theorem for chosen associated lifts.**

No projective-coherence hypothesis is required: the right lift is corrected
by the canonical comparison gauge derived above. -/
def CentralIsomorphismWitness.butterflyUnconditional :
    CentralIsomorphismWitness T' U' V' W' :=
  C.butterfly D P'
    (Q'.rescale
      (D.butterflyGauge C P' Q' R' S' hchar))
    R'
    (D.butterflyRightAssociated
      C P' Q' R' S' hchar)
    hchar
    (D.derivedProjectiveCoherence
      C P' Q' R' S' hchar)

/-- Existence form of the unconditional Butterfly theorem. -/
theorem centrallyIsomorphicVia_butterfly_unconditional
    (C : CentralIsomorphismWitness T U V W)
    (D : ButterflySubgroupDiagram C T' U')
    (P' : ProjectiveRepresentation ℂ A' V')
    (Q' : ProjectiveRepresentation ℂ B' W')
    (R' : AssociatedProjectiveRepresentation T' V' P')
    (S' : AssociatedProjectiveRepresentation U' W' Q')
    (hchar : D.CharacterCoherence C) :
    CentralIsomorphismWitness.CentrallyIsomorphicVia
      T' U' V' W' :=
  ⟨CentralIsomorphismWitness.butterflyUnconditional
    C D P' Q' R' S' hchar⟩

end DerivedCoherence

end CharacterTriple
end McKayConjecture
