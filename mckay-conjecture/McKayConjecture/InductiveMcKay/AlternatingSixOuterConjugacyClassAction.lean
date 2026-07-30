/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.AlternatingSixTwoAlphaOneStabilizer
import McKayConjecture.InductiveMcKay.AlternatingSixTwoAlphaTwoStabilizer
import McKayConjecture.GroupTheory.AlternatingSixSchurOuterClassActionAlphaOne
import McKayConjecture.GroupTheory.AlternatingSixSchurOuterClassActionAlphaTwo

/-!
# Conjugacy-class actions of the two audited `6.A₆` automorphisms

The checked conjugacy certificate identifies the 31 class indices of the
computable Schur-cover coordinates with their actual conjugacy classes.
Conjugating the genuine class action through that equivalence gives
permutations of `Fin 31`.  This file constructs those permutations for the
two audited automorphisms and relates them to the corresponding transported
automorphisms of the canonical universal cover.

No character-row action and no identification with the separately audited
CTblLib permutations is asserted here.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

/-- The checked 31-class enumeration transported from Schur coordinates to
the canonical universal cover. -/
def alternatingSixUniversalCoverClassIndexEquiv :
    Fin 31 ≃ ConjClasses AlternatingSixUniversalCover :=
  alternatingSixSchurCoordinateConjugacyClassEquiv.trans
    (conjugacyClassesEquivOfMulEquiv
      alternatingSixSchurCoordinatesEquivUniversalCover)

/-- The action of a Schur-coordinate automorphism on the checked finite
conjugacy-class index. -/
def alternatingSixSchurClassIndexPermutation
    (α : MulAut AlternatingSixSchurCoordinates) :
    Equiv.Perm (Fin 31) :=
  alternatingSixSchurCoordinateConjugacyClassEquiv.trans
    ((conjugacyClassesEquivOfMulEquiv α).trans
      alternatingSixSchurCoordinateConjugacyClassEquiv.symm)

/-- Transporting conjugacy classes through a group equivalence intertwines
an automorphism with its conjugate automorphism on the target group. -/
theorem conjugacyClassesEquivOfMulEquiv_map_congr
    {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (α : MulAut G)
    (c : ConjClasses G) :
    conjugacyClassesEquivOfMulEquiv e
        (ConjClasses.map α.toMonoidHom c) =
      ConjClasses.map (MulAut.congr e α).toMonoidHom
        (conjugacyClassesEquivOfMulEquiv e c) := by
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
  change
    ConjClasses.mk (e (α x)) =
      ConjClasses.mk ((MulAut.congr e α) (e x))
  congr 1
  simp [MulAut.congr]

/-- Applying the finite class-index action and then returning to actual
coordinate conjugacy classes is the genuine class action of `α`. -/
theorem alternatingSixSchurClassIndexPermutation_class
    (α : MulAut AlternatingSixSchurCoordinates)
    (i : Fin 31) :
    alternatingSixSchurCoordinateConjugacyClassEquiv
        (alternatingSixSchurClassIndexPermutation α i) =
      ConjClasses.map α.toMonoidHom
        (alternatingSixSchurCoordinateConjugacyClassEquiv i) := by
  simp [alternatingSixSchurClassIndexPermutation,
    conjugacyClassesEquivOfMulEquiv]

/-- The inverse checked class enumeration sends the class of a coordinate
to its certified class index. -/
theorem alternatingSixSchurCoordinateConjugacyClassEquiv_symm_mk
    (x : AlternatingSixSchurCoordinates) :
    alternatingSixSchurCoordinateConjugacyClassEquiv.symm
        (ConjClasses.mk x) =
      alternatingSixSchurClassIndex x := by
  apply alternatingSixSchurCoordinateConjugacyClassEquiv.injective
  rw [alternatingSixSchurCoordinateConjugacyClassEquiv.apply_symm_apply]
  change
    ConjClasses.mk x =
      ConjClasses.mk
        (alternatingSixSchurClassRepresentative
          (alternatingSixSchurClassIndex x))
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  exact
    (isConj_iff.mpr
      ⟨alternatingSixSchurClassConjugator x,
        alternatingSixSchurClassConjugator_spec x⟩).symm

/-- Concrete evaluation of the semantic finite permutation: apply the
automorphism to the advertised representative and read its checked class
label. -/
theorem alternatingSixSchurClassIndexPermutation_apply
    (α : MulAut AlternatingSixSchurCoordinates)
    (i : Fin 31) :
    alternatingSixSchurClassIndexPermutation α i =
      alternatingSixSchurClassIndex
        (α (alternatingSixSchurClassRepresentative i)) := by
  exact
    alternatingSixSchurCoordinateConjugacyClassEquiv_symm_mk
      (α (alternatingSixSchurClassRepresentative i))

/-- The genuine class-index permutation induced by the first audited
Schur-cover automorphism. -/
def alternatingSixAlphaOneConjugacyClassPermutation :
    Equiv.Perm (Fin 31) :=
  alternatingSixSchurClassIndexPermutation
    alternatingSixSchurAlphaOneAutomorphism

/-- The genuine class-index permutation induced by the second audited
Schur-cover automorphism. -/
def alternatingSixAlphaTwoConjugacyClassPermutation :
    Equiv.Perm (Fin 31) :=
  alternatingSixSchurClassIndexPermutation
    alternatingSixSchurAlphaTwoAutomorphism

/-- Zero-based finite vector for the first audited automorphism's action on
the checked conjugacy-class order. -/
def alternatingSixAlphaOneConjugacyClassVector :
    Fin 31 → Fin 31 :=
  ![
    0, 5, 4, 3, 2, 1, 8, 7, 6, 12, 11, 10, 9, 14, 13, 21,
    26, 25, 24, 23, 22, 15, 20, 19, 18, 17, 16, 27, 28, 29, 30
  ]

/-- Zero-based finite vector for the second audited automorphism's action
on the checked conjugacy-class order. -/
def alternatingSixAlphaTwoConjugacyClassVector :
    Fin 31 → Fin 31 :=
  ![
    0, 5, 4, 3, 2, 1, 8, 7, 6, 9, 14, 13, 12, 11, 10, 19,
    18, 17, 16, 15, 20, 23, 22, 21, 26, 25, 24, 29, 30, 27, 28
  ]

/-- Coordinate-level evaluation of the first class permutation. -/
theorem alternatingSixAlphaOneConjugacyClassPermutation_apply
    (i : Fin 31) :
    alternatingSixAlphaOneConjugacyClassPermutation i =
      alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaOneAutomorphism
          (alternatingSixSchurClassRepresentative i)) :=
  alternatingSixSchurClassIndexPermutation_apply
    alternatingSixSchurAlphaOneAutomorphism i

/-- Coordinate-level evaluation of the second class permutation. -/
theorem alternatingSixAlphaTwoConjugacyClassPermutation_apply
    (i : Fin 31) :
    alternatingSixAlphaTwoConjugacyClassPermutation i =
      alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaTwoAutomorphism
          (alternatingSixSchurClassRepresentative i)) :=
  alternatingSixSchurClassIndexPermutation_apply
    alternatingSixSchurAlphaTwoAutomorphism i

/-- The displayed first vector is computed from the underlying coordinate
endomorphism on every certified class representative. -/
theorem alternatingSixAlphaOneEndomorphism_classIndex_eq_vector
    (i : Fin 31) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaOneEndomorphism
          (alternatingSixSchurClassRepresentative i)) =
      alternatingSixAlphaOneConjugacyClassVector i := by
  calc
    _ = alternatingSixSchurAlphaOneClassIndexAction i :=
      alternatingSixSchurAlphaOneAutomorphism_classIndex_representative i
    _ = alternatingSixAlphaOneConjugacyClassVector i := rfl

/-- The semantic first conjugacy-class permutation is exactly its displayed
finite vector. -/
theorem alternatingSixAlphaOneConjugacyClassPermutation_eq_vector
    (i : Fin 31) :
    alternatingSixAlphaOneConjugacyClassPermutation i =
      alternatingSixAlphaOneConjugacyClassVector i := by
  rw [alternatingSixAlphaOneConjugacyClassPermutation_apply]
  change
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaOneEndomorphism
          (alternatingSixSchurClassRepresentative i)) =
      alternatingSixAlphaOneConjugacyClassVector i
  exact alternatingSixAlphaOneEndomorphism_classIndex_eq_vector i

/-- The displayed second vector is computed from the underlying coordinate
endomorphism on every certified class representative. -/
theorem alternatingSixAlphaTwoEndomorphism_classIndex_eq_vector
    (i : Fin 31) :
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaTwoEndomorphism
          (alternatingSixSchurClassRepresentative i)) =
      alternatingSixAlphaTwoConjugacyClassVector i := by
  calc
    _ = alternatingSixSchurAlphaTwoClassIndexAction i :=
      alternatingSixSchurAlphaTwoAutomorphism_classIndex_representative i
    _ = alternatingSixAlphaTwoConjugacyClassVector i := rfl

/-- The semantic second conjugacy-class permutation is exactly its displayed
finite vector. -/
theorem alternatingSixAlphaTwoConjugacyClassPermutation_eq_vector
    (i : Fin 31) :
    alternatingSixAlphaTwoConjugacyClassPermutation i =
      alternatingSixAlphaTwoConjugacyClassVector i := by
  rw [alternatingSixAlphaTwoConjugacyClassPermutation_apply]
  change
    alternatingSixSchurClassIndex
        (alternatingSixSchurAlphaTwoEndomorphism
          (alternatingSixSchurClassRepresentative i)) =
      alternatingSixAlphaTwoConjugacyClassVector i
  exact alternatingSixAlphaTwoEndomorphism_classIndex_eq_vector i

/-- On the canonical universal cover, the first finite permutation is the
actual conjugacy-class action of the transported first automorphism. -/
theorem alternatingSixAlphaOneConjugacyClassPermutation_universalCover
    (i : Fin 31) :
    alternatingSixUniversalCoverClassIndexEquiv
        (alternatingSixAlphaOneConjugacyClassPermutation i) =
      ConjClasses.map
        alternatingSixUniversalCoverAlphaOneAutomorphism.toMonoidHom
        (alternatingSixUniversalCoverClassIndexEquiv i) := by
  rw [alternatingSixUniversalCoverClassIndexEquiv,
    Equiv.trans_apply, Equiv.trans_apply,
    alternatingSixAlphaOneConjugacyClassPermutation,
    alternatingSixSchurClassIndexPermutation_class]
  exact
    conjugacyClassesEquivOfMulEquiv_map_congr
      alternatingSixSchurCoordinatesEquivUniversalCover
      alternatingSixSchurAlphaOneAutomorphism
      (alternatingSixSchurCoordinateConjugacyClassEquiv i)

/-- On the canonical universal cover, the second finite permutation is the
actual conjugacy-class action of the transported second automorphism. -/
theorem alternatingSixAlphaTwoConjugacyClassPermutation_universalCover
    (i : Fin 31) :
    alternatingSixUniversalCoverClassIndexEquiv
        (alternatingSixAlphaTwoConjugacyClassPermutation i) =
      ConjClasses.map
        alternatingSixUniversalCoverAlphaTwoAutomorphism.toMonoidHom
        (alternatingSixUniversalCoverClassIndexEquiv i) := by
  rw [alternatingSixUniversalCoverClassIndexEquiv,
    Equiv.trans_apply, Equiv.trans_apply,
    alternatingSixAlphaTwoConjugacyClassPermutation,
    alternatingSixSchurClassIndexPermutation_class]
  exact
    conjugacyClassesEquivOfMulEquiv_map_congr
      alternatingSixSchurCoordinatesEquivUniversalCover
      alternatingSixSchurAlphaTwoAutomorphism
      (alternatingSixSchurCoordinateConjugacyClassEquiv i)

end InductiveMcKay
end McKayConjecture
