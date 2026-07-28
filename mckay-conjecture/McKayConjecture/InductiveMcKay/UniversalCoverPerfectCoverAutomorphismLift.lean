/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.UniversalCentralExtensionAutomorphism
import McKayConjecture.InductiveMcKay.CentralExtensionAutomorphismLift

/-!
# Canonical Sylow-automorphism lifts from a universal cover

Let `U → S` be a universal central extension and let `A → S` be a perfect
central cover.  Every automorphism of `A` induces an automorphism of the
centerless simple group `S`, hence lifts canonically to `U`.  Universality
shows that this lift intertwines the canonical quotient `U → A`.

If the automorphism of `A` stabilizes a chosen Sylow subgroup, its lift
stabilizes the unique Sylow subgroup of `U` above it.  This produces the
coherent `SylowAutomorphismLift` needed for full central-extension descent,
without an extra hypothesis.
-/

noncomputable section

open scoped IsMulCommutative Pointwise

universe u

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory

variable {p : ℕ} [Fact p.Prime]
variable {U S A : Type u}
variable [Group U] [Group S] [Group A]
variable [Finite U] [Finite A]

namespace UniversalCoverAutomorphismLift

/-- The canonical lift to `U` of an automorphism of a central cover `A`. -/
def coverAutomorphismLiftMonoidHom
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S)
    (hs : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S) :
    MulAut A →* MulAut U :=
  E.targetAutomorphismLiftMonoidHom.comp
    (F.inducedTargetAutomorphismMonoidHom hs hnoncomm)

/-- The canonical lifted automorphism intertwines the map from the
universal cover to the perfect cover. -/
theorem coverAutomorphismLift_projection
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S)
    (hs : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S)
    (hperfect : Group.IsPerfect A)
    (α : MulAut A) (u : U) :
    (E.centralExtensionToPerfectCover F hperfect).projection
        (coverAutomorphismLiftMonoidHom
          E F hs hnoncomm α u) =
      α
        ((E.centralExtensionToPerfectCover
          F hperfect).projection u) := by
  exact DFunLike.congr_fun
    (E.targetAutomorphismLift_intertwines_mapToCentralExtension
      F hs hnoncomm α) u

/-- A Sylow-stabilizing automorphism of the perfect cover lifts to a
Sylow-stabilizing automorphism of the universal cover. -/
theorem coverAutomorphismLift_smul_sylowLift
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S)
    (hs : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S)
    (hperfect : Group.IsPerfect A)
    (P : Sylow p A)
    (α : SylowAutStabilizer P) :
    coverAutomorphismLiftMonoidHom
          E F hs hnoncomm α.1 •
        (E.centralExtensionToPerfectCover
          F hperfect).sylowLift P =
      (E.centralExtensionToPerfectCover
        F hperfect).sylowLift P := by
  let C : CentralExtension U A :=
    E.centralExtensionToPerfectCover F hperfect
  let φ : MulAut U :=
    coverAutomorphismLiftMonoidHom
      E F hs hnoncomm α.1
  apply
    (C.eq_sylowLift_iff_mapSurjective_eq
      P (φ • C.sylowLift P)).2
  apply Sylow.ext
  change
    ((φ • C.sylowLift P : Sylow p U) :
        Subgroup U).map C.projection =
      (P : Subgroup A)
  rw [Sylow.pointwise_smul_def,
    Subgroup.pointwise_smul_def]
  have haction :
      (MulDistribMulAction.toMonoidEnd
        (MulAut U) U) φ =
        φ.toMonoidHom := by
    ext u
    rfl
  rw [haction, Subgroup.map_map]
  have hintertwine :
      C.projection.comp φ.toMonoidHom =
        α.1.toMonoidHom.comp C.projection := by
    ext u
    exact coverAutomorphismLift_projection
      E F hs hnoncomm hperfect α.1 u
  rw [hintertwine, ← Subgroup.map_map,
    C.sylowLift_map P,
    MulEquiv.toMonoidHom_eq_coe,
    SylowAutStabilizer.map_sylow_eq α]

/-- The canonical coherent lift of all automorphisms stabilizing `P`. -/
def sylowAutomorphismLift
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S)
    (hs : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S)
    (hperfect : Group.IsPerfect A)
    (P : Sylow p A) :
    SylowAutomorphismLift
      (E.centralExtensionToPerfectCover F hperfect) P where
  lift :=
    ((coverAutomorphismLiftMonoidHom
      E F hs hnoncomm).comp
        (SylowAutStabilizer P).subtype).codRestrict
      (SylowAutStabilizer
        ((E.centralExtensionToPerfectCover
          F hperfect).sylowLift P))
      (by
        intro α
        exact coverAutomorphismLift_smul_sylowLift
          E F hs hnoncomm hperfect P α)
  projection_commutes := by
    intro α u
    exact coverAutomorphismLift_projection
      E F hs hnoncomm hperfect α.1 u

end UniversalCoverAutomorphismLift
end InductiveMcKay
end McKayConjecture
