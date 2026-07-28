/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.UniversalCoverDominatesPerfectCover
import McKayConjecture.InductiveMcKay.CentralExtensionPerfectDescent
import McKayConjecture.InductiveMcKay.QuasisimpleHypothesis
import McKayConjecture.InductiveMcKay.UniversalCoverPerfectCoverAutomorphismLift

/-!
# Descent from a universal cover to a perfect central cover

Every perfect central cover of a fixed simple group is a quotient of its
universal cover.  Combining that group-theoretic fact with central-extension
descent gives three precise consequences of the universal-cover inductive
McKay hypothesis:

* the numerical local correspondence descends with no extra hypothesis;
* exact normalized central values descend with no extra hypothesis;
* the complete local inductive-McKay datum descends once automorphisms
  stabilizing the Sylow subgroup are lifted coherently through the quotient.

The source of the quotient is the universal cover, hence perfect.  This
perfectness is exactly what prevents the ambient centralizer from growing
after passage to the quotient, and therefore makes the scalar-agreement
clause descend.
-/

noncomputable section

universe u

namespace McKayConjecture
namespace InductiveMcKay

open GroupTheory
open scoped IsMulCommutative

variable {p : ℕ} [Fact p.Prime]
variable {U S A : Type u}
variable [Group U] [Group S] [Group A]
variable [Finite U] [Finite S] [Finite A]

namespace UniversalCoverInductiveMcKayHypothesis

/-- Universal-cover data supplies a numerical local correspondence on every
perfect central cover of the same simple target. -/
theorem localCorrespondence_on_perfect_cover
    (covers : UniversalCoverInductiveMcKayHypothesis.{u} p)
    (hs : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S)
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S)
    (hperfect : Group.IsPerfect A)
    (P : Sylow p A) :
    Nonempty (LocalCorrespondence P) := by
  let C : CentralExtension U A :=
    E.centralExtensionToPerfectCover F hperfect
  obtain ⟨d⟩ :=
    covers S hs hnoncomm U E (C.sylowLift P)
  exact ⟨d.quotientLocalCorrespondence C P⟩

/-- Universal-cover data also supplies the exact central-scalar numerical
condition on every perfect central cover. -/
theorem centralScalarLocalCorrespondence_on_perfect_cover
    (covers : UniversalCoverInductiveMcKayHypothesis.{u} p)
    (hs : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S)
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S)
    (hperfect : Group.IsPerfect A)
    (P : Sylow p A) :
    Nonempty (CentralScalarLocalCorrespondence P) := by
  let C : CentralExtension U A :=
    E.centralExtensionToPerfectCover F hperfect
  obtain ⟨d⟩ :=
    covers S hs hnoncomm U E (C.sylowLift P)
  exact
    ⟨d.quotientCentralScalarLocalCorrespondence
      C P E.sourcePerfect⟩

/-- After a coherent lift of Sylow-stabilizing automorphisms is supplied,
the entire equivariant numerical correspondence descends from the universal
cover to a perfect central cover. -/
theorem equivariantLocalCorrespondence_on_perfect_cover
    (covers : UniversalCoverInductiveMcKayHypothesis.{u} p)
    (hs : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S)
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S)
    (hperfect : Group.IsPerfect A)
    (P : Sylow p A)
    (L : SylowAutomorphismLift
      (E.centralExtensionToPerfectCover F hperfect) P) :
    Nonempty (EquivariantLocalCorrespondence P) := by
  let C : CentralExtension U A :=
    E.centralExtensionToPerfectCover F hperfect
  obtain ⟨d⟩ :=
    covers S hs hnoncomm U E (C.sylowLift P)
  exact ⟨L.quotientEquivariantLocalCorrespondence d⟩

/-- After a coherent lift of Sylow-stabilizing automorphisms is supplied,
the full local inductive-McKay datum descends from the universal cover to a
perfect central cover.  No additional character-triple or projective
representation hypothesis is required. -/
theorem localInductiveMcKayData_on_perfect_cover_of_sylowAutomorphismLift
    (covers : UniversalCoverInductiveMcKayHypothesis.{u} p)
    (hs : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S)
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S)
    (hperfect : Group.IsPerfect A)
    (P : Sylow p A)
    (L : SylowAutomorphismLift
      (E.centralExtensionToPerfectCover F hperfect) P) :
    Nonempty (LocalInductiveMcKayData P) := by
  let C : CentralExtension U A :=
    E.centralExtensionToPerfectCover F hperfect
  obtain ⟨d⟩ :=
    covers S hs hnoncomm U E (C.sylowLift P)
  letI : Group.IsPerfect U := E.sourcePerfect
  exact ⟨L.quotientLocalInductiveMcKayData d⟩

/-- Full local inductive-McKay data descend from the universal cover to
every perfect central cover.  The required coherent Sylow-automorphism lift
is canonical, so this theorem has no residual lifting hypothesis. -/
theorem localInductiveMcKayData_on_perfect_cover
    (covers : UniversalCoverInductiveMcKayHypothesis.{u} p)
    (hs : IsSimpleGroup S)
    (hnoncomm : ¬IsMulCommutative S)
    (E : UniversalCentralExtension U S)
    (F : CentralExtension A S)
    (hperfect : Group.IsPerfect A)
    (P : Sylow p A) :
    Nonempty (LocalInductiveMcKayData P) :=
  covers.localInductiveMcKayData_on_perfect_cover_of_sylowAutomorphismLift
    hs hnoncomm E F hperfect P
    (UniversalCoverAutomorphismLift.sylowAutomorphismLift
      E F hs hnoncomm hperfect P)

end UniversalCoverInductiveMcKayHypothesis
end InductiveMcKay
end McKayConjecture
