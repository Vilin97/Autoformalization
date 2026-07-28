/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralExtensionRestrictedWitnessDescent

/-!
# Full local inductive-McKay descent from a perfect central extension

A coherent lift of the Sylow-stabilizing automorphisms already descends the
equivariant numerical correspondence.  When the source of the central
extension is perfect, the restricted upstairs character-triple witnesses
descend as well.  Consequently the entire local inductive-McKay datum
descends, with no additional representation-theoretic premise.
-/

noncomputable section

universe u v

namespace McKayConjecture
namespace InductiveMcKay
namespace SylowAutomorphismLift

open GroupTheory
open CharacterTriple

variable {A : Type u} {Q : Type v}
variable [Group A] [Group Q] [Finite A] [Finite Q]
variable [Group.IsPerfect A]
variable {p : ℕ} [Fact p.Prime]
variable {E : CentralExtension A Q} {S : Sylow p Q}

/-- Full local inductive-McKay data descend along a central extension with
perfect source once a coherent lift of the Sylow-stabilizing automorphisms
has been chosen. -/
def quotientLocalInductiveMcKayData
    (L : SylowAutomorphismLift E S)
    (d : LocalInductiveMcKayData (E.sylowLift S)) :
    LocalInductiveMcKayData S where
  toEquivariantLocalCorrespondence :=
    L.quotientEquivariantLocalCorrespondence d
  triple_compatible := by
    intro χ
    obtain
      ⟨V, W, addV, moduleV, finiteV, nontrivialV,
        addW, moduleW, finiteW, nontrivialW, C, hC⟩ :=
      d.triple_compatible (inflatedCharacter E χ)
    letI : AddCommGroup V := addV
    letI : Module ℂ V := moduleV
    letI : Module.Finite ℂ V := finiteV
    letI : Nontrivial V := nontrivialV
    letI : AddCommGroup W := addW
    letI : Module ℂ W := moduleW
    letI : Module.Finite ℂ W := finiteW
    letI : Nontrivial W := nontrivialW
    let restricted :=
      restrictCentralIsomorphismWitness L d χ C hC
    exact
      (descendProjectiveCompatibilityWitness
        L d χ restricted rfl).tripleCompatible

end SylowAutomorphismLift
end InductiveMcKay
end McKayConjecture
