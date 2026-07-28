/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.InductiveMcKay.CentralExtensionRestrictedTripleWitness
import McKayConjecture.InductiveMcKay.CentralTripleCliffordAssembly

/-!
# Bundled complete witness after stabilizer restriction

The generic restriction construction works in arbitrary universes.  This
file packages its universe-zero specialization in the bundled
`CompleteCentralIsomorphismWitness` interface used by the finite-group
reduction.
-/

noncomputable section

namespace McKayConjecture
namespace InductiveMcKay
namespace SylowAutomorphismLift

variable {A Q : Type}
variable [Group A] [Group Q] [Finite A]
variable {p : ℕ} [Fact p.Prime]
variable {E : GroupTheory.CentralExtension A Q} {S : Sylow p Q}

/-- The full upstairs inductive-McKay datum supplies a bundled complete
witness after restriction to the selected lifts of the downstairs character
stabilizer. -/
theorem nonempty_restrictedCompleteCentralIsomorphismWitness
    (L : SylowAutomorphismLift E S)
    (d : LocalInductiveMcKayData (E.sylowLift S))
    (χ : PPrimeIrreducibleCharacter Q p) :
    Nonempty
      (CompleteCentralIsomorphismWitness
        (restrictedAmbientTriple L χ)
        (restrictedIntermediateTriple L d χ)) := by
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
  exact
    ⟨{ leftSpace := V
       rightSpace := W
       witness :=
         restrictCentralIsomorphismWitness
           L d χ C hC }⟩

end SylowAutomorphismLift
end InductiveMcKay
end McKayConjecture
