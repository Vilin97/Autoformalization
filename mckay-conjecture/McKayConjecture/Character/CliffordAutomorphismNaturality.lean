/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.AutomorphismInertiaPPrime
import McKayConjecture.Character.CliffordPPrimeCorrespondence
import McKayConjecture.Character.InductionEquivalenceTransport

/-!
# Naturality of Clifford induction under automorphisms

An ambient automorphism preserving a normal subgroup transports both a
normal character and its inertia character fibre.  Clifford induction of
the transported fibre character is the pullback of the original induced
character.  This is the pointwise character identity needed to prove
blockwise naturality of active Clifford assemblies.
-/

noncomputable section

namespace McKayConjecture

open CliffordCorrespondence
open CliffordEquivalence

namespace IrreducibleCharacter

variable {G : Type} [Group G] [Finite G]
variable (N : Subgroup G) [N.Normal]

noncomputable local instance cliffordAutomorphismNaturalityFintypeG :
    Fintype G :=
  Fintype.ofFinite G

/-- The inertia index is unchanged when a normal character is transported
by an ambient automorphism preserving the normal subgroup. -/
theorem inertia_index_smul_eq
    (a : NormalSubgroupAutStabilizer N)
    (θ : IrreducibleCharacter N) :
    (inertia N (a • θ)).index =
      (inertia N θ).index := by
  rw [← map_inertia_eq N a θ,
    Subgroup.index_map_equiv]

/-- Clifford induction commutes pointwise with automorphism transport on a
prime-to-`p` inertia fibre. -/
theorem cliffordPPrimeCorrespondence_transport_character
    (p : ℕ)
    (hp : p.Prime)
    (a : NormalSubgroupAutStabilizer N)
    (θ : IrreducibleCharacter N)
    (hindex : ¬p ∣ (inertia N θ).index)
    (χ : PPrimeIrreducibleCharactersOverInertia N θ p) :
    ((cliffordPPrimeCorrespondence
        N (a • θ) hp
        (by simpa only [inertia_index_smul_eq N a θ] using hindex))
      (pPrimeInertiaFibreTransportEquiv N p a θ χ)).1.1 =
      ((cliffordPPrimeCorrespondence
        N θ hp hindex χ).1.1).comap a.1.symm := by
  let eI := inertiaEquiv N a θ
  let χ' :=
    pPrimeInertiaFibreTransportEquiv N p a θ χ
  let leftCharacter :=
    (cliffordPPrimeCorrespondence
      N (a • θ) hp
      (by simpa only [inertia_index_smul_eq N a θ] using hindex)
      χ').1.1
  let rightCharacter :=
    (cliffordPPrimeCorrespondence
      N θ hp hindex χ).1.1
  have hcomm :
      a.1.symm.toMonoidHom.comp
          (inertia N (a • θ)).subtype =
        (inertia N θ).subtype.comp
          eI.symm.toMonoidHom := by
    ext x
    exact inertiaEquiv_symm_apply_coe N a θ x
  have hinduce :=
    ClassFunction.induce_comap_equiv
      (inertia N θ)
      (inertia N (a • θ))
      a.1.symm
      eI.symm
      hcomm
      χ.1.1.toClassFunction
  have hleft :
      leftCharacter.toClassFunction =
        ClassFunction.induce
          (inertia N (a • θ))
          χ'.1.1.toClassFunction := by
    exact
      inducedIrreducibleCharacter_toClassFunction
        N (a • θ) χ'.1.1
          (inertiaInduction_simple
            N (a • θ) χ'.1.1 χ'.1.2)
  have hright :
      rightCharacter.toClassFunction =
        ClassFunction.induce
          (inertia N θ)
          χ.1.1.toClassFunction := by
    exact
      inducedIrreducibleCharacter_toClassFunction
        N θ χ.1.1
          (inertiaInduction_simple
            N θ χ.1.1 χ.1.2)
  apply IrreducibleCharacter.ext
  funext g
  change
    leftCharacter.values g =
      rightCharacter.values (a.1.symm g)
  change
    leftCharacter.toClassFunction g =
      rightCharacter.toClassFunction (a.1.symm g)
  rw [hleft, hright]
  have hχ' :
      χ'.1.1.toClassFunction =
        ClassFunction.comapLinearEquiv
          eI.symm χ.1.1.toClassFunction := by
    ext x
    rfl
  rw [hχ']
  exact congrArg (fun f : ClassFunction G ↦ f g) hinduce

end IrreducibleCharacter
end McKayConjecture
