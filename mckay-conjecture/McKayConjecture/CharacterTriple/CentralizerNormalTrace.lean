/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.CharacterTriple.CentralCorrespondence

/-!
# Traces of centralizer-times-normal decompositions

In a central isomorphism of character triples, a pair of matched normal
elements has the prescribed normal-character traces.  Multiplying both by a
matched centralizer residual multiplies those traces by one common scalar.
-/

noncomputable section

namespace McKayConjecture
namespace CharacterTriple
namespace CentralIsomorphismWitness

variable {A B : Type} [Finite A] [Finite B] [Group A] [Group B]
variable {T : CharacterTriple A} {U : CharacterTriple B}
variable {V W : Type}
variable [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] [Nontrivial V]
variable [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] [Nontrivial W]

/-- A centralizer residual followed by matched normal elements gives traces
which differ from the two normal-character values by one common scalar. -/
theorem exists_common_trace_scalar_of_centralizer_mul_normal
    (C : CentralIsomorphismWitness T U V W)
    (b z : B) (x : T.normalSubgroup) (y : U.normalSubgroup)
    (hb : b = z * (y : B))
    (hmatch : C.embedding (y : B) = (x : A))
    (hz :
      C.embedding z ∈
        Subgroup.centralizer (T.normalSubgroup : Set A)) :
    ∃ c : ℂˣ,
      LinearMap.trace ℂ V
          (C.leftProjective.operator (C.embedding b)) =
          (c : ℂ) * T.character.values x ∧
        LinearMap.trace ℂ W
          (C.rightProjective.operator b) =
          (c : ℂ) * U.character.values y := by
  obtain ⟨c, hleft, hright⟩ :=
    C.scalar_agreement z hz
  refine ⟨c, ?_, ?_⟩
  · have hop :
        C.leftProjective.operator (C.embedding b) =
          (c : ℂ) •
            (C.leftProjective.operator (x : A) :
              V →ₗ[ℂ] V) := by
      ext v
      rw [hb, map_mul, hmatch, C.leftAssociated.mul_normal,
        hleft]
      simp
    change
      LinearMap.trace ℂ V
          (C.leftProjective.operator (C.embedding b) :
            V →ₗ[ℂ] V) =
        _
    have htrace :=
      C.leftAssociated.traceFunction_normal x
    change
      LinearMap.trace ℂ V
          (C.leftProjective.operator (x : A) :
            V →ₗ[ℂ] V) =
        T.character.values x at htrace
    rw [hop, map_smul, htrace]
    rfl
  · have hop :
        C.rightProjective.operator b =
          (c : ℂ) •
            (C.rightProjective.operator (y : B) :
              W →ₗ[ℂ] W) := by
      ext w
      rw [hb, C.rightAssociated.mul_normal, hright]
      simp
    change
      LinearMap.trace ℂ W
          (C.rightProjective.operator b :
            W →ₗ[ℂ] W) =
        _
    have htrace :=
      C.rightAssociated.traceFunction_normal y
    change
      LinearMap.trace ℂ W
          (C.rightProjective.operator (y : B) :
            W →ₗ[ℂ] W) =
        U.character.values y at htrace
    rw [hop, map_smul, htrace]
    rfl

/-- Cross-multiplied trace identity for a centralizer-times-normal
decomposition.  This version avoids choosing or dividing by the common
scalar. -/
theorem trace_cross_of_centralizer_mul_normal
    (C : CentralIsomorphismWitness T U V W)
    (b z : B) (x : T.normalSubgroup) (y : U.normalSubgroup)
    (hb : b = z * (y : B))
    (hmatch : C.embedding (y : B) = (x : A))
    (hz :
      C.embedding z ∈
        Subgroup.centralizer (T.normalSubgroup : Set A)) :
    LinearMap.trace ℂ V
          (C.leftProjective.operator (C.embedding b)) *
        U.character.values y =
      LinearMap.trace ℂ W
          (C.rightProjective.operator b) *
        T.character.values x := by
  obtain ⟨c, hleft, hright⟩ :=
    C.exists_common_trace_scalar_of_centralizer_mul_normal
      b z x y hb hmatch hz
  rw [hleft, hright]
  ring

end CentralIsomorphismWitness
end CharacterTriple
end McKayConjecture
