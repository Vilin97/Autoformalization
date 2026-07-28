/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.Character.FinitePermutationRepresentationBasis
import McKayConjecture.Character.PrimitivePermutationModuleNormalizerExtension

/-!
# Normalizer extensions from an intrinsic finite permutation basis

`FinitePermutationBasis` packages a permutation basis directly for an
arbitrary representation.  This file transfers it to the typeclass-based
`PermutationModuleBasis` interface, identifies the reconstructed
representation with the original one, and exposes the resulting
Brauer-normalizer extension for that local typeclass realization.
-/

noncomputable section

namespace Representation
namespace FinitePermutationBasis

variable {p : ℕ} [Fact p.Prime]
variable {k P V : Type}
variable [Field k] [CharP k p]
variable [Group P] [Finite P]
variable [AddCommGroup V] [Module k V]

variable {ρ : Representation k P V}
variable (B : FinitePermutationBasis ρ)

/-- The vector action encoded by a representation, installed only locally
when using the typeclass-based permutation-module API. -/
@[instance_reducible]
def representationDistribMulAction
    (ρ : Representation k P V) :
    DistribMulAction P V where
  smul g v := ρ g v
  one_smul v := by
    change ρ 1 v = v
    rw [map_one]
    rfl
  mul_smul g h v := by
    change ρ (g * h) v = ρ g (ρ h v)
    rw [map_mul]
    rfl
  smul_add g x y :=
    (ρ g).map_add x y
  smul_zero g :=
    (ρ g).map_zero

omit [Finite P] in
/-- The representation action commutes with scalar multiplication. -/
theorem representationSMulCommClass
    (ρ : Representation k P V)
    [SMul P V]
    (hsmul : ∀ g v, g • v = ρ g v) :
    SMulCommClass P k V where
  smul_comm g a v := by
    rw [hsmul, (ρ g).map_smul, hsmul]

/-- The permutation action encoded in the intrinsic basis. -/
@[instance_reducible]
def indexMulAction :
    MulAction P B.Index where
  smul g i := B.action g i
  one_smul i := by
    change B.action 1 i = i
    rw [map_one]
    rfl
  mul_smul g h i := by
    change B.action (g * h) i =
      B.action g (B.action h i)
    rw [map_mul]
    rfl

/-- Regard an intrinsic finite permutation basis as a
`PermutationModuleBasis` for its locally installed actions. -/
def toPermutationModuleBasis :
    letI : DistribMulAction P V :=
      representationDistribMulAction ρ
    letI : SMulCommClass P k V :=
      representationSMulCommClass ρ (fun _ _ ↦ rfl)
    letI : MulAction P B.Index :=
      B.indexMulAction
    PermutationModuleBasis
      (k := k) (P := P) (V := V) (ι := B.Index) := by
  letI : DistribMulAction P V :=
    representationDistribMulAction ρ
  letI : SMulCommClass P k V :=
    representationSMulCommClass ρ (fun _ _ ↦ rfl)
  letI : MulAction P B.Index :=
    B.indexMulAction
  exact
    { basis := B.basis
      smul_basis := fun g i ↦ B.map_basis g i }

omit [Finite P] in
/-- The representation reconstructed from the local actions is the original
representation. -/
theorem toPermutationModuleBasis_representation :
    letI : DistribMulAction P V :=
      representationDistribMulAction ρ
    letI : SMulCommClass P k V :=
      representationSMulCommClass ρ (fun _ _ ↦ rfl)
    letI : MulAction P B.Index :=
      B.indexMulAction
    B.toPermutationModuleBasis.representation = ρ := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  rfl

include B

/-- A faithful representation with an intrinsic finite permutation basis
has a full Brauer-normalizer extension for its typeclass-action
realization. -/
theorem hasBrauerNormalizerExtension_of_typeclassRealization
    (hP : IsPGroup p P)
    (hfaithful : Function.Injective ρ) :
    letI : Fintype P := Fintype.ofFinite P
    letI : Fintype B.Index := B.indexFintype
    letI : DistribMulAction P V :=
      representationDistribMulAction ρ
    letI : SMulCommClass P k V :=
      representationSMulCommClass ρ (fun _ _ ↦ rfl)
    letI : MulAction P B.Index :=
      B.indexMulAction
    let C := B.toPermutationModuleBasis
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction C.representation)
    letI :=
      endomorphismConjugation_smulCommClass
        (representationLinearAction C.representation)
    HasBrauerNormalizerExtension (k := k)
      (representationInteriorAction C.representation) := by
  letI : Fintype P :=
    Fintype.ofFinite P
  letI : Fintype B.Index :=
    B.indexFintype
  letI : DistribMulAction P V :=
    representationDistribMulAction ρ
  letI : SMulCommClass P k V :=
    representationSMulCommClass ρ (fun _ _ ↦ rfl)
  letI : MulAction P B.Index :=
    B.indexMulAction
  let C := B.toPermutationModuleBasis
  have hC : C.representation = ρ :=
    B.toPermutationModuleBasis_representation
  have hfaithfulC : Function.Injective C.representation := by
    rw [hC]
    exact hfaithful
  have h :=
    C.hasBrauerNormalizerExtension_of_faithfulPermutationBasis
      hP hfaithfulC
  exact h

/-- The homomorphism field required by the primitive residue-Dade interface,
obtained by forgetting the conjugation certificate for the typeclass-action
realization. -/
theorem hasBrauerNormalizerHomExtension_of_typeclassRealization
    (hP : IsPGroup p P)
    (hfaithful : Function.Injective ρ) :
    letI : Fintype P := Fintype.ofFinite P
    letI : Fintype B.Index := B.indexFintype
    letI : DistribMulAction P V :=
      representationDistribMulAction ρ
    letI : SMulCommClass P k V :=
      representationSMulCommClass ρ (fun _ _ ↦ rfl)
    letI : MulAction P B.Index :=
      B.indexMulAction
    let C := B.toPermutationModuleBasis
    letI :=
      endomorphismConjugationMulSemiringAction
        (representationLinearAction C.representation)
    letI :=
      endomorphismConjugation_smulCommClass
        (representationLinearAction C.representation)
    HasBrauerNormalizerHomExtension (k := k)
      (representationInteriorAction C.representation) := by
  letI : Fintype P :=
    Fintype.ofFinite P
  letI : Fintype B.Index :=
    B.indexFintype
  letI : DistribMulAction P V :=
    representationDistribMulAction ρ
  letI : SMulCommClass P k V :=
    representationSMulCommClass ρ (fun _ _ ↦ rfl)
  letI : MulAction P B.Index :=
    B.indexMulAction
  let C := B.toPermutationModuleBasis
  letI :=
    endomorphismConjugationMulSemiringAction
      (representationLinearAction C.representation)
  letI :=
    endomorphismConjugation_smulCommClass
      (representationLinearAction C.representation)
  exact Nonempty.map
    BrauerNormalizerExtension.toHomExtension
    (B.hasBrauerNormalizerExtension_of_typeclassRealization
      hP hfaithful)

end FinitePermutationBasis
end Representation
