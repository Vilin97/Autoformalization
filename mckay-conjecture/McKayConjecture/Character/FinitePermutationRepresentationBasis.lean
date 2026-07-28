/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.RepresentationTheory.Intertwining

/-!
# Finite permutation bases intrinsic to a representation

`PermutationModuleBasis` is phrased using ambient scalar-action
instances.  For recursive decomposition arguments it is more
convenient to package the same data directly for an arbitrary
representation.  The index type is bundled together with its finite
group action.
-/

noncomputable section

namespace Representation

variable {k P V W : Type}
variable [Field k] [Group P]
variable [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]

/-- A finite basis which is permuted by a given representation. -/
structure FinitePermutationBasis
    (ρ : Representation k P V) where
  /-- The finite indexing type. -/
  Index : Type
  /-- Finiteness data for the indexing type. -/
  indexFintype : Fintype Index
  /-- The permutation action on the indexing type. -/
  action : P →* Equiv.Perm Index
  /-- The underlying vector-space basis. -/
  basis : Module.Basis Index k V
  /-- The representation permutes the basis according to `action`. -/
  map_basis :
    ∀ (g : P) (i : Index),
      ρ g (basis i) = basis (action g i)

namespace FinitePermutationBasis

variable {ρ : Representation k P V}
variable {σ : Representation k P W}

/-- Transport a finite permutation basis backwards along an
equivalence of representations. -/
def transport (C : FinitePermutationBasis σ)
    (e : ρ.Equiv σ) :
    FinitePermutationBasis ρ where
  Index := C.Index
  indexFintype := C.indexFintype
  action := C.action
  basis := C.basis.map e.symm.toLinearEquiv
  map_basis := by
    intro g i
    rw [Module.Basis.map_apply]
    change ρ g (e.symm (C.basis i)) =
      e.symm (C.basis (C.action g i))
    rw [← C.map_basis g i]
    symm
    exact LinearMap.congr_fun
      (e.symm.toIntertwiningMap.isIntertwining' g)
      (C.basis i)

/-- The componentwise action on the disjoint union of two permutation
indexing types. -/
def sumAction
    (C : FinitePermutationBasis ρ)
    (D : FinitePermutationBasis σ) :
    P →* Equiv.Perm (C.Index ⊕ D.Index) where
  toFun g := Equiv.sumCongr (C.action g) (D.action g)
  map_one' := by
    simp only [map_one]
    exact
      (Equiv.Perm.sumCongr_one
        (α := C.Index) (β := D.Index))
  map_mul' g h := by
    simp only [map_mul]
    exact
      (Equiv.Perm.sumCongr_mul
        (C.action g) (D.action g)
        (C.action h) (D.action h)).symm

@[simp]
theorem sumAction_apply_inl
    (C : FinitePermutationBasis ρ)
    (D : FinitePermutationBasis σ)
    (g : P) (i : C.Index) :
    C.sumAction D g (Sum.inl i) =
      Sum.inl (C.action g i) :=
  rfl

@[simp]
theorem sumAction_apply_inr
    (C : FinitePermutationBasis ρ)
    (D : FinitePermutationBasis σ)
    (g : P) (i : D.Index) :
    C.sumAction D g (Sum.inr i) =
      Sum.inr (D.action g i) :=
  rfl

/-- Products of finite permutation representations are finite
permutation representations. -/
def prod
    (C : FinitePermutationBasis ρ)
    (D : FinitePermutationBasis σ) :
    FinitePermutationBasis (ρ.prod σ) := by
  letI : Fintype C.Index := C.indexFintype
  letI : Fintype D.Index := D.indexFintype
  exact
    { Index := C.Index ⊕ D.Index
      indexFintype := inferInstance
      action := C.sumAction D
      basis := C.basis.prod D.basis
      map_basis := by
        intro g i
        cases i with
        | inl i =>
            rw [C.sumAction_apply_inl]
            have hsource :
                C.basis.prod D.basis (Sum.inl i) =
                  (C.basis i, 0) := by
              apply Prod.ext
              · exact Module.Basis.prod_apply_inl_fst _ _ i
              · exact Module.Basis.prod_apply_inl_snd _ _ i
            have htarget :
                C.basis.prod D.basis
                    (Sum.inl (C.action g i)) =
                  (C.basis (C.action g i), 0) := by
              apply Prod.ext
              · exact Module.Basis.prod_apply_inl_fst _ _
                  (C.action g i)
              · exact Module.Basis.prod_apply_inl_snd _ _
                  (C.action g i)
            rw [hsource, htarget]
            change
              (ρ g (C.basis i), σ g 0) =
                (C.basis (C.action g i), 0)
            rw [C.map_basis, map_zero]
        | inr i =>
            rw [C.sumAction_apply_inr]
            have hsource :
                C.basis.prod D.basis (Sum.inr i) =
                  (0, D.basis i) := by
              apply Prod.ext
              · exact Module.Basis.prod_apply_inr_fst _ _ i
              · exact Module.Basis.prod_apply_inr_snd _ _ i
            have htarget :
                C.basis.prod D.basis
                    (Sum.inr (D.action g i)) =
                  (0, D.basis (D.action g i)) := by
              apply Prod.ext
              · exact Module.Basis.prod_apply_inr_fst _ _
                  (D.action g i)
              · exact Module.Basis.prod_apply_inr_snd _ _
                  (D.action g i)
            rw [hsource, htarget]
            change
              (ρ g 0, σ g (D.basis i)) =
                (0, D.basis (D.action g i))
            rw [D.map_basis, map_zero] }

/-- The zero representation has the empty permutation basis. -/
def empty (ρ : Representation k P V) [Subsingleton V] :
    FinitePermutationBasis ρ where
  Index := PEmpty
  indexFintype := inferInstance
  action := 1
  basis := Module.Basis.empty V
  map_basis := fun _ i => PEmpty.elim i

end FinitePermutationBasis
end Representation
