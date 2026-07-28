/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.Algebra.Central.End
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# Finite-dimensional endomorphism algebras

The endomorphism algebra of a nonzero finite-dimensional vector space is
central simple and finite-dimensional.  Mathlib already provides centrality
and finite-dimensionality.  This file records the remaining simplicity
instance by transporting the matrix-ring instance through a finite basis.
-/

noncomputable section

namespace Representation

universe u v

variable {k : Type u} {V : Type v}
variable [Field k]
variable [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V] [Nontrivial V]

/-- The endomorphism ring of a nonzero finite-dimensional vector space over
a field is simple. -/
theorem endomorphism_isSimpleRing :
    IsSimpleRing (Module.End k V) := by
  let n := Module.finrank k V
  let b : Module.Basis (Fin n) k V :=
    Module.finBasis k V
  have hn : 0 < n := Module.finrank_pos
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  letI : IsSimpleRing (Matrix (Fin n) (Fin n) k) :=
    IsSimpleRing.matrix (Fin n) k
  exact
    IsSimpleRing.of_ringEquiv
      (LinearMap.toMatrixAlgEquiv b).symm.toRingEquiv
      (inferInstance :
        IsSimpleRing (Matrix (Fin n) (Fin n) k))

/-- Packaged central-simple and finite-dimensional structure of an
endomorphism algebra. -/
structure EndomorphismCentralSimpleData where
  /-- Centrality over the coefficient field. -/
  isCentral : Algebra.IsCentral k (Module.End k V)
  /-- Simplicity of the endomorphism ring. -/
  isSimple : IsSimpleRing (Module.End k V)
  /-- Finite-dimensionality over the coefficient field. -/
  finiteDimensional :
    FiniteDimensional k (Module.End k V)

/-- Canonical central-simple data for a nonzero finite-dimensional vector
space. -/
theorem endomorphismCentralSimpleData :
    EndomorphismCentralSimpleData (k := k) (V := V) where
  isCentral := inferInstance
  isSimple := endomorphism_isSimpleRing
  finiteDimensional := inferInstance

end Representation
