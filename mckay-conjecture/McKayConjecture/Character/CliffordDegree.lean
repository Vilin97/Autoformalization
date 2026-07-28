/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import Mathlib.LinearAlgebra.DFinsupp
import McKayConjecture.Character.SimpleConstituent

/-!
# Degree divisibility for Clifford constituents

Every irreducible constituent of the restriction of an irreducible
representation to a normal subgroup has degree dividing the ambient
degree.  We prove this directly from the isotypic decomposition in
`CliffordTheorem`: the restricted module is the direct sum of its finitely
many homogeneous components, and each component is a sum of copies of
the chosen simple constituent.
-/

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra

universe u v

namespace McKayConjecture

namespace CliffordTheorem

variable {k : Type u} [Field k]
variable {G : Type v} [Group G] [Finite G]

/-- The dimension of the chosen simple constituent of a normal-subgroup
restriction divides the dimension of the ambient simple representation. -/
theorem finrank_simpleConstituent_dvd
    (V : FDRep k G) [Simple V]
    (N : Subgroup G) [N.Normal] :
    Module.finrank k (simpleConstituent V N) ∣
      Module.finrank k V := by
  let components :
      Set (Submodule k[N] (restrictedModule V N)) :=
    Set.range (homogeneousComponent V N)
  let componentMap : G → components :=
    fun g ↦
      ⟨homogeneousComponent V N g, ⟨g, rfl⟩⟩
  letI : Finite components :=
    Finite.of_surjective componentMap (by
      rintro ⟨C, ⟨g, rfl⟩⟩
      exact ⟨g, rfl⟩)
  letI : Fintype components := Fintype.ofFinite components
  letI :
      ∀ C : components, Module.Finite k C.1 :=
    fun C ↦
      FiniteDimensional.of_injective
        (show C.1 →ₗ[k] restrictedModule V N from
          C.1.subtype.restrictScalars k)
        C.1.subtype_injective
  have hind :
      iSupIndep
        (fun C : components ↦ C.1) := by
    exact
      (sSupIndep_iff components).mp
        (sSupIndep_range_homogeneousComponent V N)
  have htop :
      ⨆ C : components, C.1 = ⊤ := by
    rw [← sSup_eq_iSup']
    exact sSup_range_homogeneousComponent_eq_top V N
  let decomposition :
      restrictedModule V N ≃ₗ[k]
        (∀ C : components, C.1) :=
    ((hind.linearEquiv htop).restrictScalars k).symm.trans
      (DFinsupp.linearEquivFunOnFintype (R := k))
  have hfinrank :
      Module.finrank k (restrictedModule V N) =
        ∑ C : components, Module.finrank k C.1 := by
    calc
      Module.finrank k (restrictedModule V N) =
          Module.finrank k (∀ C : components, C.1) :=
        decomposition.finrank_eq
      _ = ∑ C : components, Module.finrank k C.1 :=
        Module.finrank_pi_fintype k
  change
    Module.finrank k (simpleConstituent V N) ∣
      Module.finrank k (restrictedModule V N)
  rw [hfinrank]
  apply Finset.dvd_sum
  intro C _
  rcases C with ⟨C, ⟨g, rfl⟩⟩
  rw [finrank_homogeneousComponent_eq_multiplicity_mul,
    finrank_conjugateConstituent]
  exact dvd_mul_left _ _

end CliffordTheorem

namespace FDRep

variable {G : Type} [Group G]

/-- The packaged constituent has the vector-space dimension of the
underlying simple submodule selected by Clifford theory. -/
@[simp]
theorem normalSimpleConstituent_finrank
    (V : FDRep ℂ G) [Simple V]
    (N : Subgroup G) [N.Normal] :
    Module.finrank ℂ (normalSimpleConstituent V N) =
      Module.finrank ℂ
        (CliffordTheorem.simpleConstituent V N) :=
  rfl

end FDRep

namespace IrreducibleCharacter

variable {G : Type} [Group G] [Finite G]

/-- The degree of the canonical normal-subgroup constituent divides the
degree of the ambient irreducible character. -/
theorem normalSimpleConstituent_degree_dvd
    (χ : IrreducibleCharacter G)
    (N : Subgroup G) [N.Normal] :
    (χ.normalSimpleConstituent N).degree ∣ χ.degree := by
  rw [normalSimpleConstituent,
    ofSimple_degree,
    FDRep.normalSimpleConstituent_finrank,
    ← χ.realization_finrank]
  exact
    CliffordTheorem.finrank_simpleConstituent_dvd
      χ.realization N

/-- A constituent of the restriction of a prime-to-`p` irreducible
character to a normal subgroup again has prime-to-`p` degree. -/
theorem normalSimpleConstituent_isPPrimeDegree
    {p : ℕ} (χ : IrreducibleCharacter G)
    (N : Subgroup G) [N.Normal]
    (hχ : χ.IsPPrimeDegree p) :
    (χ.normalSimpleConstituent N).IsPPrimeDegree p := by
  intro hp
  exact hχ
    (hp.trans (χ.normalSimpleConstituent_degree_dvd N))

end IrreducibleCharacter

end McKayConjecture
