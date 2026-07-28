/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixGeneration
import McKayConjecture.GroupTheory.AlternatingSixRewriteNormalForm

/-!
# A presentation for the sixfold central cover of `A₆`

There are two noncentral generators `a,b` and four central generators
`k₀,…,k₃`.  The latter record the values of the four ATLAS relators.
The final two relations are the two relation-module rows used by the
standard Schur-cover construction.
-/

noncomputable section

open scoped commutatorElement

namespace McKayConjecture
namespace GroupTheory

/-- The six free generators: `a`, `b`, then the four central relator
values. -/
def alternatingSixSchurGenerator (i : Fin 6) :
    FreeGroup (Fin 6) :=
  FreeGroup.of i

/-- The two noncentral free generators. -/
def alternatingSixSchurFreeA : FreeGroup (Fin 6) :=
  alternatingSixSchurGenerator 0

def alternatingSixSchurFreeB : FreeGroup (Fin 6) :=
  alternatingSixSchurGenerator 1

/-- The `i`th central free generator. -/
def alternatingSixSchurFreeK (i : Fin 4) :
    FreeGroup (Fin 6) :=
  alternatingSixSchurGenerator ⟨i.val + 2, by omega⟩

/-- The four ATLAS relator words before adjoining their central values. -/
def alternatingSixSchurBaseRelator :
    Fin 4 → FreeGroup (Fin 6) :=
  ![
    alternatingSixSchurFreeA ^ 2,
    alternatingSixSchurFreeB ^ 4,
    (alternatingSixSchurFreeA * alternatingSixSchurFreeB) ^ 5,
    (alternatingSixSchurFreeA * alternatingSixSchurFreeB ^ 2) ^ 5
  ]

/-- The relation saying that the `i`th ATLAS relator equals `kᵢ`. -/
def alternatingSixSchurDefinitionRelator
    (i : Fin 4) :
    FreeGroup (Fin 6) :=
  alternatingSixSchurBaseRelator i *
    (alternatingSixSchurFreeK i)⁻¹

/-- Centrality of every `kᵢ` is included explicitly. -/
def alternatingSixSchurCentralityRelator
    (index : Fin 4 × Fin 6) :
    FreeGroup (Fin 6) :=
  ⁅alternatingSixSchurFreeK index.1,
    alternatingSixSchurGenerator index.2⁆

/-- The first relation-module row, `k₀³ k₂⁻² k₃ = 1`. -/
def alternatingSixSchurLatticeRelatorOne :
    FreeGroup (Fin 6) :=
  alternatingSixSchurFreeK 0 ^ 3 *
    alternatingSixSchurFreeK 2 ^ (-2 : ℤ) *
      alternatingSixSchurFreeK 3

/-- The second relation-module row, `k₁⁴ k₂³ k₃⁻³ = 1`. -/
def alternatingSixSchurLatticeRelatorTwo :
    FreeGroup (Fin 6) :=
  alternatingSixSchurFreeK 1 ^ 4 *
    alternatingSixSchurFreeK 2 ^ 3 *
      alternatingSixSchurFreeK 3 ^ (-3 : ℤ)

/-- Relators of the sixfold-cover presentation. -/
def alternatingSixSchurRelators :
    Set (FreeGroup (Fin 6)) :=
  Set.range alternatingSixSchurDefinitionRelator ∪
    Set.range alternatingSixSchurCentralityRelator ∪
      {alternatingSixSchurLatticeRelatorOne,
        alternatingSixSchurLatticeRelatorTwo}

/-- The group defined by the sixfold-cover presentation. -/
abbrev AlternatingSixSchurPresentedGroup :=
  PresentedGroup alternatingSixSchurRelators

/-- The six presented generators. -/
def alternatingSixSchurPresentedGenerator (i : Fin 6) :
    AlternatingSixSchurPresentedGroup :=
  PresentedGroup.of i

def alternatingSixSchurPresentedA :
    AlternatingSixSchurPresentedGroup :=
  alternatingSixSchurPresentedGenerator 0

def alternatingSixSchurPresentedB :
    AlternatingSixSchurPresentedGroup :=
  alternatingSixSchurPresentedGenerator 1

def alternatingSixSchurPresentedK (i : Fin 4) :
    AlternatingSixSchurPresentedGroup :=
  alternatingSixSchurPresentedGenerator ⟨i.val + 2, by omega⟩

/-- Every named presentation relator evaluates to one. -/
theorem alternatingSixSchurRelator_eq_one
    {relator : FreeGroup (Fin 6)}
    (hrelator : relator ∈ alternatingSixSchurRelators) :
    PresentedGroup.mk alternatingSixSchurRelators relator = 1 :=
  PresentedGroup.mk_eq_one_iff.mpr
    (Subgroup.subset_normalClosure hrelator)

/-- The four base relators have the advertised central values. -/
theorem alternatingSixSchurPresented_baseRelator
    (i : Fin 4) :
    PresentedGroup.mk alternatingSixSchurRelators
        (alternatingSixSchurBaseRelator i) =
      alternatingSixSchurPresentedK i := by
  have h :=
    alternatingSixSchurRelator_eq_one
      (Set.mem_union_left _ <|
        Set.mem_union_left _ ⟨i, rfl⟩ :
        alternatingSixSchurDefinitionRelator i ∈
          alternatingSixSchurRelators)
  change
    PresentedGroup.mk alternatingSixSchurRelators
        (alternatingSixSchurBaseRelator i *
          (alternatingSixSchurFreeK i)⁻¹) = 1 at h
  rw [map_mul, map_inv] at h
  exact mul_inv_eq_one.mp h

/-- Each `kᵢ` commutes with every presented generator. -/
theorem alternatingSixSchurPresentedK_commute_generator
    (i : Fin 4) (j : Fin 6) :
    Commute (alternatingSixSchurPresentedK i)
      (alternatingSixSchurPresentedGenerator j) := by
  have h :=
    alternatingSixSchurRelator_eq_one
      (Set.mem_union_left _ <|
        Set.mem_union_right _ ⟨(i, j), rfl⟩ :
        alternatingSixSchurCentralityRelator (i, j) ∈
          alternatingSixSchurRelators)
  change
    PresentedGroup.mk alternatingSixSchurRelators
        ⁅alternatingSixSchurFreeK i,
          alternatingSixSchurGenerator j⁆ = 1 at h
  rw [map_commutatorElement] at h
  change
    ⁅alternatingSixSchurPresentedK i,
      alternatingSixSchurPresentedGenerator j⁆ = 1 at h
  exact commutatorElement_eq_one_iff_commute.mp h

/-- Every `kᵢ` is central in the presented group. -/
theorem alternatingSixSchurPresentedK_mem_center
    (i : Fin 4) :
    alternatingSixSchurPresentedK i ∈
      Subgroup.center AlternatingSixSchurPresentedGroup := by
  rw [Subgroup.mem_center_iff]
  intro g
  symm
  apply PresentedGroup.induction_on g
  intro freeWord
  refine Quot.inductionOn freeWord ?_
  intro word
  induction word with
  | nil =>
      change Commute (alternatingSixSchurPresentedK i) 1
      exact Commute.one_right _
  | cons letter word ih =>
      rw [FreeGroup.quot_mk_eq_mk]
      rcases letter with ⟨j, positive⟩
      cases positive
      · change
          Commute (alternatingSixSchurPresentedK i)
            (PresentedGroup.mk alternatingSixSchurRelators
              (FreeGroup.mk ((j, false) :: word)))
        rw [show
          FreeGroup.mk ((j, false) :: word) =
            (FreeGroup.of j)⁻¹ * FreeGroup.mk word by rfl,
          map_mul]
        exact
          (alternatingSixSchurPresentedK_commute_generator i j).inv_right.mul_right ih
      · change
          Commute (alternatingSixSchurPresentedK i)
            (PresentedGroup.mk alternatingSixSchurRelators
              (FreeGroup.mk ((j, true) :: word)))
        rw [show
          FreeGroup.mk ((j, true) :: word) =
            FreeGroup.of j * FreeGroup.mk word by rfl,
          map_mul]
        exact
          (alternatingSixSchurPresentedK_commute_generator i j).mul_right ih

/-- The concrete `A₆` values assigned to the six presentation
generators. -/
def alternatingSixSchurProjectionGenerator
    (i : Fin 6) :
    AlternatingSix :=
  if i = 0 then alternatingSixPresentationA
  else if i = 1 then alternatingSixPresentationB
  else 1

/-- The concrete generator assignment kills every Schur-cover relator. -/
theorem alternatingSixSchurProjectionGenerator_kills_relators :
    ∀ r ∈ alternatingSixSchurRelators,
      FreeGroup.lift alternatingSixSchurProjectionGenerator r = 1 := by
  intro r hr
  rcases hr with hr | hr
  · rcases hr with ⟨i, rfl⟩ | ⟨ij, rfl⟩
    · fin_cases i
      · simpa [alternatingSixSchurDefinitionRelator,
          alternatingSixSchurBaseRelator,
          alternatingSixSchurFreeA, alternatingSixSchurFreeB,
          alternatingSixSchurFreeK,
          alternatingSixSchurGenerator,
          alternatingSixSchurProjectionGenerator] using
            alternatingSixPresentation_relations.1
      · simpa [alternatingSixSchurDefinitionRelator,
          alternatingSixSchurBaseRelator,
          alternatingSixSchurFreeA, alternatingSixSchurFreeB,
          alternatingSixSchurFreeK,
          alternatingSixSchurGenerator,
          alternatingSixSchurProjectionGenerator] using
            alternatingSixPresentation_relations.2.1
      · simpa [alternatingSixSchurDefinitionRelator,
          alternatingSixSchurBaseRelator,
          alternatingSixSchurFreeA, alternatingSixSchurFreeB,
          alternatingSixSchurFreeK,
          alternatingSixSchurGenerator,
          alternatingSixSchurProjectionGenerator] using
            alternatingSixPresentation_relations.2.2.1
      · simpa [alternatingSixSchurDefinitionRelator,
          alternatingSixSchurBaseRelator,
          alternatingSixSchurFreeA, alternatingSixSchurFreeB,
          alternatingSixSchurFreeK,
          alternatingSixSchurGenerator,
          alternatingSixSchurProjectionGenerator] using
            alternatingSixPresentation_relations.2.2.2
    · rcases ij with ⟨i, j⟩
      have hk :
          FreeGroup.lift alternatingSixSchurProjectionGenerator
              (alternatingSixSchurFreeK i) = 1 := by
        fin_cases i <;>
          simp [alternatingSixSchurFreeK,
            alternatingSixSchurGenerator,
            alternatingSixSchurProjectionGenerator]
      simp [alternatingSixSchurCentralityRelator, hk]
  · rcases hr with rfl | hr
    · simpa [alternatingSixSchurDefinitionRelator,
        alternatingSixSchurLatticeRelatorOne,
        alternatingSixSchurFreeK,
        alternatingSixSchurGenerator,
        alternatingSixSchurProjectionGenerator]
    · have hr' :
          r = alternatingSixSchurLatticeRelatorTwo := by
        simpa using hr
      subst r
      simp [alternatingSixSchurLatticeRelatorTwo,
        alternatingSixSchurFreeK,
        alternatingSixSchurGenerator,
        alternatingSixSchurProjectionGenerator]

/-- Projection of the Schur-cover presentation onto concrete `A₆`. -/
def alternatingSixSchurProjection :
    AlternatingSixSchurPresentedGroup →* AlternatingSix :=
  PresentedGroup.toGroup
    alternatingSixSchurProjectionGenerator_kills_relators

@[simp]
theorem alternatingSixSchurProjection_a :
    alternatingSixSchurProjection
        alternatingSixSchurPresentedA =
      alternatingSixPresentationA := by
  simp [alternatingSixSchurProjection,
    alternatingSixSchurPresentedA,
    alternatingSixSchurPresentedGenerator,
    alternatingSixSchurProjectionGenerator]

@[simp]
theorem alternatingSixSchurProjection_b :
    alternatingSixSchurProjection
        alternatingSixSchurPresentedB =
      alternatingSixPresentationB := by
  simp [alternatingSixSchurProjection,
    alternatingSixSchurPresentedB,
    alternatingSixSchurPresentedGenerator,
    alternatingSixSchurProjectionGenerator]

@[simp]
theorem alternatingSixSchurProjection_k
    (i : Fin 4) :
    alternatingSixSchurProjection
        (alternatingSixSchurPresentedK i) = 1 := by
  fin_cases i <;>
    simp [alternatingSixSchurProjection,
      alternatingSixSchurPresentedK,
      alternatingSixSchurPresentedGenerator,
      alternatingSixSchurProjectionGenerator]

/-- The Schur-cover presentation maps onto `A₆`. -/
theorem alternatingSixSchurProjection_surjective :
    Function.Surjective alternatingSixSchurProjection := by
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  rw [← alternatingSixGeneratorSubgroup_eq_top,
    Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact ⟨alternatingSixSchurPresentedA,
      alternatingSixSchurProjection_a⟩
  · exact ⟨alternatingSixSchurPresentedB,
      alternatingSixSchurProjection_b⟩

end GroupTheory
end McKayConjecture
