import Aristotle.GrothendieckVanishing.main.SetupCore
import Aristotle.GrothendieckVanishing.main.ReducibleVanishing

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

/-- On an irreducible noetherian space of positive Krull dimension, one can choose a proper
closed subset `Z ⊊ X` of strictly smaller Krull dimension, and the ambient cohomological bound
`n > dim X` automatically implies `n > dim Z`. This isolates the closed-subset selection used at
the start of Hartshorne Step 3. -/
theorem exists_closed_subset_lt_dim_of_irreducible_pos
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X) (hpos : topologicalKrullDim X > 0) :
    ∃ Z : Set X, IsClosed Z ∧ Z ≠ Set.univ ∧
      topologicalKrullDim (TopCat.of Z) < topologicalKrullDim X ∧
      ↑n > topologicalKrullDim (TopCat.of Z) := by
  simp only [topologicalKrullDim, gt_iff_lt] at hpos
  rw [Order.krullDim_pos_iff] at hpos
  obtain ⟨a, b, hab⟩ := hpos
  have hZ_ne_univ : a.carrier ≠ Set.univ := by
    intro h; exact lt_irrefl a (lt_of_lt_of_le hab
      (show b.carrier ⊆ a.carrier from by rw [h]; exact Set.subset_univ _))
  have hZ_dim : topologicalKrullDim (TopCat.of a.carrier) < topologicalKrullDim X :=
    topologicalKrullDim_lt_of_isIrreducible_of_isClosed a.isClosed' hZ_ne_univ
      (lt_of_le_of_lt (topologicalKrullDim_subspace_le X a.carrier)
        (lt_of_lt_of_le (show topologicalKrullDim X < ⊤ from
          lt_of_lt_of_le hn le_top) le_top))
  refine ⟨a.carrier, a.isClosed', hZ_ne_univ, hZ_dim, lt_trans hZ_dim hn⟩

/-! ## Remaining sub-lemmas and main theorem

The auxiliary lemmas and `irreduciblePosVanishing` are now in `IrreducibleStep.lean`
where they have access to `zeroOutsideInt_vanishing`, `cokernel_openHom_vanishing`,
and the stalk computation tools needed for their proofs. -/
