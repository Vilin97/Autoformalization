import Aristotle.GrothendieckVanishing.main.SetupCore
import Aristotle.GrothendieckVanishing.main.ReducibleVanishing

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

/-! ## Main vanishing theorems -/

/-- **Reducible vanishing** (Hartshorne III.2.7, reducible case).
    This is proved in `ReducibleVanishing.lean`; `Setup.lean` re-exports the
    finished theorem so downstream files do not depend on the auxiliary primed
    name. -/
theorem ReducibleVanishing
    (X : TopCat.{u}) [NoetherianSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hNotIrred : ¬ IrreducibleSpace X) [Nonempty X]
    (ih_irred : ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
      [IrreducibleSpace Y] (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y ≤ topologicalKrullDim X →
      n > topologicalKrullDim Y → Subsingleton (Sheaf.H G n)) :
    Subsingleton (Sheaf.H F n) :=
  ReducibleVanishing' X n hn F hNotIrred ih_irred

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
    intro h
    exact lt_irrefl a (lt_of_lt_of_le hab
      (show b.carrier ⊆ a.carrier from by
        rw [show a.carrier = Set.univ from h]
        exact Set.subset_univ _))
  have hZ_dim : topologicalKrullDim (TopCat.of a.carrier) < topologicalKrullDim X := by
    exact topologicalKrullDim_lt_of_isIrreducible_of_isClosed a.isClosed' hZ_ne_univ
      (lt_of_le_of_lt (topologicalKrullDim_subspace_le X a.carrier)
        (lt_of_lt_of_le (show topologicalKrullDim X < ⊤ from by
          exact lt_of_lt_of_le hn le_top) le_top))
  refine ⟨a.carrier, a.isClosed', hZ_ne_univ, hZ_dim, lt_trans hZ_dim hn⟩

/-- In the irreducible positive-dimensional case, once a proper closed subset `Z` of smaller
dimension has been chosen, the pushforward term `i_*(i^*F)` in the closed-immersion short exact
sequence vanishes in degree `n` by the induction hypothesis on `Z`. -/
theorem irreduciblePos_pushforward_subsingleton
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X]
    (n : ℕ) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (ih : ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
      (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y < topologicalKrullDim X →
      n > topologicalKrullDim Y →
      Subsingleton (Sheaf.H G n))
    (Z : Set X) (hZ_closed : IsClosed Z)
    (hZ_dim : topologicalKrullDim (TopCat.of Z) < topologicalKrullDim X)
    (hn_Z : ↑n > topologicalKrullDim (TopCat.of Z))
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X))
    (hS₃ : S.X₃ = (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)).obj F)) :
    Subsingleton (Sheaf.H S.X₃ n) := by
  rw [hS₃]
  exact PushforwardHVanishing Z hZ_closed _ n (@ih (TopCat.of Z) _ _ hZ_dim hn_Z)

/-- Hartshorne III.2.7 Steps 3-5, isolated as the remaining kernel lemma. Starting from the
closed-immersion short exact sequence `0 → K → F → i_*(i^*F) → 0` attached to a proper closed
subset `Z ⊊ X`, this is the genuine missing argument: one must prove vanishing for the kernel
term `K` via direct limits, finite-generator reduction, and the `zeroOutsideInt` analysis. -/
theorem irreduciblePos_kernel_subsingleton
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X) (hpos : topologicalKrullDim X > 0)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (ih : ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
      (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y < topologicalKrullDim X →
      n > topologicalKrullDim Y →
      Subsingleton (Sheaf.H G n))
    (Z : Set X) (hZ_closed : IsClosed Z) (hZ_ne_univ : Z ≠ Set.univ)
    (hZ_dim : topologicalKrullDim (TopCat.of Z) < topologicalKrullDim X)
    (hn_Z : ↑n > topologicalKrullDim (TopCat.of Z))
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X))
    (hSE : S.ShortExact) (hS₂ : S.X₂ = F)
    (hS₃ : S.X₃ = (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)).obj F)) :
    Subsingleton (Sheaf.H S.X₁ n) := by
  sorry -- Hartshorne III.2.7 Steps 3-5 via zeroOutsideInt/direct limits

set_option synthInstance.maxHeartbeats 80000 in
/-- **Irreducible positive-dimension vanishing** (Hartshorne III.2.7, irreducible case).
    For an irreducible Noetherian space `X` of dim `d ≥ 1`, cohomology vanishing above
    the dimension follows from vanishing on all spaces of strictly smaller dimension.

    **Important:** the naive closed-support argument for the kernel of
    `F → i_*(i^*F)` is *not* valid on an irreducible space: from
    `K_x = 0` on a proper closed subset `Z`, one only gets
    `supp(K) ⊆ X \ Z`, and `X \ Z` may be dense of the same dimension as `X`.

    The correct proof is Hartshorne's Steps 3-5:
    1. write `F` as a filtered colimit of finitely generated subsheaves and use
       cohomology/direct-limit compatibility on noetherian spaces;
    2. reduce by induction on the number of generators to the case where `F` is
       generated by one section `s ∈ F(U)`;
    3. realize that singly generated sheaf as a quotient of `Z_U`
       (formalized here by `zeroOutsideInt U`);
    4. reduce vanishing for subsheaves of `Z_U` to vanishing for `Z_V` on a
       smaller nonempty open `V ⊆ U`;
    5. prove vanishing of `Z_U` from `0 → Z_U → Z → Z_Y → 0`, using that the
       constant sheaf `Z` is flasque on irreducible spaces and that
       `Y = X \ U` has strictly smaller dimension.

    The present code below only sets up the initial proper closed subset and the
    pushforward vanishing term. The kernel term remains the genuine Hartshorne
    Steps 3-5 gap. -/
theorem IrreduciblePosVanishing
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X) (hpos : topologicalKrullDim X > 0)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (ih : ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
      (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y < topologicalKrullDim X →
      n > topologicalKrullDim Y →
      Subsingleton (Sheaf.H G n)) :
    Subsingleton (Sheaf.H F n) := by
  obtain ⟨Z, hZ_closed, hZ_ne_univ, hZ_dim, hn_Z⟩ :=
    exists_closed_subset_lt_dim_of_irreducible_pos X n hn hpos
  obtain ⟨S, hSE, hS₂, hS₃⟩ := ClosedImmersionSES Z hZ_closed F
  have hPush : Subsingleton (Sheaf.H S.X₃ n) :=
    irreduciblePos_pushforward_subsingleton X n F ih Z hZ_closed hZ_dim hn_Z S hS₃
  have hKer : Subsingleton (Sheaf.H S.X₁ n) :=
    irreduciblePos_kernel_subsingleton X n hn hpos F ih Z hZ_closed hZ_ne_univ hZ_dim hn_Z
      S hSE hS₂ hS₃
  rw [← hS₂]
  exact subsingleton_sheafH_of_shortExact_middle hSE n hKer hPush
