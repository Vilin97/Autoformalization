import Aristotle.GrothendieckVanishing.main.IrreducibleStep

/-!
  GrothendieckVanishing.lean — Main theorem

  Grothendieck's vanishing theorem (Hartshorne III.2.7):
  For a Noetherian topological space X of dimension n, and any sheaf F
  of abelian groups on X, H^i(X, F) = 0 for all i > n.

  The proof assembles (FULLY PROVED — 0 sorry's):
  - Reduction to irreducible: ReducibleVanishing,
    grothendieck_vanishing_of_irreducible
  - irreducible dim-zero base case here; positive-dimensional irreducible step in
    IrreducibleStep.lean
-/

universe u

open CategoryTheory TopologicalSpace Order Limits Opposite

/-! ## Reduction to irreducible spaces -/

theorem ReducibleVanishing
    (X : TopCat.{u}) [NoetherianSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X)
    {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf)
    (_ : ¬ IrreducibleSpace X) [Nonempty X]
    (ih_irred : ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
      [IrreducibleSpace Y] {G : TopCat.Presheaf AddCommGrpCat.{u} Y} (hG : G.IsSheaf),
      topologicalKrullDim Y ≤ topologicalKrullDim X →
      n > topologicalKrullDim Y →
      Subsingleton (Sheaf.H (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} Y) n)) :
    Subsingleton (Sheaf.H ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n) := by
  classical
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := X)
  set comps := hfin.toFinset with comps_def
  have hcover : ∀ x : X, x ∈ ⋃₀ (comps : Set (Set X)) := fun x => by
    simpa [comps_def, Set.Finite.toFinset] using Set.mem_sUnion.mp
      (sUnion_irreducibleComponents (X := (↑X : Type u)) ▸ Set.mem_univ x)
  have hcomp_irred : ∀ Z ∈ comps, Z ∈ irreducibleComponents X := by simp [comps_def]
  suffices ∀ (s : Finset (Set X)),
      (∀ Z ∈ s, Z ∈ irreducibleComponents X) →
      ∀ (Gsh : TopCat.Sheaf AddCommGrpCat.{u} X),
      (∀ x : X, x ∉ ⋃₀ (s : Set (Set X)) →
        ∀ (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj Gsh.val),
        a = 0) →
      Subsingleton (Sheaf.H Gsh n) by
    exact this comps hcomp_irred ⟨F, hF⟩ (fun x hx => absurd (hcover x) hx)
  intro s; induction s using Finset.induction_on with
  | empty =>
    intro _ Gsh hG_stalks
    exact sheafH_subsingleton_of_isZero
      (sheaf_isZero_of_zero_stalks X Gsh.cond (fun x a => hG_stalks x (by simp) a)) n
  | @insert Z s' hZ_notin ih =>
    intro hs_irred Gsh hG_stalks
    have hZ_comp := hs_irred Z (Finset.mem_insert_self Z s')
    have hZ_closed := isClosed_of_mem_irreducibleComponents Z hZ_comp
    let GZ := ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (TopCat.closedIncl hZ_closed)).obj Gsh)
    let S := closedImmersionSES (Z := Z) (hZ := hZ_closed) Gsh
    have hSE := closedImmersionSES_shortExact (Z := Z) (hZ := hZ_closed) Gsh
    have hker : Subsingleton (Sheaf.H S.X₁ n) := by
      apply ih (fun Z' hZ' => hs_irred Z' (Finset.mem_insert_of_mem hZ')) S.X₁
      intro x hx a
      by_cases hxZ : x ∈ Z
      · -- closedIncl_unit_stalk_isIso: iso on stalks at z ∈ Z
        haveI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.g.val) := by
          simpa [S] using
            (TopCat.closedIncl_unit_stalk_isIso (C := AddCommGrpCat.{u})
              (hs := hZ_closed) Gsh ⟨x, hxZ⟩)
        exact stalk_zero_of_ses_g_iso S hSE x inferInstance a
      · have hx' : x ∉ ⋃₀ ((insert Z s' : Finset (Set X)) : Set (Set X)) := by
          simpa only [Finset.coe_insert, Set.sUnion_insert, Set.mem_union, not_or] using ⟨hxZ, hx⟩
        exact stalk_zero_of_shortExact_kernel S hSE x (hG_stalks x hx') a
    exact subsingleton_sheafH_of_closedImmersion_middle
      (Z := Z) (hZ := hZ_closed) Gsh n
      (by simpa [S] using hker)
      (by
        haveI : IrreducibleSpace (TopCat.of Z) :=
          isIrreducible_iff_irreducibleSpace.mp hZ_comp.1
        simpa [GZ] using
          ih_irred (TopCat.of Z) (G := GZ.val) GZ.cond
            (topologicalKrullDim_subspace_le (X := (↑X : Type u)) Z)
            (topologicalKrullDim_subspace_lt_of_lt (X := (↑X : Type u)) Z hn))

private theorem irreducible_dim_zero_vanishing
    {X : TopCat.{u}} [NoetherianSpace X] [IrreducibleSpace X]
    {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf)
    (n : ℕ) (hn : n > topologicalKrullDim X)
    (hdim : topologicalKrullDim X ≤ 0) :
    Subsingleton (Sheaf.H (⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) n) := by
  let Fsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F, hF⟩
  change Subsingleton (Sheaf.H Fsh n)
  have hFlasque : IsFlasqueSheaf Fsh := fun {U V} i => by
    rcases opens_eq_bot_or_top_of_irreducibleSpace_dim_zero hdim U with rfl | rfl
    · exact Fsh.isTerminalOfEmpty.isZero.epi _
    · have hV := le_antisymm le_top (homOfLE le_top ≫ i |>.le); subst hV
      rw [Subsingleton.elim i (𝟙 ⊤), op_id, F.map_id]; infer_instance
  have hn_ne : n ≠ 0 := fun h => by
    subst h; exact absurd hn (not_lt.mpr topologicalKrullDim_nonneg)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn_ne
  exact sheafH_subsingleton_of_flasque X Fsh hFlasque m

theorem grothendieck_vanishing_of_irreducible
    (X : TopCat.{u}) [TopologicalSpace.NoetherianSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X)
    {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf)
    (ih_irred : ∀ (Y : TopCat.{u}) [TopologicalSpace.NoetherianSpace Y]
      [IrreducibleSpace Y] (m : ℕ) {G : TopCat.Presheaf AddCommGrpCat.{u} Y} (hG : G.IsSheaf),
      topologicalKrullDim Y ≤ topologicalKrullDim X →
      m > topologicalKrullDim Y →
      Subsingleton (Sheaf.H (⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} Y) m)) :
    Subsingleton (Sheaf.H ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n) := by
  let Fsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F, hF⟩
  change Subsingleton (Sheaf.H Fsh n)
  by_cases hEmpty : IsEmpty X
  · letI := hEmpty
    simpa using sheafH_subsingleton_of_isEmpty Fsh n
  · rw [not_isEmpty_iff] at hEmpty
    by_cases hIrred : IrreducibleSpace X
    · exact ih_irred X n hF le_rfl hn
    · exact ReducibleVanishing X n hn (F := F) hF hIrred
        (fun Y [_] [_] {G} hG hle hY => ih_irred Y n (G := G) hG hle hY)

/-! ## Main theorem -/

/-- **Grothendieck's vanishing theorem** (Hartshorne III, Theorem 2.7). -/
theorem GrothendieckVanishing (X : TopCat.{u}) [NoetherianSpace X]
    (n : ℕ) (h : n > topologicalKrullDim X)
    {F : TopCat.Presheaf AddCommGrpCat.{u} X} (hF : F.IsSheaf) :
    Subsingleton (Sheaf.H ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n) := by
  let Fsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F, hF⟩
  change Subsingleton (Sheaf.H Fsh n)
  have hwf : WellFounded (fun (a b : WithBot ℕ∞) => a < b) := IsWellFounded.wf
  exact hwf.induction (C := fun d =>
    ∀ (X : TopCat.{u}) [NoetherianSpace X]
      (n : ℕ) (F : TopCat.Presheaf AddCommGrpCat.{u} X) (hF : F.IsSheaf),
      topologicalKrullDim X = d → n > d →
        Subsingleton (Sheaf.H ((⟨F, hF⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n))
    (topologicalKrullDim X) (fun d ih X _ n F hF hd hn => by
      let Fsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F, hF⟩
      -- Reduce to irreducible X
      simpa [Fsh] using
        (grothendieck_vanishing_of_irreducible X n (hd ▸ hn) (F := F) hF
          (fun Y _ _ m {G} hG hle hY => by
            by_cases hposY : topologicalKrullDim Y > 0
            · exact IrreduciblePosVanishing (F := G) hG hposY m hY
                (by
                  intro Z _ m' G' hG' hlt hm'
                  exact ih (topologicalKrullDim Z) (lt_of_lt_of_le hlt (hd ▸ hle))
                    Z m' G' hG' rfl hm')
            · exact irreducible_dim_zero_vanishing (F := G) hG m hY (le_of_not_gt hposY))))
    X n F hF rfl h
