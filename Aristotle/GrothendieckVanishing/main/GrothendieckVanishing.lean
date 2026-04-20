import Aristotle.GrothendieckVanishing.main.IrreducibleStep

/-!
  GrothendieckVanishing.lean — Main theorem

  Grothendieck's vanishing theorem (Hartshorne III.2.7):
  For a Noetherian topological space X of dimension n, and any sheaf F
  of abelian groups on X, H^i(X, F) = 0 for all i > n.

  The proof assembles (FULLY PROVED — 0 sorry's):
  - Reduction to irreducible: ReducibleVanishing',
    grothendieck_vanishing_of_irreducible
  - IrreduciblePosVanishing (IrreducibleStep): irreducible case (all dimensions)
-/

universe u

open CategoryTheory TopologicalSpace Order Limits

/-! ## Reduction to irreducible spaces -/

private theorem ReducibleVanishing'
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
  let Fsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F, hF⟩
  change Subsingleton (Sheaf.H Fsh n)
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := X)
  set comps := hfin.toFinset with comps_def
  have hcover : ∀ x : X, x ∈ ⋃₀ (comps : Set (Set X)) := by
    intro x; simp [comps_def, Set.Finite.toFinset]
    exact Set.mem_sUnion.mp
      (sUnion_irreducibleComponents (X := (↑X : Type u)) ▸ Set.mem_univ x)
  have hcomp_irred : ∀ Z ∈ comps, Z ∈ irreducibleComponents X := by
    intro Z hZ; simp [comps_def] at hZ; exact hZ
  suffices ∀ (s : Finset (Set X)),
      (∀ Z ∈ s, Z ∈ irreducibleComponents X) →
      ∀ (G : TopCat.Presheaf AddCommGrpCat.{u} X) (hG : G.IsSheaf),
      (∀ x : X, x ∉ ⋃₀ (s : Set (Set X)) →
        ∀ (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj G),
        a = 0) →
      Subsingleton (Sheaf.H ((⟨G, hG⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n) by
    exact this comps hcomp_irred F hF (fun x hx => absurd (hcover x) hx)
  intro s; induction s using Finset.induction_on with
  | empty =>
    intro _ G hG hG_stalks
    let Gsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨G, hG⟩
    exact _root_.sheafH_subsingleton_of_isZero Gsh
      (by
        have hG_zero : IsZero Gsh :=
          sheaf_isZero_of_zero_stalks X hG (fun x a => hG_stalks x (by simp) a)
        simpa [Gsh] using hG_zero) n
  | @insert Z s' hZ_notin ih =>
    intro hs_irred G hG hG_stalks
    have hZ_comp := hs_irred Z (Finset.mem_insert_self Z s')
    have hZ_closed := isClosed_of_mem_irreducibleComponents Z hZ_comp
    have hZ_irred := hZ_comp.1
    let i := TopCat.closedIncl hZ_closed
    let Gsh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨G, hG⟩
    let GZ := ((TopCat.Sheaf.pullback AddCommGrpCat.{u} i).obj Gsh)
    let S := closedImmersionSES (Z := Z) (hZ := hZ_closed) (F := G) hG
    have hSE := closedImmersionSES_shortExact (Z := Z) (hZ := hZ_closed) (F := G) hG
    have hpush : Subsingleton (Sheaf.H S.X₃ n) := by
      haveI : IrreducibleSpace (TopCat.of Z) :=
        isIrreducible_iff_irreducibleSpace.mp hZ_irred
      let e : Sheaf.H GZ n ≃ Sheaf.H S.X₃ n := by
        simpa [S, closedImmersionSES, i, Gsh, GZ] using
          Equiv.ofBijective
            (ConcreteCategory.hom (PushforwardHIso Z hZ_closed GZ.cond n).hom)
            (ConcreteCategory.bijective_of_isIso (PushforwardHIso Z hZ_closed GZ.cond n).hom)
      exact (e.subsingleton_congr).mp
        (ih_irred (TopCat.of Z) (G := GZ.val) GZ.cond
          (topologicalKrullDim_subspace_le (X := (↑X : Type u)) Z)
          (lt_of_le_of_lt (topologicalKrullDim_subspace_le (X := (↑X : Type u)) Z) hn))
    have hker : Subsingleton (Sheaf.H S.X₁ n) := by
      have hker' :
          Subsingleton
            (Sheaf.H ((⟨S.X₁.val, S.X₁.cond⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) n) := by
        apply ih (fun Z' hZ' => hs_irred Z' (Finset.mem_insert_of_mem hZ')) S.X₁.val S.X₁.cond
        intro x hx a
        by_cases hxZ : x ∈ Z
        · -- closedIncl_unit_stalk_isIso: iso on stalks at z ∈ Z
          haveI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map S.g.val) := by
            simpa [S, closedImmersionSES, i, Gsh] using
              (TopCat.closedIncl_unit_stalk_isIso hZ_closed Gsh ⟨x, hxZ⟩)
          exact stalk_zero_of_ses_g_iso hSE x inferInstance a
        · have hx' : x ∉ ⋃₀ ((insert Z s' : Finset (Set X)) : Set (Set X)) := by
            simp only [Finset.coe_insert, Set.sUnion_insert, Set.mem_union] at hx ⊢
            push_neg; exact ⟨hxZ, hx⟩
          exact stalk_zero_of_shortExact_kernel hSE x (fun b => hG_stalks x hx' b) a
      simpa using hker'
    exact subsingleton_sheafH_of_shortExact_middle hSE n hker hpush

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
  · exact sheafH_subsingleton_of_isEmpty Fsh n
  · rw [not_isEmpty_iff] at hEmpty
    by_cases hIrred : IrreducibleSpace X
    · exact ih_irred X n hF le_rfl hn
    · exact ReducibleVanishing' X n hn (F := F) hF hIrred
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
          (fun Y _ _ m {G} hG hle hY =>
            IrreduciblePosVanishing (F := G) hG m hY
              (by
                intro Z _ m' G' hG' hlt hm'
                exact ih (topologicalKrullDim Z) (lt_of_lt_of_le hlt (hd ▸ hle))
                  Z m' G' hG' rfl hm'))))
    X n F hF rfl h
