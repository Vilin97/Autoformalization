/-
  IrreducibleStep.lean — Vanishing for irreducible spaces of positive dimension

  Key results:
  - subsingleton_ext_of_ses: PROVED — abstract LES vanishing
  - constantSheaf_flasque_of_irreducible: PROVED (in ConstantSheafFlasque.lean)
  - constantSheaf_cohomology_vanishing: PROVED from flasque + FlasqueVanishing
  - grothendieck_vanishing_irreducible_pos: uses IrreduciblePosVanishing (sorry)
-/
import Aristotle.GrothendieckVanishing.main.Setup
import Aristotle.GrothendieckVanishing.main.ConstantSheafFlasque

universe u

open CategoryTheory TopologicalSpace Abelian

/-- Given a short exact sequence `0 → X₁ → X₂ → X₃ → 0`, if `Ext(Z, X₃, n) = 0`
    and `Ext(Z, X₂, n+1) = 0`, then `Ext(Z, X₁, n+1) = 0`. -/
theorem subsingleton_ext_of_ses {C : Type*} [Category C] [Abelian C] [HasExt C]
    {S : ShortComplex C} (hS : S.ShortExact) (Z : C) (n : ℕ)
    (h₃ : Subsingleton (Ext Z S.X₃ n))
    (h₂ : Subsingleton (Ext Z S.X₂ (n + 1))) :
    Subsingleton (Ext Z S.X₁ (n + 1)) := by
  constructor
  intro a b
  have h_a_f : a.comp (Ext.mk₀ S.f) rfl = 0 := Subsingleton.elim _ _
  have h_b_f : b.comp (Ext.mk₀ S.f) rfl = 0 := Subsingleton.elim _ _
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ Z hS a h_a_f rfl
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₁ Z hS b h_b_f rfl
  rw [← hc, ← hd, Subsingleton.elim c d]

/-- Given a short exact sequence `0 → X₁ → X₂ → X₃ → 0`, if `Ext(Z, X₁, n) = 0`
    and `Ext(Z, X₃, n) = 0`, then `Ext(Z, X₂, n) = 0`.
    This is the "middle term" version of `subsingleton_ext_of_ses`. -/
theorem subsingleton_ext_of_ses_middle {C : Type*} [Category C] [Abelian C] [HasExt C]
    {S : ShortComplex C} (hS : S.ShortExact) (Z : C) (n : ℕ)
    (h₁ : Subsingleton (Ext Z S.X₁ n))
    (h₃ : Subsingleton (Ext Z S.X₃ n)) :
    Subsingleton (Ext Z S.X₂ n) := by
  constructor
  intro a b
  have h₃' : Subsingleton (Ext Z S.X₃ (n + 0)) := (add_zero n) ▸ h₃
  have ha : a.comp (Ext.mk₀ S.g) (add_zero n) = 0 := Subsingleton.elim _ _
  have hb : b.comp (Ext.mk₀ S.g) (add_zero n) = 0 := Subsingleton.elim _ _
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₂ Z hS a ha
  obtain ⟨d, hd⟩ := Ext.covariant_sequence_exact₂ Z hS b hb
  rw [← hc, ← hd, Subsingleton.elim c d]

/-- The constant sheaf on an irreducible space has vanishing higher cohomology. -/
theorem constantSheaf_cohomology_vanishing
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X] (n : ℕ) :
    Subsingleton (Sheaf.H ((constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))) (n + 1)) :=
  FlasqueVanishing X _ (fun i => constantSheaf_flasque_of_irreducible X i) n

/-- **Step 5** (Hartshorne III.2.7): For an irreducible Noetherian space X with dim ≥ 1,
    the kernel of the adjunction unit `Z_X → i_*(i^*Z_X)` has vanishing cohomology
    above dim X. This uses:
    1. `constantSheaf_cohomology_vanishing`: H^n(Z_X) = 0 for n ≥ 1 (flasque)
    2. `PushforwardHVanishing` + IH: H^{n-1}(i_*(i^*Z_X)) = 0
    3. `subsingleton_ext_of_ses` at shifted degree -/
set_option synthInstance.maxHeartbeats 80000 in
theorem constantSheaf_kernel_vanishing
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X]
    (Z : Set X) (hZ : IsClosed Z) (hZ_ne : Z ≠ Set.univ)
    (n : ℕ) (hn : n > topologicalKrullDim X) (hpos : topologicalKrullDim X > 0)
    (ih : ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
      (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y < topologicalKrullDim X →
      n > topologicalKrullDim Y →
      Subsingleton (Sheaf.H G n)) :
    let Z_X := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))
    ∀ (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)),
      S.ShortExact → S.X₂ = Z_X →
      S.X₃ = (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of Z ⟶ X)).obj Z_X) →
      Subsingleton (Sheaf.H S.X₁ n) := by
  intro Z_X S hSE hS₂ hS₃
  -- dim Z < dim X (Z is a proper closed subset of irreducible X)
  have hZ_dim : topologicalKrullDim (TopCat.of Z) < topologicalKrullDim X :=
    topologicalKrullDim_lt_of_isIrreducible_of_isClosed hZ hZ_ne
      (lt_of_le_of_lt (topologicalKrullDim_subspace_le X Z)
        (lt_of_lt_of_le (show topologicalKrullDim X < ⊤ from lt_of_lt_of_le hn le_top) le_top))
  -- n > dim Z + 1 (since n > dim X ≥ dim Z + 1)
  have hn_Z : ↑n > topologicalKrullDim (TopCat.of Z) := lt_trans hZ_dim hn
  -- Pushforward of Z_Y vanishes at degree n
  have hPush : Subsingleton (Sheaf.H S.X₃ n) := by
    rw [hS₃]
    exact PushforwardHVanishing Z hZ _ n (@ih (TopCat.of Z) _ _ hZ_dim hn_Z)
  -- Constant sheaf vanishes at degree n (n ≥ 2 since n > dim X ≥ 1)
  -- We need n = m + 1 for some m ≥ 1, then constantSheaf_cohomology_vanishing gives H^{m+1} = 0
  have hn_ge1 : n ≥ 1 := by
    have := topologicalKrullDim_nonneg_of_irreducible (X := X)
    omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  -- H^{m+1}(Z_X) = 0
  have hConst : Subsingleton (Sheaf.H Z_X (m + 1)) :=
    constantSheaf_cohomology_vanishing X m
  -- Apply subsingleton_ext_of_ses at degree m:
  -- h₃: Subsingleton(Ext(Z, X₃, m))   [pushforward vanishing at m]
  -- h₂: Subsingleton(Ext(Z, X₂, m+1)) [constant sheaf vanishing at m+1]
  -- → Subsingleton(Ext(Z, X₁, m+1))   [kernel vanishing at m+1 = n]
  -- For h₃ at degree m: need m > dim Z (i.e., n - 1 > dim Z)
  have hm_Z : ↑m > topologicalKrullDim (TopCat.of Z) := by
    simp only [topologicalKrullDim, gt_iff_lt] at hn_Z ⊢
    omega
  have hPush_m : Subsingleton (Sheaf.H S.X₃ m) := by
    rw [hS₃]
    exact PushforwardHVanishing Z hZ _ m (@ih (TopCat.of Z) _ _ hZ_dim hm_Z)
  exact hS₂ ▸ subsingleton_ext_of_ses hSE _ m hPush_m (hS₂ ▸ hConst)

/-- Key identity: `zeroOutsideInt ⊤ = constantSheaf Z_X` (definitional). -/
theorem zeroOutsideInt_top_eq_constantSheaf (X : TopCat.{u}) :
    TopCat.Sheaf.zeroOutsideInt (⊤ : Opens X) =
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ)) := rfl

/-- Hartshorne Steps 3-5: uses IrreduciblePosVanishing (sorry). -/
private theorem grothendieck_reduction
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X) (hpos : topologicalKrullDim X > 0)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (ih : ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
      (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y < topologicalKrullDim X →
      n > topologicalKrullDim Y →
      Subsingleton (Sheaf.H G n)) :
    Subsingleton (Sheaf.H F n) :=
  IrreduciblePosVanishing X n hn hpos F ih

/-- Positive-dimensional irreducible vanishing. -/
theorem grothendieck_vanishing_irreducible_pos
    (X : TopCat.{u}) [TopologicalSpace.NoetherianSpace X] [IrreducibleSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X)
    (hpos : topologicalKrullDim X > 0)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (ih : ∀ (Y : TopCat.{u}) [TopologicalSpace.NoetherianSpace Y]
      (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y < topologicalKrullDim X →
      n > topologicalKrullDim Y →
      Subsingleton (Sheaf.H G n)) :
    Subsingleton (Sheaf.H F n) :=
  grothendieck_reduction X n hn hpos F ih
