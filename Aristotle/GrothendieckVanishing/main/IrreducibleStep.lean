/-
  IrreducibleStep.lean — Vanishing for irreducible spaces of positive dimension

  Hartshorne III.2.7, Steps 3–5: For an irreducible Noetherian space X of
  dimension d ≥ 1, reduce H^n(X, F) = 0 for n > d to lower-dimensional spaces.

  Key results:
  - subsingleton_ext_of_ses: PROVED — abstract LES vanishing from Ext exact sequences
  - constantSheaf_flasque_of_irreducible: sorry (nonempty case needs sheafification)
  - constantSheaf_cohomology_vanishing: proved from flasque + FlasqueVanishing
  - grothendieck_vanishing_irreducible_pos: sorry (needs Prop 2.9 + extension by zero)

  Based on Aristotle output (bc3176de) + manual work.
-/
import Aristotle.GrothendieckVanishing.main.Setup
import Aristotle.GrothendieckVanishing.main.Auxiliary

universe u

open CategoryTheory TopologicalSpace Abelian

/-! ## Abstract LES vanishing lemma -/

/-- Given a short exact sequence `0 → X₁ → X₂ → X₃ → 0`, if `Ext(Z, X₃, n) = 0`
    and `Ext(Z, X₂, n+1) = 0`, then `Ext(Z, X₁, n+1) = 0`.
    This follows from the covariant long exact sequence in Ext. -/
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

/-! ## Constant sheaf flasqueness -/

/-- On an irreducible space, the constant sheaf Z has epi restriction maps (is flasque).

    The U = ⊥ case is proved; the nonempty case requires sheafification internals. -/
theorem constantSheaf_flasque_of_irreducible
    (X : TopCat.{u}) [IrreducibleSpace X]
    {U V : Opens X} (i : U ⟶ V) :
    Epi (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))).val.map i.op) := by
  by_cases hU : (U : Set X) = ∅
  · -- U = ∅: F(V) → F(∅) is epi because F(∅) is terminal (zero)
    have : U = ⊥ := Opens.ext (by simpa using hU)
    subst this
    have hcov : ⊥ ∈ (Opens.grothendieckTopology X) ⊥ :=
      fun x hx => (Opens.mem_bot.mp hx).elim
    exact epi_of_isTerminal_tgt (Sheaf.isTerminalOfBotCover _ ⊥ hcov) _
  · -- U nonempty: needs sheafification argument
    admit

/-- The constant sheaf Z on an irreducible Noetherian space has vanishing
    higher cohomology. Follows from flasque + FlasqueVanishing. -/
theorem constantSheaf_cohomology_vanishing
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X] (n : ℕ) :
    Subsingleton (Sheaf.H ((constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))) (n + 1)) :=
  FlasqueVanishing X _ (fun i => constantSheaf_flasque_of_irreducible X i) n

/-! ## Main reduction (Steps 3-5) -/

/-- Hartshorne Steps 3-5: reduction from arbitrary sheaves to lower-dimensional spaces.
    Uses Prop 2.9 (direct limits), Z_U SES, and FlasqueVanishing.
    SORRY — needs extension by zero + Prop 2.9 infrastructure. -/
private theorem grothendieck_reduction
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X) (hpos : topologicalKrullDim X > 0)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (ih : ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
      (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y < topologicalKrullDim X →
      n > topologicalKrullDim Y →
      Subsingleton (Sheaf.H G n)) :
    Subsingleton (Sheaf.H F n) := by
  sorry

/-- For an irreducible Noetherian space X of positive dimension, vanishing
    of H^n for n > dim X follows from vanishing on all lower-dimensional spaces. -/
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
