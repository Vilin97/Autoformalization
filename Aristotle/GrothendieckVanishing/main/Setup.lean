/-
  Setup.lean — Category instances and the single remaining gap for Grothendieck vanishing

  Provides:
  1. Categorical infrastructure for sheaf cohomology on AddCommGrpCat
  2. FlasqueVanishing (the only remaining gap — Grothendieck's vanishing theorem)
  3. ReducibleVanishing (proved from FlasqueVanishing)
  4. IrreduciblePosVanishing (proved from FlasqueVanishing)

  The full proof of FlasqueVanishing requires infrastructure not yet in Mathlib v4.28:
  extension by zero (j_!), Proposition 2.9 (direct limits), derived adjunction for
  pushforward along closed embeddings. The partial proof (dim 0 case, constant sheaf
  flasque, CohomologyIso, subsingleton_ext_of_ses) is verified in the other files.
-/
import Mathlib

universe u

open CategoryTheory TopologicalSpace

instance : HasSeparator AddCommGrpCat.{u} where
  hasSeparator := by
    use AddCommGrpCat.of (ULift ℤ)
    intro A B f g h
    simp_all only [ObjectProperty.singleton_iff, AddCommGrpCat.ext_iff,
      AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply, forall_eq',
      ULift.forall]
    intro x
    specialize h (AddCommGrpCat.ofHom
      (AddMonoidHom.mk' (fun y => y • x) fun y z => by simp only [add_smul])) 1
    aesop

instance : IsGrothendieckAbelian.{u} AddCommGrpCat.{u} where

instance (X : TopCat.{u}) : Abelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (Abelian (CategoryTheory.Sheaf _ _))

instance (X : TopCat.{u}) : IsGrothendieckAbelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (IsGrothendieckAbelian (CategoryTheory.Sheaf _ _))

set_option synthInstance.maxHeartbeats 80000 in
/-- **Grothendieck's vanishing theorem** — the single unproved statement in this project.

    For a Noetherian topological space X of dimension d, and any sheaf F
    of abelian groups on X, H^n(X, F) = 0 for all n > d.

    The standard proof (Hartshorne III.2.7) requires:
    - Extension by zero (j_!) for open embeddings (NOT in Mathlib v4.28)
    - The closed-open SES: 0 → j_!(F|_U) → F → i_*(F|_Z) → 0
    - Proposition 2.9: cohomology commutes with direct limits on Noetherian spaces
    - Derived adjunction: Ext_X(Z, i_*G, n) ≅ Ext_Y(Z_Y, G, n) for closed i: Y ↪ X -/
theorem FlasqueVanishing (X : TopCat.{u}) [NoetherianSpace X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) (hn : n > topologicalKrullDim X) :
    Subsingleton (Sheaf.H F n) := by
  sorry

set_option synthInstance.maxHeartbeats 80000 in
/-- Reducible case: follows immediately from FlasqueVanishing. -/
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
  FlasqueVanishing X F n hn

set_option synthInstance.maxHeartbeats 80000 in
/-- Irreducible positive-dim case: follows immediately from FlasqueVanishing. -/
theorem IrreduciblePosVanishing
    (X : TopCat.{u}) [NoetherianSpace X] [IrreducibleSpace X]
    (n : ℕ) (hn : n > topologicalKrullDim X) (hpos : topologicalKrullDim X > 0)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (ih : ∀ (Y : TopCat.{u}) [NoetherianSpace Y]
      (G : TopCat.Sheaf AddCommGrpCat.{u} Y),
      topologicalKrullDim Y < topologicalKrullDim X →
      n > topologicalKrullDim Y →
      Subsingleton (Sheaf.H G n)) :
    Subsingleton (Sheaf.H F n) :=
  FlasqueVanishing X F n hn
