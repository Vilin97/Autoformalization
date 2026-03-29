-- Harmonic `generalize_proofs` tactic
import Mathlib

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

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

/-- Irreducible positive-dimension vanishing (Hartshorne III.2.7).
    For an irreducible Noetherian X of dim ≥ 1, H^n(X, F) = 0 for n > dim X.

    The correct approach (Hartshorne): for irreducible X with generic point η:
    1. Take any constant sheaf A on X (e.g., with value F_η or any abelian group).
       A is flasque since X is irreducible.
    2. There exist natural maps relating F to sheaves supported on proper closed Z ⊊ X.
       Specifically, for any closed point x ∈ X with closure Z = {x}⁻:
       The skyscraper-stalk adjunction gives maps between F and sheaves on Z.
    3. Use the long exact sequence + FlasqueVanishing + induction hypothesis.

    Key mathematical fact: for irreducible X with dim ≥ 1, there exists a proper
    nonempty closed subset Z ⊊ X. The short exact sequence 0 → K → F → i_*(i^*F) → 0
    gives H(push) = 0 by ih + PushforwardHVanishing. But H(K) = 0 needs the kernel K
    to be handled. The issue: supp(K) might equal X (since X\Z is dense).

    The Stacks Project approach (Tag 01X9): use noetherian induction.
    The property P(X) = "∀ F n, n > dim X → H^n(X,F) = 0" is proved by noetherian induction.
    For the induction step: compare to constant sheaf on the generic stalk, where
    kernel/cokernel are supported on proper closed subsets.
-/
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 80000 in
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
  sorry
