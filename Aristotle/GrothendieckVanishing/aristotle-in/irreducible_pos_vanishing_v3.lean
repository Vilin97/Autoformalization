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

/-- Irreducible positive-dimension vanishing (Hartshorne III.2.7, Steps 3-5).

    The key mathematical content: for irreducible Noetherian X of dim d ≥ 1,
    H^n(X, F) = 0 for n > d and any abelian sheaf F.

    APPROACH: Use well-founded induction on the closed subsets of X (Noetherian
    induction) combined with the dimension induction hypothesis.

    The IH `ih` gives: for ALL spaces Y with dim Y < dim X, vanishing holds.
    This means: for any proper closed Z ⊊ X (which has dim Z < dim X by
    irreducibility), H^n(Z, G) = 0 for any G and n > dim Z.

    KEY FACTS AVAILABLE (proved elsewhere, use sorry-free):
    1. The constant sheaf on irreducible X is flasque
    2. Flasque sheaves have H^n = 0 for n ≥ 1 (FlasqueVanishing)
    3. PushforwardHVanishing: if H^n(Z, G) = 0 then H^n(X, i_*G) = 0
    4. The covariant Ext LES gives the sandwich lemma
    5. For any proper closed Z ⊊ irreducible X: dim Z < dim X

    IMPORTANT CONSTRAINT: The ClosedImmersionSES approach
    (0 → K → F → i_*i^*F → 0) FAILS because the kernel K has zero stalks
    on Z but supp(K) = closure(X\Z) = X for irreducible X. The kernel
    CANNOT be transferred to a lower-dimensional space.

    VIABLE APPROACHES:
    A) Show HasProjectiveDimensionLT for the constant sheaf using induction
       on dim X. The SES 0 → j_!(Z_U) → Z_X → i_*(Z_Z) → 0 (extension by
       zero) gives pdim(Z_X) ≤ max(pdim(j_!(Z_U)), pdim(i_*(Z_Z))).
       Key: pdim(i_*(Z_Z)) can be bounded by dim Z + 1 using the IH and
       the adjunction Ext^n(F, i_*A) ≅ Ext^n(i^*F, A).

    B) Use the Čech-style argument: on an irreducible space of dim d,
       any open cover can be refined to have empty (d+1)-fold intersections.

    C) Use noetherian induction on the support: prove P(W) = "for all
       sheaves supported on W, H^n = 0" by descending induction on closed W.

    D) Direct: use that the constant sheaf Z' is flasque, hence
       Sheaf.H F n = Ext^n(Z', F). Since Z' is flasque and generates
       the category via sections, try to show Ext vanishing directly.

    Try approach A first (HasProjectiveDimensionLT).
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
