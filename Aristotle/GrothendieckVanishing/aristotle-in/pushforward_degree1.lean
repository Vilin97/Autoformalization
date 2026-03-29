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
  inferInstanceAs (Abelian (Sheaf _ _))

instance (X : TopCat.{u}) : IsGrothendieckAbelian.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (IsGrothendieckAbelian (Sheaf _ _))

/-- Pushforward along a closed immersion preserves cohomological vanishing at degree 1.
    That is: Subsingleton(H G 1) → Subsingleton(H(i_*G) 1)
    where i : Z ↪ X is a closed immersion.

    Key fact: Γ_X(i_*G) = G(⊤_Z) by definitional equality (since (Opens.map i).obj ⊤ = ⊤).
    This gives a natural isomorphism Γ_X ∘ i_* ≅ Γ_Z.

    Approach: From the injective presentation 0 → G → J → R → 0 on Z:
    - LES on Z: Γ(J) → Γ(R) → H¹(G) → 0. So H¹(G) = coker(Γ(J) → Γ(R)).
    - Pushed-forward LES on X: Γ(i_*J) → Γ(i_*R) → H¹(i_*G) → H¹(i_*J)
      Since i_*J is flasque: H¹(i_*J) = 0.
      So H¹(i_*G) = coker(Γ(i_*J) → Γ(i_*R)).
    - Since Γ(i_*J) = Γ(J) and Γ(i_*R) = Γ(R) (by the Γ equality), and the maps
      correspond (naturality): coker(Γ(i_*J) → Γ(i_*R)) = coker(Γ(J) → Γ(R)).
    - So H¹(i_*G) ≅ H¹(G) as abelian groups.
    - Subsingleton(H G 1) → Subsingleton(H(i_*G) 1).

    Alternative approach: show i_* is exact (preserves ShortExact) for closed immersions,
    then use the pushed-forward injective resolution directly.
-/
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 80000 in
theorem pushforward_H_vanishing_degree1
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    [NoetherianSpace X]
    (G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z))
    (h : Subsingleton (Sheaf.H G 1)) :
    let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    Subsingleton (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G) 1) := by
  sorry
