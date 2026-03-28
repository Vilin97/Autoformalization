-- Harmonic `generalize_proofs` tactic
import Mathlib

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

/-- For x ∉ Z (closed), every element of the stalk of i_*(G) at x is 0.

    Proof: The stalk is a filtered colimit over opens V ∋ x.
    For any germ_V(s) with V ∋ x and s ∈ (i_*G)(V):
    - Take V' = V ∩ (X \ Z). V' ∋ x, V' ≤ V.
    - (i_*G)(V') = G(V' ∩ Z) = G(∅) = 0 (terminal).
    - s|_{V'} ∈ (i_*G)(V') = 0, so s|_{V'} = 0.
    - By germ_res_apply: germ_V(s) = germ_{V'}(s|_{V'}) = germ_{V'}(0) = 0.

    Key API: TopCat.Presheaf.germ_res_apply for restriction coherence.
    The element decomposition (every stalk element = some germ) follows from
    Types.jointly_surjective + forget preserves filtered colimits.
    Use colimit.w_apply or germ_res_apply for the transport step. -/
theorem stalk_zero_of_pushforward_outside_closed
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    (G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z))
    (x : X) (hx : x ∉ Z) :
    let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    ∀ (b : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj G).val), b = 0 := by
  sorry
