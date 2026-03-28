# Summary of changes
Successfully proved `toPlus_surjective_of_irreducible_const` in `ToSheafifySurjective.lean`.

The proof shows that on an irreducible topological space X, the `toPlus` map for the constant presheaf `(Functor.const _).obj (AddCommGrpCat.of (ULift ℤ))` is surjective at any nonempty open U.

The proof is decomposed into 6 helper lemmas:

1. **`constPresheaf_map_eq_id`**: The constant presheaf maps act as the identity (since `P.map f = 𝟙` for all `f`).

2. **`cover_arrows_related`**: Any two arrows I₁, I₂ in a cover S of a nonempty U are connected by a relation. The witness is Z = I₁.Y ⊓ I₂.Y with the obvious inclusion morphisms (which commute since morphisms in `Opens X` are unique/subsingleton).

3. **`meq_const_values_eq`**: All values of a matching family for the constant presheaf are equal. Uses `cover_arrows_related` to get a relation, then the compatibility condition plus `constPresheaf_map_eq_id` forces equality.

4. **`cover_nonempty_arrow`**: A cover of a nonempty open has at least one arrow (by unfolding the covering sieve condition at a point of U).

5. **`meq_eq_mk_of_values_eq`**: A matching family with all values equal to `a` equals `Meq.mk S a`.

6. **`meq_mk_refine_eq`**: `Meq.mk` refined along any cover morphism gives `Meq.mk` again (for the constant presheaf).

The main theorem combines these: given y in the plus object, represent it as `Plus.mk x` via `exists_rep`, show all values of x are equal to some `a`, rewrite as `Meq.mk S a`, then show `toPlus a = Plus.mk (Meq.mk ⊤ a) = Plus.mk (Meq.mk S a) = y` using `toPlus_eq_mk` and `eq_mk_iff_exists`.

The proof uses only standard axioms (propext, Classical.choice, Quot.sound).