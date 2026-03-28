# Summary of changes
## Completed Work

### Sorry 1: `constantSheaf_flasque_of_irreducible` — **PROVED** ✅

The constant sheaf on an irreducible topological space has epi (surjective) restriction maps, making it flasque. The proof was decomposed into a chain of 10 helper lemmas, all fully proved without sorry:

1. **`nonempty_open_irreducible`** / **`nonempty_open_connected`**: Nonempty open subsets of an irreducible space are irreducible (hence connected).
2. **`const_presheaf_map_id`**: The constant presheaf sends every restriction map to the identity.
3. **`const_presheaf_equalizerSieve_bot`**: For the constant presheaf, the equalizer sieve of two distinct elements is ⊥.
4. **`bot_not_mem_grothendieck_of_nonempty`**: The ⊥ sieve is not covering for nonempty opens.
5. **`toSheafify_const_injective_of_nonempty`**: On an irreducible space, `toSheafify` for the constant presheaf is injective at nonempty opens (combines lemmas 3–4 with local injectivity of sheafification).
6. **`sheaf_sections_eq_of_agree_on_cover`**: Two sections of a sheaf that agree on a covering sieve are equal.
7. **`toSheafify_const_nat`**: Naturality of `toSheafify` at element level — restricting η_U(a) to V equals η_V(a).
8. **`sheaf_section_empty_subsingleton`**: Sections of a sheaf over the empty open are trivial.
9. **`const_local_preimages_agree`**: Two local preimages from nonempty opens in the image sieve must agree (uses irreducibility for nonempty intersection + injectivity).
10. **`toSheafify_const_epi_of_nonempty`**: The full surjectivity argument — uses local surjectivity of `toSheafify`, uniqueness of local preimages (lemma 9), and the sheaf gluing condition.

The main theorem `constantSheaf_flasque_of_irreducible` then follows by:
- **Nonempty case**: Naturality + epi of `toSheafify` implies epi of the restriction map.
- **Empty case**: F(∅) is terminal (zero), so any map into it is epi.

All proofs use only standard axioms (propext, Classical.choice, Quot.sound).

### Sorry 2: `grothendieck_reduction` — **DOCUMENTED** 📝

Steps 3–5 of Hartshorne's proof (Theorem III.2.7) are left as `sorry` with detailed documentation of four Mathlib blockers:

1. **Extension by zero (j_!)**: Not available in Mathlib for sheaves on topological spaces.
2. **Prop 2.9** (cohomology commutes with filtered colimits on Noetherian spaces): Missing infrastructure.
3. **Support theory for sheaves**: Dimension of support of kernels/quotients not formalized.
4. **Long exact sequence glue**: Connecting abstract derived functor LES to concrete `Sheaf.H`.

### Main theorem: `grothendieck_vanishing_irreducible_pos`

Structured to use both results: `constantSheaf_flasque_of_irreducible` + `FlasqueVanishing` (admitted axiom) prove the constant sheaf case, and `grothendieck_reduction` (sorry'd with documentation) handles the general case reduction.

### Other items preserved
- `FlasqueVanishing` remains as `admit` per the "DO NOT PROVE — axiom" annotation.
- All original user-provided content is preserved.