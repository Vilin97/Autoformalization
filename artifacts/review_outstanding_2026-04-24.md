# Outstanding review items

Distilled from the original code review. Only items that an audit of the current tree
(as of 2026-04-24) shows are still unfinished are listed here. Cross-cutting items first,
then per-file. Line numbers from the original review are intentionally omitted — the
tree has shifted since, and the items below are phrased by symbol/file semantics so they
remain locatable.

---

## Cross-cutting

### Ext leaks outside `CohomologyAPI.lean`

`CohomologyAPI.lean` was created, but the definition of `Sheaf.H` in terms of `Ext` still
leaks through downstream files:

- `PresheafFilteredColimit.lean` calls `Ext.subsingleton_of_injective _ _ n` directly (several sites) to supply `Subsingleton (Sheaf.H · (n+1))` for injective sheaves.
- `ClosedImmersionCohomology.lean` does the same at ~3 sites.
- `FlasqueVanishing.lean` declares a `HasExt.{u} (TopCat.Sheaf …)` instance and otherwise still imports/uses the Ext layer for scaffolding.

A `CohomologyAPI.sheafH_subsingleton_of_injective` wrapper would close this; then the
`Ext.*` calls in downstream files can be rewritten to API calls. As it stands, `Ext` is
not an implementation detail — it is co-equal public API, which contradicts the
goal of the CohomologyAPI file.

### `CohomologyAPI.lean` exposes Ext as a first-class surface

Roughly two dozen Ext-named declarations (`ext_dimension_shift`, `ext_dimension_shift_X₃`,
`Ext.subsingleton_of_isZero_tgt`, `extClass_naturality`, `extClass_postcomp_bijective_of_subsingleton_middle`,
`extClass_postcompAddEquiv_of_subsingleton_middle`, multiple `sheafH_extClass*` variants)
are exported at the top level. The reviewer's intent was that `Sheaf.H` is the API, `Ext`
is the proof tool. Either these Ext-level lemmas should move into a `private` /
`CohomologyAPI.Internal` namespace, or their public consumers should be rewritten to call
only `Sheaf.H`-level lemmas.

### `CohomologyAPI` structure is "sheaf + `_presheaf` wrapper pairs"

The file contains ~32 `*_presheaf` variants matched 1:1 with non-presheaf siblings
(`sheafH_subsingleton_of_isZero_presheaf` + `sheafH_subsingleton_of_isZero`, etc.). The
reviewer's intended idiom is the opposite: the `{F : Presheaf …} (hF : IsSheaf F)` form
should be the *primary* lemma; the sheaf-level variant, if it exists at all, is a thin
`simpa`-wrapper. The refactor kept both, effectively doubling surface area. Pass to
decide, per lemma, whether the sheaf-level wrapper earns its keep.

### `PushforwardHVanishing` kept alongside `PushforwardHIso`

`PushforwardHIso` was proved (good). But `PushforwardHVanishing`
(`Subsingleton → Subsingleton`) was kept as a legacy wrapper rather than replaced. The
review explicitly asked for "A ≅ B" to replace "if A = 0 then B = 0"; keeping both just
adds surface.

---

## Per-file

### `FlasqueVanishing.lean` / `FlasqueCohomology.lean`

- **Not combined.** The review said "there only needs to be one file on flasque sheaves."
  `FlasqueVanishing.lean` (511 lines) and `FlasqueCohomology.lean` (59 lines) both still exist.
- **Misnamed.** `FlasqueVanishing.lean` contains zero declaration named `FlasqueVanishing`;
  the instance of that name lives in `FlasqueCohomology.lean`. The file's own docstring
  admits this. Merge the files, then name the result for what it actually proves.
- **Zorn's lemma argument still hand-rolled.** `sigmaPreorder` / `IsPartialLift` /
  `partialLift_chain_ub` / `partialLift_maximal_eq_U` span roughly 100 lines. The
  reviewer's PR has a cleaner version — port it.

### `FiniteGeneratorReduction.lean`

- **Not renamed.** The review called the name "bad"; no rename happened.
- **Not split as specified.** The review asked for one file on "general colimits of
  sheaves" and another on the Noetherian case. `PresheafFilteredColimit.lean` was
  extracted, but it mixes general filtered-colimit-of-presheaves helpers with the
  Noetherian-specific `isSheaf_of_isColimit_of_isSheaf`. The split axis is wrong.

### `PresheafFilteredColimit.lean`

- **Not rewritten.** File is **3171 lines**. The reviewer called for an entire rewrite and
  said the main comparison theorem alone "should not need to be more than ~100 lines."
  Current main theorem + compatibility lemmas sprawl to many hundreds of lines
  (`sheafH_filtered_colimit_comparison_succ_compatibility_presheaf` alone is ~180 lines).
- Presheaf-typed signatures are in place, but the file still proves things
  specifically for presheaves on a topological space that already exist in Mathlib in
  the functor-category setting. Many helpers should be either deleted or pushed to
  Mathlib.

### `ConstantSheafFlasque.lean`

- **Flasqueness is still expressed as `Epi (…)`, not `IsFlasqueSheaf (…)`.** The file
  generalized over `A : AddCommGrpCat` (good), but its main theorems still state raw
  `Epi (…map i.op)` conclusions. Only the final top-level `isFlasqueSheaf_zeroOutsideInt_top`
  instance packages the class. The intermediate flasqueness-of-constant-sheaf lemma
  should itself be `IsFlasqueSheaf (constantSheaf … A)`.

### `ULiftInt.lean`

- **Cosmetic rename.** The file contains `uliftZMultiplesHom_add`, `uliftZMultiplesAddEquiv`,
  and a 33-line `ulift_int_subgroup_cyclic` that transports `Int.subgroup_cyclic` through
  `AddEquiv.ulift`. The review said this kind of lemma is "ridiculous" and should either
  be a trivial derivation from `Int.subgroup_cyclic` (stated idiomatically in terms of the
  subgroup generated by an element) or inlined into its one call site. Renaming the file
  did not make the contents more general.

### `TopologicalKrullDim.lean`

- **Missing API lemma:** `topologicalKrullDim X = ⊥ ↔ IsEmpty X` (or the ``< ⊥``/
  nonempty contrapositive). The review asked for this explicitly; the file only has
  `topologicalKrullDim_nonneg` for nonempty spaces, which is one direction.
- Several remaining lemmas (`topologicalKrullDim_lt_of_add_one_le_of_lt_top`,
  `exists_closed_subset_lt_dim_of_irreducible_pos`) are still clearly call-site-shaped.
  Either lift them to genuine API with general statements, or inline them at the one
  place they're used.

### `GrothendieckVanishing.lean` — partial

- The dim-zero case now lives in `IrreducibleStep.lean`, not `GrothendieckVanishing.lean`.
  The review asked for `DimZeroVanishing.lean` contents to move into `GrothendieckVanishing.lean`
  directly, so the main theorem file is self-contained at the leaves of the induction.
