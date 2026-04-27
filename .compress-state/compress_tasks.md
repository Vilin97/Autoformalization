# Compress Tasks

Mechanically-derived task list seeded by the initial comprehensive scan.
Each task may have a `COMPLETE_IF: <shell>` line; the loop controller
does NOT flip to `- [x]` unless that command exits 0.

Markers:
- `- [ ]` = not started
- `- [>]` = in progress (multi-cycle, may be re-targeted)
- `- [x]` = complete

Hard rules (enforced by the gate, not just by the prompts):
- Every committed cycle MUST decrease normalized LOC
  (`python3.9 scripts/normalized_loc.py`). No scaffolding cycles.
- Deleting comments or blank lines does NOT count as compression.
- Stacking tactics on one line via `;` or `<;>` does NOT count.
- 0 sorry's, 0 axioms, 0 admits must be preserved.
- Loop stops when raw `wc -l` of `main/*.lean` < 5000.

---

## Phase 1: Sheaf reversion (highest leverage; reviewer-flagged)

The previous refactor over-applied the `(F : Presheaf X) (hF : F.IsSheaf)`
public idiom. Many lemmas should take `(F : TopCat.Sheaf AddCommGrpCat.{u} X)`
directly, especially when several presheaf+IsSheaf triples are packaged into
`(⟨F, h⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)` inside the theorem statement.

Canonical example: `CohomologyAPI.lean:1734-1776` is a 43-line theorem with
**six** `(F : Presheaf) (h : F.IsSheaf)` triples and six `(⟨F, h⟩ : Sheaf …)`
packagings inside a `ShortComplex.mk` body. It should be ~1 line if it took
`(S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X))` directly.

Mechanical signal: `find_repeated_blocks.py` reports 40 occurrences of the
7-line `(X₁ := ⟨F₁, h₁⟩ : TopCat.Sheaf …) (X₂ := …) (X₃ := …)` packaging
boilerplate, with ~273 lines of potential savings. Phase 1 is the single
highest-leverage area in the entire compress loop.

- [x] In `CohomologyAPI.lean`, rewrite each theorem that takes one or more
      `(F : Presheaf X) (h : F.IsSheaf)` triples and ends up packaging them
      into `(⟨F, h⟩ : Sheaf …)` inside its body. Replace each triple with a
      single `Sheaf` argument, delete the corresponding `_presheaf` wrapper
      where the sheaf-level lemma was the underlying truth, and propagate
      the change to call sites in the same file. Target: at least 600 LOC
      removed from `CohomologyAPI.lean`.
      COMPLETE_IF: test $(wc -l < Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean) -lt 1200

- [x] Repeat the Phase-1 reversion across `FlasqueVanishing.lean`,
      `PresheafFilteredColimit{,Core,General}.lean`, `IrreducibleStep.lean`,
      `ClosedImmersion.lean`, `ClosedImmersionCohomology.lean`, and any other
      file with multi-arg `IsSheaf` packaging. Target: total `main/*.lean`
      raw `wc -l` below 6500 once Phase 1 is done across the tree.
      COMPLETE_IF: test $(cat Aristotle/GrothendieckVanishing/main/*.lean | wc -l) -lt 6500

---

## Phase 2: Unused declarations

Auto-extracted from `lake env lean scripts/unused_decls.lean`. Each item
is a public declaration not transitively reached from `GrothendieckVanishing`.
Verify reachability before deletion (private helpers it depends on may also
become unreachable, cascading the deletion).

- [x] Delete unused declaration `TopCat.closedIncl_image_map_eq_inter` from `ClosedImmersion.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) TopCat\.closedIncl_image_map_eq_inter\b' Aristotle/GrothendieckVanishing/main/ClosedImmersion.lean
- [x] Delete unused declaration `TopCat.coe_closedIncl` from `ClosedImmersion.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) TopCat\.coe_closedIncl\b' Aristotle/GrothendieckVanishing/main/ClosedImmersion.lean
- [x] Delete unused declaration `epi_pushforward_map_closedIncl` from `ClosedImmersion.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) epi_pushforward_map_closedIncl\b' Aristotle/GrothendieckVanishing/main/ClosedImmersion.lean
- [x] Delete unused declaration `epi_app_top_of_subsingleton_sheafH1_presheaf` from `CohomologyAPI.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) epi_app_top_of_subsingleton_sheafH1_presheaf\b' Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean
- [x] Delete unused declaration `sheafCohomologyFunctor_additive` from `CohomologyAPI.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) sheafCohomologyFunctor_additive\b' Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean
- [x] Delete unused declaration `sheafCohomologyFunctor_map_succ_of_map_eq_presheaf` from `CohomologyAPI.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) sheafCohomologyFunctor_map_succ_of_map_eq_presheaf\b' Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean
- [x] Delete unused declaration `sheafCohomologyFunctor_obj` from `CohomologyAPI.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) sheafCohomologyFunctor_obj\b' Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean
- [x] Delete unused declaration `sheafH0NatIsoSections_hom_app` from `CohomologyAPI.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) sheafH0NatIsoSections_hom_app\b' Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean
- [x] Delete unused declaration `sheafH0NatIsoSections_inv_app` from `CohomologyAPI.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) sheafH0NatIsoSections_inv_app\b' Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean
- [x] Delete unused declaration `sheafH_dimension_shift_X₃_presheaf` from `CohomologyAPI.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) sheafH_dimension_shift_X₃_presheaf\b' Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean
- [ ] Delete unused declaration `sheafH_exists_preimage_of_subsingleton_middle_presheaf` from `CohomologyAPI.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) sheafH_exists_preimage_of_subsingleton_middle_presheaf\b' Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean
- [x] Delete unused declaration `sheafH_subsingleton_of_isEmpty` from `CohomologyAPI.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) sheafH_subsingleton_of_isEmpty\b' Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean
- [ ] Delete unused declaration `sheafH_succ_map_presheaf_eq_succ_iso_hom` from `CohomologyAPI.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) sheafH_succ_map_presheaf_eq_succ_iso_hom\b' Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean
- [ ] Delete unused declaration `sheafH_succ_map_presheaf_natural_of_map_eq` from `CohomologyAPI.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) sheafH_succ_map_presheaf_natural_of_map_eq\b' Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean
- [x] Delete unused declaration `stalk_zero_of_shortExact_cokernel_presheaf` from `CohomologyAPI.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) stalk_zero_of_shortExact_cokernel_presheaf\b' Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean
- [x] Delete unused declaration `ulift_int_projective` from `CohomologyAPI.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) ulift_int_projective\b' Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean
- [ ] Delete unused declaration `IsFlasqueSheaf.casesOn` from `FlasqueVanishing.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) IsFlasqueSheaf\.casesOn\b' Aristotle/GrothendieckVanishing/main/FlasqueVanishing.lean
- [ ] Delete unused declaration `IsFlasqueSheaf.rec` from `FlasqueVanishing.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) IsFlasqueSheaf\.rec\b' Aristotle/GrothendieckVanishing/main/FlasqueVanishing.lean
- [ ] Delete unused declaration `IsFlasqueSheaf.recOn` from `FlasqueVanishing.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) IsFlasqueSheaf\.recOn\b' Aristotle/GrothendieckVanishing/main/FlasqueVanishing.lean
- [ ] Delete unused declaration `sheafH_subsingleton_H1_of_flasque_of_epi_app_top_map_presheaf` from `FlasqueVanishing.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) sheafH_subsingleton_H1_of_flasque_of_epi_app_top_map_presheaf\b' Aristotle/GrothendieckVanishing/main/FlasqueVanishing.lean
- [ ] Delete unused declaration `sheafH_subsingleton_H1_of_flasque_of_epi_app_top_presheaf` from `FlasqueVanishing.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) sheafH_subsingleton_H1_of_flasque_of_epi_app_top_presheaf\b' Aristotle/GrothendieckVanishing/main/FlasqueVanishing.lean
- [ ] Delete unused declaration `sheafShortComplexOfPresheaf_f_val` from `FlasqueVanishing.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) sheafShortComplexOfPresheaf_f_val\b' Aristotle/GrothendieckVanishing/main/FlasqueVanishing.lean
- [ ] Delete unused declaration `sheafShortComplexOfPresheaf_g_val` from `FlasqueVanishing.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) sheafShortComplexOfPresheaf_g_val\b' Aristotle/GrothendieckVanishing/main/FlasqueVanishing.lean
- [x] Delete unused declaration `TopCat.Sheaf.SectionIndex` from `GeneratedSubsheaf.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) TopCat\.Sheaf\.SectionIndex\b' Aristotle/GrothendieckVanishing/main/GeneratedSubsheaf.lean
- [x] Delete unused declaration `TopCat.Sheaf.allSectionMap` from `GeneratedSubsheaf.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) TopCat\.Sheaf\.allSectionMap\b' Aristotle/GrothendieckVanishing/main/GeneratedSubsheaf.lean
- [x] Delete unused declaration `TopCat.Sheaf.allSectionMap_epi` from `GeneratedSubsheaf.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) TopCat\.Sheaf\.allSectionMap_epi\b' Aristotle/GrothendieckVanishing/main/GeneratedSubsheaf.lean
- [x] Delete unused declaration `TopCat.Sheaf.familyGeneratedSheaf` from `GeneratedSubsheaf.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) TopCat\.Sheaf\.familyGeneratedSheaf\b' Aristotle/GrothendieckVanishing/main/GeneratedSubsheaf.lean
- [x] Delete unused declaration `TopCat.Sheaf.familyGeneratedSheaf_ι_eq` from `GeneratedSubsheaf.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) TopCat\.Sheaf\.familyGeneratedSheaf_ι_eq\b' Aristotle/GrothendieckVanishing/main/GeneratedSubsheaf.lean
- [x] Delete unused declaration `TopCat.Sheaf.familyGeneratedSheafι` from `GeneratedSubsheaf.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) TopCat\.Sheaf\.familyGeneratedSheafι\b' Aristotle/GrothendieckVanishing/main/GeneratedSubsheaf.lean
- [x] Delete unused declaration `TopCat.Sheaf.familyGeneratorMap` from `GeneratedSubsheaf.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) TopCat\.Sheaf\.familyGeneratorMap\b' Aristotle/GrothendieckVanishing/main/GeneratedSubsheaf.lean
- [x] Delete unused declaration `TopCat.Sheaf.familyImage_ι_eq` from `GeneratedSubsheaf.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) TopCat\.Sheaf\.familyImage_ι_eq\b' Aristotle/GrothendieckVanishing/main/GeneratedSubsheaf.lean
- [x] Delete unused declaration `TopCat.Sheaf.familyImageι` from `GeneratedSubsheaf.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) TopCat\.Sheaf\.familyImageι\b' Aristotle/GrothendieckVanishing/main/GeneratedSubsheaf.lean
- [x] Delete unused declaration `TopCat.Sheaf.finsetGeneratedSheaf` from `GeneratedSubsheaf.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) TopCat\.Sheaf\.finsetGeneratedSheaf\b' Aristotle/GrothendieckVanishing/main/GeneratedSubsheaf.lean
- [x] Delete unused declaration `TopCat.Sheaf.finsetGeneratorMap` from `GeneratedSubsheaf.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) TopCat\.Sheaf\.finsetGeneratorMap\b' Aristotle/GrothendieckVanishing/main/GeneratedSubsheaf.lean
- [x] Delete unused declaration `epiImage_zeroOutsideInt_vanishing` from `IrreducibleStep.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) epiImage_zeroOutsideInt_vanishing\b' Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean
- [x] Delete unused declaration `sheafH_preserves_filtered_colimits_presheaf_hom_epi` from `PresheafFilteredColimit.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) sheafH_preserves_filtered_colimits_presheaf_hom_epi\b' Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean
- [ ] Delete unused declaration `sheafH_filtered_colimit_presheafCocone_sheafToPresheaf` from `PresheafFilteredColimitCore.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) sheafH_filtered_colimit_presheafCocone_sheafToPresheaf\b' Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean
- [ ] Delete unused declaration `sheafH_filtered_colimit_presheafDiagram_sheafToPresheaf` from `PresheafFilteredColimitCore.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) sheafH_filtered_colimit_presheafDiagram_sheafToPresheaf\b' Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean
- [ ] Delete unused declaration `sheafH_filtered_colimit_surj_presheaf` from `PresheafFilteredColimitCore.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) sheafH_filtered_colimit_surj_presheaf\b' Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean
- [ ] Delete unused declaration `sheafH_presheafDiagram_sheafToPresheaf` from `PresheafFilteredColimitCore.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) sheafH_presheafDiagram_sheafToPresheaf\b' Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean
- [ ] Delete unused declaration `TopologicalSpace.IrreducibleCloseds.height_eq_order_height` from `TopologicalKrullDim.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) TopologicalSpace\.IrreducibleCloseds\.height_eq_order_height\b' Aristotle/GrothendieckVanishing/main/TopologicalKrullDim.lean
- [ ] Delete unused declaration `TopologicalSpace.IrreducibleCloseds.height_mono` from `TopologicalKrullDim.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) TopologicalSpace\.IrreducibleCloseds\.height_mono\b' Aristotle/GrothendieckVanishing/main/TopologicalKrullDim.lean
- [ ] Delete unused declaration `topologicalKrullDim_eq_bot_iff_isEmpty` from `TopologicalKrullDim.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) topologicalKrullDim_eq_bot_iff_isEmpty\b' Aristotle/GrothendieckVanishing/main/TopologicalKrullDim.lean
- [ ] Delete unused declaration `TopCat.Presheaf.zeroOutside.sHom_app` from `ZeroOutside.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) TopCat\.Presheaf\.zeroOutside\.sHom_app\b' Aristotle/GrothendieckVanishing/main/ZeroOutside.lean
- [ ] Delete unused declaration `TopCat.Presheaf.zeroOutside_map` from `ZeroOutside.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) TopCat\.Presheaf\.zeroOutside_map\b' Aristotle/GrothendieckVanishing/main/ZeroOutside.lean
- [ ] Delete unused declaration `TopCat.Presheaf.zeroOutside_obj` from `ZeroOutside.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) TopCat\.Presheaf\.zeroOutside_obj\b' Aristotle/GrothendieckVanishing/main/ZeroOutside.lean
- [ ] Delete unused declaration `TopCat.Presheaf.zeroOutside_openHom_app` from `ZeroOutside.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) TopCat\.Presheaf\.zeroOutside_openHom_app\b' Aristotle/GrothendieckVanishing/main/ZeroOutside.lean
- [ ] Delete unused declaration `TopCat.Sheaf.zeroOutsideInt.sHom_val` from `ZeroOutside.lean` (and any helpers it depended on that become unreachable).
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) TopCat\.Sheaf\.zeroOutsideInt\.sHom_val\b' Aristotle/GrothendieckVanishing/main/ZeroOutside.lean

---

## Phase 3: Factor repeated tactic blocks

Auto-extracted from `find_repeated_blocks.py --min-lines 4`. Each entry is a
multi-line tactic block that recurs ≥2x. Many of these will dissolve once
Phase 1 is done — DO NOT extract a helper for a block that will go away after
the Sheaf reversion. Only factor when the block is irreducibly necessary.

- [ ] Repeated 7-line block × 40 (potential savings: ~273 lines). First sites: CohomologyAPI.lean:310, CohomologyAPI.lean:322, CohomologyAPI.lean:347 (+37 more). Snippet head: `(X₁ := (⟨F₁, h₁⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)) / (X₂ := (⟨F₂, h₂⟩ : TopCat.Sheaf AddCommGrpCat.{u} X))`. Decide whether Phase 1 already eliminates it; otherwise factor a single helper.
- [ ] Repeated 12-line block × 17 (potential savings: ~192 lines). First sites: CohomologyAPI.lean:306, CohomologyAPI.lean:343, CohomologyAPI.lean:380 (+14 more). Snippet head: `{F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X} / (h₁ : F₁.IsSheaf) (h₂ : F₂.IsSheaf) (h₃ : F₃.IsSheaf)`. Decide whether Phase 1 already eliminates it; otherwise factor a single helper.
- [ ] Repeated 26-line block × 6 (potential savings: ~130 lines). First sites: CohomologyAPI.lean:239, CohomologyAPI.lean:1325, CohomologyAPI.lean:1424 (+3 more). Snippet head: `{F₁₁ F₁₂ F₁₃ F₂₁ F₂₂ F₂₃ : TopCat.Presheaf AddCommGrpCat.{u} X} / (h₁₁ : F₁₁.IsSheaf) (h₁₂ : F₁₂.IsSheaf) (h₁₃ : F₁₃.IsS`. Decide whether Phase 1 already eliminates it; otherwise factor a single helper.
- [ ] Repeated 5-line block × 14 (potential savings: ~65 lines). First sites: PresheafFilteredColimit.lean:315, PresheafFilteredColimit.lean:399, PresheafFilteredColimit.lean:649 (+11 more). Snippet head: `{X : TopCat.{u}} [NoetherianSpace X] / {J' : Type u} [SmallCategory J'] [IsFiltered J']`. Decide whether Phase 1 already eliminates it; otherwise factor a single helper.
- [ ] Repeated 12-line block × 6 (potential savings: ~60 lines). First sites: CohomologyAPI.lean:857, CohomologyAPI.lean:927, CohomologyAPI.lean:966 (+3 more). Snippet head: `{F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X} / (h₁ : F₁.IsSheaf) (h₂ : F₂.IsSheaf) (h₃ : F₃.IsSheaf)`. Decide whether Phase 1 already eliminates it; otherwise factor a single helper.
- [ ] Repeated 4-line block × 15 (potential savings: ~56 lines). First sites: PresheafFilteredColimit.lean:316, PresheafFilteredColimit.lean:400, PresheafFilteredColimit.lean:650 (+12 more). Snippet head: `{J' : Type u} [SmallCategory J'] [IsFiltered J'] / (Y : J' ⥤ TopCat.Presheaf AddCommGrpCat.{u} X)`. Decide whether Phase 1 already eliminates it; otherwise factor a single helper.
- [ ] Repeated 47-line block × 2 (potential savings: ~47 lines). First sites: PresheafFilteredColimit.lean:323, PresheafFilteredColimit.lean:410. Snippet head: `let Ysh := sheafH_filtered_colimit_presheafDiagram Y hY / let csh := sheafH_filtered_colimit_presheafCocone Y hY c hc_pt`. Decide whether Phase 1 already eliminates it; otherwise factor a single helper.
- [ ] Repeated 14-line block × 3 (potential savings: ~28 lines). First sites: CohomologyAPI.lean:452, CohomologyAPI.lean:505, CohomologyAPI.lean:649. Snippet head: `{X : TopCat.{u}} / {F₁ F₂ F₃ : TopCat.Presheaf AddCommGrpCat.{u} X}`. Decide whether Phase 1 already eliminates it; otherwise factor a single helper.

---

## Phase 4: Long proofs / simple statements

Top declarations by body line count, plus declarations whose body is ≥4x their
signature (the "simple statement, long proof" heuristic). These are golf
candidates: a 60-line proof for a 3-line statement usually has a 10-line core.

Top 40 declarations by body line count:

- [ ] Golf `sheafH_filtered_colimit_comparison_one_iso_presheaf_boundary_hom` in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean:398` (signature 9L, body 241L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `exists_section_generating_stalks` in `Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean:133` (signature 12L, body 161L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `sheafH_filtered_colimit_surj_presheaf` in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean:550` (signature 13L, body 145L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `sheafH_filtered_colimit_comparison_isIso_presheaf_succ_succ` in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean:817` (signature 16L, body 142L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `sheafH_filtered_colimit_comparison_succ_compatibility_sheaf_aux` in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean:862` (signature 25L, body 141L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `filtered_colimit_exists_compatible_representatives` in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitGeneral.lean:204` (signature 13L, body 130L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `sheafH1_cokernel_iso_of_subsingleton_middle_presheaf` in `Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean:714` (signature 6L, body 111L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `finsetGeneratedSheaf_vanishing` in `Aristotle/GrothendieckVanishing/main/FinitelyGeneratedVanishing.lean:162` (signature 12L, body 98L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `sheafH_filtered_colimit_succ_shiftNatIso` in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean:359` (signature 7L, body 98L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `PushforwardHIso` in `Aristotle/GrothendieckVanishing/main/ClosedImmersionCohomology.lean:34` (signature 7L, body 85L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `sheafH_filtered_colimit_comparison_one_iso_presheaf_boundary` in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean:314` (signature 9L, body 74L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `ReducibleVanishing` in `Aristotle/GrothendieckVanishing/main/GrothendieckVanishing.lean:23` (signature 11L, body 73L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `sheafH_filtered_colimit_h1_cokernelFunctorIso` in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean:101` (signature 7L, body 72L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `sheafH1_cokernel_iso_of_subsingleton_middle_presheaf_natural` in `Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean:1324` (signature 8L, body 67L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `closedIncl_unit_stalk_isIso` in `Aristotle/GrothendieckVanishing/main/ClosedImmersion.lean:408` (signature 14L, body 64L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `sheafH_comp_extClass_naturality_presheaf` in `Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean:238` (signature 8L, body 59L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `sheafH_subsingleton_H1_of_flasque_of_epi_app_top_map_presheaf` in `Aristotle/GrothendieckVanishing/main/FlasqueVanishing.lean:514` (signature 7L, body 54L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `epi_app_of_shortExact_of_epi_restrictions_presheaf` in `Aristotle/GrothendieckVanishing/main/FlasqueVanishing.lean:320` (signature 6L, body 52L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `finsetGenCocone_isColimit` in `Aristotle/GrothendieckVanishing/main/FinitelyGeneratedVanishing.lean:65` (signature 2L, body 51L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `subsingleton_sheafH_of_closedImmersion_middle_presheaf` in `Aristotle/GrothendieckVanishing/main/ClosedImmersionCohomology.lean:126` (signature 5L, body 50L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `sheafH_filtered_colimit_h1_boundary_square` in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean:230` (signature 5L, body 50L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `closedComplementVanishing` in `Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean:376` (signature 9L, body 48L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `stalk_zero_of_ses_g_iso_presheaf` in `Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean:451` (signature 7L, body 46L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `epi_pushforward_map_closedIncl_of_locallySurjective` in `Aristotle/GrothendieckVanishing/main/ClosedImmersion.lean:263` (signature 11L, body 44L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `stalk_zero_of_g_is_cokernel_of_stalk_epi_presheaf` in `Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean:554` (signature 6L, body 44L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `subsheaf_zeroOutsideInt_vanishing` in `Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean:512` (signature 8L, body 44L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `sheafH_filtered_colimit_h1_cokernelFunctor` in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean:51` (signature 6L, body 44L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `sheafH_filtered_colimit_succ_quotientCocone_isColimit` in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean:268` (signature 3L, body 44L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `stalk_zero_of_shortExact_kernel_presheaf` in `Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean:504` (signature 7L, body 43L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `toPlus_surjective_of_firstPlus` in `Aristotle/GrothendieckVanishing/main/ConstantSheafFlasque.lean:62` (signature 5L, body 43L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `colimit_exists_gluing_of_compatible_finite_subcover` in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitGeneral.lean:347` (signature 16L, body 42L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `sheafH_filtered_colimit_h1_stageNatIso` in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean:180` (signature 8L, body 41L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `isFlasque_filtered_colimit_presheaf` in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean:60` (signature 9L, body 41L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `sheafH_extClassAddEquiv_of_subsingleton_middle_presheaf_apply` in `Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean:1581` (signature 6L, body 40L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `closedIncl_counit_isIso_presheaf` in `Aristotle/GrothendieckVanishing/main/ClosedImmersion.lean:185` (signature 13L, body 39L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `sHom_stalk_bijective_at` in `Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean:35` (signature 15L, body 38L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `filtered_colimit_restriction_eventually_zero_of_zero` in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitGeneral.lean:117` (signature 13L, body 38L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `cohomology_vanishing_of_finitelyGenerated_vanishing` in `Aristotle/GrothendieckVanishing/main/FinitelyGeneratedVanishing.lean:118` (signature 8L, body 36L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `exists_nonzero_stalk_in_V` in `Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean:88` (signature 9L, body 36L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.
- [ ] Golf `epi_app_top_of_subsingleton_sheafH1_presheaf` in `Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean:856` (signature 6L, body 35L). Look for redundant `simp` chains, manual `rfl`s after `simp`, unfolded `apply` sequences that `exact?`/`aesop` could close.

Body-to-signature ratio outliers (≥4x, body ≥ 15 lines):

- [ ] Golf `sheafH_filtered_colimit_comparison_one_iso_presheaf_boundary_hom` in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean:398` (body/sig ratio 26.8, body 241L, sig 9L).
- [ ] Golf `finsetGenCocone_isColimit` in `Aristotle/GrothendieckVanishing/main/FinitelyGeneratedVanishing.lean:65` (body/sig ratio 25.5, body 51L, sig 2L).
- [ ] Golf `sheafH1_cokernel_iso_of_subsingleton_middle_presheaf` in `Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean:714` (body/sig ratio 18.5, body 111L, sig 6L).
- [ ] Golf `zeroOutside` in `Aristotle/GrothendieckVanishing/main/ZeroOutside.lean:39` (body/sig ratio 17.0, body 17L, sig 1L).
- [ ] Golf `_root_.isZero_zeroOutsideInt_bot` in `Aristotle/GrothendieckVanishing/main/ZeroOutside.lean:366` (body/sig ratio 15.0, body 30L, sig 2L).
- [ ] Golf `sheafH_filtered_colimit_succ_quotientCocone_isColimit` in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean:268` (body/sig ratio 14.7, body 44L, sig 3L).
- [ ] Golf `sHom` in `Aristotle/GrothendieckVanishing/main/ZeroOutside.lean:175` (body/sig ratio 14.5, body 29L, sig 2L).
- [ ] Golf `sheafH_filtered_colimit_succ_shiftNatIso` in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean:359` (body/sig ratio 14.0, body 98L, sig 7L).
- [ ] Golf `exists_section_generating_stalks` in `Aristotle/GrothendieckVanishing/main/IrreducibleStep.lean:133` (body/sig ratio 13.4, body 161L, sig 12L).
- [ ] Golf `PushforwardHIso` in `Aristotle/GrothendieckVanishing/main/ClosedImmersionCohomology.lean:34` (body/sig ratio 12.1, body 85L, sig 7L).
- [ ] Golf `sheafH_filtered_colimit_surj_presheaf` in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean:550` (body/sig ratio 11.2, body 145L, sig 13L).
- [ ] Golf `topologicalKrullDim_add_one_eq_iSup_height_add_one` in `Aristotle/GrothendieckVanishing/main/TopologicalKrullDim.lean:183` (body/sig ratio 11.0, body 33L, sig 3L).
- [ ] Golf `sheafH_filtered_colimit_h1_cokernelFunctorIso` in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean:101` (body/sig ratio 10.3, body 72L, sig 7L).
- [ ] Golf `subsingleton_sheafH_of_closedImmersion_middle_presheaf` in `Aristotle/GrothendieckVanishing/main/ClosedImmersionCohomology.lean:126` (body/sig ratio 10.0, body 50L, sig 5L).
- [ ] Golf `sheafH_filtered_colimit_h1_boundary_square` in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean:230` (body/sig ratio 10.0, body 50L, sig 5L).
- [ ] Golf `filtered_colimit_exists_compatible_representatives` in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitGeneral.lean:204` (body/sig ratio 10.0, body 130L, sig 13L).
- [ ] Golf `sHom_app_generator` in `Aristotle/GrothendieckVanishing/main/ZeroOutside.lean:207` (body/sig ratio 9.5, body 19L, sig 2L).
- [ ] Golf `isFlasque_of_injective` in `Aristotle/GrothendieckVanishing/main/FlasqueVanishing.lean:430` (body/sig ratio 9.0, body 18L, sig 2L).
- [ ] Golf `sheafH_filtered_colimit_comparison_isIso_presheaf_succ_succ` in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean:817` (body/sig ratio 8.9, body 142L, sig 16L).
- [ ] Golf `epi_app_of_shortExact_of_epi_restrictions_presheaf` in `Aristotle/GrothendieckVanishing/main/FlasqueVanishing.lean:320` (body/sig ratio 8.7, body 52L, sig 6L).
- [ ] Golf `toPlus_surjective_of_firstPlus` in `Aristotle/GrothendieckVanishing/main/ConstantSheafFlasque.lean:62` (body/sig ratio 8.6, body 43L, sig 5L).
- [ ] Golf `sheafH_subsingleton_H1_of_flasque_presheaf` in `Aristotle/GrothendieckVanishing/main/FlasqueVanishing.lean:450` (body/sig ratio 8.5, body 34L, sig 4L).
- [ ] Golf `sheafH1_cokernel_iso_of_subsingleton_middle_presheaf_natural` in `Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean:1324` (body/sig ratio 8.4, body 67L, sig 8L).
- [ ] Golf `sheafH_filtered_colimit_comparison_one_iso_presheaf_boundary` in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimit.lean:314` (body/sig ratio 8.2, body 74L, sig 9L).
- [ ] Golf `finsetGeneratedSheaf_vanishing` in `Aristotle/GrothendieckVanishing/main/FinitelyGeneratedVanishing.lean:162` (body/sig ratio 8.2, body 98L, sig 12L).
- [ ] Golf `extClass_naturality` in `Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean:185` (body/sig ratio 8.0, body 32L, sig 4L).
- [ ] Golf `sheafH_filtered_colimit_succ_inj_subsingleton_presheaf` in `Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean:514` (body/sig ratio 8.0, body 32L, sig 4L).
- [ ] Golf `sheafH_subsingleton_H1_of_flasque_of_epi_app_top_map_presheaf` in `Aristotle/GrothendieckVanishing/main/FlasqueVanishing.lean:514` (body/sig ratio 7.7, body 54L, sig 7L).
- [ ] Golf `ext_subsingleton_of_isZero_tgt` in `Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean:221` (body/sig ratio 7.5, body 15L, sig 2L).
- [ ] Golf `sheafH_comp_extClass_naturality_presheaf` in `Aristotle/GrothendieckVanishing/main/CohomologyAPI.lean:238` (body/sig ratio 7.4, body 59L, sig 8L).

---

## Phase 5: Structural opportunities

Cross-file restructurings the auto-scanner cannot detect, sourced from
`.compress-state/structural_ideas.md`. Each item below is a single-cycle
entry point for a larger initiative documented there. Prefer these over
small-yield Phase-4 golf when both are available.

- [ ] **Idea 1 entry cycle — sheafify `PresheafFilteredColimitCore.lean`.** Replace the four remaining `_presheaf` decls (`sheafH_filtered_colimit_succ_inj_subsingleton_presheaf`, `sheafH_filtered_colimit_surj_presheaf`, `sheafH_filtered_colimit_comparison_presheaf`, `sheafH_filtered_colimit_comparison_succ_compatibility_presheaf`) with sheaf-level analogues using `Sheaf.colimit` / `presheafToSheaf`-preserves-colimits. Update callers in `PresheafFilteredColimit.lean`. Expected -150 to -250 raw LOC; full initiative target -400 to -700. Highest-leverage remaining work — do before any Phase 4 golf in these files.
      COMPLETE_IF: ! grep -qE '^(theorem|lemma|noncomputable def|def|abbrev|instance) sheafH_filtered_colimit_(succ_inj_subsingleton|surj|comparison|comparison_succ_compatibility)_presheaf\b' Aristotle/GrothendieckVanishing/main/PresheafFilteredColimitCore.lean
- [ ] **Idea 2 — collapse `class IsFlasqueSheaf` to a `def`.** The class at `FlasqueVanishing.lean:34` is a one-field wrapper around `IsFlasque F.val`; the auto-generated `casesOn`/`rec`/`recOn` are confirmed unused. Convert to `def IsFlasqueSheaf F := IsFlasque F.val` (or remove entirely and inline `IsFlasque F.val` at use sites). Update ~20 use sites in `FlasqueVanishing` + `IrreducibleStep` + `ConstantSheafFlasque`. Expected -30 to -50 raw LOC.
      COMPLETE_IF: ! grep -qE '^class IsFlasqueSheaf\b' Aristotle/GrothendieckVanishing/main/FlasqueVanishing.lean
- [ ] **Idea 3 — eliminate `ULiftInt.lean`.** Search Mathlib for an existing `(AddCommGrpCat.of (ULift ℤ) ⟶ G) ≃+ G` equivalence (try `lean_leansearch` for "ULift Int additive equivalence", `lean_loogle` for `ULift ℤ →+ _ ≃+ _`). If found, replace the 5 call sites (CohomologyAPI:541, ZeroOutside:180/201/202/220) and delete the file. If not, inline as a local `let` / fold into `ZeroOutside.lean`. Expected -20 to -28 raw LOC.
      COMPLETE_IF: ! test -f Aristotle/GrothendieckVanishing/main/ULiftInt.lean
- [ ] **Idea 4 — merge `ZeroOutsideFinset.lean` into `ZeroOutside.lean`.** Used only by `FinitelyGeneratedVanishing.lean`, same namespace, 77 lines + 3 decls. Move all decls into the bottom of `ZeroOutside.lean`; update imports in `FinitelyGeneratedVanishing.lean` and `GrothendieckVanishingOverview.lean`; delete the file. Expected -10 to -20 raw LOC + one fewer file.
      COMPLETE_IF: ! test -f Aristotle/GrothendieckVanishing/main/ZeroOutsideFinset.lean
- [ ] **Idea 6 — submit a Phase-4 ratio outlier to Aristotle for golf.** Pick a self-contained target NOT covered by Idea 1: `finsetGenCocone_isColimit` (FinitelyGeneratedVanishing.lean:65, body/sig 25.5), `zeroOutside` (ZeroOutside.lean:39, body/sig 17.0), or `isFlasque_of_injective` (FlasqueVanishing.lean:430, body/sig 9.0). Use `mcp__aristotle__submit_directory` with the prompt: "Golf the proof of `<name>` in this file. Minimize tactic count. Do not change the statement, signature, or any other declaration. Reply with just the rewritten proof body." Defer broader golf in `PresheafFilteredColimit*` until after Idea 1.


