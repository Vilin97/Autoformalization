# Distilled Mathlib Conventions

A 50-rule distillation of <https://github.com/Vilin97/mathlib-conventions/blob/main/conventions.md>
(792 rules across 14 categories), focused on what matters when writing or
refactoring real Lean 4 / Mathlib-style code outside Mathlib itself.

The original frequencies are noted in brackets — a convention with
`[mentioned 287×]` is one reviewers cite constantly.

## A. Proof style

**1. Reuse existing API before writing long proofs.** [≈323+] If a proof is
longer than expected, search for `_iff`, `_apply`, `_def`, `mem_*`, `map_*`
lemmas first. Prefer `exact`, `apply`, `rw`, `simpa`, `.mp`, `.mpr` over
reproving standard facts. Treat definitions as opaque when interface lemmas
exist — do not `unfold`.

**2. Prefer clear structure over golfing.** [≈70] Avoid dense one-liners,
deep nesting, giant `exact` terms, and `rw [show ... by ...]` tricks (rule 45
of the source). When several rewrites are needed, use `calc` or intermediate
`have`s rather than a long opaque `rw [...]` chain.

**3. Use `simpa` / `simpa using h` for short adaptations.** [≈110] If a proof
is just an existing lemma plus harmless rewriting, write `simpa using h`, not
`rw [...]; exact h` or `simp [...] at h; exact h`.

**4. Use `suffices` to expose the key intermediate goal.** [≈36] When a proof
naturally proceeds through a simpler claim, state it with `suffices` —
clearer than a long chain of local rewrites.

**5. Use `calc` for chained equalities and inequalities.** [≈62] Don't fake
calc with `Eq.trans`, `le_trans`, or repeated `rw`.

**6. Destructure hypotheses early with `obtain` / `rcases` / `rintro`.**
[≈90] Don't carry `h.1.2.1` projection chains. Use `rintro rfl` and `obtain
rfl` to eliminate equalities of variables on the spot.

**7. Use `subst` (or `rintro rfl`, `obtain rfl`) early for variable
equalities.** [≈25] If a hypothesis identifies a local variable with a term,
eliminate it; don't carry the equality around.

**8. Keep one active goal at a time.** [≈34] Use bullets (`·`), `case`, or
`refine ⟨…, ?_⟩` so every subgoal is handled visibly. Don't rely on fragile
goal ordering.

**9. Use `refine ⟨…, ?_⟩` with `?_`, not `_`, for goal-generating holes.**
[≈40] `_` is for elaboration; `?_` is for explicit subgoals.

**10. Use term-style proofs when natural.** [≈30] Don't wrap a one-term proof
in `by exact`. Conversely, inside tactic mode use `exact` for known terms,
`apply` only when you want subgoals.

**11. Keep main proof branch visually prominent (line-of-sight rule).**
[≈22] Indent subordinate branches under bullets, but keep the main flow easy
to scan top-to-bottom.

**12. Avoid blank lines inside proofs.** [≈18] Use proof structure or a brief
comment for visual separation, not empty lines.

## B. Tactic usage

**13. Prefer the simplest specialized tactic.** [≈80] Use `ring`, `omega`,
`linarith`, `norm_num`, `norm_cast`, `positivity`, `gcongr`, `fun_prop`,
`field_simp` when they match the goal shape. Don't default to broad
automation.

**14. Use `rintro` for introduction-with-destructuring.** [≈40] Replace
`intro h; obtain ⟨a, b⟩ := h` with `rintro ⟨a, b⟩`.

**15. Prefer `obtain` over `rcases` for non-branching destructuring.** [≈25]
Use `rcases` for actual case splits.

**16. Combine consecutive `rw` calls.** [≈45] One `rw [a, b, c]` beats three
separate `rw`s.

**17. Use `induction ... with | … => …` (Lean 4 form), not `induction'` /
`cases'`.** [≈30] Same goes for `refine` over `refine'`. Avoid legacy Lean 3
tactics.

**18. Use `gcongr` for monotonicity goals; `positivity` for `0 ≤ _` /
`0 < _`.** [≈40] These are the right tools — don't chain monotonicity lemmas
by hand.

**19. Avoid `erw`.** [≈48] Replace with `rw` after `dsimp`/`change`/`simp
only`, or add a proper API lemma.

**20. Avoid `convert` unless it clearly simplifies reuse.** [≈25] Prefer
`simpa using` or precise rewriting. If `convert` is the right tool, use
`convert h using n` to bound match depth.

**21. Use `change` only when definitional reshaping is the actual point.**
[≈15] Don't use it as routine goal massaging.

**22. Replace search tactics (`exact?`, `apply?`, `simp?`) with concrete
output.** [≈18] They're for discovery, not committed proof scripts.

## C. simp usage

**23. Use `simp only [...]` for non-terminal simplification.** [≈287] Bare
`simp` mid-proof is fragile. Exception: `simp` immediately followed by a
normalizing tactic like `ring`, `omega`, `norm_num`, `abel`.

**24. Use plain terminal `simp` to close goals.** [≈55] Don't pre-emptively
restrict to `simp only` for terminal calls unless stability/perf demands it.

**25. Pass local hypotheses to `simp` explicitly.** [≈35] `simp [h]` or
`simpa using h`, not `simp; exact h`.

**26. Use `simp_rw` for repeated rewriting or rewriting under binders.**
[≈25] Better than chaining `rw`s through `∀`/`∃`.

**27. Avoid `simp_all` and `simp at *`.** [≈20] Prefer targeted `simp [...]
at h ⊢`. `simp_all` rewrites the entire context and is hard to debug.

**28. Only mark `@[simp]` on lemmas that fire often, simplify toward a
canonical form, and don't loop.** [≈85] LHS more complex than RHS; stable
constant head; no hard side conditions.

**29. Prove definitional facts with `:= rfl`, not `:= by simp` or `:= by
rfl`.** [≈45] Makes them usable by `dsimp` and signals intent.

## D. Code style & formatting

**30. Make inferable arguments implicit `{...}`, non-inferable explicit
`(...)`.** [≈220] Use named arguments `(R := R)` over `@foo _ _ _` when
specifying implicits manually.

**31. Use `lowerCamelCase` for definitions / projections / bundled maps;
`UpperCamelCase` for types / structures / classes / namespaces / files;
`snake_case` for theorems and lemmas.** [≈90] Preserve established acronyms
(`FG`, `ULift`, `ENNReal`).

**32. Prefer `fun x ↦ ...` over `fun x => ...` for lambdas.** [≈45] `=>` is
for `match` arms.

**33. Prefer `Type*` over `Type _` or explicit universe parameters.** [≈30]
Add explicit universes only when truly needed.

**34. Open namespaces narrowly.** [≈40] Prefer `open … in <decl>`, qualified
names, or `open scoped` over file-wide `open`. Same for `Classical`.

**35. Don't restate parameters already in scope; use `variable` blocks.**
[≈35] But still write each declaration with the binders you want it to
depend on. Close `section`s when assumptions are no longer needed.

**36. Drop redundant namespace qualifiers when inside `namespace X`.** [≈20]
Inside `namespace Foo`, write `bar`, not `Foo.bar`.

**37. Use named projections (`.val`, `.fst`, field names) over `.1`, `.2`,
`.3`.** [≈25] More robust to refactor.

**38. Use `where` and named fields for structures and instances.** [≈15]
```lean
instance : Foo α where
  bar := ...
  baz := ...
```

**39. Keep `:=`, `by`, infix operators at the end of the previous line, not
the start of the next.** [≈18] Don't begin a line with `=`, `+`, `*`, `≫`,
`∘`, `:`, `:=`, `by`.

**40. Prefer `≤` and `<` over `≥` and `>` in statements.** [≈12] Matches
Mathlib normal forms.

**41. Don't shadow names; use descriptive fresh names.** [≈22] Avoid
overloading `h`, `this` across nested scopes when possible. Avoid `rename_i`
— name binders directly.

**42. Use `<|` and `|>` over `$`.** [≈15]

**43. Don't write trivial trailing comments** that restate the code, or
narrate "this lemma is used by X". Comments earn their place by explaining
non-obvious *why*.

## E. Naming

**44. Mirror existing Mathlib names: `_iff`, `_of_`, `_eq_`, `_apply`,
`_def`, `_left`, `_right`, `_symm`, `map_*`, `mem_*`, `coe_*`, `_mono`.**
[≈367+] Build names from the statement, left-to-right (`image_union`, not
`union_image`). Use `_iff` only for genuine `↔`.

**45. Place declarations in the namespace of their primary receiver, so dot
notation reads naturally.** [≈135] First explicit argument should be the
"receiver".
```lean
namespace IsOpen
theorem preperfect (hU : IsOpen U) : ... := ...
end IsOpen
```

**46. Don't repeat the namespace inside the identifier.** [≈20] Inside
`namespace Foo`, write `bar`, not `fooBar`.

## F. Generalization & hypotheses

**47. State results under the weakest assumptions actually used.** [≈453+]
`Semiring` over `Ring`, `Preorder` over `LinearOrder`, `Finite` over
`Fintype`, `x ≠ 0` over `0 < x`. Remove unused hypotheses.

**48. Keep `Classical` / `Decidable` / `noncomputable` local.** [≈55] Use
`by classical` or `letI`/`haveI` inside a proof rather than adding it to the
statement. Mark only the smallest declaration `noncomputable`.

**49. Prefer `↔` for genuinely bidirectional results.** [≈30] Variables
appearing on both sides should usually be implicit so `rw [foo_iff]` and
`.mp`/`.mpr` work without extra arguments.

## G. Documentation

**50. Add a module docstring `/-! # Title ... -/` to every substantive file,
right after the imports.** [≈45] Describe mathematical purpose, main
definitions, main results — not PR history.

**51. Use `/-- ... -/` for declaration docstrings on public, user-facing
declarations.** [≈329+] Describe what the declaration *means
mathematically*, not what its tactics do. Self-contained — don't say "above"
or "this".

**52. Mark internal helpers `private` or note they are implementation
details.** [≈25] Don't simulate privacy with leading underscores.

---

## Refactor checklist

When applying this to existing code, scan in roughly this order:

1. **Naming pass** (rule 44): rename `snake_case` defs to `camelCase`;
   `camelCase` lemmas to `snake_case`; rename anything that doesn't follow
   the standard suffix patterns.
2. **`fun => ↦`** (rule 32) and **`Type _ → Type*`** (rule 33) — mechanical.
3. **`simp only` discipline** (rules 23, 27): replace non-terminal `simp`
   with `simp only [...]`; replace `simp_all` / `simp at *` with targeted
   `simp [...] at h ⊢`.
4. **`rw [show ... by ...]` chains** (rule 2) → introduce `have` or `calc`.
5. **Inlined-everything golfing** that hurts readability (rule 2) → restore
   one or two `have`s with names.
6. **Long `rw [a, b, c, d, e, f, ...]`** (rule 16 + rule 5): if it's
   semantically a chain of equalities, rewrite as `calc`.
7. **`.1` / `.2` projection chains** (rule 37) → named fields.
8. **`constructor; · ...; · ...` / `refine ⟨_, _⟩`** (rule 9) → `refine ⟨?_,
   ?_⟩` or `⟨ha, hb⟩` with explicit names.
9. **Module docstrings missing** (rule 50) → add `/-! # Title -/` after
   imports.
10. **Redundant namespace qualifiers** (rule 36) inside `namespace` blocks.
11. **`rfl`-by-simp / `by rfl`** (rule 29) → `:= rfl`.
12. **Erase `erw`** (rule 19) — replace with `rw` after `dsimp`/`change`.

This is the working set used for the Clawristotle 2026-04-29 refactor pass.
