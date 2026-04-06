# /simplify — Systematic code simplification, compression, and generalization

Improve code quality of a completed Lean 4 formalization. This is post-completion polish: the project compiles with 0 sorry's, and the goal is to make it shorter, cleaner, more general, and more maintainable.

**Constraint**: Everything must still compile at default heartbeats (200000). Deleting comments or docstrings does not count as simplification.

## Phase 0: Assess and plan (do NOT skip)

1. **Measure**: `wc -l <project>/main/*.lean | sort -rn | head -10` — know the starting total and biggest files.
2. **Understand the math**: Read the module docstrings and CLAUDE.md to understand the proof architecture. You cannot simplify what you do not understand.
3. **Identify the 3 biggest wins**: Use the decision tree below. Estimate lines saved for each. Write them down before touching any code.
4. **Work top-down**: Always start with the highest-impact structural change, not local golfing. A single helper extraction can save 50–100 lines; a single `intro; obtain` merge saves 1 line. Do the big things first.

## Decision tree: "This proof seems too long"

```
Proof seems too long or complex
├─ Is it doing something "basic" in 20+ lines?
│   ├─ Search Mathlib — the lemma probably exists
│   │   Tools: lean_leansearch, lean_loogle, lean_leanfinder, lean_local_search
│   │   Action: Replace with Mathlib API call
│   │   └─ Not found → State in Mathlib-ready generality (see Missing Lemmas below)
│   └─ Still hard → Definition might be fighting you (see Definition Problems below)
├─ Same pattern appears 2+ times?
│   └─ Extract helper in MAXIMUM generality (see Helper Extraction below)
├─ Proof has a complex case split?
│   └─ Look for a congr/EqOn/EventuallyEq approach
├─ Proof manually threads through a definition?
│   └─ Search for a simp lemma about the definition
└─ Proof is inherently complex, just long?
    └─ Use local golfing techniques (Phase 3 below)
```

## Phase 1: Structural refactoring (biggest wins, do first)

### 1A. Helper extraction (same pattern appears 2+ times)

**How to find**: Grep for repeated proof blocks. Common signatures:
```bash
# Repeated SES construction
grep -n "ShortComplex.mk.*kernel.ι" main/*.lean
# Repeated adjunction unit / closed immersion pattern  
grep -n "epi_unit_of_closedImmersion" main/*.lean
# Repeated stalk vanishing arguments
grep -n "sheaf_isZero_of_zero_stalks" main/*.lean
# Repeated dimension arguments
grep -n "topologicalKrullDim_lt_of_isIrreducible" main/*.lean
```

**How to extract**: 
1. Find the MOST GENERAL common pattern (parameterize over all differences).
2. State the helper with the weakest possible hypotheses.
3. Place it in the earliest file in the import chain that has all prerequisites.
4. Replace all call sites. Each should become 1–5 lines.
5. Verify: `rm -f .lake/build/lib/lean/<module>.olean && lake build`

**Key principle**: If two objects are isomorphic and you're proving a property of both separately, prove the isomorphism instead and transfer the property. Don't prove "vanishing of A implies vanishing of B" in 30 lines when A ≅ B via a 5-line isomorphism.

### 1B. Mathlib replacement (doing something basic in 20+ lines)

**How to find**: Read each proof and ask "is this a standard mathematical fact?" If yes, it's probably in Mathlib.

**Search strategy**:
1. `lean_leansearch "natural language description"` — for conceptual search
2. `lean_loogle "Type → Type → Prop"` — for type-pattern search  
3. `lean_local_search "name_fragment"` — for name-based search
4. `lean_leanfinder "concept"` — for semantic search

**Common wins**:
- Filtered colimit preservation → `HasFilteredColimitsOfSize`, `createsColimitOfIsSheaf`
- Stalk computations for closed immersions → `stalkPushforward_iso_of_isInducing`
- Exactness preservation under functors → `map_of_preservesLeftHomologyOf`
- Injective → flasque → acyclic chain → check if Mathlib has `Injective.isFlasque`

**When Mathlib doesn't have it**: State your lemma in Mathlib-ready generality (e.g., for general sites, not just topological spaces). This often simplifies the proof by removing unnecessary specificity.

### 1C. Definition problems (definition is fighting you)

**Symptoms**: Lots of `change`, `show`, `conv`, `eqToHom` in proofs. These indicate the definitions don't match what you need.

**Solutions**:
- Add `@[simp]` lemmas for your definitions
- Use `abbrev` instead of `def` when you want definitional unfolding
- Restructure the definition to match how it's used (e.g., if you always unfold it immediately, it shouldn't be a `def`)

### 1D. Moving declarations for better import structure

If a helper is defined in file A but needed in file B (which A doesn't import), either:
- Move the helper to a common ancestor in the import chain
- Create a small shared file for cross-cutting helpers
- Restructure imports if the current dependency order is wrong

## Phase 2: Medium-scale refactoring

### 2A. Merge cases that share structure

If an induction has cases that share 80% of their proof:
1. Extract the shared part as a lemma parameterized over what differs
2. Each case becomes a 2–3 line application

Example: `PushforwardHVanishing_one` and `PushforwardHVanishing_succ` share the pattern "push injective presentation, show flasque, dimension shift." Merge into one lemma for n ≥ 1.

### 2B. Generalize hypotheses

Look for:
- `[IrreducibleSpace X]` that isn't needed (the proof works for general spaces)
- `(n : ℕ)` that could be `(n : ℤ)` or `(n : WithBot ℕ∞)`
- Specific sheaf types (`zeroOutsideInt V`) that could be arbitrary sheaves with a property
- `AddCommGrpCat` that could be any abelian category

### 2C. Deduplicate across files

Common culprits:
- Presheaf vs sheaf versions of the same lemma (often the sheaf version is a trivial corollary via `toSheafify`)
- `finsetCoproductIncl` vs `finsetCoproductInclGen` (one is a special case of the other)
- Multiple `IsFlasqueSheaf` proofs for pushforwards of injectives

## Phase 3: Local golfing (do AFTER structural changes)

Only after Phases 1–2 are exhausted. These give diminishing returns.

### Safe mechanical compressions (apply in bulk):

```
# Find intro/tactic pairs to merge with semicolons
grep -Pn '^\s+intro \w+$' main/*.lean

# Find single-use `have` bindings
# Pattern: `have X := Y` followed by single use of X

# Find `by exact X` that could be just `X`
grep -n 'by exact' main/*.lean

# Find `constructor; intro a b` that could be `⟨fun a b => by ...⟩`
grep -n 'constructor; intro' main/*.lean
```

### Compression patterns (safest first):
1. `intro x; obtain` → `intro x; obtain` on one line (saves 1 line each, no risk)
2. `have X := Y; exact Z X` where X used once → `exact Z Y`  
3. `have X : T := by exact Y` → `have X : T := Y`
4. `rw [...]; rfl` → check if `simp [...]` works
5. `constructor; intro a b; ...` → `⟨fun a b => by ...⟩` (when proof is short)
6. Merge sequential `simp only [A]; simp only [B]` → `simp only [A, B]`
7. `cases e; rfl` on two lines → `cases e; rfl` on one line

### What NOT to do:
- Don't inline `have` bindings that are used 2+ times
- Don't merge tactics if it makes the line > 100 chars
- Don't change `by` proofs to term-mode if it hurts readability
- Don't delete comments or docstrings
- Don't increase heartbeats

## Phase 4: Verify and commit

After each batch of changes:
1. **Delete stale .olean files**: `rm -f .lake/build/lib/lean/<project>/main/*.olean`
2. **Full rebuild**: `lake build 2>&1 | grep error`
3. **Check line count**: `wc -l <project>/main/*.lean | tail -1`
4. **Commit** via `/commit` with a message summarizing:
   - Lines saved (net)
   - What was changed (helpers extracted, Mathlib replacements, local golf)
   - Files affected

## Anti-patterns to avoid

1. **Golf addiction**: Spending 30 minutes to save 2 lines. If a change takes more than 5 minutes and saves < 5 lines, skip it.
2. **Breaking working code**: Always rebuild after changes. Never commit code that doesn't compile.
3. **Bottom-up only**: Starting with `intro` merges instead of structural refactoring. The order matters: Phase 1 → 2 → 3.
4. **Dimension arithmetic hell**: `WithBot ℕ∞` arithmetic is fragile. If a proof needs 10 lines of `lift`/`exact_mod_cast`, extract it as a helper or accept the verbosity.
5. **Touching PresheafFilteredColimit.lean**: This file has deeply entangled `change`/`show` patterns for concrete category coercions. Only touch it if you have a clear structural win.
6. **Ignoring the mathematics**: The biggest wins come from understanding the math and finding the right abstraction, not from syntactic manipulation.
