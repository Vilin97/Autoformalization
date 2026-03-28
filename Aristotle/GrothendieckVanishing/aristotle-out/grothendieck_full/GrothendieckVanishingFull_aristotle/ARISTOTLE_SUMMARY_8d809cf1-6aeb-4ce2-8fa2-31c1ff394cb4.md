# Summary of changes
## Grothendieck's Vanishing Theorem — Partial Formalization

I structured a proof of Grothendieck's vanishing theorem (Hartshorne III.2.7) in `GrothendieckVanishingFull.lean`, reducing it to a single sorry that requires infrastructure not available in Mathlib.

### What was proved (sorry-free)

1. **`WithBot.ENat.lt_nat_cases`** — Order-theoretic extraction: if `x < n` in `WithBot ℕ∞` for `n : ℕ`, then either `x = ⊥` or `x = ↑↑d` for some `d < n`.

2. **`Opens.subsingleton_of_isEmpty`** — On an empty topological space, the type of opens is a subsingleton (only `⊥`).

3. **`Abelian.Ext.subsingleton_of_isZero`** — In any abelian category, `Ext(X, Y, n)` is subsingleton when `X` is the zero object. Uses the key identity `α = (mk₀(𝟙 X)).comp α` combined with `𝟙 X = 0` (since X is zero), `mk₀(0) = 0` (additivity of mk₀), and `0.comp α = 0` (Ext.zero_comp).

4. **`TopCat.Sheaf.isZero_of_isEmpty`** — Every sheaf on an empty topological space is the zero object. Uses `TopCat.Sheaf.isTerminalOfEmpty` (F(⊥) is terminal) and `IsTerminal.isZero` (terminal → zero in abelian categories).

5. **`sheafCohomology_subsingleton_of_empty_dim`** — Sheaf cohomology vanishes on empty spaces. Shows `topologicalKrullDim X = ⊥` implies `IsEmpty X` (via irreducible components), then applies the previous two lemmas.

6. **`FlasqueVanishing`** (main theorem, modulo one sorry) — Reduces `n > topologicalKrullDim X` to either the empty case (fully proved) or the finite-dimension case (sorry).

### What remains as sorry

**`grothendieck_vanishing_nat`** — The core vanishing lemma for spaces of finite dimension. This requires the **extension by zero functor j_!** (left adjoint of restriction to an open subset), which is **not available in Mathlib**.

### Why j_! is needed (documented in docstrings)

The standard proof (Hartshorne III.2.7) uses Noetherian induction on dimension. The inductive step requires the short exact sequence:
```
0 → j_!(F|_U) → F → i_*(F|_Z) → 0
```
where Z ⊂ X is a proper closed subset and U = X \ Z. Without j_!, this exact sequence cannot be constructed. All alternative approaches (Čech cohomology, direct limits, local cohomology) also require infrastructure absent from Mathlib. The docstring also notes that the "flasque → injective" approach is **false** (ℤ on a point is flasque but not injective).