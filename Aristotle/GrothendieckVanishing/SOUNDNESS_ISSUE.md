# Soundness Issue: `lean_run_code` Environment Pollution

**Date**: 2026-04-03
**Status**: Investigated, root cause identified, NOT a project/Mathlib bug

## Summary

When using the MCP lean-lsp `lean_run_code` tool (which creates temporary `.lean` files in the project root), `Subsingleton (Abelian.Ext X Y n)` is provable by `inferInstance` for **any** abelian category, any objects X Y, and any n. Combined with `Ext.addEquiv₀ : Ext X Y 0 ≃+ (X ⟶ Y)`, this proves `False`.

**This bug does NOT affect the actual project files.** In the real `FiniteGeneratorReduction.lean`, `inferInstance` correctly fails to synthesize `Subsingleton (Sheaf.H c'.pt 0)`.

## Root Cause

The `lean_run_code` MCP tool creates temporary `.lean` snippet files in the project root. These files appear to pick up definitions and instances from other root-level `.lean` files — specifically `codex-file.lean` — even though `codex-file.lean` is not part of the `Aristotle` lean_lib and is not imported by any project module.

The suspected mechanism: the LSP server's environment may cache instances from previously-opened/checked files (like `codex-file.lean`), making them available to subsequently-created snippet files.

## MWE (reproduces only in `lean_run_code`, NOT in real project files)

```lean
import Mathlib

open CategoryTheory Abelian

universe u

-- Step 1: Ext^0(Z,Z) is Subsingleton (SHOULD NOT hold -- Ext^0 ≃ Hom)
example (X Y : AddCommGrpCat.{u}) :
    Subsingleton (Ext X Y 0) := inferInstance

-- Step 2: Hom(Z,Z) is NOT Subsingleton (correct)
example : ¬ Subsingleton
    (AddCommGrpCat.of (ULift.{u} ℤ) ⟶ AddCommGrpCat.of (ULift.{u} ℤ)) := by
  intro h
  have : (0 : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ _) = 𝟙 _ := Subsingleton.elim _ _
  have h0 : (0 : ULift.{u} ℤ → ULift.{u} ℤ) ⟨1⟩ = ⟨0⟩ := rfl
  rw [this] at h0; simp at h0

-- Step 3: Contradiction via Ext.addEquiv₀ : Ext^0(X,Y) ≃+ (X ⟶ Y)
noncomputable example : False := by
  let Z := AddCommGrpCat.of (ULift.{u} ℤ)
  have h1 : Subsingleton (Ext.{u} Z Z 0) := inferInstance
  have h2 : Ext.{u} Z Z 0 ≃+ (Z ⟶ Z) := Ext.addEquiv₀
  have h3 : Subsingleton (Z ⟶ Z) := h2.toEquiv.subsingleton
  exact absurd (Subsingleton.elim (0 : Z ⟶ Z) (𝟙 Z)) (by
    intro heq
    have : (0 : ULift.{u} ℤ → ULift.{u} ℤ) ⟨1⟩ = (𝟙 Z : ULift.{u} ℤ → ULift.{u} ℤ) ⟨1⟩ := by
      rw [heq]
    simp at this)
```

## Verification that the project is NOT affected

In `FiniteGeneratorReduction.lean`, at the sorry on line 204 (n=0 base case):
`exact inferInstance` produces:
```
failed to synthesize instance of type class
  Subsingleton (Sheaf.H c'.pt 0)
```
This is the CORRECT behavior.

## Implications

1. **Project soundness is NOT compromised.** The sorry's in `FiniteGeneratorReduction.lean` are genuine open problems.
2. **Do NOT trust `lean_run_code` for soundness-critical testing.** Always verify proofs in the actual project files using `lean_diagnostic_messages` or `lean_goal`.
3. **`codex-file.lean` should be cleaned up or removed** — it contains scratch code, a `sorry`, and instance declarations that leak into the LSP environment.

## Recommendation

- Delete or rename `codex-file.lean` (and any `_mcp_snippet_*.lean` files) to prevent instance pollution in the LSP.
- When writing proofs, always verify via `lean_diagnostic_messages` on the actual file, not `lean_run_code`.
