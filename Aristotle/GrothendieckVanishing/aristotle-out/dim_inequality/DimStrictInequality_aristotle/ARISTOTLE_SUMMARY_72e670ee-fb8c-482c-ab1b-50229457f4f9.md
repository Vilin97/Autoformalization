# Summary of changes
I analyzed and proved the theorem about topological Krull dimension on irreducible spaces. Here's what I found and did:

## Key Finding: The Original Statement is False in General

The original theorem `topologicalKrullDim Y < topologicalKrullDim X` (without finiteness assumptions) is **false** when both `Y` and `X` have infinite Krull dimension. For example, `X = Spec(k[x₁,x₂,...])` is irreducible with `topologicalKrullDim = ⊤`, and `Y = V(x₁) ≅ Spec(k[x₂,x₃,...])` is a proper closed subset also with `topologicalKrullDim = ⊤`. Since `⊤ < ⊤` is false in `WithBot ℕ∞`, the strict inequality fails.

## What I Proved

I proved two theorems in `DimStrictInequality.lean`:

1. **`topologicalKrullDim_add_one_le_of_isIrreducible_of_isClosed`** (unconditional):
   `topologicalKrullDim Y + 1 ≤ topologicalKrullDim X`
   This is the strongest statement that holds without finiteness assumptions.

2. **`topologicalKrullDim_lt_of_isIrreducible_of_isClosed`** (corrected, with finiteness):
   Adding the hypothesis `topologicalKrullDim Y < ⊤` gives the strict inequality `topologicalKrullDim Y < topologicalKrullDim X`.

## Proof Structure (following the suggested strategy)

The proof uses exactly the tools suggested:

- **`IrreducibleCloseds.map`**: The inclusion `Y ↪ X` induces a map `IrreducibleCloseds(Y) → IrreducibleCloseds(X)`.
- **`IrreducibleCloseds.map_strictMono_of_isInducing`**: This map is strictly monotone.
- **`height_add_one_le`**: Since every element in the image is `< ⟨Set.univ, ...⟩` (the top of `IrreducibleCloseds(X)` — X itself is irreducible), we get `height(f(s)) + 1 ≤ height(⊤_X)` for each `s`.
- **`height_le_height_apply_of_strictMono`**: The strict monotonicity gives `height(s) ≤ height(f(s))`.
- **`krullDim_eq_iSup_height`** + **`iSup_le`**: Taking the supremum yields `topologicalKrullDim Y + 1 ≤ topologicalKrullDim X`.

The original theorem statement is preserved as a commented-out block with an explanation of why it's false.