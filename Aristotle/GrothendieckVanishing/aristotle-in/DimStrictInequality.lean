import Mathlib

universe u

open TopologicalSpace Order

/-- On an irreducible space, a proper closed subset has strictly smaller Krull dimension.
    Every irreducible closed subset of Y is also one of X, but X itself is not in Y.
    The embedding IrreducibleCloseds(Y) → IrreducibleCloseds(X) is strictly monotone
    and misses X (the maximum of IrreducibleCloseds(X)), so every chain in Y can be
    extended by X in X, giving dim(Y) + 1 ≤ dim(X), hence dim(Y) < dim(X).

    Proof strategy:
    1. The inclusion Y ↪ X induces a map IrreducibleCloseds(Y) → IrreducibleCloseds(X)
       via IrreducibleCloseds.map (sending Z to closure of Z in X, but Z is already
       closed so it equals Z).
    2. This map is strictly monotone (IrreducibleCloseds.map_strictMono_of_isInducing).
    3. Every element Z in the image satisfies Z ≤ Y' < X where Y' corresponds to Y
       (as an irreducible-closed or just closed set). More precisely, Z ⊆ Y ⊊ X.
    4. Therefore height(Z in X-poset) + 1 ≤ height(X in X-poset) for every Z in image.
       Use Order.height_add_one_le.
    5. dim(Y) = krullDim(IClosed(Y)) ≤ krullDim(image) ≤ sup of heights in X ≤ dim(X) - 1
    6. Conclude dim(Y) < dim(X).

    Mathlib tools: topologicalKrullDim_subspace_le, IrreducibleCloseds.map,
    IrreducibleCloseds.map_strictMono_of_isInducing, krullDim_le_of_strictMono,
    height_add_one_le, height_le_krullDim. -/
theorem topologicalKrullDim_lt_of_isIrreducible_of_isClosed {X : Type u} [TopologicalSpace X]
    [IrreducibleSpace X] {Y : Set X} (hY : IsClosed Y) (hne : Y ≠ Set.univ) :
    topologicalKrullDim Y < topologicalKrullDim X := by
  sorry
