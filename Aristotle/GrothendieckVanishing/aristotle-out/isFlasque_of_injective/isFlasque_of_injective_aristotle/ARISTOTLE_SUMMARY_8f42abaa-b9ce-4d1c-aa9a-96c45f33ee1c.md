# Summary of changes
Successfully proved that injective sheaves are flasque (`isFlasque_of_injective`) in `isFlasque_of_injective.lean`.

**Proof strategy:** For opens `U ⊆ V` in a topological space `X` and an injective sheaf `I`, we show the restriction map `I(V) → I(U)` is epi by constructing a mono in the sheaf category and using the injective lifting property:

1. **Free abelian presheaf** (`freeAbPresheaf U`): The composition `yoneda.obj U ⋙ AddCommGrpCat.free`, sending `W` to `FreeAbelianGroup(Hom(W, U))`.

2. **Free abelian sheaf** (`freeAbSheaf U`): The sheafification of the free abelian presheaf.

3. **Yoneda-like identification** (`freeAbSheafHomEquiv`): A chain of three adjunctions gives `(freeAbSheaf U ⟶ I) ≃ I(U)`:
   - Sheafification adjunction
   - Free–forgetful adjunction on functor categories
   - Yoneda lemma

4. **Mono construction** (`freeAbSheafMap_mono`): The inclusion `i : U ⟶ V` induces a mono `freeAbSheaf U ↪ freeAbSheaf V`, since:
   - `yoneda.map i` is mono (thin category)
   - `AddCommGrpCat.free` preserves monos
   - Sheafification preserves monos (preserves finite limits)

5. **Main argument**: Since `I` is injective, any morphism `freeAbSheaf U → I` factors through the mono `freeAbSheaf U ↪ freeAbSheaf V`. By the naturality of the equivalence (`freeAbSheafHomEquiv_naturality`), this factorization corresponds to the restriction map being surjective, hence epi.