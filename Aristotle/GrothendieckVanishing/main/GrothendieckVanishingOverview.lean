import Aristotle.GrothendieckVanishing.main.ClosedImmersion
import Aristotle.GrothendieckVanishing.main.ZeroOutside
import Aristotle.GrothendieckVanishing.main.GrothendieckVanishing

/-!
# Grothendieck's vanishing theorem

Umbrella module for the Hartshorne III, Theorem 2.7 formalization.

For a Noetherian topological space `X` of dimension `n` and a sheaf `F` of abelian groups
on `X`, the imports below assemble `Hⁱ(X, F) = 0` for all `i > n`. The `#check`s expose
the headline results.
-/

#check GrothendieckVanishing
#check sheafH_subsingleton_of_flasque
