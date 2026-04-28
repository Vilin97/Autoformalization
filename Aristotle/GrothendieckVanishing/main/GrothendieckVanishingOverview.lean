import Aristotle.GrothendieckVanishing.main.ClosedImmersion
import Aristotle.GrothendieckVanishing.main.ZeroOutside
import Aristotle.GrothendieckVanishing.main.GrothendieckVanishing

/-!
# Grothendieck's Vanishing Theorem

Umbrella module for the Hartshorne III, Theorem 2.7 formalization.

For a Noetherian topological space `X` of dimension `n` and a sheaf `F` of abelian groups on
`X`, the development imported here proves `H^i(X, F) = 0` for all `i > n`.

The imported files provide the closed-immersion comparison maps, extension-by-zero machinery,
and the final vanishing theorems. The `#check`s at the end expose the headline results from
this assembled development.
-/

#check GrothendieckVanishing
#check sheafH_subsingleton_of_flasque
