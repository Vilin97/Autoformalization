/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.MinimalNormalFactors
import McKayConjecture.GroupTheory.SimpleQuasisimple

/-!
# Quasisimplicity of the factors of a nonabelian minimal normal subgroup
-/

noncomputable section

universe u

namespace McKayConjecture
namespace GroupTheory
namespace MinimalNormalFactors

open scoped IsMulCommutative

variable {G : Type u} [Group G]
variable {N : Subgroup G} [N.Normal]

namespace NonabelianMinimalNormalDecomposition

/-- Every simple factor in a nonabelian minimal-normal decomposition is
quasisimple (indeed, it is already centerless and simple). -/
theorem factor_isQuasisimple
    (D : NonabelianMinimalNormalDecomposition N)
    (i : D.ι) :
    IsQuasisimple (D.factor i) :=
  isQuasisimple_of_isSimpleGroup
    (D.factor_simple i) (D.factor_nonabelian i)

end NonabelianMinimalNormalDecomposition

end MinimalNormalFactors
end GroupTheory
end McKayConjecture
