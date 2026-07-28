/-
Copyright (c) 2026 Clawristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clawristotle contributors
-/
import McKayConjecture.GroupTheory.AlternatingSixHopfKernel
import McKayConjecture.GroupTheory.AlternatingSixSchurCoverExact

/-!
# The Schur multiplier of `A₆`

The explicit universal central extension has center of order six.
Uniqueness of universal central extensions transports that calculation to
the canonical free-presentation cover, and hence to its Hopf-formula
kernel.
-/

noncomputable section

namespace McKayConjecture
namespace GroupTheory

/-- The canonical Hopf-formula kernel for `A₆` has order six. -/
theorem alternatingSixHopfKernelHasOrderSix :
    AlternatingSixHopfKernelHasOrderSix := by
  apply
    alternatingSixHopfKernelHasOrderSix_iff_center.mpr
  rw [Nat.card_congr
    (Subgroup.centerCongr
      (alternatingSixUniversalCentralExtension.sourceEquiv
        alternatingSixSchurUniversalCentralExtension)).toEquiv]
  exact
    natCard_center_alternatingSixSchurPresentedGroup

end GroupTheory
end McKayConjecture
