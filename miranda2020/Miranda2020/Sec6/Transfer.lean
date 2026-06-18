import Miranda2020.Sec5.Signed

set_option linter.style.header false

/-!
# Miranda 2020, Section 6: transfer from unrestricted algorithms

Section 6 uses existing approximation algorithms for unrestricted rearrangement
problems and replaces each long operation by a bounded-length sequence. This
file formalizes the algebraic core of that transfer argument, without yet
formalizing concrete rearrangement operations.
-/

namespace Miranda2020
namespace Sec6

/-- The five rearrangement models considered in the paper. -/
inductive Model where
  | unsignedReversal
  | transposition
  | unsignedReversalTransposition
  | signedReversal
  | signedReversalTransposition
  deriving DecidableEq, Repr

/-- The abstract inequality behind Lemma 13: every `λ`-bounded solution is also
an unrestricted solution, so the unrestricted optimum is no larger. -/
def UnrestrictedLeBounded (unrestrictedOpt boundedOpt : ℝ) : Prop :=
  unrestrictedOpt ≤ boundedOpt

/-- The abstract expansion guarantee supplied by Lemma 14.  `expandedCost` is
the cost after replacing long unrestricted operations by `λ`-bounded operation
sequences. -/
def ExpansionBound (factor unrestrictedCost expandedCost : ℝ) : Prop :=
  expandedCost ≤ factor * unrestrictedCost

/-- Algebraic core of Theorems 4--6.

If an unrestricted algorithm has cost at most `x * unrestrictedOpt`, replacing
its operations increases cost by at most `factor`, and Lemma 13 gives
`unrestrictedOpt ≤ boundedOpt`, then the resulting bounded algorithm has cost at
most `(factor * x) * boundedOpt`. -/
theorem transfer_approx
    {unrestrictedOpt boundedOpt unrestrictedAlgCost expandedCost factor x : ℝ}
    (hOpt : UnrestrictedLeBounded unrestrictedOpt boundedOpt)
    (hAlg : unrestrictedAlgCost ≤ x * unrestrictedOpt)
    (hExpand : ExpansionBound factor unrestrictedAlgCost expandedCost)
    (hFactor : 0 ≤ factor) (hx : 0 ≤ x) :
    expandedCost ≤ (factor * x) * boundedOpt := by
  have h1 : expandedCost ≤ factor * (x * unrestrictedOpt) := by
    exact le_trans hExpand (mul_le_mul_of_nonneg_left hAlg hFactor)
  calc
    expandedCost ≤ factor * (x * unrestrictedOpt) := h1
    _ = (factor * x) * unrestrictedOpt := by ring
    _ ≤ (factor * x) * boundedOpt := by
      exact mul_le_mul_of_nonneg_left hOpt (mul_nonneg hFactor hx)

/-- A convenience specialization matching the paper's `O(xn/λ)` wording: if the
replacement factor is bounded by `scale`, the approximation factor becomes
`scale * x`. -/
theorem transfer_approx_of_factor_le
    {unrestrictedOpt boundedOpt unrestrictedAlgCost expandedCost factor scale x : ℝ}
    (hOpt : UnrestrictedLeBounded unrestrictedOpt boundedOpt)
    (hAlg : unrestrictedAlgCost ≤ x * unrestrictedOpt)
    (hExpand : ExpansionBound factor unrestrictedAlgCost expandedCost)
    (hFactorLe : factor ≤ scale)
    (hScale : 0 ≤ scale) (hx : 0 ≤ x)
    (hAlgNonneg : 0 ≤ unrestrictedAlgCost) :
    expandedCost ≤ (scale * x) * boundedOpt := by
  have hExpandedLeScale : expandedCost ≤ scale * unrestrictedAlgCost := by
    exact le_trans hExpand
      (mul_le_mul_of_nonneg_right hFactorLe hAlgNonneg)
  exact transfer_approx hOpt hAlg hExpandedLeScale hScale hx

end Sec6
end Miranda2020
