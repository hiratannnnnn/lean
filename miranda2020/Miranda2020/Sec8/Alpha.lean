import Miranda2020.Sec7.Short

set_option linter.style.header false

/-!
# Miranda 2020, Section 8: powers of operation length

This file keeps the low-friction algebraic pieces of the `α > 1` section:
the powered length cost and the approximation argument obtained by comparing
an algorithmic upper bound with an optimal-cost lower bound.
-/

namespace Miranda2020
namespace Sec8

/-- Length-weighted cost for a natural exponent `α`.  The paper allows real
`α`; the integer-exponent version is enough for the stated `α ≥ 2` and
`α ≥ 3` regimes. -/
def lengthCost (alpha length : Nat) : Nat :=
  length ^ alpha

@[simp] theorem lengthCost_one (alpha : Nat) :
    lengthCost alpha 1 = 1 := by
  simp [lengthCost]

@[simp] theorem lengthCost_two (alpha : Nat) :
    lengthCost alpha 2 = 2 ^ alpha := rfl

/-- Abstract approximation sandwich used repeatedly in Section 8.  If an
algorithm has cost at most `upperFactor * measure`, and every optimum has cost
at least `lowerFactor * measure`, then the approximation factor is
`upperFactor / lowerFactor`. -/
theorem sandwich_approx
    {algCost optCost measure upperFactor lowerFactor : ℝ}
    (hAlg : algCost ≤ upperFactor * measure)
    (hOpt : lowerFactor * measure ≤ optCost)
    (hUpper : 0 ≤ upperFactor)
    (hLower : 0 < lowerFactor) :
    algCost ≤ (upperFactor / lowerFactor) * optCost := by
  have hLowerNonneg : 0 ≤ lowerFactor := le_of_lt hLower
  have h1 : lowerFactor * algCost ≤ lowerFactor * (upperFactor * measure) :=
    mul_le_mul_of_nonneg_left hAlg hLowerNonneg
  have h2 : lowerFactor * (upperFactor * measure) =
      upperFactor * (lowerFactor * measure) := by
    ring
  have h3 : upperFactor * (lowerFactor * measure) ≤ upperFactor * optCost :=
    mul_le_mul_of_nonneg_left hOpt hUpper
  have hmul : lowerFactor * algCost ≤ upperFactor * optCost := by
    exact le_trans h1 (h2 ▸ h3)
  calc
    algCost = (1 / lowerFactor) * (lowerFactor * algCost) := by
      field_simp [hLower.ne']
    _ ≤ (1 / lowerFactor) * (upperFactor * optCost) := by
      exact mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = (upperFactor / lowerFactor) * optCost := by
      field_simp [hLower.ne']

/-- The specific unsigned `α ≥ 2` sandwich in the paper: upper factor
`2^α`, lower factor `2^(α-1)`, hence approximation factor `2`.  We keep this
as an algebraic assumption over reals, avoiding operation-specific proofs. -/
theorem two_approx_from_double_sandwich
    {algCost optCost measure base : ℝ}
    (hAlg : algCost ≤ (2 * base) * measure)
    (hOpt : base * measure ≤ optCost)
    (hbase : 0 < base) :
    algCost ≤ 2 * optCost := by
  have h := sandwich_approx hAlg hOpt (mul_nonneg zero_le_two (le_of_lt hbase)) hbase
  have hfactor : (2 * base) / base = (2 : ℝ) := by
    field_simp [hbase.ne']
  simpa [hfactor] using h

/-- The signed `α ≥ 2` proof in Section 8 combines two lower bounds, giving a
`2 + 1 = 3` approximation. -/
theorem three_approx_from_split_bounds
    {algCost optCost : ℝ}
    (hAlg : algCost ≤ 2 * optCost + optCost) :
    algCost ≤ 3 * optCost := by
  nlinarith

end Sec8
end Miranda2020
