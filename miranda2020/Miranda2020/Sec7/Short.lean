import Miranda2020.Sec6.Transfer

set_option linter.style.header false

/-!
# Miranda 2020, Section 7: short rearrangements

This file records the lightweight formal content of the `λ = 3` section.  The
graph-theoretic definition of odd connected components is intentionally left as
a parameter, since formalizing the inversion graph is a separate project.
-/

namespace Miranda2020
namespace Sec7

open Sec5

variable {n : Nat}

/-- Length at most two: "super short" in the paper. -/
def SuperShort (length : Nat) : Prop :=
  length ≤ 2

/-- Length at most three: "short" in the paper. -/
def Short (length : Nat) : Prop :=
  length ≤ 3

/-- Every super-short rearrangement is short. -/
theorem superShort_is_short {length : Nat} (h : SuperShort length) :
    Short length := by
  unfold SuperShort Short at *
  omega

/-- The `ψ` potential from Section 7, parameterized by the odd-component count
`codd`. -/
noncomputable def PsiPotential
    (codd : SignedPerm n → Nat) (π : SignedPerm n) : Nat :=
  2 * π.Inv + codd π

/-- The `ψ` potential is zero at the identity if `codd` is zero there. -/
theorem psiPotential_identity_eq_zero
    {codd : SignedPerm n → Nat} (hcodd : codd (SignedPerm.identity n) = 0) :
    PsiPotential codd (SignedPerm.identity n) = 0 := by
  simp [PsiPotential, SignedPerm.inv_identity_eq_zero, hcodd]

/-- The five approximation factors summarized in Section 7. -/
def shortApproxFactor : Sec6.Model → ℚ
  | .unsignedReversal => 2
  | .transposition => (4 : ℚ) / 3
  | .unsignedReversalTransposition => 2
  | .signedReversal => 3
  | .signedReversalTransposition => (7 : ℚ) / 3

@[simp] theorem shortApproxFactor_unsignedReversal :
    shortApproxFactor .unsignedReversal = 2 := rfl

@[simp] theorem shortApproxFactor_transposition :
    shortApproxFactor .transposition = (4 : ℚ) / 3 := rfl

@[simp] theorem shortApproxFactor_unsignedReversalTransposition :
    shortApproxFactor .unsignedReversalTransposition = 2 := rfl

@[simp] theorem shortApproxFactor_signedReversal :
    shortApproxFactor .signedReversal = 3 := rfl

@[simp] theorem shortApproxFactor_signedReversalTransposition :
    shortApproxFactor .signedReversalTransposition = (7 : ℚ) / 3 := rfl

end Sec7
end Miranda2020
