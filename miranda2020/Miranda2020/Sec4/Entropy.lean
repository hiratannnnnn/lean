import Miranda2020.Sec3.Inversions

set_option linter.style.header false

/-!
# Miranda 2020, Section 4: entropy for unsigned permutations

This file records the displacement/entropy quantity used later in the paper.
The paper indexes positions and values from `1` to `n`; here `Fin n` is
zero-based, but the distance `|π i - i|` is unchanged by this shift.
-/

namespace Miranda2020
namespace Sec4

open Sec3

variable {n : Nat}

/-- The displacement entropy of one element at position `i`. -/
def elemEnt (π : Equiv.Perm (Fin n)) (i : Fin n) : Nat :=
  Nat.dist (π i).val i.val

/-- The total entropy `ent(π)`. -/
noncomputable def Ent (π : Equiv.Perm (Fin n)) : Nat :=
  ∑ i : Fin n, elemEnt π i

/-- The identity permutation has zero element entropy at every position. -/
theorem elemEnt_identity_eq_zero (i : Fin n) :
    elemEnt (Sec3.ι n) i = 0 := by
  simp [elemEnt, Sec3.ι]

/-- The identity permutation has total entropy zero. -/
theorem ent_identity_eq_zero : Ent (Sec3.ι n) = 0 := by
  simp [Ent, elemEnt_identity_eq_zero]

/-- If all element entropies are zero, then the permutation is the identity. -/
theorem eq_identity_of_forall_elemEnt_eq_zero (π : Equiv.Perm (Fin n))
    (h : ∀ i : Fin n, elemEnt π i = 0) :
    π = Sec3.ι n := by
  ext i
  have hi : (π i).val = i.val := Nat.eq_of_dist_eq_zero (h i)
  simpa [Sec3.ι] using hi

/-- Zero total entropy forces every element entropy to be zero. -/
theorem forall_elemEnt_eq_zero_of_ent_eq_zero (π : Equiv.Perm (Fin n))
    (h : Ent π = 0) :
    ∀ i : Fin n, elemEnt π i = 0 := by
  intro i
  classical
  have hmem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => Nat.zero_le (elemEnt π j))).mp h i hmem

/-- Section 4 basic property: entropy is zero iff the permutation is sorted. -/
theorem ent_eq_zero_iff_eq_identity (π : Equiv.Perm (Fin n)) :
    Ent π = 0 ↔ π = Sec3.ι n := by
  constructor
  · intro h
    exact eq_identity_of_forall_elemEnt_eq_zero π
      (forall_elemEnt_eq_zero_of_ent_eq_zero π h)
  · intro h
    rw [h]
    exact ent_identity_eq_zero

end Sec4
end Miranda2020
