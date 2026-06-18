import Mathlib

set_option linter.style.header false

/-!
# Miranda 2020, Section 3: unsigned inversions

This file starts a Lean formalization of the inversion-count part of Section 3.
An unsigned permutation of length `n` is represented as `Equiv.Perm (Fin n)`.
-/

namespace Miranda2020
namespace Sec3

variable {n : Nat}

/-- A pair of positions is an inversion when the earlier position carries a
larger value. This is the unsigned definition from Section 3. -/
def IsInversion (π : Equiv.Perm (Fin n)) (i j : Fin n) : Prop :=
  i < j ∧ π i > π j

instance (π : Equiv.Perm (Fin n)) (i j : Fin n) : Decidable (IsInversion π i j) := by
  unfold IsInversion
  infer_instance
/- hirata memo: 型クラス検索がIsInversionがDecidableであること
  を検証できないため、instanceとして登録して奥必要がある -/

/-- The finite set of inversion pairs of a permutation. -/
def inversionPairs (π : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  (Finset.univ.product Finset.univ).filter fun p =>
    IsInversion π p.1 p.2

/-- The inversion count `Inv(π)`. -/
def Inv (π : Equiv.Perm (Fin n)) : Nat :=
  (inversionPairs π).card
-- hirata memo: card stand for cardinality.

/-- The identity permutation, corresponding to the sorted unsigned permutation. -/
def ι (n : Nat) : Equiv.Perm (Fin n) :=
  Equiv.refl (Fin n)

/-- The identity permutation has no inversion at any chosen pair of positions. -/
theorem not_isInversion_identity (i j : Fin n) :
    ¬ IsInversion (ι n) i j := by
  intro h
  have hij : i < j := h.1
  have hji : j < i := h.2
  have hij_le : i <= j := le_of_lt hij
  have not_hji : ¬ j < i := not_lt_of_ge hij_le
  exact not_hji hji
  -- exact (not_lt_of_ge (le_of_lt h.1)) h.2

/-- The identity permutation has inversion count zero. -/
theorem inv_identity_eq_zero : Inv (ι n) = 0 := by
  classical
  rw [Inv, inversionPairs, Finset.card_eq_zero]
  ext p
  constructor
  · intro hp
    rw [Finset.mem_filter] at hp
    exact False.elim (not_isInversion_identity p.1 p.2 hp.2)
  · intro hp
    simp at hp

/-- `Inv π = 0` is equivalent to saying that no inversion pair exists. -/
theorem inv_eq_zero_iff_no_inversions (π : Equiv.Perm (Fin n)) :
    Inv π = 0 ↔ ∀ i j : Fin n, ¬ IsInversion π i j := by
  classical
  constructor
  · intro h i j hij
    have hp : (i, j) ∈ inversionPairs π := by
      rw [inversionPairs, Finset.mem_filter]
      constructor
      · exact Finset.mem_product.mpr ⟨Finset.mem_univ i, Finset.mem_univ j⟩
      · exact hij
    have hpos : 0 < (inversionPairs π).card := Finset.card_pos.mpr ⟨(i, j), hp⟩
    rw [Inv] at h
    rw [h] at hpos
    exact Nat.not_lt_zero 0 hpos
  · intro h
    rw [Inv, inversionPairs, Finset.card_eq_zero]
    ext p
    constructor
    · intro hp
      rw [Finset.mem_filter] at hp
      exact False.elim (h p.1 p.2 hp.2)
    · intro hp
      simp at hp

/-- Positive inversion count is equivalent to existence of an inversion pair. -/
theorem inv_pos_iff_exists_inversion (π : Equiv.Perm (Fin n)) :
    0 < Inv π ↔ ∃ i j : Fin n, IsInversion π i j := by
  classical
  constructor
  · intro h
    rw [Inv] at h
    rcases Finset.card_pos.mp h with ⟨p, hp⟩
    rw [inversionPairs, Finset.mem_filter] at hp
    exact ⟨p.1, p.2, hp.2⟩
  · rintro ⟨i, j, hij⟩
    rw [Inv]
    apply Finset.card_pos.mpr
    refine ⟨(i, j), ?_⟩
    rw [inversionPairs, Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ i, Finset.mem_univ j⟩, hij⟩

/-- If a permutation has no inversions, then it is strictly monotone. -/
theorem strictMono_of_no_inversions (π : Equiv.Perm (Fin n))
    (h : ∀ i j : Fin n, ¬ IsInversion π i j) :
    StrictMono π := by
  intro i j hij
  by_contra hnot
  have hge : π j ≤ π i := le_of_not_gt hnot
  have hne : π j ≠ π i := by
    intro heq
    exact (ne_of_lt hij) (π.injective heq.symm)
  have hgt : π i > π j := lt_of_le_of_ne hge hne
  exact h i j ⟨hij, hgt⟩

/-- A strictly monotone permutation of `Fin n` is the identity permutation. -/
theorem eq_identity_of_strictMono (π : Equiv.Perm (Fin n)) (hπ : StrictMono π) :
    π = ι n := by
  let e : Fin n ≃o Fin n := StrictMono.orderIsoOfSurjective π hπ π.surjective
  ext i
  have he : e i = π i := rfl
  rw [← he]
  simp [ι]

/-- Section 3 basic property: an unsigned permutation has no inversions iff it
is the identity permutation. -/
theorem inv_eq_zero_iff_eq_identity (π : Equiv.Perm (Fin n)) :
    Inv π = 0 ↔ π = ι n := by
  constructor
  · intro h
    exact eq_identity_of_strictMono π
      (strictMono_of_no_inversions π ((inv_eq_zero_iff_no_inversions π).mp h))
  · intro h
    rw [h]
    exact inv_identity_eq_zero

/-- A predicate for adjacent positions in `Fin n`. -/
def Adjacent (i j : Fin n) : Prop :=
  i.val + 1 = j.val

/-- An adjacent inversion is an inversion between consecutive positions. -/
def IsAdjacentInversion (π : Equiv.Perm (Fin n)) (i j : Fin n) : Prop :=
  Adjacent i j ∧ IsInversion π i j

/-- If a permutation of `Fin (m + 1)` has no adjacent inversions, then it is
strictly monotone. -/
theorem strictMono_of_no_adjacent_inversions_succ {m : Nat}
    (π : Equiv.Perm (Fin (m + 1)))
    (h : ∀ i j : Fin (m + 1), ¬ IsAdjacentInversion π i j) :
    StrictMono π := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  by_contra hnot
  have hge : π i.succ ≤ π i.castSucc := le_of_not_gt hnot
  have hne : π i.succ ≠ π i.castSucc := by
    intro heq
    have hidx : i.succ = i.castSucc := π.injective heq
    exact (ne_of_lt (i.castSucc_lt_succ)) hidx.symm
  have hgt : π i.castSucc > π i.succ := lt_of_le_of_ne hge hne
  have hinv : IsInversion π i.castSucc i.succ := by
    exact ⟨i.castSucc_lt_succ, hgt⟩
  have hadj : Adjacent i.castSucc i.succ := by
    simp [Adjacent]
  exact h i.castSucc i.succ ⟨hadj, hinv⟩

/-- Lemma 1 from Section 3: if an unsigned permutation has an inversion, then
it has an adjacent inversion. -/
theorem exists_adjacent_inversion_of_inv_pos (π : Equiv.Perm (Fin n))
    (h : 0 < Inv π) :
    ∃ i j : Fin n, IsAdjacentInversion π i j := by
  classical
  by_contra hnone
  have hNo : ∀ i j : Fin n, ¬ IsAdjacentInversion π i j := by
    intro i j hij
    exact hnone ⟨i, j, hij⟩
  have hEq : π = ι n := by
    cases n with
    | zero =>
        exact Subsingleton.elim π (ι 0)
    | succ m =>
        exact eq_identity_of_strictMono π
          (strictMono_of_no_adjacent_inversions_succ π hNo)
  have hzero : Inv π = 0 := (inv_eq_zero_iff_eq_identity π).mpr hEq
  rw [hzero] at h
  exact Nat.not_lt_zero 0 h

end Sec3
end Miranda2020
