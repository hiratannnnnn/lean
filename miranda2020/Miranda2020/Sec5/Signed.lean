import Miranda2020.Sec4.Entropy

set_option linter.style.header false

/-!
# Miranda 2020, Section 5: signed permutations and the score potential

A signed permutation is represented by an unsigned permutation of positions to
absolute values, together with a Boolean sign bit for each position. `true`
means positive and `false` means negative.
-/

namespace Miranda2020
namespace Sec5

open Sec3 Sec4

variable {n : Nat}

/-- A signed permutation: an absolute-value permutation plus a sign at each
position. -/
structure SignedPerm (n : Nat) where
  abs : Equiv.Perm (Fin n)
  pos : Fin n → Bool

namespace SignedPerm

/-- The sorted signed permutation `(+1 +2 ... +n)`. -/
def identity (n : Nat) : SignedPerm n where
  abs := Sec3.ι n
  pos := fun _ => true

/-- The displacement entropy of the element at position `i`, using its absolute
value. -/
def elemEnt (π : SignedPerm n) (i : Fin n) : Nat :=
  Sec4.elemEnt π.abs i

/-- The total entropy of a signed permutation, ignoring signs. -/
noncomputable def Ent (π : SignedPerm n) : Nat :=
  Sec4.Ent π.abs

/-- Inversions compare absolute values only. -/
def IsInversion (π : SignedPerm n) (i j : Fin n) : Prop :=
  Sec3.IsInversion π.abs i j

/-- Inversion pairs of the absolute-value permutation. -/
noncomputable def inversionPairs (π : SignedPerm n) : Finset (Fin n × Fin n) :=
  Sec3.inversionPairs π.abs

/-- Inversion count of the absolute-value permutation. -/
noncomputable def Inv (π : SignedPerm n) : Nat :=
  Sec3.Inv π.abs

/-- Elements that are negative and have even entropy. This is `E⁻_even`. -/
noncomputable def EMinusEven (π : SignedPerm n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => π.pos i = false ∧ Even (π.elemEnt i)

/-- Elements that are positive and have odd entropy. This is `E⁺_odd`. -/
noncomputable def EPlusOdd (π : SignedPerm n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => π.pos i = true ∧ Odd (π.elemEnt i)

/-- The Section 5 potential underlying the score function `φ`. -/
noncomputable def PhiPotential (π : SignedPerm n) : Nat :=
  2 * π.Inv + (π.EMinusEven).card + (π.EPlusOdd).card

/-- The identity signed permutation has no inversions. -/
theorem inv_identity_eq_zero : (identity n).Inv = 0 := by
  simp [Inv, identity, Sec3.inv_identity_eq_zero]

/-- The identity signed permutation has empty `E⁻_even`. -/
theorem eMinusEven_identity_eq_empty : EMinusEven (identity n) = ∅ := by
  classical
  ext i
  simp [EMinusEven, identity]

/-- The identity signed permutation has empty `E⁺_odd`. -/
theorem ePlusOdd_identity_eq_empty : EPlusOdd (identity n) = ∅ := by
  classical
  ext i
  simp [EPlusOdd, identity, elemEnt, Sec4.elemEnt_identity_eq_zero]

/-- The Section 5 potential is zero at the identity signed permutation. -/
theorem phiPotential_identity_eq_zero : PhiPotential (identity n) = 0 := by
  simp [PhiPotential, inv_identity_eq_zero, eMinusEven_identity_eq_empty,
    ePlusOdd_identity_eq_empty]

/-- If the absolute values are sorted and all signs are positive, then the
signed permutation is the identity. -/
theorem eq_identity_of_abs_eq_identity_of_all_positive (π : SignedPerm n)
    (habs : π.abs = Sec3.ι n) (hpos : ∀ i : Fin n, π.pos i = true) :
    π = identity n := by
  cases π with
  | mk abs pos =>
      have habs' : abs = Sec3.ι n := habs
      have hposFun : pos = fun _ : Fin n => true := by
        funext i
        exact hpos i
      subst habs'
      subst hposFun
      rfl


/-- If the Section 5 potential is zero, then the absolute-value inversion count
is zero. -/
theorem inv_eq_zero_of_phiPotential_eq_zero (π : SignedPerm n)
    (h : π.PhiPotential = 0) :
    π.Inv = 0 := by
  rw [PhiPotential] at h
  omega

/-- If the Section 5 potential is zero, then `E⁻_even` is empty. -/
theorem eMinusEven_eq_empty_of_phiPotential_eq_zero (π : SignedPerm n)
    (h : π.PhiPotential = 0) :
    π.EMinusEven = ∅ := by
  rw [PhiPotential] at h
  apply Finset.card_eq_zero.mp
  omega

/-- If the Section 5 potential is zero, then `E⁺_odd` is empty. -/
theorem ePlusOdd_eq_empty_of_phiPotential_eq_zero (π : SignedPerm n)
    (h : π.PhiPotential = 0) :
    π.EPlusOdd = ∅ := by
  rw [PhiPotential] at h
  apply Finset.card_eq_zero.mp
  omega


/-- Zero Section 5 potential forces the absolute-value permutation to be sorted. -/
theorem abs_eq_identity_of_phiPotential_eq_zero (π : SignedPerm n)
    (h : π.PhiPotential = 0) :
    π.abs = Sec3.ι n := by
  exact (Sec3.inv_eq_zero_iff_eq_identity π.abs).mp
    (inv_eq_zero_of_phiPotential_eq_zero π h)


/-- Zero Section 5 potential forces every sign to be positive. -/
theorem all_positive_of_phiPotential_eq_zero (π : SignedPerm n)
    (h : π.PhiPotential = 0) :
    ∀ i : Fin n, π.pos i = true := by
  classical
  intro i
  by_cases hp : π.pos i = true
  · exact hp
  · have hneg : π.pos i = false := by
      cases hpi : π.pos i <;> simp [hpi] at hp ⊢
    have habs : π.abs = Sec3.ι n := abs_eq_identity_of_phiPotential_eq_zero π h
    have hent : π.elemEnt i = 0 := by
      rw [elemEnt, habs]
      exact Sec4.elemEnt_identity_eq_zero i
    have hmem : i ∈ π.EMinusEven := by
      rw [EMinusEven, Finset.mem_filter]
      exact ⟨Finset.mem_univ i, hneg, by rw [hent]; exact ⟨0, by rfl⟩⟩
    have hempty : π.EMinusEven = ∅ := eMinusEven_eq_empty_of_phiPotential_eq_zero π h
    rw [hempty] at hmem
    simp at hmem

/-- Section 5 basic property: the score potential is zero iff the signed
permutation is sorted. -/
theorem phiPotential_eq_zero_iff_eq_identity (π : SignedPerm n) :
    π.PhiPotential = 0 ↔ π = identity n := by
  constructor
  · intro h
    exact eq_identity_of_abs_eq_identity_of_all_positive π
      (abs_eq_identity_of_phiPotential_eq_zero π h)
      (all_positive_of_phiPotential_eq_zero π h)
  · intro h
    rw [h]
    exact phiPotential_identity_eq_zero

end SignedPerm
end Sec5
end Miranda2020
