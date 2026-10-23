import Mathlib

/-!
# Integer versions of the well-ordering principle and the division algorithm

* `wellOr` — every nonempty set of natural numbers has a least element.
* `wellOrInt` — every nonempty set of integers that is bounded below has a least element.
* `divalgoint` — the division algorithm over `ℤ` with a positive divisor.
* `wellOrUnique_int` — the least element in `wellOrInt` is unique.
-/

-- Every nonempty set of natural numbers has a least element.
theorem wellOr (E : Set ℕ) (hne : E ≠ ∅) : ∃ x ∈ E, ∀ y ∈ E, x ≤ y := by
  obtain ⟨e, he⟩ := Set.nonempty_iff_ne_empty.mpr hne
  classical
  refine ⟨Nat.find ⟨e, he⟩, Nat.find_spec ⟨e, he⟩, fun y hy => Nat.find_min' _ hy⟩

-- A nonempty set of integers that is bounded below has a least element.
-- (ℤ is not well-ordered, so the lower-bound hypothesis is essential.)
theorem wellOrInt (E : Set ℤ) (hne : E ≠ ∅) (hbdd : ∃ b, ∀ y ∈ E, b ≤ y) :
    ∃ x ∈ E, ∀ y ∈ E, x ≤ y := by
  obtain ⟨b, hb⟩ := hbdd
  let E' : Set ℕ := {n | b + (n : ℤ) ∈ E}
  have hne' : E' ≠ ∅ := by
    obtain ⟨e, he⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hmem : (e - b).toNat ∈ E' := by
      have key : b + ((e - b).toNat : ℤ) = e := by
        rw [Int.toNat_of_nonneg (by linarith [hb e he] : (0:ℤ) ≤ e - b)]; ring
      have hmem' := key.symm ▸ he
      exact hmem'
    exact (Set.nonempty_of_mem hmem).ne_empty
  obtain ⟨x₀, hx₀E', hx₀min⟩ := wellOr E' hne'
  use b + (x₀ : ℤ), hx₀E'
  intro y hy
  have hmem : (y - b).toNat ∈ E' := by
    have key : b + ((y - b).toNat : ℤ) = y := by
      rw [Int.toNat_of_nonneg (by linarith [hb y hy] : (0:ℤ) ≤ y - b)]; ring
    have hmem' := key.symm ▸ hy
    exact hmem'
  have hle : x₀ ≤ (y - b).toNat := hx₀min _ hmem
  have hcast : (x₀ : ℤ) ≤ ((y - b).toNat : ℤ) := by exact_mod_cast hle
  rw [Int.toNat_of_nonneg (by linarith [hb y hy] : (0:ℤ) ≤ y - b)] at hcast
  linarith

-- Division algorithm over ℤ.
theorem divalgoint (a d : ℤ) : d > 0 → ∃ q r : ℤ, a = d*q + r ∧ 0 ≤ r ∧ r < d := by
  intro dpos
  let E : Set ℤ := {m | 0 ≤ m ∧ ∃ z : ℤ, m = a - d*z}
  have hne : E ≠ ∅ := by
    have h0 : 0 ≤ a + d * |a| := by
      rcases le_or_gt 0 a with ha | ha
      · have : 0 ≤ d * |a| := mul_nonneg (le_of_lt dpos) (abs_nonneg a)
        linarith
      · rw [abs_of_neg ha]
        have key : 0 ≤ (d - 1) * (-a) := mul_nonneg (by omega) (by linarith)
        nlinarith [key]
    have hmem : (a + d * |a|) ∈ E := ⟨h0, -|a|, by ring⟩
    exact (Set.nonempty_of_mem hmem).ne_empty
  have hbdd : ∃ b, ∀ y ∈ E, b ≤ y := ⟨0, fun y hy => hy.1⟩
  obtain ⟨r, hrE, hrmin⟩ := wellOrInt E hne hbdd
  obtain ⟨hr0, q, hq⟩ := hrE
  use q, r, (by linarith [hq]), hr0
  by_contra hrd
  push_neg at hrd
  have hr1mem : (r - d) ∈ E := ⟨by linarith, q + 1, by linear_combination hq⟩
  have hmin := hrmin (r - d) hr1mem
  linarith

-- Integer version of wellOrUnique:
-- a nonempty set of integers bounded below has a unique least element.
theorem wellOrUnique_int (E : Set ℤ) (hne : E ≠ ∅) (hbdd : ∃ b, ∀ y ∈ E, b ≤ y) :
    ∃! x ∈ E, ∀ y ∈ E, x ≤ y := by
  obtain ⟨x, hx⟩ := wellOrInt E hne hbdd
  use x
  simp
  constructor
  exact hx -- existence from wellOrInt
  intro y yinE hy1
  exact le_antisymm (hy1 x hx.left) (hx.right y yinE) -- uniqueness
