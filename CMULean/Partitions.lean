import Mathlib

/-!
# Conjugate partitions

The number of partitions of `n` into exactly `k` parts equals the number of
partitions of `n` whose largest part is `k`. The proof builds the conjugate
partition, shows conjugation is an involution that swaps "number of parts" and
"largest part", and concludes via a bijection (`card_eq`).
-/

open Finset

namespace PartitionProof

/-- In Fin N, exactly m indices have value < m, provided m ≤ N. -/
theorem card_fin_lt {N : ℕ} (m : ℕ) (h : m ≤ N) :
    (univ.filter (fun i : Fin N => (i : ℕ) < m)).card = m := by
  conv_rhs => rw [← Finset.card_range m]
  apply Finset.card_bij (fun (i : Fin N) _ => i.val)
  · -- maps into range m
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    simpa only [mem_range] using hi
  · -- injective
    intro a _ b _ hab
    exact Fin.val_injective hab
  · -- surjective onto range m
    intro b hb
    simp only [mem_range] at hb
    exact ⟨⟨b, by omega⟩, by simp only [mem_filter, mem_univ, true_and]; exact hb, rfl⟩

variable {n : ℕ}

/-- A partition of n: a non-increasing sequence indexed by Fin (n+1) summing
    to n. Index 0 holds the largest part; unused slots are 0. -/
structure Partition (n : ℕ) where
  a        : Fin (n + 1) → ℕ
  anti     : Antitone a
  sum_eq   : ∑ i, a i = n
  positive : ∀ i, a i ≠ 0 → 0 < a i

namespace Partition

-- AI helped generate this; it is needed so that to prove p = q we need only
-- show p.a = q.a, not anti, sum_eq as well.
@[ext] theorem ext {p q : Partition n} (h : p.a = q.a) : p = q := by
  cases p; cases q; cases h; rfl

/-- No single part exceeds the total. -/
theorem le_n (p : Partition n) (i : Fin (n + 1)) : p.a i ≤ n :=
  calc p.a i ≤ ∑ j, p.a j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (mem_univ i)
    _ = n := p.sum_eq

/-- Number of positive parts. -/
def numParts (p : Partition n) : ℕ := (univ.filter (fun i => 0 < p.a i)).card

/-- Largest part (sits at index 0 since a is antitone). -/
def largest (p : Partition n) : ℕ := p.a 0

/-! ### The conjugate -/

/-- conjFun p j = #{ i | j < a i }, the j-th part of the conjugate. -/
def conjFun (p : Partition n) (j : Fin (n + 1)) : ℕ :=
  (univ.filter (fun i => (j : ℕ) < p.a i)).card

theorem conjFun_anti (p : Partition n) : Antitone (conjFun p) := by
  intro j j' hjj'
  apply Finset.card_le_card
  intro i hi
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  exact lt_of_le_of_lt hjj' hi  -- uses Fin.le defeq val ≤ val; else Fin.le_def.mp hjj'

/-- For an antitone a, the parts exceeding threshold j form an initial segment,
    so "more than k parts exceed j" ⟺ "the k-th part exceeds j". -/
theorem prefix_duality {a : Fin (n + 1) → ℕ} (ha : Antitone a) (j : ℕ) (k : Fin (n + 1)) :
    (k : ℕ) < (univ.filter (fun i => j < a i)).card ↔ j < a k := by
  constructor
  · intro hcard
    by_contra hle
    push_neg at hle                         -- hle : a k ≤ j
    have hsub : (univ.filter (fun i => j < a i))
        ⊆ (univ.filter (fun i : Fin (n+1) => (i : ℕ) < (k : ℕ))) := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      by_contra hik
      push_neg at hik                       -- hik : (k:ℕ) ≤ (i:ℕ)
      have hki : k ≤ i := by rw [Fin.le_def]; omega
      have := ha hki                        -- a i ≤ a k
      omega
    have hc : (univ.filter (fun i : Fin (n+1) => (i : ℕ) < (k : ℕ))).card = (k : ℕ) :=
      card_fin_lt (k : ℕ) (by have := k.isLt; omega)
    have := Finset.card_le_card hsub
    omega
  · intro hj
    have hsub : (univ.filter (fun i : Fin (n+1) => (i : ℕ) < (k : ℕ) + 1))
        ⊆ (univ.filter (fun i => j < a i)) := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      have hik : i ≤ k := by rw [Fin.le_def]; omega
      have := ha hik                        -- a k ≤ a i
      omega
    have hc : (univ.filter (fun i : Fin (n+1) => (i : ℕ) < (k : ℕ) + 1)).card = (k : ℕ) + 1 :=
      card_fin_lt ((k : ℕ) + 1) (by have := k.isLt; omega)
    have := Finset.card_le_card hsub
    omega

/-! ### Conjugation preserves the sum (so conj lands in Partition n) -/

theorem conjFun_sum (p : Partition n) : ∑ j, conjFun p j = n := by
  have step : ∀ i : Fin (n+1),
      (univ.filter (fun j : Fin (n+1) => (j:ℕ) < p.a i)).card = p.a i :=
    fun i => card_fin_lt (p.a i) (by have := p.le_n i; omega)
  calc ∑ j, conjFun p j
      = ∑ j : Fin (n+1), ∑ i : Fin (n+1), (if (j:ℕ) < p.a i then 1 else 0) := by
        simp only [conjFun, Finset.card_filter]
    _ = ∑ i : Fin (n+1), ∑ j : Fin (n+1), (if (j:ℕ) < p.a i then 1 else 0) :=
        Finset.sum_comm
    _ = ∑ i : Fin (n+1), p.a i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.card_filter]; exact step i
    _ = n := p.sum_eq

-- positivity
theorem conjFun_pos (p : Partition n) :
    ∀ j, conjFun p j ≠ 0 → 0 < conjFun p j :=
  fun _ h => Nat.pos_of_ne_zero h

/-- The conjugate partition. -/
def conj (p : Partition n) : Partition n where
  a        := conjFun p
  anti     := conjFun_anti p
  sum_eq   := conjFun_sum p
  positive := conjFun_pos p

/-! ### Conjugation swaps largest and numParts -/

/-- Largest part of the conjugate = number of parts of the original (Lemma 6). -/
theorem largest_conj (p : Partition n) : (conj p).largest = p.numParts := by
  simp only [Partition.largest, Partition.conj, conjFun, Partition.numParts, Fin.val_zero]
  -- the two sides differ only in a hidden decidability instance; `congr` closes that
  congr

/-- Number of parts of the conjugate = largest part of the original. -/
theorem numParts_conj (p : Partition n) : (conj p).numParts = p.largest := by
  simp only [numParts, largest]
  have key : ∀ j : Fin (n + 1), (0 < (conj p).a j) ↔ ((j : ℕ) < p.a 0) := by
    intro j
    have h := prefix_duality p.anti (j : ℕ) (0 : Fin (n + 1))
    simpa [conj, conjFun, Fin.val_zero] using h
  rw [Finset.filter_congr (fun j _ => key j)]
  exact card_fin_lt (p.a 0) (by have := p.le_n 0; omega)

/-! ### Conjugate is its own inverse -/

theorem conj_conj (p : Partition n) : conj (conj p) = p := by
  ext i
  have key : ∀ j : Fin (n + 1), ((i : ℕ) < (conj p).a j) ↔ ((j : ℕ) < p.a i) := by
    intro j
    have h := prefix_duality p.anti (j : ℕ) i
    simpa [conj, conjFun] using h
  have hset : (univ.filter (fun j : Fin (n + 1) => (i : ℕ) < (conj p).a j))
      = (univ.filter (fun j : Fin (n + 1) => (j : ℕ) < p.a i)) := by
    ext j; simp only [mem_filter, mem_univ, true_and]; exact key j
  calc (conj (conj p)).a i
      = (univ.filter (fun j : Fin (n + 1) => (i : ℕ) < (conj p).a j)).card := rfl
    _ = (univ.filter (fun j : Fin (n + 1) => (j : ℕ) < p.a i)).card := by rw [hset]
    _ = p.a i := card_fin_lt (p.a i) (by have := p.le_n i; omega)

theorem conj_bijOn (n k : ℕ) :
    Set.BijOn (conj (n := n)) {p | p.numParts = k} {p | p.largest = k} := by
  have hmaps : Set.MapsTo (conj (n := n)) {p | p.numParts = k} {p | p.largest = k} := by
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    rw [largest_conj]; exact hp
  have hinj : Set.InjOn (conj (n := n)) {p | p.numParts = k} := by
    intro p _ q _ h
    have := congrArg conj h
    simpa [conj_conj] using this
  have hsurj : Set.SurjOn (conj (n := n)) {p | p.numParts = k} {p | p.largest = k} := by
    intro q hq
    simp only [Set.mem_setOf_eq] at hq
    have hmem : conj q ∈ {p : Partition n | p.numParts = k} := by
      simp only [Set.mem_setOf_eq]
      rw [numParts_conj]; exact hq
    exact ⟨conj q, hmem, conj_conj q⟩
  exact ⟨hmaps, hinj, hsurj⟩

theorem card_eq (n k : ℕ) :
    {p : Partition n | p.numParts = k}.ncard = {p : Partition n | p.largest = k}.ncard := by
  have hb := conj_bijOn n k  -- the conjugate function is a bijection on these two sets
  -- (`Set.ncard_image_of_injOn` was renamed to `Set.InjOn.ncard_image` in current Mathlib)
  rw [← hb.image_eq, hb.injOn.ncard_image]

end Partition
end PartitionProof
